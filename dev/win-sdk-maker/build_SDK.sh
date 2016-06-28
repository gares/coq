#!/bin/bash

# Author: Michael Soegtrop, Intel Mobile Communications
# With very valuable help on building GTK from
#   https://wiki.gnome.org/Projects/GTK+/Win32/MSVCCompilationOfGTKStack
#   http://www.gaia-gis.it/spatialite-3.0.0-BETA/mingw64_how_to.html

###################### Script safety and debugging settings ######################

set -o nounset
set -o errexit
#set -x

# Set this to 1 if all module directories shall be removed before build (no incremental make)
RMDIR_BEFORE_BUILD=1

###################### NOTES #####################

# - This file goes together with MakeCoq_ForMigngw_UsingCygwin.bat, which sets up cygwin
#   with all required packages and then calls this script.
#
# - This script uses set -o errexit, so if anything fails, the script will stop
#
# - cygwin provided mingw64 packages like mingw64-x86_64-zlib are installed to
#   /usr/$TARGET_ARCH/sys-root/mingw, so we use this as install prefix
#
# - if mingw64-x86_64-pkg-config is installed BEFORE building libpng or pixman,
#   the .pc files are properly created in /usr/$TARGET_ARCH/sys-root/mingw/lib/pkgconfig
#
# - pango and some others uses pkg-config executable names without path, which doesn't work in cross compile mode
#   There are several possible solutions
#     1.) patch build files to get the prefix from pkg-config und use $prefix/bin/ as path
#         - doesn't work for pango because automake goes wild
#         - mingw tools are not able to handle cygwin path (they need absolute windows paths)
#     2.) export PATH=$PATH:/usr/$TARGET_ARCH/sys-root/mingw/bin
#         - a bit dangerous because this exposes much more than required
#         - mingw tools are not able to handle cygwin path (they need absolute windows paths)
#     3.) Install required tools via cygwin modules libglib2.0-devel and libgdk_pixbuf2.0-devel
#         - Possibly version compatibility issues
#         - Possibly mingw/cygwin compatibility isses, e.g. when building font or terminfo databases
#     4.) Build required tools for mingw and cygwin
#         - Possibly mingw/cygwin compatibility isses, e.g. when building font or terminfo databases
#
#   We use method 3 below
#
# - It is tricky to build 64 bit binaries with 32 bit cross tools and vice versa
#   This is because the linker needs to load DLLs from C:\windows\system32, which contains
#   both 32 bit and 64 bit DLLs, and which one you get depends by some black magic on if the using
#   app is a 32 bit or 64 bit app. So better build 32 bit mingw with 32 bit cygwin and 64 with 64.
#   Alternatively the required 32 bit or 64 bit DLLs need ot be copied with a 32 bit/64bit cp to some
#   folder withotu such black magic. 


###################### PARAMETERS #####################

# The OS on which the build of the tool/lib runs
BUILD=`gcc -dumpmachine`

# The OS on which the tool runs
# "`find /bin -name "*mingw32-gcc.exe"`" -dumpmachine
HOST=$TARGET_ARCH

# The OS for which the tool creates code/for which the libs are
TARGET=$TARGET_ARCH

# sysroot prefix for the above /build/host/target combination
PREFIX=/usr/$TARGET_ARCH/sys-root/mingw

export  PKG_CONFIG_PATH=/usr/$TARGET_ARCH/sys-root/mingw/lib/pkgconfig

###################### UTILITY FUNCTIONS #####################

# ------------------------------------------------------------------------------
# Prepare a module build
# - check if build is already done (name.finished file exists) - if so return 1
# - create name.started
# - wget tar ball
# - create folder
# - cd to folder and extract tar ball
# - create bin_special subfolder and add it to $PATH
# - remember things for build_post
# 
# Parameters
# $1 file server name including protocol prefix
# $2 file name (without extension)
# $3 file extension
# $4 [optional] number of path levels to strip from tar (usually 1)
# $5 [optional] module name (if different from archive)
# ------------------------------------------------------------------------------

function build_prep {
  # Handle optional parameters
  if [ "$#" -ge 4 ] ; then
    strip=$4
  else
    strip=1
  fi

  if [ "$#" -ge 5 ] ; then
    name=$5
  else
    name=$2
  fi
  
  # Check if build was done before
  if [ ! -f $name.finished ] ; then
    BUILD_PACKAGE_NAME=$name
    BUILD_OLDPATH=$PATH
    BUILD_OLDPWD=`pwd`

    touch $name.started
    if [ ! -f $name.$3 ] ; then
      if [ -f $LOCAL_REPOSITORY_CFMT/$2.$3 ] ; then
        cp $LOCAL_REPOSITORY_CFMT/$2.$3 .
      else
        wget -nc $1/$2.$3
      fi
      mv $2.$3 $name.$3
    fi
    if [ $RMDIR_BEFORE_BUILD -eq 1 ] ; then
      rm -f -r $name
    fi
    mkdir -p $name
    cd $name
    if [ "$3" == "zip" ] ; then
      unzip ../$name.$3
      if [ "$strip" == "1" ] ; then
        # Ok, this is dirty, but it works and it fails if there are name clashes
        mv */* .
      else
        echo "Unzip strip count not supported"
        return 1
      fi
    else
      tar xaf ../$name.$3 --strip $strip
    fi
    
    # Create a folder and add it to path, where we can put special binaries
    # The path is restored in build_post
    mkdir bin_special
    PATH=`pwd`/bin_special:$PATH
    
    return 0
  else  
    return 1
  fi
}

# ------------------------------------------------------------------------------
# Finalize a module build
# - create name.finished
# - go back to base folder
# ------------------------------------------------------------------------------

function build_post {
  if [ ! -f $BUILD_PACKAGE_NAME.finished ]; then
    cd $BUILD_OLDPWD
    touch $BUILD_PACKAGE_NAME.finished
    PATH=$BUILD_OLDPATH
  fi
}

# ------------------------------------------------------------------------------
# Build and install a module using the standard configure/make/make install process
# - prepare build (as above)
# - configure
# - make
# - make install
# - finalize build (as above)
#
# parameters
# $1 file server name including protocol prefix
# $2 file name (without extension)
# $3 file extension
# $4 patch function to call between untar and configure (or true if none)
# $5.. extra configure arguments
# ------------------------------------------------------------------------------

function build_conf_make_inst {
  if build_prep $1 $2 $3 ; then
    (
    $4
    ./configure --build=$BUILD --host=$HOST --target=$TARGET --prefix=$PREFIX "${@:5}"
    make $MAKE_OPT
    make install
    ) >../$BUILD_PACKAGE_NAME.log 2>&1 
    # make clean
    build_post
  fi
}


###################### MODULE BUILD FUNCTIONS #####################

##### LIBPNG #####

function make_libpng {
  build_conf_make_inst  http://prdownloads.sourceforge.net/libpng  libpng-1.6.18  tar.gz  true
}

##### PIXMAN #####

function make_pixman {
  build_conf_make_inst  http://cairographics.org/releases  pixman-0.32.8  tar.gz  true
}

##### FREETYPE #####

function make_freetype {
  build_conf_make_inst  http://sourceforge.net/projects/freetype/files/freetype2/2.6.1  freetype-2.6.1  tar.bz2  true
}

##### EXPAT #####

function make_expat {
  build_conf_make_inst  http://sourceforge.net/projects/expat/files/expat/2.1.0  expat-2.1.0  tar.gz  true
}

##### FONTCONFIG #####

function make_fontconfig {
  make_freetype
  make_expat
  # CONFIGURE PARAMETERS
  # build/install fails without --disable-docs 
  build_conf_make_inst  http://www.freedesktop.org/software/fontconfig/release  fontconfig-2.11.94  tar.gz  true  --disable-docs
}

##### ICONV #####

function make_libiconv {
  build_conf_make_inst  http://ftp.gnu.org/pub/gnu/libiconv  libiconv-1.14  tar.gz  true
}

##### UNISTRING #####

function make_libunistring {
  build_conf_make_inst  http://ftp.gnu.org/gnu/libunistring  libunistring-0.9.5  tar.xz  true
}

##### NCURSES #####

function make_ncurses {
  # NOTE: ncurses is not required below. This is just kept for documentary purposes in case I need it later.
  #
  # NOTE: make install fails building the terminfo database because
  # : ${TIC_PATH:=unknown} in run_tic.sh
  # As a result pkg-config .pc files are not generated
  # Also configure of gettext gives two "considers"
  # checking where terminfo library functions come from... not found, consider installing GNU ncurses
  # checking where termcap library functions come from... not found, consider installing GNU ncurses
  # gettext make/make install work anyway
  #
  # CONFIGURE PARAMETERS
  # --enable-term-driver --enable-sp-funcs is rewuired for mingw (see README.MinGW)
  # additional changes 
  # ADD --with-pkg-config
  # ADD --enable-pc-files
  # ADD --without-manpages
  # REM --with-pthread
  build_conf_make_inst  http://ftp.gnu.org/gnu/ncurses  ncurses-5.9  tar.gz  true  --disable-home-terminfo --enable-reentrant --enable-sp-funcs --enable-term-driver --enable-interop --with-pkg-config --enable-pc-files --without-manpages
}

##### GETTEXT #####

function make_gettext {
  # Cygwin packet dependencies: (not 100% sure) libiconv-devel,libunistring-devel,libncurses-devel
  # Cygwin packet dependencies for gettext users: (not 100% sure) gettext-devel,libgettextpo-devel
  # gettext configure complains that ncurses is also required, but it builds without it
  # Ncurses is tricky to install/configure for mingw64, so I dropped ncurses
  make_libiconv
  make_libunistring
  build_conf_make_inst  http://ftp.gnu.org/pub/gnu/gettext  gettext-0.19  tar.gz  true
}

##### LIBFFI #####

function make_libffi {
  # NOTE: The official download server is down  ftp://sourceware.org/pub/libffi/libffi-3.2.1.tar.gz
  build_conf_make_inst  http://www.mirrorservice.org/sites/sourceware.org/pub/libffi  libffi-3.2.1  tar.gz  true
}

##### LIBEPOXY #####

function make_libepoxy {
  build_conf_make_inst  https://github.com/anholt/libepoxy/releases/download/v1.3.1  libepoxy-1.3.1  tar.bz2  true
}

##### GLIB #####

function patch_glib {
  # glocalefile.h uses _wstat32i64, which is in libmsvcr110, so add this
  # sed -i.bak 's/G_LIBS_EXTRA="-lws2_32 -lole32 -lwinmm -lshlwapi"/G_LIBS_EXTRA="-lws2_32 -lole32 -lwinmm -lshlwapi -lmsvcr110"/' configure
  # The above dosn't work. It compiles and links, but it crashes then in msvcrt
  patch -p1 -i ../glib-2.46.0.patch
}

function make_glib {
  # Cygwin packet dependencies: mingw64-x86_64-zlib
  make_gettext
  make_libffi
  build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/glib/2.46  glib-2.46.0  tar.xz  patch_glib
}

##### ATK #####

function make_atk {
  make_gettext
  make_glib
  build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/atk/2.18  atk-2.18.0  tar.xz  true
}

##### PIXBUF #####

function make_gdk-pixbuf {
  # Cygwin packet dependencies: mingw64-x86_64-zlib
  make_libpng
  make_gettext
  make_glib
  # CONFIGURE PARAMETERS
  # --with-included-loaders=yes statically links the image file format handlers
  # This avoids "Cannot open pixbuf loader module file '/usr/x86_64-w64-mingw32/sys-root/mingw/lib/gdk-pixbuf-2.0/2.10.0/loaders.cache': No such file or directory"
  build_conf_make_inst  http://ftp.gnome.org/pub/GNOME/sources/gdk-pixbuf/2.32  gdk-pixbuf-2.32.1  tar.xz  true  --with-included-loaders=yes 
}

##### CAIRO #####

function make_cairo {
  # Cygwin packet dependencies: mingw64-x86_64-zlib
  make_libpng
  make_glib
  make_pixman
  make_fontconfig
  build_conf_make_inst  http://cairographics.org/releases  cairo-1.14.2  tar.xz  true
}

##### PANGO #####

function make_pango {
  make_cairo
  make_glib
  make_fontconfig
  build_conf_make_inst  http://ftp.gnome.org/pub/GNOME/sources/pango/1.38  pango-1.38.0  tar.xz  true
}

##### GTK2 #####

function patch_gtk2 {
  rm gtk/gtk.def
}

function make_gtk2 {
  # Cygwin packet dependencies: gtk-update-icon-cache
  make_glib
  make_atk
  make_pango
  make_gdk-pixbuf
  make_cairo
  build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/gtk+/2.24  gtk+-2.24.28  tar.xz  patch_gtk2
}

##### GTK3 #####

function make_gtk3 {
  make_glib
  make_atk
  make_pango
  make_gdk-pixbuf
  make_cairo
  make_libepoxy
  build_conf_make_inst  http://ftp.gnome.org/pub/gnome/sources/gtk+/3.16  gtk+-3.16.7  tar.xz  true

  # make all incl. tests and examples runs trhough fine
  # make install fails with issue with 
  # 
  # make[5]: Entering directory '/home/soegtrop/GTK/gtk+-3.16.7/demos/gtk-demo'
  # test -n "" || ../../gtk/gtk-update-icon-cache --ignore-theme-index --force "/usr/x86_64-w64-mingw32/sys-root/mingw/share/icons/hicolor"
  # gtk-update-icon-cache.exe: Failed to open file /usr/x86_64-w64-mingw32/sys-root/mingw/share/icons/hicolor/.icon-theme.cache : No such file or directory
  # Makefile:1373: recipe for target 'install-update-icon-cache' failed
  # make[5]: *** [install-update-icon-cache] Error 1
  # make[5]: Leaving directory '/home/soegtrop/GTK/gtk+-3.16.7/demos/gtk-demo'
}

##### LIBXML2 #####

function make_libxml2 {
  # Cygwin packet dependencies: libtool automake
  # Note: latest release version 2.9.2 fails during configuring lzma, so using 2.9.1
  # Note: python binding requires <sys/select.h> which doesn't exist on cygwin
  if build_prep https://git.gnome.org/browse/libxml2/snapshot  libxml2-2.9.1  tar.xz ; then
    (
    ./autogen.sh --build=$BUILD --host=$HOST --target=$TARGET --prefix=$PREFIX --without-python
    make $MAKE_OPT all
    make install
    ) >../$BUILD_PACKAGE_NAME.log  2>&1
    build_post
  fi
}

##### GTK-SOURCEVIEW2 #####

function patch_gtk_sourceview2 {
  patch -p1 -i ../gtksourceview-2.11.2.patch
}

function make_gtk_sourceview2 {
  # Cygwin packet dependencies: intltool
  # gtksourceview-2.11.2 requires GTK2
  # gtksourceview-2.91.9 requires GTK3
  # => We use gtksourceview-2.11.2 which seems to be the newest GTK2 based one
  make_gtk2
  make_libxml2
  build_conf_make_inst  https://download.gnome.org/sources/gtksourceview/2.11  gtksourceview-2.11.2  tar.bz2  patch_gtk_sourceview2
}

##### FLEXDLL FLEXLINK #####

function install_flexdll {
  cp flexdll.h /usr/$TARGET_ARCH/sys-root/mingw/include
  if [ "$BITS" = "32" ]; then
    cp flexdll*_mingw.o /usr/$TARGET_ARCH/bin
    cp flexdll*_mingw.o $RESULT_INSTALLDIR_CFMT/bin
  else
    cp flexdll*_mingw64.o /usr/$TARGET_ARCH/bin
    cp flexdll*_mingw64.o $RESULT_INSTALLDIR_CFMT/bin
  fi
}

function install_flexlink {
  cp flexlink.exe /usr/$TARGET_ARCH/bin
    
  cp flexlink.exe $RESULT_INSTALLDIR_CFMT/bin
}

function make_flexdll {
  if build_prep http://alain.frisch.fr/flexdll flexdll-0.34 tar.gz 1 flexdll-0.34-dll; then
    make $MAKE_OPT build_mingw64
    install_flexdll
    # make clean
    build_post
  fi
}

function make_flexlink {
  if build_prep http://alain.frisch.fr/flexdll flexdll-0.34 tar.gz 1 flexdll-0.34-exe; then
    make $MAKE_OPT flexlink.exe
    install_flexlink
    # make clean
    build_post
  fi
}

function get_flex_dll_bin {
  if build_prep http://alain.frisch.fr/flexdll flexdll-bin-0.34 zip 1 ; then
    install_flexdll
    install_flexlink
    build_post
  fi
}

##### OCAML #####

# This is from experiments with configure 64 bit mingw ocaml in cygwin
#
# make runtest ignore Windows CRs
# cp ~/runtest config/auto-aux
#
# Replace long with long long in all C files
# find . \( -name "*.c" -o -name "*.h" \) -exec sed -i "s/\blong\b/long long/g" {} \;
# Undo any long long -> long long long long replaces
# find . \( -name "*.c" -o -name "*.h" \) -exec sed -i "s/\blong long long\b/long long/g" {} \;
# find . \( -name "*.c" -o -name "*.h" \) -exec sed -i "s/\blong long long\b/long long/g" {} \;

function make_ocaml {
  get_flex_dll_bin
  if build_prep http://caml.inria.fr/pub/distrib/ocaml-4.02 ocaml-4.02.3 tar.gz 1 ; then
    (
    # See README.win32
    cp config/m-nt.h config/m.h
    cp config/s-nt.h config/s.h
    if [ "$BITS" = "32" ]; then
    	cp config/Makefile.mingw config/Makefile
    else
	cp config/Makefile.mingw64 config/Makefile
    fi
    sed -i "s|PREFIX=.*|PREFIX=$RESULT_INSTALLDIR_MFMT|" config/Makefile
    export PATH=$PATH:/usr/$TARGET_ARCH/bin
    
    # Note: ocaml doesn't support -j 8, so don't pass MAKE_OPT
    make -f Makefile.nt world
    make -f Makefile.nt bootstrap
    make -f Makefile.nt opt
    make -f Makefile.nt opt.opt
    make -f Makefile.nt install
    ) >../$BUILD_PACKAGE_NAME.log  2>&1

    # make clean
    build_post
  fi
}

##### FINDLIB Ocaml library manager #####

function make_findlib {
  make_ocaml
  if build_prep http://download.camlcity.org/download findlib-1.5.6 tar.gz 1 ; then
    (
    ./configure -bindir $RESULT_INSTALLDIR_MFMT\\bin -sitelib $RESULT_INSTALLDIR_MFMT\\lib\\site-lib -config $RESULT_INSTALLDIR_MFMT\\etc\\findlib.conf
    # Note: findlib doesn't support -j 8, so don't pass MAKE_OPT
    make all
    make opt
    make install
    ) >../$BUILD_PACKAGE_NAME.log  2>&1
    build_post
  fi
}

##### MENHIR Ocaml Parser Generator #####

function make_menhir {
  make_ocaml
  make_findlib
  # if build_prep http://gallium.inria.fr/~fpottier/menhir menhir-20151112 tar.gz 1 ; then
  if build_prep http://gallium.inria.fr/~fpottier/menhir menhir-20151012 tar.gz 1 ; then
    (
    # Note: menhir doesn't support -j 8, so don't pass MAKE_OPT
    make PREFIX=$RESULT_INSTALLDIR_MFMT all
    make PREFIX=$RESULT_INSTALLDIR_MFMT install
    ) >../$BUILD_PACKAGE_NAME.log  2>&1
    build_post
  fi
}

##### CAMLP4 Ocaml Preprocessor #####

function make_camlp4 {
  make_ocaml
  make_findlib
  if build_prep https://github.com/ocaml/camlp4/archive 4.02+6 tar.gz 1 camlp4-4.02+6 ; then
    (
    # See https://github.com/ocaml/camlp4/issues/41#issuecomment-112018910
    patch -p1 -i ../camlp4-4.02+6.patch
    ./configure
    # Note: camlp4 doesn't support -j 8, so don't pass MAKE_OPT
    make all
    make install
    ) >../$BUILD_PACKAGE_NAME.log  2>&1
    build_post
  fi
}

##### CAMLP5 Ocaml Preprocessor #####

function make_camlp5 {
  make_ocaml
  make_findlib
  if build_prep http://camlp5.gforge.inria.fr/distrib/src camlp5-6.14 tgz 1 ; then
    (
    ./configure
    # Somehow my virus scanner has the boot.new/SAVED directory locked after the move for a second => repeat until success
    sed -i 's/mv boot.new boot/until mv boot.new boot; do sleep 1; done/' Makefile
    make $MAKE_OPT world.opt
    make install
    # For some reason gramlib.a is not copied, but it is required by Coq
    cp lib/gramlib.a $RESULT_INSTALLDIR_MFMT/lib/camlp5/
    ) >../$BUILD_PACKAGE_NAME.log  2>&1
    build_post
  fi
}

##### LABLGTK Ocaml GTK binding #####

# Note: when rebuilding lablgtk ny deleting the .finished file,
# also delete <root>\usr\x86_64-w64-mingw32\sys-root\mingw\lib\site-lib
# Otherwise make install fails

function make_lablgtk {
  make_ocaml
  make_findlib
  make_camlp4
  if build_prep https://forge.ocamlcore.org/frs/download.php/1479 lablgtk-2.18.3 tar.gz 1 ; then
    (
    patch -p1 -i ../lablgtk-2.18.3.patch
    # configure should be fixed to search for $TARGET_ARCH-pkg-config.exe
    cp /bin/$TARGET_ARCH-pkg-config.exe  bin_special/pkg-config.exe
    sed  -i 's/OCAMLFIND=no//' configure
    ./configure --build=$BUILD --host=$HOST --target=$TARGET --prefix=$PREFIX
    # See https://sympa.inria.fr/sympa/arc/caml-list/2015-10/msg00204.html
    make $MAKE_OPT world || true
    $TARGET_ARCH-strip.exe --strip-unneeded src/dlllablgtk2.dll
    make $MAKE_OPT world
    make install
    ) >../$BUILD_PACKAGE_NAME.log  2>&1
    build_post
  fi
}

##### COQ #####

function make_coq {
  make_ocaml
  make_lablgtk
  make_camlp5
  #if build_prep https://coq.inria.fr/distrib/V8.5beta2/files coq-8.5beta2 tar.gz ; then
  #if build_prep https://github.com/coq/coq/archive trunk zip 1 coq-8.5trunk ; then
  if build_prep https://coq.inria.fr/distrib/V8.5/files coq-8.5 tar.gz ; then
    (
    ./configure -prefix $RESULT_INSTALLDIR_MFMT
    # The windows resource compiler binayr name is hard coded
    sed -i "s/i686-w64-mingw32-windres/$TARGET_ARCH-windres/" Makefile.build 
    make $MAKE_OPT world
    make install
    ) >../$BUILD_PACKAGE_NAME.log 2>&1
    build_post
  fi
}

#################### NSIS ##################

function install_nsis {
   wget -nc http://prdownloads.sourceforge.net/nsis/nsis-2.51-src.tar.bz2
   wget -nc http://prdownloads.sourceforge.net/nsis/nsis-2.51.zip
   rm -rf $RESULT_INSTALLDIR_CFMT/../NSIS
   mkdir $RESULT_INSTALLDIR_CFMT/../NSIS
   ( cd $RESULT_INSTALLDIR_CFMT/../NSIS; unzip ~/nsis-2.51.zip; mv */* . ) >nsis.log 2>&1
   chmod a+x $RESULT_INSTALLDIR_CFMT/../NSIS/*.exe
}

###################### TOP LEVEL BUILD #####################

mkdir -p $RESULT_INSTALLDIR_CFMT/bin

make_gtk2
make_gtk_sourceview2
#make_gtk3
make_ocaml
make_findlib
make_camlp4
make_lablgtk
make_camlp5
install_nsis
#make_menhir
#make_coq

mkdir -p $RESULT_INSTALLDIR_CFMT/../sources
cp *gz *xz *bz2 *.patch $RESULT_INSTALLDIR_CFMT/../sources
cp environ $RESULT_INSTALLDIR_CFMT/
cp README-SDK.txt $RESULT_INSTALLDIR_CFMT/../
BASE=$RESULT_INSTALLDIR_CFMT
cat > "$BASE/lib/ld.conf.in" <<- EOF
	@BASE@/lib
	@BASE@/lib/stublibs
	EOF
cat > "$BASE/etc/findlib.conf.in" <<- EOF
	destdir="@BASE@/lib/site-lib"
	path="@BASE@/lib/site-lib"
	stdlib="@BASE@/lib"
	ldconf="@BASE@/lib/ld.conf"
	ocamlc="ocamlc.opt"
	ocamlopt="ocamlopt.opt"
	ocamldep="ocamldep.opt"
	ocamldoc="ocamldoc.opt"
	EOF
perl -pe "s|\\Q$RESULT_INSTALLDIR_WFMT\\E|@BASE@|g"  $BASE/lib/topfind > $BASE/lib/topfind.in

rm -rf *
