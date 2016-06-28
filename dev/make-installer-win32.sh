#!/bin/sh

set -e

NSIS="$BASE/../NSIS/makensis"
ZIP=_make.zip
URL1=http://sourceforge.net/projects/gnuwin32/files/make/3.81/make-3.81-bin.zip/download
URL2=http://sourceforge.net/projects/gnuwin32/files/make/3.81/make-3.81-dep.zip/download

[ -e config/Makefile ] || ./configure -debug -prefix ./ -with-doc no
make
if [ ! -e bin/make.exe ]; then
  wget -O $ZIP $URL1 && unzip $ZIP "bin/*"
  wget -O $ZIP $URL2 && unzip $ZIP "bin/*"
  rm -rf $ZIP
fi
VERSION=`grep ^VERSION= config/Makefile | cut -d = -f 2`
cd dev/nsis
"$NSIS" -DVERSION=$VERSION -DGTK_RUNTIME="`cygpath -w $BASE/../cygwin32/usr/i686-w64-mingw32/sys-root/mingw/`" -DARCH="win32" coq.nsi
echo Installer:
ls -h $PWD/*exe
cd ../..
