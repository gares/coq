@ECHO OFF
REM ========== ADJUSTABLE PARAMETERS ==========

SET BITS=64
SET COQ_VERSION=v8.6
SET SDK_VERSION=1

REM SET PROXY= -p <host>
SET PROXY=
SET CYGWIN_REPOSITORY=http://ftp.inf.tu-dresden.de/software/windows/cygwin

SET MAKE_OPT=-j 1

REM ========== DERIVED PARAMETERS ==========

SET SDK_NAME=CoqSDK-%COQ_VERSION%-win%BITS%-%SDK_VERSION%
SET CYGWIN_INSTALLDIR_WFMT=C:\%SDK_NAME%\cygwin%BITS%
SET RESULT_INSTALLDIR_WFMT=C:\%SDK_NAME%\SDK
SET LOCAL_REPOSITORY_WFMT=C:\%SDK_NAME%\sources
IF [%BITS%] EQU [64] (
  SET ARCH_NAME=x86_64
  SET CYGWIN_INSTALLER=setup-x86_64.exe
) ELSE (
  SET ARCH_NAME=i686
  SET CYGWIN_INSTALLER=setup-x86.exe
)
SET TARGET_ARCH=%ARCH_NAME%-w64-mingw32

REM ========== DERIVED VARIABLES ==========

SET BASH=%CYGWIN_INSTALLDIR_WFMT%\bin\bash
SET HERE=%~dp0

REM Convert pathes to various formats
REM WFMT = windows format (C:\..)          Used in this batch file.
REM CFMT = cygwin format (\cygdrive\c\..)  Used for Cygwin PATH varible, which is : separated, so C: doesn't work.
REM MFMT = MinGW format (C:/...)           Used for the build, because \\ requires escaping. Mingw can handle \ and /.

SET CYGWIN_INSTALLDIR_MFMT=%CYGWIN_INSTALLDIR_WFMT:\=/%
SET RESULT_INSTALLDIR_MFMT=%RESULT_INSTALLDIR_WFMT:\=/%
SET LOCAL_REPOSITORY_MFMT=%LOCAL_REPOSITORY_WFMT:\=/%

SET CYGWIN_INSTALLDIR_CFMT=%CYGWIN_INSTALLDIR_MFMT:C:/=/cygdrive/c/%
SET RESULT_INSTALLDIR_CFMT=%RESULT_INSTALLDIR_MFMT:C:/=/cygdrive/c/%
SET LOCAL_REPOSITORY_CFMT=%LOCAL_REPOSITORY_MFMT:C:/=/cygdrive/c/%

SET CYGWIN_INSTALLDIR_CFMT=%CYGWIN_INSTALLDIR_CFMT:D:/=/cygdrive/d/%
SET RESULT_INSTALLDIR_CFMT=%RESULT_INSTALLDIR_CFMT:D:/=/cygdrive/d/%
SET LOCAL_REPOSITORY_CFMT=%LOCAL_REPOSITORY_CFMT:D:/=/cygdrive/d/%

SET CYGWIN_INSTALLDIR_CFMT=%CYGWIN_INSTALLDIR_CFMT:E:/=/cygdrive/e/%
SET RESULT_INSTALLDIR_CFMT=%RESULT_INSTALLDIR_CFMT:E:/=/cygdrive/e/%
SET LOCAL_REPOSITORY_CFMT=%LOCAL_REPOSITORY_CFMT:E:/=/cygdrive/e/%

ECHO CYGWIN INSTALL DIR (WIN)    = %CYGWIN_INSTALLDIR_WFMT%
ECHO CYGWIN INSTALL DIR (MINGW)  = %CYGWIN_INSTALLDIR_MFMT%
ECHO CYGWIN INSTALL DIR (CYGWIN) = %CYGWIN_INSTALLDIR_CFMT%
ECHO RESULT INSTALL DIR (WIN)    = %RESULT_INSTALLDIR_WFMT%
ECHO RESULT INSTALL DIR (MINGW)  = %RESULT_INSTALLDIR_MFMT%
ECHO RESULT INSTALL DIR (CYGWIN) = %RESULT_INSTALLDIR_CFMT%
ECHO TARGET_ARCH = %TARGET_ARCH%

ECHO ========== INSTALL CYGWIN ==========
REM For Cygwin setup command line options
REM see https://cygwin.com/faq/faq.html#faq.setup.cli


%CYGWIN_INSTALLER% -q ^
  %PROXY% ^
  -s %CYGWIN_REPOSITORY% ^
  -R %CYGWIN_INSTALLDIR_WFMT% ^
  -l %~dp0 ^
  -P wget,curl,make,unzip,zip ^
  -P mingw64-%ARCH_NAME%-binutils,mingw64-%ARCH_NAME%-gcc-core,mingw64-%ARCH_NAME%-gcc-g++,mingw64-%ARCH_NAME%-pkg-config,mingw64-%ARCH_NAME%-windows_default_manifest ^
  -P mingw64-%ARCH_NAME%-headers,mingw64-%ARCH_NAME%-runtime,mingw64-%ARCH_NAME%-pthreads,mingw64-%ARCH_NAME%-zlib ^
  -P gcc-core,gcc-g++ ^
  -P liblzma5 ^
  -P patch,automake1.14,automake1.15 ^
  -P gettext-devel ^
  -P libglib2.0-devel ^
  -P libiconv-devel,libunistring-devel,libncurses-devel ^
  -P libgettextpo-devel ^
  -P libfontconfig1 ^
  -P libgdk_pixbuf2.0-devel ^
  -P gtk-update-icon-cache ^
  -P libtool,automake ^
  -P intltool

REM like most setup programs, cygwin setup starts the real setup as a separate process, so wait for it
:waitsetup
tasklist /fi "imagename eq %CYGWIN_INSTALLER%" | find ":" > NUL
if errorlevel 1 goto waitsetup

ECHO ========== CONFIGURE CYGWIN USER ACCOUNT ==========

copy %HERE%\configure_profile.sh %CYGWIN_INSTALLDIR_WFMT%\var\tmp
%BASH% --login %CYGWIN_INSTALLDIR_WFMT%\var\tmp\configure_profile.sh %PROXY%

ECHO ========== BUILD SDK ==========

copy %HERE%\build_SDK.sh %CYGWIN_INSTALLDIR_WFMT%\home\%USERNAME%
copy %HERE%\*.patch %CYGWIN_INSTALLDIR_WFMT%\home\%USERNAME%
copy %HERE%\environ %CYGWIN_INSTALLDIR_WFMT%\home\%USERNAME%
copy %HERE%\README-SDK.txt %CYGWIN_INSTALLDIR_WFMT%\home\%USERNAME%
%BASH% --login %CYGWIN_INSTALLDIR_WFMT%\home\%USERNAME%\build_SDK.sh

ECHO ========== REMOVE UNNEEDED PKGS ======

%CYGWIN_INSTALLER% -q ^
  %PROXY% ^
  -s %CYGWIN_REPOSITORY% ^
  -R %CYGWIN_INSTALLDIR_WFMT% ^
  -l %~dp0 ^
  -P wget,curl,make,unzip,zip ^
  -P mingw64-%ARCH_NAME%-binutils,mingw64-%ARCH_NAME%-gcc-core,mingw64-%ARCH_NAME%-gcc-g++,mingw64-%ARCH_NAME%-pkg-config,mingw64-%ARCH_NAME%-windows_default_manifest ^
  -P mingw64-%ARCH_NAME%-headers,mingw64-%ARCH_NAME%-runtime,mingw64-%ARCH_NAME%-pthreads,mingw64-%ARCH_NAME%-zlib ^
  -x gcc-core,gcc-g++ ^
  -x liblzma5 ^
  -x patch,automake1.14,automake1.15 ^
  -x gettext-devel ^
  -x libglib2.0-devel ^
  -x libiconv-devel,libunistring-devel,libncurses-devel ^
  -x libgettextpo-devel ^
  -x libfontconfig1 ^
  -x libgdk_pixbuf2.0-devel ^
  -x gtk-update-icon-cache ^
  -x libtool,automake ^
  -x intltool

REM like most setup programs, cygwin setup starts the real setup as a separate process, so wait for it
:waitsetup2
tasklist /fi "imagename eq %CYGWIN_INSTALLER%" | find ":" > NUL
if errorlevel 1 goto waitsetup2

ECHO ========== FINISHED ==========
