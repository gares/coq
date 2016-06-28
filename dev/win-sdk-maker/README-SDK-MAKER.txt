These scripts build 64 bit Windows/MinGW Coq including all requisites like GTK and OCAML.
A fresh Cygwin is also setup automatically.
All required sources are downloaded from the internet (if not found in a local repository).
Currently this only works for MinGW64 bit, I am working on adjusting it for 32 bit (some minor issues with glib).

Usage:

- Expand zip file in arbitrary folder.
- Download setup-x86_64.exe from https://cygwin.com/install.html into the same folder
- Adjust parameters (paths) in MakeCoq_ForMigngw_UsingCygwin.bat below ADJUSTABLE PARAMETERS
  It shouldn't be required to modify anything else.
- Run MakeCoq_ForMigngw_UsingCygwin.bat from a command prompt (normal user, no admin console)
- During the Cygwin setup, it asks you for elevating privileges.
  Answer yes when you run this for the first time. In later runs (if Cygwin is setup fine) you can answer No.
- The build takes about 90 minutes on a workstation

Possible issues:

- I never tested this with PROXY set to " ", since this doesn't work for me.
  In this case it should jump over setting the proxy environment vars in "configure_profile.sh"
  Please check if your C:\bin\cygwin64coq\home\<user>\.bash_profile looks reasonable and if not fix configure_profile.sh

- Not all installs honor the RESULT_INSTALLDIR_WFMT setting as yet. The build will work, but some DLLs required
  by CoqIDE will be in C:\bin\cygwin64coq\usr\x86_64-w64-mingw32\sys-root\mingw and others in what you
  setup with RESULT_INSTALLDIR_WFMT. So for the time being it is recommended to set both with the same root
  as with the default settings.
  I will later fix this to fully support a separate output directory, so that Cygwin can be deleted after build.
  
- The batch file uses this line

    tasklist /fi "imagename eq setup-x86_64.exe" | find ":" > NUL
  
  to wait for the Cygwin setup to finish. I am not sure if tasklist is available on all windows.
  It should be in C:\Windows\system32. If you don't have it, let me check where I got it from.

- The scripts look for tar balls in LOCAL_REPOSITORY_WFMT, but don't copy them there.
  To avoid downoading the files several times in several runs, copy them there manually.

- Not sure what happens if the path pointed to by LOCAL_REPOSITORY_WFMT doesn't exist