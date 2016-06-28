#!/bin/bash

rcfile=~/.bash_profile
donefile=~/.bash_profile.upated

if [ ! -f $donefile ] ; then

    echo >> $rcfile
    
    if [ -n "$2" ]; then
      echo  export http_proxy="http://$2" >> $rcfile
      echo export https_proxy="http://$2" >> $rcfile
      echo export ftp_proxy="http://$2" >> $rcfile
    fi
    
    mkdir -p $RESULT_INSTALLDIR_CFMT/bin
    
    echo export PATH="/usr/local/bin:/usr/bin:$RESULT_INSTALLDIR_CFMT/bin:/cygdrive/c/Windows/system32:/cygdrive/c/Windows" >> $rcfile

    touch $donefile
fi