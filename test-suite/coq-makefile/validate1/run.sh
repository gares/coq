#!/bin/sh

#set -x
set -e

. ../template/init.sh

coq_makefile -f _CoqProject -o Makefile
make
exec make validate
