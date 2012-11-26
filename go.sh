#!/bin/sh
set -e

rm -f gmon.out ocamlprof.dump

build_aux() {
  if [ $1 -ot $2 ]; then
    $3 -I kernel -I lib -c $2
  fi	  
}
build() {
  build_aux $1.cmo $1.ml ocamlcp
  build_aux $1.cmx $1.ml "ocamlopt -p"
}

mktest() {
cat > /tmp/test.v <<EOT
Fixpoint fact n := match n with 0 => 1 | S m => fact m * n end.
Let n := $1. 
Let test := (fact n - fact n).

Fixpoint fact_s n := match n with 0 => 1 | S m => n * fact_s m end.
Let n_s := $1.
Let test_s := (fact_s n_s - fact_s n_s).

Goal True.

idtac "------------ $2, without sharing --------------".
Time Eval $2 in test.

idtac "------------- $2, with sharing ---------------".
idtac "----> $2".
Time Eval $2 in test_s.

Abort. 
EOT
}

echo compiling with profiling enabled
build kernel/conversion
build kernel/closure

echo building Coq
make -j2 states bin/coqtop.byte > /tmp/coqlog 2>&1 || \
	(cat /tmp/coqlog; exit 1)
grep warning /tmp/coqlog || true

OPT=9
BYTE=9

echo 'running *************** opt ' $OPT ' *****************'
mktest $OPT mine
OCAMLRUNPARAM='s=33554432,o=120' bin/coqtop -compile /tmp/test
echo generating gprof.mine.out
gprof bin/coqtop > gprof.mine.out
mktest $OPT lazy
OCAMLRUNPARAM='s=33554432,o=120' bin/coqtop -compile /tmp/test
echo generating gprof.lazy.out
gprof bin/coqtop > gprof.lazy.out

echo 'running *************** byte ' $BYTE ' ******************'
mktest $BYTE mine
OCAMLRUNPARAM='s=33554432,o=120' bin/coqtop.byte -compile /tmp/test

echo generating annot.out
echo '(* vim: set ft=ocaml: *)' > annot.out
ocamlprof kernel/conversion.ml >> annot.out
ocamlprof kernel/closure.ml >> annot.out

mktest $BYTE lazy
OCAMLRUNPARAM='s=33554432,o=120' bin/coqtop.byte -compile /tmp/test

echo type: gvim -o gprof.mine.out annot.out
