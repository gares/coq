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
Let n_s := $2.
Let test_s := (fact_s n_s - fact_s n_s).

Goal True.

idtac "        ------------ with no sharing --------------".
idtac "----> conversion".
Time Eval mine in test.
idtac "".
idtac "----> closure".
Time Eval lazy in test.
idtac "".

idtac "        ------------- with sharing ---------------".
idtac "----> conversion".
Time Eval mine in test_s.
idtac "".
idtac "----> closure".
Time Eval lazy in test_s.
Abort. 
EOT
}

echo compiling with profiling enabled
build kernel/conversion
build kernel/closure

echo building Coq
make -j2 states bin/coqtop.byte > /tmp/coqlog 2>&1 || \
	(cat /tmp/coqlog; exit 1)

OPT=8
BYTE=8

echo 'running *************** opt ' $OPT ' *****************'
mktest $OPT $OPT
OCAMLRUNPARAM='s=33554432,o=120' bin/coqtop -compile /tmp/test

echo generating gprof.out
gprof bin/coqtop > gprof.out

echo 'running *************** byte ' $BYTE ' ******************'
mktest $BYTE $BYTE
OCAMLRUNPARAM='s=33554432,o=120' bin/coqtop.byte -compile /tmp/test

echo generating annot.out
echo '(* vim: set ft=ocaml: *)' > annot.out
ocamlprof kernel/conversion.ml >> annot.out
ocamlprof kernel/closure.ml >> annot.out

echo type: gvim -o gprof.out annot.out
