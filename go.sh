#!/bin/bash
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

mksanitytest() {
  TEST=/tmp/sanitytest
  cat > $TEST.v <<-EOT
  Definition test1 := 
     (fun (T : Type) (a b : T) (F : T -> T) => 
       (fun f x y => f y x) (fun x y => F x) a b).
  Definition test2 := 
     (fun (T : Type) (a b : T) (F G H : T -> T) (pair : T -> T -> T) => 
       (fun f x y => f (G y) x) (fun x y => pair (F x) a) a (H b)).
  
  Eval $1 in test1.
  Eval $1 in test2.
  Eval $1 in (33 * 4 + 2 - 1).
EOT
}

mktest() {
  TEST=/tmp/test
  cat > $TEST.v <<-EOT
  Fixpoint fact n := match n with 0 => 1 | S m => fact m * n end.
  Let n := $1. 
  Let test := (fact n - fact n).
  
  Fixpoint fact_s n := match n with 0 => 1 | S m => n * fact_s m end.
  Let n_s := $1.
  Let test_s := (fact_s n_s - fact_s n_s).
  
  Let test3 := n * n * (n * n * n) - (n * n * n) * n.
  Let test4 s o := 
    (fun (f:nat -> nat) (x : nat) => ( ( (f (f (f (f x)))))))
     ((fun (f:nat -> nat) (x : nat) => ( ( (f (f (f (f x))))))) s)
     o.
  Let test6 := (fun x => x - x) (fact_s n_s).
  
  Goal True.
  Time Eval $2 in test.
  Time Eval $2 in test_s.
  Time Eval $2 in test3.
  Time Eval $2 in test4.
  Time Eval $2 in (test4 S).
  Time Eval $2 in (test4 S 0).
  Time Eval $2 in test6.
  
  Abort. 
EOT
}
runcoq() {
  OCAMLRUNPARAM='s=33554432,o=120,b' "$@"
}

print() {
  echo "INFO: $@"
}
# -------------------------------------------------------------------

print "compiling kernel/* with profiling enabled"
build kernel/conversion
build kernel/closure
build kernel/reduction

print "building coqtop"
make -j2 states bin/coqtop.byte > /tmp/coqlog 2>&1 || \
	(cat /tmp/coqlog; exit 1)
grep -i warning /tmp/coqlog || true

print 'running sanity check'
mksanitytest lazy
runcoq bin/coqtop -compile $TEST 2>/dev/null 1>/tmp/t1
mksanitytest mines
runcoq bin/coqtop -compile $TEST 2>/dev/null 1>/tmp/t2
diff /tmp/t1 /tmp/t2

if [ $# -gt 0 ]; then
  print "running $@"
  runcoq "$@"
  exit 0
fi

OPT=4
BYTE=4

print "running test in opt size $OPT"
mktest $OPT lazy
runcoq bin/coqtop -compile $TEST > /tmp/t1
grep ^Finished /tmp/t1
# print generating gprof.lazy.out
# gprof bin/coqtop > gprof.lazy.out
mktest $OPT mines
runcoq bin/coqtop -compile $TEST > /tmp/t2
grep ^Finished /tmp/t2
# print generating gprof.mine.out
# gprof bin/coqtop > gprof.mine.out
diff <(grep -v ^Finished /tmp/t1) <(grep -v ^Finished /tmp/t2)

print "running test in byte size $BYTE"
mktest $BYTE lazy
runcoq bin/coqtop.byte -compile $TEST > /tmp/t1
grep ^Finished /tmp/t1
mktest $BYTE mines
runcoq bin/coqtop.byte -compile $TEST > /tmp/t2
grep ^Finished /tmp/t2
diff <(grep -v ^Finished /tmp/t1) <(grep -v ^Finished /tmp/t2)
# print generating annot.out
# echo '(* vi' 'm:' 'set ft=ocaml: *)' > annot.out
# ocamlprof kernel/conversion.ml >> annot.out || true
# ocamlprof kernel/closure.ml >> annot.out || true
# ocamlprof kernel/reduction.ml >> annot.out || true
# print "type: gvim -o gprof.mine.out annot.out"
