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
  Fixpoint f1 (T : Type) n : nat :=
    match n with
    | 0 => 1
    | S m => f2 T T m (f1 T m) end
  with f2 (T1 T2 : Type) n : nat -> nat :=
    match n with
    | 0 => fun x => x
    | S m => fun x => x + (f1 T1 m) end.
  
  Eval $1 in test1.
  Eval $1 in test2.
  Eval $1 in (3 * 4 + 2 - 1).
  Eval $1 in (f1 nat 4).
  Eval $1 in (forall (f : nat -> Prop) (a b : nat), ((fun x => f x -> f x) (S b))).

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
  OCAMLRUNPARAM='s=33554432,o=120,b' /usr/bin/time -o /tmp/time.log -f "%e" "$@"
}

print() { echo "INFO: $@"; }
print_n() { echo -n "INFO: $@"; }
print_begin_action(){ print_n "       $1"; }
print_end_action(){ echo -e "\rINFO: [$1]"; }

sanity_check() {
  print 'running sanity check'
  mksanitytest lazy
  runcoq $COQBINARY -compile $TEST 2>/dev/null 1>/tmp/t1
  mksanitytest mines
  runcoq $COQBINARY -compile $TEST 2>/dev/null 1>/tmp/t2
  diff /tmp/t1 /tmp/t2
}

parse_args() {
  if [ "$1" = "bin/coqtop.byte" ]; then
  	COQBINARY=bin/coqtop.byte
  	OPT=1
  else
  	COQBINARY=bin/coqtop
  	OPT=0
  fi
}

compile() {
  print "compiling kernel/* with profiling enabled"
  build kernel/conversion
  build kernel/closure
  build kernel/reduction
  
  print "building coqtop"
  if [ $OPT = 0 ]; then
  	make -j2 bin/coqtop.byte > /tmp/coqlog 2>&1 || \
  	(cat /tmp/coqlog; exit 1)
  else
  	make -j2 states bin/coqtop.byte > /tmp/coqlog 2>&1 || \
  	(cat /tmp/coqlog; exit 1)
  fi
  grep -i warning /tmp/coqlog || true
}

bench_reduction() {
  print "running test in $2 size $1"
  if [ "$2" = "byte" ]; then EXT=.byte; fi
  mktest $1 lazy
  runcoq bin/coqtop$EXT -compile $TEST > /tmp/t1
  grep ^Finished /tmp/t1
  # print generating gprof.lazy.out
  # gprof bin/coqtop > gprof.lazy.out
  mktest $1 mines
  runcoq bin/coqtop$EXT -compile $TEST > /tmp/t2
  grep ^Finished /tmp/t2
  # print generating gprof.mine.out
  # gprof bin/coqtop > gprof.mine.out
  diff <(grep -v ^Finished /tmp/t1) <(grep -v ^Finished /tmp/t2)
  # print generating annot.out
  # echo '(* vi' 'm:' 'set ft=ocaml: *)' > annot.out
  # ocamlprof kernel/conversion.ml >> annot.out || true
  # ocamlprof kernel/closure.ml >> annot.out || true
  # ocamlprof kernel/reduction.ml >> annot.out || true
  # print "type: gvim -o gprof.mine.out annot.out"
}

regression_check() {
  print "regression check:"
  for f in `sprt -n -k2 PASSED | cut -d ' ' -f 1`; do
    print_begin_action "checking $f"
    runcoq bin/coqtop -boot -run-conv-pbs today -compile $f 2> /tmp/run.log
    if grep -q -F ERR /tmp/run.log; then
      print_end_action "FAIL"
      cat /tmp/run.log
      exit 1
    else
      print_end_action "OK"
    fi
  done
}

run_all() {
  local TOTAL=`find . -name \*.vc| wc -l|cut -d ' ' -f 1`
  local PASSED=`wc -l PASSED|cut -d ' ' -f 1`
  print "running all problems not passed yet (`expr \\( $TOTAL - $PASSED \\) \* 100 / $TOTAL`%):"
  for f in `find theories -name \*.vc | sort; find plugins -name \*.vc`; do
    f=`echo $f | sed -e 's/.vc$//' -e 's/^\.\///'`
    if ! grep -q -F $f PASSED; then
      print_begin_action "running $f  (`du -h $f.vc | cut -f1`)"
      runcoq bin/coqtop -boot -run-conv-pbs today -compile $f 2> /tmp/run.log
      if ! grep -q -F ERR /tmp/run.log; then
	print_end_action "OK"
        echo $f `cat /tmp/time.log` >> PASSED
      else
	print_end_action "FAIL"
        cat /tmp/run.log
	FAIL="$f $FAIL"
      fi
    fi
  done
}

# -------------------------------------------------------------------

parse_args "$@"
compile
sanity_check

if [ $# -gt 0 ]; then
  print "running $@"
  runcoq "$@"
else
  #bench_reduction 6 opt
  #bench_reduction 4 byte
  run_all
  regression_check
fi
if [ ! -z "$FAIL" ]; then
  print "$FAIL FAILED!"
  exit 1
fi

