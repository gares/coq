(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

exception Notconvertible

type timing = {
  mutable setup : float;     (* data structures allocation *)
  mutable hashcons : float;  (* hashconsing input *)
  mutable red : float;       (* time spent in reduction *)
  mutable conv : float;      (* time spent in conversion (includes red) *)
}

val mk_timing : unit -> timing
val add_timing : timing:timing -> extra:timing -> unit

val are_convertible : 
  ?timing:timing ->
  Names.transparent_state ->
  Mini_evd.conv_pb -> (* CONV | CUMUL *)
  l2r:bool ->
  Mini_evd.EvarMap.t ->
  Environ.env -> Term.constr -> Term.constr -> Univ.constraints

val red_whd : Environ.env -> Mini_evd.evar_map -> Term.constr -> Term.constr
val red_strong : Environ.env -> Mini_evd.evar_map -> Term.constr -> Term.constr

val do_unlock : bool ref (* XXX unlock SSR constants on the fly *)
