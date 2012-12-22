(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

exception NotConvertible

val are_convertible : 
  Names.transparent_state ->
  Mini_evd.conv_pb -> (* CONV | CUMUL *)
  l2r:bool ->
  Mini_evd.EvarMap.t ->
  Environ.env -> Term.constr -> Term.constr -> Univ.constraints

val red_whd : Environ.env -> Mini_evd.evar_map -> Term.constr -> Term.constr
val red_strong : Environ.env -> Mini_evd.evar_map -> Term.constr -> Term.constr
