(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val clos_fconv : 
  Names.Idpred.t * Names.Cpred.t ->
  Mini_evd.conv_pb ->
  bool ->
  Mini_evd.EvarMap.t ->
  Environ.env -> Term.constr -> Term.constr -> Univ.constraints

val red_whd : Environ.env -> Mini_evd.evar_map -> Term.constr -> Term.constr
