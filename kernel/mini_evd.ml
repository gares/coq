(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Environ

type evar = existential_key

type evar_body =
  | Evar_empty
  | Evar_defined of constr

type evar_info = {
  evar_concl : constr;
  evar_hyps : named_context_val;
  evar_body : evar_body;
  evar_filter : bool list;
  evar_source : Evar_kinds.t Loc.located;
  evar_candidates : constr list option;  (* if not None, list of allowed instances *)
  evar_extra : Store.t }

let string_of_existential evk = "?" ^ string_of_int evk
let evar_concl evi = evi.evar_concl
let evar_hyps evi = evi.evar_hyps
let evar_context evi = named_context_of_val evi.evar_hyps
let evar_body evi = evi.evar_body
let evar_filter evi = evi.evar_filter
(* let evar_unfiltered_env evi = Global.env_of_context evi.evar_hyps *)
let evar_filtered_context evi =
  snd (List.filter2 (fun b c -> b) (evar_filter evi,evar_context evi))
(*
let evar_env evi =
  List.fold_right push_named (evar_filtered_context evi)
    (reset_context (Global.env()))
*)

let eq_evar_info ei1 ei2 =
  ei1 == ei2 ||
    eq_constr ei1.evar_concl ei2.evar_concl &&
    eq_named_context_val (ei1.evar_hyps) (ei2.evar_hyps) &&
    ei1.evar_body = ei2.evar_body

module ExistentialMap = Intmap
module ExistentialSet = Intset

(* This exception is raised by *.existential_value *)
exception NotInstantiatedEvar

(* Note: let-in contributes to the instance *)
let make_evar_instance sign args =
  let rec instrec = function
    | (id,_,_) :: sign, c::args when isVarId id c -> instrec (sign,args)
    | (id,_,_) :: sign, c::args -> (id,c) :: instrec (sign,args)
    | [],[] -> []
    | [],_ | _,[] -> anomaly "Signature and its instance do not match"
  in
    instrec (sign,args)

let instantiate_evar sign c args =
  let inst = make_evar_instance sign args in
  if inst = [] then c else replace_vars inst c

module EvarInfoMap = struct
  type t = evar_info ExistentialMap.t * evar_info ExistentialMap.t

  let empty = ExistentialMap.empty, ExistentialMap.empty

  let is_empty (d,u) = ExistentialMap.is_empty d && ExistentialMap.is_empty u

  let has_undefined (_,u) = not (ExistentialMap.is_empty u)

  let to_list (def,undef) =
    (* Workaround for change in Map.fold behavior in ocaml 3.08.4 *)
    let l = ref [] in
    ExistentialMap.iter (fun evk x -> l := (evk,x)::!l) def;
    ExistentialMap.iter (fun evk x -> l := (evk,x)::!l) undef;
    !l

  let undefined_list (def,undef) =
    (* Order is important: needs ocaml >= 3.08.4 from which "fold" is a
       "fold_left" *)
    ExistentialMap.fold (fun evk evi l -> (evk,evi)::l) undef []

  let undefined_evars (def,undef) = (ExistentialMap.empty,undef)
  let defined_evars (def,undef) = (def,ExistentialMap.empty)

  let find (def,undef) k =
    try ExistentialMap.find k def
    with Not_found -> ExistentialMap.find k undef
  let find_undefined (def,undef) k = ExistentialMap.find k undef
  let remove (def,undef) k =
    (ExistentialMap.remove k def,ExistentialMap.remove k undef)
  let mem (def,undef) k =
    ExistentialMap.mem k def || ExistentialMap.mem k undef
  let fold (def,undef) f a =
    ExistentialMap.fold f def (ExistentialMap.fold f undef a)
  let fold_undefined (def,undef) f a =
    ExistentialMap.fold f undef a
  let exists_undefined (def,undef) f =
    ExistentialMap.fold (fun k v b -> b || f k v) undef false

  let add (def,undef) evk newinfo =
    if newinfo.evar_body = Evar_empty then
      (def,ExistentialMap.add evk newinfo undef)
    else
      (ExistentialMap.add evk newinfo def,undef)

  let add_undefined (def,undef) evk newinfo =
    assert (newinfo.evar_body = Evar_empty);
    (def,ExistentialMap.add evk newinfo undef)

  let map f (def,undef) = (ExistentialMap.map f def, ExistentialMap.map f undef)

  let define (def,undef) evk body =
    let oldinfo =
      try ExistentialMap.find evk undef
      with Not_found -> 
	try ExistentialMap.find evk def
	with Not_found -> 
	  anomaly "Evd.define: cannot define undeclared evar" in
    let newinfo =
      { oldinfo with
	  evar_body = Evar_defined body } in
      match oldinfo.evar_body with
	| Evar_empty ->
	    (ExistentialMap.add evk newinfo def,ExistentialMap.remove evk undef)
	| _ ->
	    anomaly "Evd.define: cannot define an evar twice"

  let is_evar = mem

  let is_defined (def,undef) evk = ExistentialMap.mem evk def
  let is_undefined (def,undef) evk = ExistentialMap.mem evk undef

  (*******************************************************************)
  (* Formerly Instantiate module *)

  (* Existentials. *)

  let existential_type sigma (n,args) =
    let info =
      try find sigma n
      with Not_found ->
	anomaly ("Evar "^(string_of_existential n)^" was not declared") in
    let hyps = evar_filtered_context info in
      instantiate_evar hyps info.evar_concl (Array.to_list args)

  let existential_value sigma (n,args) =
    let info = find sigma n in
    let hyps = evar_filtered_context info in
      match evar_body info with
	| Evar_defined c ->
	    instantiate_evar hyps c (Array.to_list args)
	| Evar_empty ->
	    raise NotInstantiatedEvar

  let existential_opt_value sigma ev =
    try Some (existential_value sigma ev)
    with NotInstantiatedEvar -> None

end

module EvarMap = struct
  type t = EvarInfoMap.t * (Univ.UniverseLSet.t * Univ.universes)
  let empty = EvarInfoMap.empty, (Univ.UniverseLSet.empty, Univ.initial_universes)
  let is_empty (sigma,_) = EvarInfoMap.is_empty sigma
  let has_undefined (sigma,_) = EvarInfoMap.has_undefined sigma
  let add (sigma,sm) k v = (EvarInfoMap.add sigma k v, sm)
  let add_undefined (sigma,sm) k v = (EvarInfoMap.add_undefined sigma k v, sm)
  let find (sigma,_) = EvarInfoMap.find sigma
  let find_undefined (sigma,_) = EvarInfoMap.find_undefined sigma
  let remove (sigma,sm) k = (EvarInfoMap.remove sigma k, sm)
  let mem (sigma,_) = EvarInfoMap.mem sigma
  let to_list (sigma,_) = EvarInfoMap.to_list sigma
  let undefined_list (sigma,_) = EvarInfoMap.undefined_list sigma
  let undefined_evars (sigma,sm) = (EvarInfoMap.undefined_evars sigma, sm)
  let defined_evars (sigma,sm) = (EvarInfoMap.defined_evars sigma, sm)
  let fold (sigma,_) = EvarInfoMap.fold sigma
  let fold_undefined (sigma,_) = EvarInfoMap.fold_undefined sigma
  let map (sigma,x) f = EvarInfoMap.map f sigma, x
  let define (sigma,sm) k v = (EvarInfoMap.define sigma k v, sm)
  let is_evar (sigma,_) = EvarInfoMap.is_evar sigma
  let is_defined (sigma,_) = EvarInfoMap.is_defined sigma
  let is_undefined (sigma,_) = EvarInfoMap.is_undefined sigma
  let existential_value (sigma,_) = EvarInfoMap.existential_value sigma
  let existential_type (sigma,_) = EvarInfoMap.existential_type sigma
  let existential_opt_value (sigma,_) = EvarInfoMap.existential_opt_value sigma
  let progress_evar_map (sigma1,sm1 as x) (sigma2,sm2 as y) = not (x == y) &&
    (EvarInfoMap.exists_undefined sigma1
      (fun k v -> assert (v.evar_body = Evar_empty);
        EvarInfoMap.is_defined sigma2 k))

  let merge e e' = fold e' (fun n v sigma -> add sigma n v) e
  let add_constraints (sigma, (us, sm)) cstrs =
    (sigma, (us, Univ.merge_constraints cstrs sm))
  let universes (_,(_, c)) = c
  let universe_level (_,(c, _)) = c
  let set_universe_level (x,(_, y)) c = (x,(c, y))
end
module Metamap = Intmap
module Metaset = Intset

type 'a freelisted = {
  rebus : 'a;
  freemetas : Intset.t }
type instance_constraint = IsSuperType | IsSubType | Conv
type instance_typing_status =
    CoerceToType | TypeNotProcessed | TypeProcessed
type instance_status = instance_constraint * instance_typing_status
type clbinding =
  | Cltyp of name * constr freelisted
  | Clval of name * (constr freelisted * instance_status) * constr freelisted
type conv_pb =  CONV | CUMUL
type evar_constraint = conv_pb * env * constr * constr
type evar_map =
    { evars : EvarMap.t;
      conv_pbs : evar_constraint list;
      last_mods : ExistentialSet.t;
      metas : clbinding Metamap.t }

let empty_evar_map = {
  evars=EvarMap.empty;
  conv_pbs=[];
  last_mods = ExistentialSet.empty;
  metas=Metamap.empty
}


