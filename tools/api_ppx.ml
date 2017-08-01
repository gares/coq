(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Ppx_tools_402

open Ast_mapper
open Ast_helper
open Asttypes
open Parsetree
open Longident

let enabled = ref false

let args = [
   "--on",Arg.Set enabled,"Enable API bypass generation" ;
   "--off",Arg.Clear enabled,"Disable API bypass generation" ;
  ]
let reset_args () =
  enabled := false

let err ~loc str =
  raise (Location.Error(Location.error ~loc str))

let is_bypass_attribute ({ txt = x },_) = x = "bypass"

let rec filter_map f = function
  | [] -> []
  | x :: xs ->
      match f x with
      | Some y -> y :: filter_map f xs
      | None -> filter_map f xs

let equate api_name ({
       ptype_name = { txt = name };
(*     ptype_params : (core_type * Asttypes.variance) list; *)
(*     ptype_cstrs : (core_type * core_type * Location.t) list; *)
    ptype_kind (*: type_kind;*)
(*     ptype_private : Asttypes.private_flag; *)
(*     ptype_manifest; *)
  } as x) =
          { x with ptype_manifest = Some ({ ptyp_desc = 
                  Ptyp_constr(Location.mknoloc (Longident.(Ldot (Lident api_name,name))),[]) ;
                  ptyp_loc = Location.none;
                  ptyp_attributes = []}) }


let mk_type_eq_mapper name = { default_mapper with signature = fun mapper ->
  filter_map (fun ({ psig_desc } as x) ->
     match psig_desc with
     | Psig_value _ -> None
     | Psig_type ((*rf,*) [ pt ]) ->
            Some { x with psig_desc = Psig_type ((*rf,*) [ equate name pt ]) }
     | _ -> Some (default_mapper.signature_item mapper x))
  }

let mk_bypass_modtype name l =
  let mapper = mk_type_eq_mapper name in
  let desc = Pmty_signature (mapper.signature mapper l) in
  {
    pmty_desc = desc;
    pmty_loc = Location.none;
    pmty_attributes = [];
  }

let bypass { txt = name } { pmty_desc } : signature_item list =
  match pmty_desc with
  | Pmty_signature l ->
      let psig_desc = Psig_module {
        pmd_name = Location.mknoloc ("Bypass"^name);
        pmd_type = mk_bypass_modtype name l;
        pmd_attributes = [];
        pmd_loc = Location.none;
      }
      in
      [ { psig_desc; psig_loc = Location.none } ]
  | _ -> []

let api_bypass_mapper config cookies =
  { default_mapper with signature = fun mapper ->
    function
    | [ { psig_desc = Psig_module { pmd_name; pmd_type = ast; pmd_attributes; pmd_loc }} as x ]
      when List.exists is_bypass_attribute pmd_attributes ->
        let pmd_attributes = List.filter (fun x -> not (is_bypass_attribute x)) pmd_attributes in
        let x = { x with psig_desc = Psig_module { pmd_name; pmd_type = ast; pmd_attributes; pmd_loc }} in
        x :: bypass pmd_name ast
    | x -> default_mapper.signature mapper x
  }

open Migrate_parsetree
let () =
  Driver.register ~name:"API bypass" ~args ~reset_args
    Versions.ocaml_402 api_bypass_mapper
;;

