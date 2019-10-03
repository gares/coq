(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Univ
open Constr
open Mod_subst

type opaque_id = int

type work_list = (Instance.t * Id.t array) Cmap.t *
  (Instance.t * Id.t array) Mindmap.t

type cooking_info = {
  modlist : work_list;
  abstract : Constr.named_context * Univ.Instance.t * Univ.AUContext.t }

type 'a delayed_universes =
| PrivateMonomorphic of 'a
| PrivatePolymorphic of int * Univ.ContextSet.t

type opaque_proofterm = (Constr.t * unit delayed_universes) option

type proofterm = (constr * Univ.ContextSet.t delayed_universes) Future.computation

type opaque =
| Indirect of substitution list * cooking_info list * DirPath.t * opaque_id (* subst, discharge, lib, index *)

type opaquetab = {
  opaque_len : int;
  (** Size of the above map *)
  opaque_dir : DirPath.t;
}
let empty_opaquetab = {
  opaque_len = 0;
  opaque_dir = DirPath.initial;
}

let repr (Indirect (s, ci, dp, i)) = (s, ci, dp, i)

let create dp tab =
  let id = tab.opaque_len in
  let opaque_dir =
    if DirPath.equal dp tab.opaque_dir then tab.opaque_dir
    else if DirPath.equal tab.opaque_dir DirPath.initial then dp
    else CErrors.anomaly
      (Pp.str "Using the same opaque table for multiple dirpaths.") in
  let ntab = { opaque_dir; opaque_len = id + 1 } in
  Indirect ([], [], dp, id), ntab

let subst_opaque sub = function
| Indirect (s, ci, dp, i) -> Indirect (sub :: s, ci, dp, i)

let discharge_opaque info = function
| Indirect (s, ci, dp, i) ->
  assert (CList.is_empty s);
  Indirect ([], info :: ci, dp, i)
