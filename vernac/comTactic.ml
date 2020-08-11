(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Goptions

let print_info_trace =
  declare_intopt_option_and_ref ~depr:false ~key:["Info" ; "Level"]

let solve ~pstate n ~info t ~with_end_tac:b =
  let pstate, status = Declare.Proof.map_fold_endline ~f:(fun etac p ->
      let with_end_tac = if b then Some etac else None in
      let info = Option.append info (print_info_trace ()) in
      let (p,status) = Proof.solve n info t ?with_end_tac p in
      (* in case a strict subtree was completed,
         go back to the top of the prooftree *)
      let p = Proof.maximal_unfocus Vernacentries.command_focus p in
      p,status) pstate in
  if not status then Feedback.feedback Feedback.AddedAxiom;
  pstate

let par_implementation = ref (fun ~pstate ~info ~ast:_ t ~solve:_ ~abstract:_ ~with_end_tac ->
  solve ~pstate Goal_select.SelectAll ~info t ~with_end_tac)

let solve_parallel ~pstate ~info ~ast t ~solve ~abstract ~with_end_tac =
  !par_implementation ~pstate ~info ~ast t ~solve ~abstract ~with_end_tac
