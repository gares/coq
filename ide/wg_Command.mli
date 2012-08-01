(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class command_window : Coq.coqtop ->
    mark_as_broken:(Stategraph.state_id list -> unit) ->
    mark_as_processed:(Stategraph.state_id list -> unit) ->
    cur_state:(unit -> Stategraph.state_id) ->
  object
    method new_command : ?command:string -> ?term:string -> unit -> unit
    method frame : GBin.frame
    method refresh_font : unit -> unit
    method refresh_color : unit -> unit
  end
