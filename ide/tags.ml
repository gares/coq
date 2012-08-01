(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


let make_tag (tt:GText.tag_table) ~name prop =
  let new_tag = GText.tag ~name () in
  new_tag#set_properties prop;
  tt#add new_tag#as_tag;
  new_tag

let default_bg_color = "cornsilk"
let default_processed_color = "light green"
let default_processing_color = "light blue"

let processed_color   = ref default_processed_color
let processing_color  = ref default_processing_color
let broken_color      = ref "pink"

module Script =
struct
  let table = GText.tag_table ()

  let comment = make_tag table ~name:"comment" []
  let sentence = make_tag table ~name:"sentence" []
  let sentence_end = make_tag table ~name:"sentence_end" []

(* DEBUG: make the lexing phase visible
  let comment = make_tag table ~name:"comment" [`BACKGROUND "violet"]
  let sentence = make_tag table ~name:"sentence" [`BACKGROUND "grey"]
  let sentence_end = make_tag table ~name:"sentence_end" [`UNDERLINE `SINGLE]
*)

  let error = make_tag table ~name:"error"
    [ `FOREGROUND "red" ]
  let broken = make_tag table ~name:"broken"
    [ `BACKGROUND !broken_color] (*; `EDITABLE false ]*)
  let processing = make_tag table ~name:"processing"
    [ `BACKGROUND !processing_color] (* ;`EDITABLE false ]*)
  let processed = make_tag table ~name:"processed"
    [ `BACKGROUND !processed_color] (*;`EDITABLE false ]*)
  let unsafe = make_tag table ~name:"unsafe"
    [ `FOREGROUND "red"; `BACKGROUND "gold"] (*; `EDITABLE false ]*)

  let found = make_tag table ~name:"found"
    [ `BACKGROUND "blue"; `FOREGROUND "white" ]
end
module Proof =
struct
  let table = GText.tag_table ()
  let highlight = make_tag table ~name:"highlight"
    [`BACKGROUND !processed_color]
  let hypothesis = make_tag table ~name:"hypothesis" []
  let goal = make_tag table ~name:"goal" []
end
module Message =
struct
  let table = GText.tag_table ()
  let error = make_tag table ~name:"error" [`FOREGROUND "red"]
end

let string_of_color clr =
  let r = Gdk.Color.red clr in
  let g = Gdk.Color.green clr in
  let b = Gdk.Color.blue clr in
  Printf.sprintf "#%04X%04X%04X" r g b

let color_of_string s =
  let colormap = Gdk.Color.get_system_colormap () in
  Gdk.Color.alloc ~colormap (`NAME s)

let get_processed_color () = color_of_string !processed_color

let set_processed_color clr =
  let s = string_of_color clr in
  processed_color := s;
  Script.processed#set_property (`BACKGROUND s);
  Proof.highlight#set_property (`BACKGROUND s)

let get_processing_color () = color_of_string !processing_color

let set_processing_color clr =
  let s = string_of_color clr in
  processing_color := s;
  Script.processing#set_property (`BACKGROUND s)
