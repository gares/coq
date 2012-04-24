(* Futures: for now lazy computations with some purity enforcing *)

type 'a computation
type 'a value = [ `Val of 'a | `Exn of exn ]

val create    : (unit -> 'a) -> 'a computation
val from_val  : 'a -> 'a computation
val from_here : 'a -> 'a computation
val is_over   : 'a computation -> bool
val is_val    : 'a computation -> bool
val peek_val  : 'a computation -> 'a option

(* chain in an inpure way computations
 *   i.e. in [chain c f] f will execute in an environment modified by c
 *   unless ~pure:true *)
val chain    : ?id:string -> ?pure:bool -> 'a computation -> ('a -> 'b) -> 'b computation

(* pure functions forcing a computation *)
val force    : 'a computation -> 'a
val compute  : 'a computation -> 'a value

(* final call, no more impure chain allowed *)
val join     : 'a computation -> 'a

(* these are needed to get rid of side effects *)
val set_freeze : (unit -> Dyn.t) -> (Dyn.t -> unit) -> unit
(* once set_freeze is called we can purify a computation *)
val purify : ('a -> 'b) -> 'a -> 'b

(* NOTE: output computations are pure *)
val split2 : ('a * 'b) computation -> 'a computation * 'b computation
val split3 : 
  ('a * 'b * 'c) computation -> 'a computation * 'b computation * 'c computation
