(* hack to avoid side effects *)
let freeze = ref (fun () -> assert false : unit -> Dyn.t)
let unfreeze = ref (fun _ -> () : Dyn.t -> unit)
let set_freeze f g = freeze := f; unfreeze := g

(* Val is not necessarily a final state, so the
   computation restarts from the pairsed state *) 
type 'a comp =
  | Closure of (unit -> 'a)
  | Val of 'a * Dyn.t option
  | Exn of exn

type 'a computation = 'a comp ref

type 'a value = [ `Val of 'a | `Exn of exn ]

let is_over x = match !x with
  | Val _ | Exn _ -> true
  | Closure _ -> false

let is_val x = match !x with
  | Val _ -> true 
  | Exn _ | Closure _ -> false

let peek_val x = match !x with
  | Val (v, _) -> Some v
  | Exn _ | Closure _ -> None 

let create f = ref (Closure f)
let from_val v = ref (Val (v, None))
let from_here v = ref (Val (v, Some (!freeze ())))
let proj = function
  | `Val (x, _ ) -> `Val x
  | `Exn e -> `Exn e

(* TODO: get rid of try/catch *)
let compute ~pure c : 'a value = match !c with
  | Val (x, _) -> `Val x
  | Exn e -> `Exn e
  | Closure f ->
      try 
        let data = f () in
        let state = if pure then None else Some (!freeze ()) in
        c := Val (data, state); `Val data
      with e -> c := Exn e; `Exn e

let force ~pure x = match compute ~pure x with
  | `Val v -> v
  | `Exn e -> raise e

let chain ?(id="none") ?(pure=false) c f = ref (match !c with
  | Closure _ -> Closure (fun () -> f (force ~pure c))
  | Exn _ as x -> x
  | Val (v, None) -> Closure (fun () -> f v)
  | Val (v, Some _) when pure ->  Closure (fun () -> f v)
  | Val (v, Some state) -> 
       prerr_endline ("Future: restarting (check if optimizable): " ^ id);
       Closure (fun () -> !unfreeze state; f v))

let purify f x =
  let state = !freeze () in
  try 
    let v = f x in
    !unfreeze state;
    v
  with e -> !unfreeze state; raise e

let purify_future f x =
  match !x with
  | Val _ | Exn _ -> f x
  | Closure _ -> purify f x

let compute x = purify_future (compute ~pure:false) x
let force x = purify_future (force ~pure:false) x

let join x =
  let v = force x in
  (x := match !x with 
       | Val (x,_) -> Val (x, None) 
       | Exn e -> Exn e 
       | Closure f -> assert false);
  v

let split2 x =
  chain ~pure:true x (fun x -> fst x),
  chain ~pure:true x (fun x -> snd x)

let split3 x =
  chain ~pure:true x (fun x -> Util.pi1 x), 
  chain ~pure:true x (fun x -> Util.pi2 x), 
  chain ~pure:true x (fun x -> Util.pi3 x)

