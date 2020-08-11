type 'a t = 'a
let return x = x
let catch f g = try f () with e -> g e
let fail e = raise e
let bind e f = f e
module Infix = struct
  let (>>=) = bind
end
type ('a,'b) result = Ok of 'a | Error of 'b
let result_return x = Ok x
let result_fail x = Error x
let main_run x = x