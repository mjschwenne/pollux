module Part1.Polymorphism 
open FStar.Mul

let id : a:Type -> a -> a = fun a x -> x
let id' (a:Type) (x:a) = x

let _ : bool = id bool true
let _ : bool = id' bool true
let _ : int = id int (-1)
let _ : nat = id' nat 17

val apply (a b:Type) (f:a -> b) : a -> b
let apply a b f = fun x -> f x

val compose (a b c:Type) (f:b -> c) (g:a -> b) : a -> c
let compose a b c f g = fun x -> f (g x)

// implicit arguments / type inference would help improve usability.

let _ : int -> int = id _ (id _)

// That was type inference, implicit arguments would by this:
// Denoted with a '#'

let id'' (#a:Type) (x:a) : a = x
let _ : bool = id'' true
let x = id'' 0
// Assumes x is an int, but we can still pass a type if needed,
let y = id'' #nat 0
let _ = id'' #(x:int{x <> 1}) 0
