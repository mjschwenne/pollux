module Part1.Inductive
open FStar.Mul

type three = 
  | One_of_three
  | Two_of_three
  | Three_of_three

let distinct = assert (One_of_three <> Two_of_three /\ 
                       Two_of_three <> Three_of_three /\
                       Three_of_three <> One_of_three)

let exhaustive (x:three) = assert (x = One_of_three \/ 
                                   x = Two_of_three \/
                                   x = Three_of_three)

let is_one (x:three) : bool = 
  match x with 
  | One_of_three -> true
  | _ -> false 

let is_two (x:three) : bool = 
  match x with 
  | Two_of_three -> true
  | _ -> false 

let is_three (x:three) : bool = 
  match x with 
  | Three_of_three -> true 
  | _ -> false 

let three_as_int (x:three) : int = 
  if is_one x then 1
  else if is_two x then 2
  else 3

// Note that last one required three helper functions. 
// Checking if a variable has a particular constructor is 
// so common that there is a shorthand for it.
let three_as_int' (x:three) : int = 
  if One_of_three? x then 1
  else if Two_of_three? x then 2 
  else 3

// Naturally a match statement would be more direct 
let three_as_int'' (x:three) : int = 
  match x with 
  | One_of_three -> 1 
  | Two_of_three -> 2
  | Three_of_three -> 3

// We can also use this with refinement to eliminate cases 
// while maintaining exhaustiveness 
let only_two_as_int (x:three{ not (Three_of_three? x) }) : int = 
  match x with 
  | One_of_three -> 1
  | Two_of_three -> 2

type tup2 (a:Type) (b:Type) = 
  | Tup2 : fst:a -> snd:b -> tup2 a b

let tup2_fst #a #b (x:tup2 a b) : a =
  match x with 
  | Tup2 fst _ -> fst 

let tup2_snd #a #b (x:tup2 a b) : b =
  match x with 
  | Tup2 _ snd -> snd

// F* also generates projectors for any constructor T of type 
// x1:t1 -> ... -> xn:tn -> t
let tup2_fst' #a #b (x:tup2 a b) : a = Tup2?.fst x
let tup2_snd' #a #b (x:tup2 a b) : b = Tup2?.snd x

// That's before we even get to built in tuples, supported to arity 14
// Without using FStar.Mul, we can write this with type int * int as well.
let _ : int & int = 1, 2

let tup2_fst'' #a #b (x: a & b) = x._1

// Moving on from tuples, we know have records
type point3D = {x:int; y:int; z:int}
// Notice the out of order labels
let origin = { y=0; x=0; z=0 }

let dot (p0 p1:point3D) = p0.x * p1.x + p0.y * p1.y + p0.z * p1.z
// The "with" syntax builds a new record by modifying the fields mentioned in the 
// statement
let translate_X (p:point3D) (shift:int) = { p with x = p.x + shift }
// Since the fields are named, we can match them in any order 
let is_origin (x:point3D) = 
  match x with 
  | {z=0;y=0;x=0} -> true 
  | _ -> false
let is_origin' (x:point3D) = 
  match x with 
  | origin -> true 
  | _ -> false

let try_divide (x y:int) : option int =
  if y = 0 then None else Some (x / y)

let divide (x:int) (y:int{y<>0}) = x / y

// Consider the sum type or tagged union below
type either a b = 
  | Inl: v:a -> either a b
  | Inr: v:b -> either a b

let same_case #a #b #c #d (x:either a b) (y:either c d) : bool =
  match x, y with 
  | Inl _, Inl _
  | Inr _, Inr _ -> true 
  | _ -> false

let sum (x:either bool int) (y:(either bool int){same_case x y})
  : z:either bool int{ Inl? z <==> Inl? x }
  = match x, y with 
    | Inl xl, Inl yl -> Inl(xl || yl)
    | Inr xr, Inr yr -> Inr(xr + yr)

type list a = 
  | Nil : list a 
  | Cons : hd:a -> tl:list a -> list a

// Comments show standard list syntax I can't use right now since 
// the build in list is masked by my list above.
let rec length #a (l:list a) : nat = 
  match l with 
  // | [] -> 0
  | Nil -> 0
  // | _ :: tl -> 1 + length tl
  | Cons hd tl -> 1 + length tl

let rec append #a (l1:list a) (l2:list a) 
  : l:list a{length l = length l1 + length l2} 
  = match l1 with 
    | Nil -> l2
    | Cons hd tl -> Cons hd (append tl l2)
