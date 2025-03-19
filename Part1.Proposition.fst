module Part1.Proposition
open FStar.Mul

let rec factorial (n:nat) : r:nat{r >= 1 /\ r >= n} = 
  if n = 0 
  then 1
  else n * factorial (n - 1)

let sqr_is_nat (x:int) : unit = assert (x * x >= 0)

let max x y = if x > y then x else y
let _ = assert (max 0 1 = 1)
let _ = assert (forall x y. max x y >= x /\ max x y >= y /\ (max x y = x \/ max x y = y))

let sqr_is_pos (x:int) = assume (x <> 0); assert (x * x > 0)
let sqr_is_pos' (x:int{x <> 0}) = assert (x * x > 0)

let _ : nat = 4 % 2

// let factor : unit = assert (forall (x:nat) (y:nat{y > 0}). x % y = 0 ==> (exists (z:nat). x = z * y))
