module Part1.GettingOffTheGround 
open FStar.Mul

let incr (x:int) : int = x + 1
let incr1 (x:int) : y:int{y > x} = x + 1
// let incr2 (x:int) : nat = x + 1
let incr3 (x:nat) : nat = x + 1
val incr4 (x:int) : int 
let incr4 x = x + 1
let incr5 (x:int) : y:int{y = x + 1} = x + 1
let incr6 (x:int) : y:int{x = y - 1} = x + 1
// Setup for something about proving alternation of even and odd numbers for instance
let incr7 (x:int) : y:int{if x%2 = 0 then y%2 = 1 else y%2 = 0} = x + 1


val max (x:int) (y:int) : z:int{z >= x /\ z >= y /\ (z = x || z = y)}
let max x y = if x >= y then x else y

let rec factorial (n:nat) : r:nat{r >= 1 /\ r >= n} = 
  if n = 0 
  then 1
  else n * factorial (n - 1)

let rec fibonacci (n:nat) : r:nat{r >= 1 /\ r >= n} = 
  if n <= 1 
  then 1 
  else fibonacci (n - 1) + fibonacci (n - 2)
