module Part1.Termination 
open FStar.List.Tot

// let rec loop (x:unit) : False = loop x

let rec length #a (l:list a) : Tot nat (decreases l) =
  match l with 
  | [] -> 0
  | _ :: tl -> length tl

// We can use the well-founded << ordering to build lexicographical ordering 

let rec ackermann (m n:nat) : Tot nat (decreases %[m;n]) = 
  if m = 0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))

// the above function looks at the lexicographical ordering of other arguments
// in the form of a list [m;n]

// The default measure is all non-function arguments from left to right 
// compared lexicographically.

// Mutual recursion uses the "and" keyword 
type tree = 
  | Terminal : tree
  | Internal : node -> tree 

and node = {
  left : tree; 
  data : int;
  right : tree
}

let rec incr_tree (t:tree) : tree = 
  match t with 
  | Terminal -> Terminal 
  | Internal node -> Internal (incr_node node)

and incr_node (n:node) : node = {
  left = incr_tree n.left;
  data = n.data + 1;
  right = incr_tree n.right
}

// Exercise: Prove fib terminates 

let rec fibonacci (n:nat) : nat =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

let rec fib (a b n:nat) : Tot nat (decreases n) =
  match n with 
  | 0 -> a
  | _ -> fib b (a+b) (n-1)
let fibonacci' (n:nat) = fib 1 1 n

// Despite decreases n being the first thing I tried, F*
// needed the parameters to be labeled as nats before accepting fib

// Exercise: Prove rev and rev_aux terminate 

let rec rev_aux #a (l1 l2:list a) : Tot (list a) (decreases l2) =
  match l2 with 
  | [] -> l1
  | hd::tl -> rev_aux (hd :: l1) tl

let rev l = rev_aux [] l
