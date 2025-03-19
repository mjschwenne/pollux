module Proof
// Need to import multiplication... apparently
open FStar.Mul
open FStar.List.Tot

let rec factorial (n:nat) : nat = 
  if n = 0 
  then 1
  else n * factorial (n - 1)
  
let rec pow2 (n:nat) : nat =
  if n = 0 then 1 
  else 2 * pow2 (n - 1)

let proof_by_normalization ()
  : Lemma (pow2 12 == 4096)
  = normalize_term_spec (pow2 12)

let proof_fact_normalization ()
  : Lemma (factorial 3 == 6)
  = normalize_term_spec (factorial 3)

let l : list nat = [1;2;3]
let l' : list nat = [4;5;6]
let l2 : list nat = l@l'
  
// The references in the book seem outdated or incomplete. 
// I can't get F* to find some of these tactics.
// let pow2_bound_19 (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) = 
//   FStar.Math.Lemmas.pow2_le_compat 19 x;
//   assert (pow2 19 == 524288) by compute ();
//   assert (pow2 x < 1000000);
//   ()
