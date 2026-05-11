From Pollux Require Import Prelude.

Module Util.

  Definition sublist {A : Type} (first : nat) (last : nat) (l : list A) :=
    take (last - first) $ drop (first) l.

  Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool) (l1 : list A) (l2 : list A) : bool :=
    match l1, l2 with
    | [], [] => true
    | (_ :: _), []
    | [], (_ :: _) => false
    | (h1 :: t1), (h2 :: t2) => if eqb h1 h2 then
                                 list_eqb eqb t1 t2
                               else
                                 false
    end.
  
End Util.
