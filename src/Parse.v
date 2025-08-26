From Pollux Require Import Prelude.

From Pollux Require Import Descriptors.
From Pollux Require Import Varint.

Module Parse.

  Include Descriptors.
  Infix "%" := Z.modulo (at level 35) : Z_scope.
  Infix "==" := Z.eqb (at level 35) : Z_scope.

  Definition parity (z : Z) : Z :=
    if ((z % 2) == 0)%Z then 1 else (-1).

  Definition idn (c : bool) : Z := if c then 1 else 0.

  Definition uint_change_w (w : Width) (v : Z) : Z := v % (2^(unwrap_width w)).
  Definition int_change_w (w : Width) (v : Z) : Z := let pow2__w := (2^((unwrap_width w) - 1))%Z in
                                                     (v `mod` pow2__w - pow2__w * idn (( v / pow2__w) % 2 == 1)).
  Definition sint_change_w (w : Width) (v : Z) : Z := let pow2__w := (2^((unwrap_width w) - 1))%Z in
                                                      (v `mod` pow2__w - pow2__w * idn (Z.ltb v 0)).
  Definition uint_int (w : Width) (v : Z) : Z := v - (2^(unwrap_width w)) *
                                                       (idn (Z.geb v (2^(unwrap_width w - 1))%Z)).
  Definition int_uint (w : Width) (v : Z) : Z := v + (2^(unwrap_width w)) * (idn (Z.ltb v 0)).
  Definition uint_sint (w : Width) (v : Z) : Z := parity v * (v / 2) - (v % 2).
  Definition sint_uint (w : Width) (v : Z) : Z := 2 * (Z.abs v) - idn (Z.ltb v 0).
  Definition int_sint (w : Width) (v : Z) : Z := if Z.geb v 0 then
                                                   parity v * (v / 2) - (v % 2)
                                                 else
                                                   parity v * (v + (2^(unwrap_width w - 1)) - (v / 2)).
  Definition sint_int (w : Width) (v : Z) : Z := if Z.leb (- 2^(unwrap_width w - 2)) v &&
                                                      Z.leb v (2^(unwrap_width w - 2)) then
                                                   2 * (Z.abs v) - idn (Z.ltb v 0)
                                                 else
                                                   2 * (Z.abs v) - (2^(unwrap_width w)) - idn (Z.ltb v 0).

    (* NOTE: Compared to the F* version, these functions no longer have type-level assurances
       that the resulting integer is in-bounds for the given width. Now, the F* functions only
       had this assurance, so the formula could still be wrong, which is why there were / are
       tested against the official protobuf implementation.
     *)
  
End Parse.
