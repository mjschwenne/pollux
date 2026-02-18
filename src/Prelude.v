Require Stdlib.ZArith.BinIntDef Stdlib.PArith.BinPosDef Stdlib.NArith.BinNatDef.

Number Notation BinNums.Z BinIntDef.Z.of_num_int BinIntDef.Z.to_num_int : Z_scope.
Number Notation BinNums.positive BinPosDef.Pos.of_num_int BinPosDef.Pos.to_num_int : positive_scope.
Number Notation BinNums.N BinNatDef.N.of_num_int BinNatDef.N.to_num_int : N_scope.

Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.

Notation "x 'eqn' ':' p" := (exist _ x p) (only parsing, at level 20).

Ltac _mk_eq def :=
  let x := (eval red in def) in
  exact x.
Notation mk_eq def :=
  (eq_refl : ltac:(_mk_eq def) = def) (only parsing).

Require Export List.
From Stdlib Require Export Lists.List.
Export ListNotations.

From Perennial Require Export Helpers.Word.Integers.
From Stdlib Require Export Strings.String.
From coqutil Require Export Word.Interface.
From stdpp Require Export gmap.
From stdpp Require Export mapset.

Notation "x == y" := (decide (eq x y)) (no associativity, at level 70).
