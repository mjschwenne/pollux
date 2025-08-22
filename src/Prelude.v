Require Stdlib.ZArith.BinIntDef Stdlib.PArith.BinPosDef Stdlib.NArith.BinNatDef.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Number Notation BinNums.Z BinIntDef.Z.of_num_int BinIntDef.Z.to_num_int : Z_scope.
Number Notation BinNums.positive BinPosDef.Pos.of_num_int BinPosDef.Pos.to_num_int : positive_scope.
Number Notation BinNums.N BinNatDef.N.of_num_int BinNatDef.N.to_num_int : N_scope.
