Require Stdlib.ZArith.BinIntDef Stdlib.PArith.BinPosDef Stdlib.NArith.BinNatDef.

Number Notation BinNums.Z BinIntDef.Z.of_num_int BinIntDef.Z.to_num_int : Z_scope.
Number Notation BinNums.positive BinPosDef.Pos.of_num_int BinPosDef.Pos.to_num_int : positive_scope.
Number Notation BinNums.N BinNatDef.N.of_num_int BinNatDef.N.to_num_int : N_scope.

Require Import List.
Import ListNotations.
