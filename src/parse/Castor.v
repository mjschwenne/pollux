From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.
From Pollux.parse Require Import Result.
From Pollux.parse Require Import Parser.
From Pollux.parse Require Import Serializer.
From Pollux.parse Require Import Theorems.
From Pollux.parse Require Import TheoremsRel.

From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Module Castor (Input : AbstractInput).
  Declare Module R : Result Input.
  Declare Module Parser : Parser Input R.
  Declare Module Serializer : Serializer Input R.
  Declare Module T : Theorems Input R Parser Serializer with Module S := Serializer with Module P := Parser.
  Declare Module TR : TheoremsRel Input R Parser Serializer T.

  Import Input.
  Export Input.
  Import R.
  Export R.
  Import T.
  Export T.
  Import TR.
  Export TR.
End Castor.
