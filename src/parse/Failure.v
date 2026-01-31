From Pollux Require Import Prelude.
From Pollux.parse Require Import Util.
From Pollux.parse Require Import Input.

From Corelib.Program Require Import Basics Tactics.
From Stdlib.Program Require Import Program.

Module Failures (InputModule : AbstractInput).
  Section Failure.
    Import InputModule.

    Context `{EqDecision Input}.

    Inductive Level :=
    | Fatal
    | Recoverable.

    (* Record information about when a parse / serialize fails *)
    (* I'll use the failure data for the serializers too, but interpret "remaining" as "output". *)
    Inductive Data :=
    | mkData (msg : string) (remaining : Input) (next : option Data).

    Definition getMsg (data : Data) : string :=
      match data with
      | mkData msg _ _ => msg
      end.

    Definition getRemaining (data : Data) : Input :=
      match data with
      | mkData _ remaining _ => remaining
      end.

    Definition getNext (data : Data) : option Data :=
      match data with
      | mkData _ _ next => next
      end.

    (* Add more failure data to the end of the current chain of failures *)
    Fixpoint Concat (self other : Data) : Data :=
      match self with
      | mkData msg remaining next =>
          match next with
          | None => mkData msg remaining (Some other)
          | Some next_val => mkData msg remaining (Some (Concat next_val other))
          end
      end.

  End Failure.
End Failures.
