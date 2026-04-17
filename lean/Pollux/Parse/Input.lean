/-
  Pollux.Parse.Input — Abstract input interface for parsers and serializers.

  Corresponds to src/parse/Input.v in the Rocq development.

  The `Input` class abstracts over the concrete representation of byte sequences,
  providing operations (append, drop, slice, etc.) and their algebraic properties.
  `ByteInput` instantiates this with `List UInt8`.
-/
import Mathlib

namespace Pollux.Parse

/-- Abstract interface for input sequences consumed by parsers and produced by serializers. -/
class Input (ι : Type) where
  /-- The element (character) type. -/
  C : Type
  /-- Empty input. -/
  default : ι
  /-- Default element value. -/
  charDefault : C
  /-- Decidable equality on input values. -/
  [decEq : DecidableEq ι]
  /-- Decidable equality on elements. -/
  [decEqC : DecidableEq C]
  /-- Number of elements in the input. -/
  length : ι → Nat
  /-- View the input as a list of elements. -/
  view : ι → List C
  /-- Construct an input from a list of elements. -/
  toInput : List C → ι
  /-- Access the element at position `i`, returning `charDefault` if out of bounds. -/
  charAt : ι → Nat → C
  /-- Concatenate two inputs. -/
  app : ι → ι → ι
  /-- Drop the first `n` elements. -/
  drop : ι → Nat → ι
  /-- Slice from index `lo` taking `hi` elements (i.e. elements `[lo, lo+hi)`). -/
  slice : ι → Nat → Nat → ι
  -- Algebraic properties
  length_default : length default = 0
  view_length : ∀ s, (view s).length = length s
  toInput_view : ∀ r, view (toInput r) = r
  charAt_spec : ∀ s i, i < length s → charAt s i = (view s).getD i charDefault
  app_view : ∀ s₁ s₂, app s₁ s₂ = toInput (view s₁ ++ view s₂)
  app_default_left : ∀ s, app default s = s
  app_default_right : ∀ s, app s default = s
  app_assoc : ∀ s₁ s₂ s₃, app (app s₁ s₂) s₃ = app s₁ (app s₂ s₃)
  app_length : ∀ s₁ s₂, length (app s₁ s₂) = length s₁ + length s₂
  drop_view : ∀ s n, n ≤ length s → view (drop s n) = (view s).drop n
  drop_zero : ∀ s, drop s 0 = s
  drop_drop : ∀ s a b, a ≤ length s → b ≤ length s - a →
    drop s (a + b) = drop (drop s a) b
  drop_app : ∀ s₁ s₂, drop (app s₁ s₂) (length s₁) = s₂
  slice_view : ∀ s lo hi, lo ≤ hi → hi ≤ length s →
    view (slice s lo hi) = ((view s).drop lo).take (hi - lo)
  slice_app : ∀ s₁ s₂, slice (app s₁ s₂) 0 (length s₁) = s₁

attribute [reducible] Input.decEq Input.decEqC

instance [Input ι] : DecidableEq ι := Input.decEq
instance [Input ι] : DecidableEq (Input.C ι) := Input.decEqC

namespace Input

variable {ι : Type} [Input ι]

/-- `remaining` is a suffix of `input`. -/
def IsRemaining (input remaining : ι) : Prop :=
  length remaining ≤ length input ∧
  drop input (length input - length remaining) = remaining

theorem isRemaining_trans (input rem₁ rem₂ : ι)
    (h₁ : IsRemaining input rem₁) (h₂ : IsRemaining rem₁ rem₂) :
    IsRemaining input rem₂ := by
  have := h₁.2;
  -- By definition of `IsRemaining`, we know that `rem₂` is a suffix of `rem₁`.
  have h_suffix : ‹Input ι›.drop rem₁ (‹Input ι›.length rem₁ - ‹Input ι›.length rem₂) = rem₂ := by
    exact h₂.2;
  refine' ⟨ _, _ ⟩;
  · exact h₂.1.trans h₁.1;
  · convert congr_arg ( fun x => ‹Input ι›.drop x ( ‹Input ι›.length rem₁ - ‹Input ι›.length rem₂ ) ) this using 1;
    · convert ( ‹Input ι›.drop_drop _ _ _ _ _ ) using 2;
      · rw [ tsub_add_tsub_cancel h₁.1 h₂.1 ];
      · exact Nat.sub_le _ _;
      · rw [ Nat.sub_sub_self ( h₁.1 ) ];
        exact Nat.sub_le _ _;
    · exact h_suffix.symm

end Input

/-! ### ByteInput: concrete instantiation with `List UInt8` -/

instance : Input (List UInt8) where
  C := UInt8
  default := []
  charDefault := 0
  length := List.length
  view := id
  toInput := id
  charAt s i := s.getD i 0
  app := (· ++ ·)
  drop s n := s.drop n
  slice s lo hi := (s.drop lo).take (hi - lo)
  length_default := rfl
  view_length _ := rfl
  toInput_view _ := rfl
  charAt_spec := by intros; rfl
  app_view := by intros; rfl
  app_default_left := by simp [List.nil_append]
  app_default_right := by simp [List.append_nil]
  app_assoc := by simp [List.append_assoc]
  app_length := by simp [List.length_append]
  drop_view := by intros; rfl
  drop_zero := by simp [List.drop_zero]
  drop_drop := by intros; simp [List.drop_drop]
  drop_app := by
    aesop
  slice_view := by intros; rfl
  slice_app := by
    aesop

end Pollux.Parse