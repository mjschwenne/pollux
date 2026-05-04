/-
  Pollux.InterParse.Theorems.Compatible — The `Compatible` relation between
  descriptor/value pairs (used for schema-evolution correctness).
-/
import Pollux.InterParse.Theorems.SortedHelpers
import Pollux.InterParse.Theorems.SchemaCorrect

namespace Pollux.InterParse

/-! ## Compatible relation

The `Compatible` relation captures when two descriptor/value pairs represent
the same information — used for proving schema-evolution correctness. -/

inductive Compatible : Desc → Desc → Value → Value → Prop where
  | refl (d1 d2 : Desc) (v : Value) :
    ⟨ v ∷ d1 ⟩ → ⟨ v ∷ d2 ⟩ → Compatible d1 d2 v v
  | add (d1 : Desc) (v1 : Value) (d2 : Desc) (v2 : Value)
    (k : Int) (f1 f2 : Field) (v'1 v'2 : Val) :
    ⟨ v1 ∷ d1 ⟩ → ⟨ v2 ∷ d2 ⟩ →
    Compatible d1 d2 v1 v2 →
    v1.get? k = none →
    v2.get? k = none →
    d1.get? k = none →
    d2.get? k = none →
    v'1 = v'2 → f1 = f2 →
    Compatible (d1.insert k f1) (d2.insert k f2)
      (v1.insert k v'1) (v2.insert k v'2)

notation "⟨ " v1 " ∷ " d1 " ⟩≼⟨ " v2 " ∷ " d2 " ⟩" =>
  Compatible d1 d2 v1 v2

theorem compatibleEqual (d1 : Desc) (v1 : Value) (d2 : Desc) (v2 : Value) :
    Compatible d1 d2 v1 v2 → d1 = d2 → v1 = v2 := by
      intro hc
      induction hc with
      | refl _ _ _ _ _ => intro _; rfl
      | add d1' v1' d2' v2' k f1 f2 vv1 vv2 _ _ _ hv1n hv2n hd1n hd2n hveq hfeq ih =>
        intro hd
        subst hveq; subst hfeq
        have hd_eq : d1' = d2' := by
          cases d1' with | mk fs1 =>
          cases d2' with | mk fs2 =>
          have hd' : Desc.sortedInsert k f1 fs1 = Desc.sortedInsert k f1 fs2 := by
            unfold Desc.insert at hd
            simp [Desc.fields] at hd
            exact hd
          have hd1_lookup : List.lookup k fs1 = none := hd1n
          have hd2_lookup : List.lookup k fs2 = none := hd2n
          have heq : Desc.sortedErase k (Desc.sortedInsert k f1 fs1)
                     = Desc.sortedErase k (Desc.sortedInsert k f1 fs2) := by rw [hd']
          rw [desc_sortedErase_sortedInsert k f1 fs1 hd1_lookup,
              desc_sortedErase_sortedInsert k f1 fs2 hd2_lookup] at heq
          exact congrArg Desc.mk heq
        have hv_eq := ih hd_eq
        exact congrArg (fun v => v.insert k vv1) hv_eq

end Pollux.InterParse
