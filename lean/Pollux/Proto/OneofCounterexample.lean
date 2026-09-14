/-
  Pollux.Proto.OneofCounterexample — why `Value.reinterpret_valid` needs
  the *recursive* oneof side condition.

  `Desc.OneofPreserved d₁ d₂` is a one-layer statement: it quantifies
  over pairs of keys of `d₁` and `d₂` themselves. The transform, though,
  recurses into nested message fields, and at that point the pair of
  descriptors under consideration is a pair of *nested* descriptors,
  about which the one-layer hypothesis says nothing.

  So a reader can merge two fields of a nested message into a oneof
  group while its top layer is entirely oneof-free — the one-layer
  hypothesis then holds vacuously, and the value the transform produces
  violates `Value.OneofOk` one layer down. That is exactly the witness
  built here, and `not_reinterpret_valid_one_layer` proves that the
  originally stated form of `Value.reinterpret_valid` (with the
  one-layer hypothesis) is false. `Desc.OneofPreservedAll`, the
  recursive closure used in `Proto/Transform.lean`, is what rules the
  witness out.

  The descriptors are built through the public interface (`∅`,
  `Desc.insert`), so nothing here reaches through the descriptor seal.
-/
import Pollux.Proto.Transform

namespace Pollux.Proto
namespace OneofCounterexample

/-! ## The witness

Two `bool` fields, independent for the writer and grouped for the
reader, one layer down inside a message field. -/

/-- A `bool` field with explicit presence. -/
def optBool : Field := ⟨.optional, .scalar .bool⟩

/-- The same field, but a member of oneof group `0`. -/
def oneofBool : Field := ⟨.oneof 0, .scalar .bool⟩

/-- The writer's nested descriptor: two independent optional bools. -/
def innerW : Desc := ((∅ : Desc).insert 1 optBool).insert 2 optBool

/-- The reader's nested descriptor: the same two fields, now one oneof
    group. -/
def innerR : Desc := ((∅ : Desc).insert 1 oneofBool).insert 2 oneofBool

/-- The writer's message field. -/
def msgW : Field := ⟨.optional, .msg innerW⟩

/-- The reader's message field — same cardinality, nested descriptor
    changed. -/
def msgR : Field := ⟨.optional, .msg innerR⟩

/-- The writer's descriptor: one message field, no oneof anywhere at
    this layer. -/
def outerW : Desc := (∅ : Desc).insert 1 msgW

/-- The reader's descriptor: likewise no oneof at this layer. -/
def outerR : Desc := (∅ : Desc).insert 1 msgR

/-- The nested value: both fields explicitly set — legal for the writer,
    since the writer does not group them. -/
def innerV : Value :=
  .mk [⟨1, .optional (some (.bool true))⟩, ⟨2, .optional (some (.bool true))⟩]

/-- The writer's value. -/
def outerV : Value := .mk [⟨1, .optional (some (.msg innerV))⟩]

/-! ## Lookups -/

theorem innerW_get1 : innerW.get? 1 = some optBool := by
  simp only [innerW]
  rw [Desc.get?_insert_ne _ _ _ _ (by norm_num), Desc.get?_insert_same]

theorem innerW_get2 : innerW.get? 2 = some optBool := by
  simp only [innerW, Desc.get?_insert_same]

theorem innerW_get_other {k : Int} (h1 : k ≠ 1) (h2 : k ≠ 2) :
    innerW.get? k = none := by
  simp only [innerW]
  rw [Desc.get?_insert_ne _ _ _ _ (Ne.symm h2),
    Desc.get?_insert_ne _ _ _ _ (Ne.symm h1), Desc.get?_empty]

theorem innerR_get1 : innerR.get? 1 = some oneofBool := by
  simp only [innerR]
  rw [Desc.get?_insert_ne _ _ _ _ (by norm_num), Desc.get?_insert_same]

theorem innerR_get2 : innerR.get? 2 = some oneofBool := by
  simp only [innerR, Desc.get?_insert_same]

theorem innerR_get_other {k : Int} (h1 : k ≠ 1) (h2 : k ≠ 2) :
    innerR.get? k = none := by
  simp only [innerR]
  rw [Desc.get?_insert_ne _ _ _ _ (Ne.symm h2),
    Desc.get?_insert_ne _ _ _ _ (Ne.symm h1), Desc.get?_empty]

theorem outerW_get1 : outerW.get? 1 = some msgW := by
  simp only [outerW, Desc.get?_insert_same]

theorem outerW_get_other {k : Int} (h1 : k ≠ 1) : outerW.get? k = none := by
  simp only [outerW]
  rw [Desc.get?_insert_ne _ _ _ _ (Ne.symm h1), Desc.get?_empty]

theorem outerR_get1 : outerR.get? 1 = some msgR := by
  simp only [outerR, Desc.get?_insert_same]

theorem outerR_get_other {k : Int} (h1 : k ≠ 1) : outerR.get? k = none := by
  simp only [outerR]
  rw [Desc.get?_insert_ne _ _ _ _ (Ne.symm h1), Desc.get?_empty]

theorem innerV_get1 : innerV.get? 1 = some (.optional (some (.bool true))) := by
  simp [innerV, Value.get?]

theorem innerV_get2 : innerV.get? 2 = some (.optional (some (.bool true))) := by
  simp [innerV, Value.get?]

theorem innerV_get_other {k : Int} (h1 : k ≠ 1) (h2 : k ≠ 2) :
    innerV.get? k = none := by
  simp only [innerV, Value.get?, Value.entries_mk]
  rw [List.dlookup_cons_ne _ _ h1, List.dlookup_cons_ne _ _ h2]
  rfl

theorem outerV_get1 : outerV.get? 1 = some (.optional (some (.msg innerV))) := by
  simp [outerV, Value.get?]

theorem outerV_get_other {k : Int} (h1 : k ≠ 1) : outerV.get? k = none := by
  simp only [outerV, Value.get?, Value.entries_mk]
  rw [List.dlookup_cons_ne _ _ h1]
  rfl

/-! ## The writer's value is valid -/

/-- An explicitly-set `true` inhabits an optional `bool` field. -/
theorem matches_optBool :
    Slot.Matches (.optional (some (.bool true))) optBool := by
  show Slot.Matches (.optional (some (.bool true)))
    (Field.mk .optional (.scalar .bool))
  rw [Slot.Matches, Payload.Matches, Payload.MatchesScalar]
  trivial

theorem innerV_valid : Value.Valid innerW innerV := by
  refine Value.valid_of_mem ?_ ?_ ?_ ?_
  · simp [Value.WF, innerV, SortedMap.WF]
  · intro k
    by_cases h1 : k = 1
    · subst h1; rw [innerV_get1, innerW_get1]; simp
    · by_cases h2 : k = 2
      · subst h2; rw [innerV_get2, innerW_get2]; simp
      · simp [innerV_get_other h1 h2, innerW_get_other h1 h2]
  · intro k₁ k₂ f₁ f₂ g p₁ p₂ _ hd₁ _ hc₁ _ _ _
    by_cases h1 : k₁ = 1
    · subst h1; rw [innerW_get1] at hd₁; cases hd₁; simp [optBool, Field.card] at hc₁
    · by_cases h2 : k₁ = 2
      · subst h2; rw [innerW_get2] at hd₁; cases hd₁; simp [optBool, Field.card] at hc₁
      · rw [innerW_get_other h1 h2] at hd₁; exact absurd hd₁ (by simp)
  · intro e he
    simp only [innerV, Value.entries_mk, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨optBool, innerW_get1, matches_optBool⟩
    · exact ⟨optBool, innerW_get2, matches_optBool⟩

/-- The nested value inhabits the writer's message field. -/
theorem matches_msgW : Slot.Matches (.optional (some (.msg innerV))) msgW := by
  show Slot.Matches (.optional (some (.msg innerV)))
    (Field.mk .optional (.msg innerW))
  rw [Slot.Matches, Payload.Matches]
  exact innerV_valid

theorem outerV_valid : Value.Valid outerW outerV := by
  refine Value.valid_of_mem ?_ ?_ ?_ ?_
  · simp [Value.WF, outerV, SortedMap.WF]
  · intro k
    by_cases h1 : k = 1
    · subst h1; rw [outerV_get1, outerW_get1]; simp
    · simp [outerV_get_other h1, outerW_get_other h1]
  · intro k₁ k₂ f₁ f₂ g p₁ p₂ _ hd₁ _ hc₁ _ _ _
    by_cases h1 : k₁ = 1
    · subst h1; rw [outerW_get1] at hd₁; cases hd₁; simp [msgW, Field.card] at hc₁
    · rw [outerW_get_other h1] at hd₁; exact absurd hd₁ (by simp)
  · intro e he
    simp only [outerV, Value.entries_mk, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    exact ⟨msgW, outerW_get1, matches_msgW⟩

/-! ## The reader's descriptor satisfies every other hypothesis -/

theorem innerR_allWF : innerR.AllWF := by
  refine Desc.AllWF.insert 2 (Desc.AllWF.insert 1 Desc.allWF_empty ?_) ?_ <;>
    exact trivial

theorem outerR_allWF : outerR.AllWF :=
  Desc.AllWF.insert 1 Desc.allWF_empty innerR_allWF

theorem oneofBool_fieldOk {k : Int} (h : FieldNumber.Valid k) :
    Desc.FieldOk k oneofBool :=
  ⟨h, fun hc => by simp [oneofBool, Field.card] at hc⟩

theorem innerR_legal : innerR.Legal := by
  rw [Desc.legal_def]
  constructor
  · intro k f hf
    by_cases h1 : k = 1
    · subst h1
      rw [innerR_get1] at hf; cases hf
      exact oneofBool_fieldOk ⟨by norm_num, by norm_num, by norm_num⟩
    · by_cases h2 : k = 2
      · subst h2
        rw [innerR_get2] at hf; cases hf
        exact oneofBool_fieldOk ⟨by norm_num, by norm_num, by norm_num⟩
      · rw [innerR_get_other h1 h2] at hf; exact absurd hf (by simp)
  · intro k c d' hf
    by_cases h1 : k = 1
    · subst h1; rw [innerR_get1] at hf; simp [oneofBool] at hf
    · by_cases h2 : k = 2
      · subst h2; rw [innerR_get2] at hf; simp [oneofBool] at hf
      · rw [innerR_get_other h1 h2] at hf; exact absurd hf (by simp)

theorem outerR_legal : outerR.Legal := by
  rw [Desc.legal_def]
  constructor
  · intro k f hf
    by_cases h1 : k = 1
    · subst h1
      rw [outerR_get1] at hf; cases hf
      exact ⟨⟨by norm_num, by norm_num, by norm_num⟩,
        fun hc => by simp [msgR, Field.card] at hc⟩
    · rw [outerR_get_other h1] at hf; exact absurd hf (by simp)
  · intro k c d' hf
    by_cases h1 : k = 1
    · subst h1
      rw [outerR_get1] at hf
      simp only [msgR, Option.some.injEq] at hf
      obtain ⟨-, hd⟩ := Field.mk.injEq .. ▸ hf
      cases hd
      exact innerR_legal
    · rw [outerR_get_other h1] at hf; exact absurd hf (by simp)

/-- The *one-layer* oneof condition holds vacuously: the reader's own
    field list contains no oneof member at all. -/
theorem outer_oneofPreserved : Desc.OneofPreserved outerW outerR := by
  intro k₁ k₂ f₁ f₂ f₁' f₂' g _ _ hr₁ _ hc₁ _
  by_cases h1 : k₁ = 1
  · subst h1; rw [outerR_get1] at hr₁; cases hr₁; simp [msgR, Field.card] at hc₁
  · rw [outerR_get_other h1] at hr₁; exact absurd hr₁ (by simp)

/-! ## What the transform produces -/

theorem inner_reinterpret_get1 :
    (Value.reinterpret innerW innerR innerV).get? 1
      = some (.optional (some (.bool true))) := by
  rw [Value.get?_reinterpret, innerR_get1, Option.map_some,
    Value.reinterpretAt_of_shared innerW_get1 innerV_get1]
  simp [Slot.reinterpret, optBool, oneofBool, Field.card, Field.ty,
    Cardinality.explicit, Payload.reinterpret]

theorem inner_reinterpret_get2 :
    (Value.reinterpret innerW innerR innerV).get? 2
      = some (.optional (some (.bool true))) := by
  rw [Value.get?_reinterpret, innerR_get2, Option.map_some,
    Value.reinterpretAt_of_shared innerW_get2 innerV_get2]
  simp [Slot.reinterpret, optBool, oneofBool, Field.card, Field.ty,
    Cardinality.explicit, Payload.reinterpret]

theorem outer_reinterpret_get1 :
    (Value.reinterpret outerW outerR outerV).get? 1
      = some (.optional (some (.msg (Value.reinterpret innerW innerR innerV)))) := by
  rw [Value.get?_reinterpret, outerR_get1, Option.map_some,
    Value.reinterpretAt_of_shared outerW_get1 outerV_get1]
  simp [Slot.reinterpret, msgW, msgR, Field.card, Field.ty,
    Cardinality.explicit, Payload.reinterpret]

/-! ## The negation -/

/-- **The one-layer oneof hypothesis is not enough.** With
    `Desc.OneofPreserved` in place of its recursive closure, the
    conclusion of `Value.reinterpret_valid` fails: the witness above
    satisfies every hypothesis, yet the transform's output violates
    `Value.OneofOk` inside the nested message. -/
theorem not_reinterpret_valid_one_layer :
    ¬ ∀ (d₁ d₂ : Desc) (v : Value), Value.Valid d₁ v → d₂.AllWF → d₂.Legal →
        Desc.OneofPreserved d₁ d₂ →
        Value.Valid d₂ (Value.reinterpret d₁ d₂ v) := by
  intro H
  have hvalid :=
    H outerW outerR outerV outerV_valid outerR_allWF outerR_legal outer_oneofPreserved
  have hm := hvalid.matches outer_reinterpret_get1 outerR_get1
  have hm' : Value.Valid innerR (Value.reinterpret innerW innerR innerV) := by
    have : Slot.Matches
        (.optional (some (.msg (Value.reinterpret innerW innerR innerV))))
        (Field.mk .optional (.msg innerR)) := hm
    rwa [Slot.Matches, Payload.Matches] at this
  exact hm'.oneofOk 1 2 oneofBool oneofBool 0 (.bool true) (.bool true)
    (by norm_num) innerR_get1 innerR_get2 rfl rfl
    inner_reinterpret_get1 inner_reinterpret_get2

end OneofCounterexample
end Pollux.Proto
