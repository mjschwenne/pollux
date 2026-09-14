/-
  Pollux.Proto.SortedMap — the sorted sigma-list map theory, parameterized
  over the payload type.

  `Desc` (sealed) and `Value` (unsealed) both store their field map as a
  key-sorted `List ((_ : Int) × β)`. The *type* cannot be shared: a kernel
  experiment (recorded in `proto-design.org`) shows that a parameterized
  synonym

      abbrev SortedList (β : Type) := List ((_ : Int) × β)

  used as a constructor argument is rejected —

      (kernel) arg #1 of 'Desc.mk' contains a non valid occurrence
      of the datatypes being declared

  — for both `abbrev` and `def`, because the nested-inductive translation
  only recognizes literal applications of already-declared inductives.
  Each inductive must therefore write `List ((_ : Int) × ...)` out in full.

  The *theory*, however, shares fine: everything below is stated for a
  general payload `β` and instantiated at `β := Field` and `β := Slot`.
  Nothing here mentions either.

  `sortedInsert` is hand-rolled (single pass, replace on collision) rather
  than `orderedInsert ∘ kerase`: the single pass is what makes
  `dlookup_sortedInsert_self` / `dlookup_sortedInsert_ne` hold with **no**
  well-formedness hypothesis, which several downstream relations depend on
  (they carry no `WF` premises at all).
-/
import Mathlib

namespace Pollux.Proto.SortedMap

open List

variable {β γ : Type}

/-- Sorted insertion into a key-ordered entry list, replacing any existing
    entry with the same key. -/
def sortedInsert (k : Int) (x : β) :
    List ((_ : Int) × β) → List ((_ : Int) × β)
  | [] => [⟨k, x⟩]
  | ⟨k', x'⟩ :: rest =>
    if k < k' then ⟨k, x⟩ :: ⟨k', x'⟩ :: rest
    else if k = k' then ⟨k, x⟩ :: rest
    else ⟨k', x'⟩ :: sortedInsert k x rest

/-- Well-formedness of the representation: strictly sorted by key.
    No-duplicate-keys is a consequence (`WF.nodupKeys`), not a second
    conjunct. -/
def WF (l : List ((_ : Int) × β)) : Prop :=
  l.Pairwise (fun a b => a.1 < b.1)

theorem WF.nodupKeys {l : List ((_ : Int) × β)} (h : WF l) : l.NodupKeys :=
  nodupKeys_iff_pairwise.mpr (h.imp ne_of_lt)

theorem wf_nil : WF ([] : List ((_ : Int) × β)) := Pairwise.nil

/-! ### Membership and lookup -/

theorem mem_sortedInsert {k : Int} {x : β} {a : (_ : Int) × β}
    {l : List ((_ : Int) × β)} :
    a ∈ sortedInsert k x l → a = ⟨k, x⟩ ∨ a ∈ l := by
  induction l with
  | nil => simp [sortedInsert]
  | cons hd tl ih =>
    obtain ⟨k', x'⟩ := hd
    rw [sortedInsert]; split_ifs <;> grind

theorem dlookup_sortedInsert_self (k : Int) (x : β)
    (l : List ((_ : Int) × β)) :
    dlookup k (sortedInsert k x l) = some x := by
  induction l with
  | nil => simp [sortedInsert]
  | cons hd tl ih =>
    obtain ⟨k', x'⟩ := hd
    rw [sortedInsert]; split_ifs with h1 h2
    · simp [dlookup]
    · simp [dlookup]
    · simp [dlookup, Ne.symm h2, ih]

theorem dlookup_sortedInsert_ne (k k' : Int) (x : β) (h : k ≠ k')
    (l : List ((_ : Int) × β)) :
    dlookup k' (sortedInsert k x l) = dlookup k' l := by
  induction l with
  | nil => simp [sortedInsert, dlookup, h]
  | cons hd tl ih =>
    obtain ⟨k'', x''⟩ := hd
    rw [sortedInsert]; split_ifs with h1 h2
    · simp [dlookup, h]
    · subst h2; simp [dlookup, h]
    · by_cases hk : k'' = k' <;> simp [dlookup, hk, ih]

/-- Lookup through a payload-only `map`. Used to specify `Value.init`,
    which rebuilds a value's entry list from a descriptor's. -/
theorem dlookup_mapVal (k : Int) (g : β → γ) (l : List ((_ : Int) × β)) :
    dlookup k (l.map (fun e => (⟨e.1, g e.2⟩ : (_ : Int) × γ))) = (dlookup k l).map g := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨k', x'⟩ := hd
    by_cases h : k' = k <;> simp [dlookup, h, ih]

/-! ### Well-formedness preservation -/

theorem sortedInsert_wf (k : Int) (x : β) {l : List ((_ : Int) × β)}
    (h : WF l) : WF (sortedInsert k x l) := by
  induction l with
  | nil => simp [sortedInsert, WF]
  | cons hd tl ih =>
    obtain ⟨k', x'⟩ := hd
    rw [WF, sortedInsert]
    split_ifs with h1 h2
    · exact h.cons fun a ha => (mem_cons.mp ha).elim
        (fun e => e ▸ h1) (fun m => h1.trans (rel_of_pairwise_cons h m))
    · subst h2; exact h.of_cons.cons fun a ha => rel_of_pairwise_cons h ha
    · exact (ih h.of_cons).cons fun a ha => (mem_sortedInsert ha).elim
        (fun e => e ▸ lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))
        (fun m => rel_of_pairwise_cons h m)

theorem kerase_wf (k : Int) {l : List ((_ : Int) × β)} (h : WF l) :
    WF (List.kerase k l) :=
  Pairwise.sublist (kerase_sublist k _) h

theorem mapVal_wf (g : β → γ) {l : List ((_ : Int) × β)} (h : WF l) :
    WF (l.map (fun e => (⟨e.1, g e.2⟩ : (_ : Int) × γ))) :=
  Pairwise.map _ (fun _ _ h => h) h

/-! ### Extensionality

Equal lookups on well-formed lists force equality: `lookup_ext` gives a
permutation, `Perm.eq_of_pairwise` upgrades it to equality because both
sides are sorted by a strict order. -/

theorem eq_of_dlookup_eq {l₁ l₂ : List ((_ : Int) × β)}
    (h₁ : WF l₁) (h₂ : WF l₂)
    (h : ∀ k, dlookup k l₁ = dlookup k l₂) : l₁ = l₂ :=
  Perm.eq_of_pairwise
    (fun a b _ _ hab hba => absurd hab (not_lt.mpr hba.le))
    h₁ h₂ (lookup_ext h₁.nodupKeys h₂.nodupKeys (fun x y => by rw [h x]))

end Pollux.Proto.SortedMap
