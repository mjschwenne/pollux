/-
  Pollux.InterParse.Descriptor — Descriptor and Value types for the intermediate format.

  Corresponds to src/InterParse/Descriptor.v in the Rocq development.

  The intermediate format uses tagged key-value pairs with integer field numbers.
  Descriptors describe the schema (field types), and Values hold the data.

  NOTE: The mutual inductive types (`Desc`/`Field`, `Value`/`Val`) store their
  fields as `List (Int × _)` because Lean's positivity checker cannot see through
  `TreeMap.Raw`'s internal `DTreeMap.Raw` dependent-function wrapper. The `List`
  representation is standard for nested inductives; map-like operations are
  provided via `List.lookup`, etc.
-/
import Pollux.Parse.Input
import Pollux.Parse.Result

namespace Pollux.InterParse

-- ## Descriptor types

-- A descriptor maps field numbers (integers) to field types.
-- Mutually defined with `Field` which may contain nested descriptors.
-- Corresponds to `Desc`/`Field` from `InterParse/Descriptor.v`.
mutual
inductive Desc where
  | mk (fs : List (Int × Field))
inductive Field where
  | msg (d : Desc)
  | bool
  | int
end

namespace Desc

/-- Extract the field list from a descriptor. Corresponds to `Fields`. -/
def fields : Desc → List (Int × Field)
  | .mk fs => fs

/-- Lookup a field by number. Corresponds to `Fields d !! k`. -/
def get? (d : Desc) (k : Int) : Option Field := d.fields.lookup k

instance : EmptyCollection Desc := ⟨.mk []⟩

/-- Insert a field, replacing any existing entry with the same key. -/
def insert (d : Desc) (k : Int) (f : Field) : Desc :=
  .mk ((k, f) :: d.fields.filter (·.1 != k))

/-- Delete a field by key. -/
def erase (d : Desc) (k : Int) : Desc :=
  .mk (d.fields.filter (·.1 != k))

end Desc

-- ## Value types

-- A value maps field numbers to typed values.
-- Mutually defined with `Val` which may contain nested values.
-- Corresponds to `Value`/`Val` from `InterParse/Descriptor.v`.
mutual
inductive Value where
  | mk (vs : List (Int × Val))
inductive Val where
  | msg (v : Value)
  | bool (b : Bool)
  | int (z : Int)
  | missing
end

namespace Value

/-- Extract the val list from a value. Corresponds to `Vals`. -/
def vals : Value → List (Int × Val)
  | .mk vs => vs

/-- Lookup a val by field number. -/
def get? (v : Value) (k : Int) : Option Val := v.vals.lookup k

instance : EmptyCollection Value := ⟨.mk []⟩

/-- Insert a val. -/
def insert (v : Value) (k : Int) (val : Val) : Value :=
  .mk ((k, val) :: v.vals.filter (·.1 != k))

/-- Delete a val by key. -/
def erase (v : Value) (k : Int) : Value :=
  .mk (v.vals.filter (·.1 != k))

end Value

/-! ## Map helper: full outer join -/

/-- Full outer join of two association lists. Corresponds to `merge` from stdpp. -/
def listMerge {α β γ : Type} (f : Option α → Option β → Option γ)
    (m1 : List (Int × α)) (m2 : List (Int × β)) : List (Int × γ) :=
  let fromM1 := m1.filterMap fun (k, a) =>
    (f (some a) (m2.lookup k)).map (k, ·)
  let fromM2Only := m2.filterMap fun (k, b) =>
    if m1.lookup k |>.isSome then none
    else (f none (some b)).map (k, ·)
  fromM1 ++ fromM2Only

-- ## Size metrics
--
-- Structural size metrics for well-founded induction, mirroring the Rocq
-- `Desc_size`, `Field_size`, `Value_size`, `Val_size`.

mutual
def descSize : Desc → Nat
  | .mk fs => 1 + fieldListSize fs
def fieldSize : Field → Nat
  | .msg d => 1 + descSize d
  | .bool | .int => 1
def fieldListSize : List (Int × Field) → Nat
  | [] => 0
  | (_, f) :: rest => fieldSize f + fieldListSize rest
end

theorem fieldSize_positive : ∀ f : Field, fieldSize f > 0 := by
  sorry

theorem descSize_positive : ∀ d : Desc, descSize d > 0 := by
  sorry

theorem fieldInMap_smaller (m : List (Int × Field)) (k : Int) (f : Field) :
    (k, f) ∈ m → fieldSize f < 1 + fieldListSize m := by
  sorry

mutual
def valueSize : Value → Nat
  | .mk vs => 1 + valListSize vs
def valSize : Val → Nat
  | .msg v => 1 + valueSize v
  | .bool _ | .int _ | .missing => 1
def valListSize : List (Int × Val) → Nat
  | [] => 0
  | (_, v) :: rest => valSize v + valListSize rest
end

theorem valSize_positive : ∀ v : Val, valSize v > 0 := by
  sorry

theorem valueSize_positive : ∀ v : Value, valueSize v > 0 := by
  sorry

theorem valInMap_smaller (m : List (Int × Val)) (k : Int) (v : Val) :
    (k, v) ∈ m → valSize v < 1 + valListSize m := by
  sorry

-- ## Initialization
--
-- Build a default value matching a descriptor's structure. Boolean and integer
-- fields default to `V_MISSING`; message fields recurse.

mutual
def Desc.init : Desc → Value
  | .mk fs => .mk (initFieldList fs)
def initFieldList : List (Int × Field) → List (Int × Val)
  | [] => []
  | (k, .msg d) :: rest => (k, .msg d.init) :: initFieldList rest
  | (k, _) :: rest => (k, .missing) :: initFieldList rest
end

-- ## Subset and equality

mutual
/-- Check whether `v1`'s entries are a subset of `v2`'s. -/
def valueSubset : Value → Value → Bool
  | .mk vs1, v2 => subsetAux v2 vs1
def subsetAux (v2 : Value) : List (Int × Val) → Bool
  | [] => true
  | (k, v) :: rest =>
    if !subsetAux v2 rest then false
    else match v2.get? k with
      | some (.bool b') => match v with | .bool b => b == b' | _ => false
      | some (.int z')  => match v with | .int z  => z == z' | _ => false
      | some .missing   => match v with | .missing => true | _ => false
      | some (.msg v')  => match v with | .msg v'' => valueSubset v'' v' | _ => false
      | none => false
end

/-- Bidirectional subset check. -/
def valueEqb (v1 v2 : Value) : Bool :=
  valueSubset v1 v2 && valueSubset v2 v1

-- ## Validity predicates

-- `valid d v` holds when every field required by descriptor `d` exists in
-- value `v` with the correct type. Values may have extra fields.
-- Corresponds to `Valid` in the Rocq development.
mutual
def valid : Desc → Value → Prop
  | .mk fs, .mk vs => validFoldList vs fs True
def validFold (vs : List (Int × Val)) (k : Int) (f : Field) (acc : Prop) : Prop :=
  match f with
  | .bool => acc ∧ ∃ b, vs.lookup k = some (.bool b)
  | .int  => acc ∧ ∃ z, vs.lookup k = some (.int z)
  | .msg d => acc ∧ ∃ v, vs.lookup k = some (.msg v) ∧ valid d v
def validFoldList (vs : List (Int × Val)) : List (Int × Field) → Prop → Prop
  | [], acc => acc
  | (k, f) :: rest, acc => validFoldList vs rest (validFold vs k f acc)
end

-- `valid' d v` is the dual: checks that every entry in `v` is described by `d`.
-- Corresponds to `Valid'` in the Rocq development.
mutual
def valid' : Desc → Value → Prop
  | .mk fs, .mk vs => valid'FoldList fs vs True
def valid'Fold (fs : List (Int × Field)) (k : Int) (v : Val) (acc : Prop) : Prop :=
  match v with
  | .bool _ => fs.lookup k = some .bool ∧ acc
  | .int _  => fs.lookup k = some .int ∧ acc
  | .msg value => (∃ d, fs.lookup k = some (.msg d) ∧ valid' d value) ∧ acc
  | .missing => True ∧ acc
def valid'FoldList (fs : List (Int × Field)) : List (Int × Val) → Prop → Prop
  | [], acc => acc
  | (k, v) :: rest, acc => valid'FoldList fs rest (valid'Fold fs k v acc)
end

-- ## Depth and encoding length metrics
--
-- These are used by the recursive serializer's termination argument and by
-- encoding-length correctness proofs.

mutual
def valueDepth : Value → Nat
  | .mk vs => valueDepthList vs 0
def valueDepthFold (v : Val) (acc : Nat) : Nat :=
  match v with
  | .bool _ | .int _ | .missing => acc
  | .msg v' => Nat.max acc (valueDepth v' + 1)
def valueDepthList : List (Int × Val) → Nat → Nat
  | [], acc => acc
  | (_, v) :: rest, acc => valueDepthList rest (valueDepthFold v acc)
end

mutual
def valueEncLen : Value → Nat
  | .mk vs => valueEncLenList vs 0
def valueEncLenFold (v : Val) (acc : Nat) : Nat :=
  match v with
  | .bool _ => acc + 5
  | .int _  => acc + 5
  | .missing => acc
  | .msg v' => acc + 2 + valueEncLen v'
def valueEncLenList : List (Int × Val) → Nat → Nat
  | [], acc => acc
  | (_, v) :: rest, acc => valueEncLenList rest (valueEncLenFold v acc)
end

mutual
def valueEncLen' : Desc → Value → Nat
  | .mk ds, .mk vs => valueEncLen'List ds vs 0
def valueEncLen'Fold (ds : List (Int × Field)) (k : Int) (v : Val) (acc : Nat) : Nat :=
  match ds.lookup k, v with
  | none, _ => acc
  | some _, .bool _ => acc + 5
  | some _, .int _  => acc + 5
  | some (.msg d), .msg val => acc + 2 + valueEncLen' d val
  | some _, _ => acc
def valueEncLen'List (ds : List (Int × Field)) : List (Int × Val) → Nat → Nat
  | [], acc => acc
  | (k, v) :: rest, acc => valueEncLen'List ds rest (valueEncLen'Fold ds k v acc)
end

-- ## Well-formedness for serialization

mutual
def valueWf : Desc → Value → Prop
  | .mk ds, .mk vs => valWfFoldList ds vs True
def valWfFold (ds : List (Int × Field)) (k : Int) (v : Val) (acc : Prop) : Prop :=
  match ds.lookup k, v with
  | none, _ => acc
  | some .bool, .bool _ => 0 ≤ k ∧ k < 256 ∧ acc
  | some .int, .int z => acc ∧ 0 ≤ k ∧ k < 256 ∧ 0 ≤ z ∧ z < 2 ^ 32
  | some (.msg d), .msg val => acc ∧ 0 ≤ k ∧ k < 256 ∧ valueWf d val
  | _, _ => False
def valWfFoldList (ds : List (Int × Field)) : List (Int × Val) → Prop → Prop
  | [], acc => acc
  | (k, v) :: rest, acc => valWfFoldList ds rest (valWfFold ds k v acc)
end

/-- Helper shim: well-formedness for a single key-value pair. -/
def valWf (d : Desc) (kv : Int × Val) : Prop :=
  valWfFold d.fields kv.1 kv.2 True

theorem valWfFold_unfold (d : Desc) (key : Int) (val : Val) :
    valWfFold d.fields key val True =
    match d.fields.lookup key, val with
    | none, _ => True
    | some .bool, .bool _ => 0 ≤ key ∧ key < 256 ∧ True
    | some .int, .int z => True ∧ 0 ≤ key ∧ key < 256 ∧ 0 ≤ z ∧ z < 2 ^ 32
    | some (.msg d'), .msg val' => True ∧ 0 ≤ key ∧ key < 256 ∧ valueWf d' val'
    | _, _ => False := by
  sorry

/-! ## Filtering and merging for serialization -/

/-- Merge function for combining a descriptor field with a value entry.
    Corresponds to `Merge` in the Rocq development. -/
def mergeFieldVal (f : Option Field) (v : Option Val) : Option Val :=
  match f, v with
  | some f, some v =>
    match f, v with
    | .bool, .bool b => some (.bool b)
    | .int, .int z => some (.int z)
    | .msg _, .msg v' => some (.msg v')
    | _, _ => none
  | some _, none => some .missing
  | none, _ => none

/-- Build a `Value` from a descriptor and a list of key-value pairs.
    Uses `merge` to combine the descriptor's fields with the parsed entries.
    Corresponds to `list_to_value` in the Rocq development. -/
def listToValue (d : Desc) (vs : List (Int × Val)) : Value :=
  .mk (listMerge mergeFieldVal d.fields vs)

/-- Predicate for filtering value entries against a descriptor. -/
def valListFilterP (d : Desc) (kv : Int × Val) : Bool :=
  match d.fields.lookup kv.1, kv.2 with
  | some _, .missing => false
  | none, _ => false
  | _, _ => true

/-- Filter a value's entries according to a descriptor: drop missing entries
    and entries for unknown fields.
    Corresponds to `ValList` in the Rocq development. -/
def valList (d : Desc) (v : Value) : List (Int × Val) :=
  v.vals.filter (valListFilterP d)

/-- Check if a field type and value type match. -/
def fieldValMatch (f : Field) (v : Val) : Prop :=
  match v, f with
  | .bool _, .bool | .int _, .int | .msg _, .msg _ => True
  | _, _ => False

/-- A key-value pair will be encoded: the field exists in the descriptor
    and the pair is well-formed. -/
def willEncode (d : Desc) (kv : Int × Val) : Prop :=
  ∃ f, d.fields.lookup kv.1 = some f ∧ valWf d kv

/-- All entries in a list will be encoded. -/
def serialValueListWf (d : Desc) (vs : List (Int × Val)) : Prop :=
  ∀ kv ∈ vs, willEncode d kv

/-- Filter function for combining descriptor fields with value entries,
    dropping missing values and unknown fields.
    Corresponds to `Filter` in the Rocq development. -/
def filterFieldVal (f : Option Field) (v : Option Val) : Option Val :=
  match f, v with
  | none, none => none
  | some _, some .missing => none
  | some _, none => none
  | none, some _ => none
  | some _, some v => some v

/-- Alternative value list using merge-based filtering.
    Corresponds to `ValList'` in the Rocq development. -/
def valList' (d : Desc) (v : Value) : List (Int × Val) :=
  listMerge filterFieldVal d.fields v.vals

/-! ## Depth bound lemma statements -/

theorem valInMap_smallerDepth (v : Value) (k : Int) (val : Value) :
    v.get? k = some (.msg val) → valueDepth val < valueDepth v := by
  sorry

theorem valueEncLen'Fold_linear (d : Desc) (k : Int) (v : Val) (acc : Nat) :
    valueEncLen'Fold d.fields k v acc = valueEncLen'Fold d.fields k v 0 + acc := by
  sorry

end Pollux.InterParse
