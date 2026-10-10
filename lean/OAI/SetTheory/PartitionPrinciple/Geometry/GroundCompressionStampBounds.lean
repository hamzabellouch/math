import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInaccessibleOrdinalClosure

namespace OAI


namespace PartitionPilot.Forcing
universe u

noncomputable def compressionStamp (base : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => insert base base
  | n + 1 => insert (compressionStamp base n) (compressionStamp base n)

theorem compressionStamp_zero (base : ZFSet.{u}) :
    compressionStamp base 0 = insert base base := rfl

theorem compressionStamp_succ (base : ZFSet.{u}) (n : Nat) :
    compressionStamp base (n + 1) = insert (compressionStamp base n) (compressionStamp base n) := rfl

theorem compressionStamp_subset (base : ZFSet.{u}) {n m : Nat} (before : n ≤ m) :
    compressionStamp base n ⊆ compressionStamp base m := by
  induction m, before using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ m _ ih => exact fun _ hx => ZFSet.mem_insert_of_mem _ (ih hx)

theorem compressionStamp_mem_iff (base : ZFSet.{u}) (n m : Nat) :
    compressionStamp base n ∈ compressionStamp base m ↔ n < m := by
  constructor
  · intro member
    by_contra notBefore
    exact ZFSet.mem_irrefl _ (compressionStamp_subset base (Nat.le_of_not_gt notBefore) member)
  · intro before
    exact compressionStamp_subset base before (ZFSet.mem_insert _ _)

theorem compressionStamp_ordinal {base : ZFSet.{u}} (ordinal : ordinalSetProperty base) (n : Nat) :
    ordinalSetProperty (compressionStamp base n) := by
  induction n with
  | zero => exact ordinalSetProperty_succ ordinal
  | succ n ih => exact ordinalSetProperty_succ ih

theorem compressionStamp_base_mem (base : ZFSet.{u}) (n : Nat) : base ∈ compressionStamp base n :=
  compressionStamp_subset base (Nat.zero_le n) (ZFSet.mem_insert _ _)

theorem compressionStamp_old_mem {base t : ZFSet.{u}} (old : t ∈ base ∨ t = base) (n : Nat) :
    t ∈ compressionStamp base n := by
  apply compressionStamp_subset base (Nat.zero_le n)
  exact ZFSet.mem_insert_iff.2 old.symm

theorem compressionStamp_union_ordinal {base limit : ZFSet.{u}}
    (ordinal : ordinalSetProperty base) (union : NatUnionCode (compressionStamp base) limit) :
    ordinalSetProperty limit := by
  constructor
  · intro y hy z hz
    obtain ⟨n, yn⟩ := (union y).1 hy
    exact union.subset n ((compressionStamp_ordinal ordinal n).1 y yn z hz)
  · intro y hy
    obtain ⟨n, yn⟩ := (union y).1 hy
    exact (compressionStamp_ordinal ordinal n).2 y yn

structure CompressionStampCode (base stamps limit : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc ZFSet.omega limit stamps
  entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ stamps ↔ y = compressionStamp base n
  union : NatUnionCode (compressionStamp base) limit
  ordinal : ordinalSetProperty limit

namespace CompressionStampCode
variable {base stamps limit : ZFSet.{u}} (code : CompressionStampCode base stamps limit)
include code

theorem stamp_mem_limit (n : Nat) : compressionStamp base n ∈ limit :=
  code.union.subset (n + 1) ((compressionStamp_mem_iff base n (n + 1)).2 (Nat.lt_succ_self n))

theorem stamp_ne_limit (n : Nat) : compressionStamp base n ≠ limit := by
  intro equal
  exact ZFSet.mem_irrefl limit (equal ▸ code.stamp_mem_limit n)

theorem base_mem_limit : base ∈ limit := code.union.subset 0 (compressionStamp_base_mem base 0)

theorem value_ordinal (n : Nat) : ordinalSetProperty (compressionStamp base n) :=
  ordinalSetProperty_member code.ordinal (code.stamp_mem_limit n)

theorem entry_below_limit {n : Nat} {value : ZFSet.{u}}
    (entry : ZFSet.pair (natSetCode n) value ∈ stamps) : value ∈ limit ∧ value ≠ limit := by
  rw [(code.entries n value).1 entry]
  exact ⟨code.stamp_mem_limit n, code.stamp_ne_limit n⟩

end CompressionStampCode





theorem mem_compressionStamp_iff (base s : ZFSet.{u}) (n : Nat) :
    s ∈ compressionStamp base n ↔
      s ∈ base ∨ s = base ∨ ∃ m, m < n ∧ s = compressionStamp base m := by
  induction n with
  | zero =>
    rw [compressionStamp_zero, ZFSet.mem_insert_iff]
    simp only [Nat.not_lt_zero, false_and, exists_false, or_false]
    exact or_comm
  | succ n ih =>
    rw [compressionStamp_succ, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (equal | old | equal | ⟨m, before, equal⟩)
      · exact Or.inr (Or.inr ⟨n, Nat.lt_succ_self n, equal⟩)
      · exact Or.inl old
      · exact Or.inr (Or.inl equal)
      · exact Or.inr (Or.inr ⟨m, before.trans (Nat.lt_succ_self n), equal⟩)
    · rintro (old | equal | ⟨m, before, equal⟩)
      · exact Or.inr (Or.inl old)
      · exact Or.inr (Or.inr (Or.inl equal))
      · rcases lt_or_eq_of_le (Nat.le_of_lt_succ before) with lower | same
        · exact Or.inr (Or.inr (Or.inr ⟨m, lower, equal⟩))
        · exact Or.inl (same ▸ equal)

theorem compressionStamp_not_old (base : ZFSet.{u}) (n : Nat) :
    compressionStamp base n ∉ base ∧ compressionStamp base n ≠ base := by
  constructor
  · exact fun member => ZFSet.mem_asymm member (compressionStamp_base_mem base n)
  · intro equal
    have member := compressionStamp_base_mem base n
    rw [equal] at member
    exact ZFSet.mem_irrefl base member

theorem old_ne_compressionStamp {base s : ZFSet.{u}} (old : s ∈ base ∨ s = base) (n : Nat) :
    s ≠ compressionStamp base n := by
  intro equal
  rcases old with member | same
  · exact (compressionStamp_not_old base n).1 (equal ▸ member)
  · exact (compressionStamp_not_old base n).2 (equal.symm.trans same)

theorem compressionStamp_injective (base : ZFSet.{u}) : Function.Injective (compressionStamp base) := by
  intro n m equal
  rcases lt_trichotomy n m with before | same | after
  · have member := (compressionStamp_mem_iff base n m).2 before
    exact False.elim (ZFSet.mem_irrefl _ (equal ▸ member))
  · exact same
  · have member := (compressionStamp_mem_iff base m n).2 after
    exact False.elim (ZFSet.mem_irrefl _ (equal ▸ member))

namespace CompressionStampCode
variable {base stamps limit : ZFSet.{u}} (code : CompressionStampCode base stamps limit)
include code

theorem mem_limit_iff (s : ZFSet.{u}) :
    s ∈ limit ↔ s ∈ base ∨ s = base ∨ ∃ n, s = compressionStamp base n := by
  constructor
  · intro member
    obtain ⟨n, before⟩ := (code.union s).1 member
    rcases (mem_compressionStamp_iff base s n).1 before with old | same | ⟨m, _, equal⟩
    · exact Or.inl old
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr ⟨m, equal⟩)
  · rintro (old | same | ⟨n, equal⟩)
    · exact code.union.subset 0 (compressionStamp_old_mem (Or.inl old) 0)
    · exact same ▸ code.base_mem_limit
    · exact equal ▸ code.stamp_mem_limit n

end CompressionStampCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open scoped ZFSet
universe u

namespace FunctionGraphOn
variable {family : ZFSet.{u}}

noncomputable def natValue (function : FunctionGraphOn ZFSet.omega family) (n : Nat) : ZFSet.{u} :=
  function.value ⟨natSetCode n, natSetCode_mem_omega n⟩

theorem natValue_entry (function : FunctionGraphOn ZFSet.omega family) (n : Nat) :
    ZFSet.pair (natSetCode n) (function.natValue n) ∈ family :=
  function.value_entry ⟨natSetCode n, natSetCode_mem_omega n⟩

theorem natValue_entry_iff (function : FunctionGraphOn ZFSet.omega family) (n : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode n) y ∈ family ↔ y = function.natValue n := by
  constructor
  · exact fun entry => function.unique entry (function.natValue_entry n)
  · exact fun equal => equal.symm ▸ function.natValue_entry n

end FunctionGraphOn

noncomputable def naturalFamilyUnion (family : ZFSet.{u}) : ZFSet.{u} :=
  ⋃₀ relationImage ZFSet.omega (⋃₀ ⋃₀ family) family

theorem naturalFamilyUnion_code {family : ZFSet.{u}}
    (function : FunctionGraphOn ZFSet.omega family) :
    NatUnionCode function.natValue (naturalFamilyUnion family) := by
  intro x
  rw [naturalFamilyUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨value, member, hx⟩
    obtain ⟨_, index, hi, entry⟩ := (mem_relationImage _ _ _ value).1 member
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode index).1 hi
    exact ⟨n, ((function.natValue_entry_iff n value).1 entry) ▸ hx⟩
  · rintro ⟨n, hx⟩
    have entry := function.natValue_entry n
    exact ⟨function.natValue n, (mem_relationImage _ _ _ _).2
      ⟨pair_second_mem_doubleUnion entry, natSetCode n, natSetCode_mem_omega n, entry⟩, hx⟩

namespace TransitiveGround
open SetFormula

theorem naturalFamilyUnion_mem (M : TransitiveGround.{u})
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets) {family : ZFSet.{u}} (hFamily : family ∈ M.sets) :
    naturalFamilyUnion family ∈ M.sets :=
  M.union_mem unions (M.relationImage_mem separation hω
    (M.union_mem unions (M.union_mem unions hFamily)) hFamily)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_naturalStep_zero {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {p y base : ZFSet.{u}} (hzero : natSetCode 0 ∈ M.sets)
    (hp : p ∈ M.sets) (hy : y ∈ M.sets) (hb : base ∈ M.sets) :
    Realize M.sets (naturalStepFormula φ)
      (extend (natSetCode 0) (extend p (extend y (extend base params)))) ↔ y = base := by
  rw [M.realize_naturalStepFormula φ params members hzero hp hy hb]
  constructor
  · rintro (⟨_, equal⟩ | ⟨m, _, x, _, equal, _⟩)
    · exact equal
    · have impossible : m ∈ natSetCode 0 := equal.symm ▸ ZFSet.mem_insert m m
      exact False.elim (ZFSet.notMem_empty m impossible)
  · intro equal
    exact Or.inl ⟨rfl, equal⟩

theorem realize_naturalStep_succ {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    (n : Nat) {p y base : ZFSet.{u}} (hn : natSetCode n ∈ M.sets)
    (hnext : natSetCode (n + 1) ∈ M.sets)
    (hp : p ∈ M.sets) (hy : y ∈ M.sets) (hb : base ∈ M.sets) :
    Realize M.sets (naturalStepFormula φ)
      (extend (natSetCode (n + 1)) (extend p (extend y (extend base params)))) ↔
      ∃ x ∈ M.sets, ZFSet.pair (natSetCode n) x ∈ p ∧
        Realize M.sets φ (extend x (extend y params)) := by
  rw [M.realize_naturalStepFormula φ params members hnext hp hy hb]
  constructor
  · rintro (⟨empty, _⟩ | ⟨m, _, x, hx, equal, entry, next⟩)
    · exact False.elim (ZFSet.notMem_empty (natSetCode n)
        (empty ▸ ZFSet.mem_insert (natSetCode n) (natSetCode n)))
    · have same := (natSetCode_succ_eq_insert_iff n m).1 equal
      exact ⟨x, hx, same ▸ entry, next⟩
  · rintro ⟨x, hx, entry, next⟩
    exact Or.inr ⟨natSetCode n, hn, x, hx, rfl, entry, next⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable {k : Nat} (φ : SetFormula (k + 2)) (params : Fin k → ZFSet.{u})
variable (members : ∀ i, params i ∈ M.sets)
variable (value : Nat → ZFSet.{u}) (values : ∀ n, value n ∈ M.sets)
variable (nextValue : ∀ n y, y ∈ M.sets →
  (Realize M.sets φ (extend (value n) (extend y params)) ↔ y = value (n + 1)))

include members values nextValue

theorem definableNaturalTrace_value {N t : ZFSet.{u}} (hN : N ∈ M.sets)
    (ordinal : ordinalSetProperty N)
    (trace : OrdinalRecursionTrace
      (groundRecursionStep M (naturalStepFormula φ) (extend (value 0) params)) N t) :
    ∀ n, natSetCode n ∈ N → ∀ y, ZFSet.pair (natSetCode n) y ∈ t → y = value n := by
  intro n
  induction n with
  | zero =>
    intro hn y entry
    obtain ⟨hp, hy, relation⟩ := trace.2 _ hn y entry
    exact (M.realize_naturalStep_zero φ params members (M.transitive hN hn)
      hp hy (values 0)).1 relation
  | succ n ih =>
    intro hn y entry
    have previous : natSetCode n ∈ natSetCode (n + 1) :=
      (natSetCode_mem_iff n (n + 1)).2 (Nat.lt_succ_self n)
    have hnN := ordinal.1 _ hn _ previous
    obtain ⟨hp, hy, relation⟩ := trace.2 _ hn y entry
    obtain ⟨x, _, oldEntry, next⟩ := (M.realize_naturalStep_succ φ params members n
      (M.transitive hN hnN) (M.transitive hN hn) hp hy (values 0)).1 relation
    have equal := ih hnN x (pair_mem_graphRestriction.1 oldEntry).1
    rw [equal] at next
    exact (nextValue n y hy).1 next

theorem definableNaturalStepClosure (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets) :
    GroundOrdinalStepClosure M ZFSet.omega (naturalStepFormula φ) (extend (value 0) params) := by
  intro a ha p hp trace
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
  have hn (j : Nat) : natSetCode j ∈ M.sets := M.transitive hω (natSetCode_mem_omega j)
  cases n with
  | zero =>
    refine ⟨value 0, values 0,
      (M.realize_naturalStep_zero φ params members (hn 0) hp (values 0) (values 0)).2 rfl, ?_⟩
    intro y hy relation
    exact (M.realize_naturalStep_zero φ params members (hn 0) hp hy (values 0)).1 relation
  | succ n =>
    have previous : natSetCode n ∈ natSetCode (n + 1) :=
      (natSetCode_mem_iff n (n + 1)).2 (Nat.lt_succ_self n)
    have ordinal : ordinalSetProperty (natSetCode (n + 1) : ZFSet.{u}) := by
      rw [← ordinalCode_nat]
      exact ordinalSetProperty_ordinalCode _
    have entryValue := M.definableNaturalTrace_value φ params members value values nextValue
      (hn (n + 1)) ordinal trace
    obtain ⟨x, entry⟩ := trace.1.total previous
    have equal := entryValue n previous x entry
    have canonical : ZFSet.pair (natSetCode n) (value n) ∈ p := equal ▸ entry
    refine ⟨value (n + 1), values (n + 1), ?_, ?_⟩
    · exact (M.realize_naturalStep_succ φ params members n (hn n) (hn (n + 1))
        hp (values (n + 1)) (values 0)).2
          ⟨value n, values n, canonical, (nextValue n _ (values (n + 1))).2 rfl⟩
    · intro y hy relation
      obtain ⟨x, _, oldEntry, next⟩ := (M.realize_naturalStep_succ φ params members n
        (hn n) (hn (n + 1)) hp hy (values 0)).1 relation
      have same := entryValue n previous x oldEntry
      rw [same] at next
      exact (nextValue n y hy).1 next

theorem exists_definableNaturalHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace
        (groundRecursionStep M (naturalStepFormula φ) (extend (value 0) params))
        ZFSet.omega history ∧
      (∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔ y = value n) ∧
      (∀ other, OrdinalRecursionTrace
        (groundRecursionStep M (naturalStepFormula φ) (extend (value 0) params))
        ZFSet.omega other → other = history) := by
  have hω := M.omega_mem separation infinite
  have ordinal : ordinalSetProperty (ZFSet.omega : ZFSet.{u}) := by
    rw [← ordinalCode_omega]
    exact ordinalSetProperty_ordinalCode Ordinal.omega0
  obtain ⟨history, hh, trace, unique, _⟩ := M.exists_unique_ordinalRecursionTrace pairing unions
    separation collection hω ordinal (naturalStepFormula φ) (extend (value 0) params)
    (Fin.cases (values 0) members)
    (M.definableNaturalStepClosure φ params members value values nextValue hω)
  refine ⟨history, hh, trace, ?_, unique⟩
  intro n y
  have hn := natSetCode_mem_omega n
  have entryValue := M.definableNaturalTrace_value φ params members value values nextValue
    hω ordinal trace
  constructor
  · exact entryValue n hn y
  · intro equal
    obtain ⟨z, entry⟩ := trace.1.total hn
    exact equal.symm ▸ (entryValue n hn z entry ▸ entry)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem compressionStamp_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {base : ZFSet.{u}} (hBase : base ∈ M.sets) (n : Nat) :
    compressionStamp base n ∈ M.sets := by
  induction n with
  | zero => exact M.insert_mem pairing unions hBase hBase
  | succ n ih => exact M.insert_mem pairing unions ih ih

theorem exists_groundCompressionStamps
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {base : ZFSet.{u}} (hBase : base ∈ M.sets) (ordinal : ordinalSetProperty base) :
    ∃ stamps ∈ M.sets, ∃ limit ∈ M.sets,
      limit = naturalFamilyUnion stamps ∧ CompressionStampCode base stamps limit := by
  let formula : SetFormula 2 := (BoundedFormula.successorFormula 1 0).toFormula
  have values : ∀ n, compressionStamp base n ∈ M.sets := M.compressionStamp_mem pairing unions hBase
  have nextValue : ∀ n y, y ∈ M.sets →
      (Realize M.sets formula (extend (compressionStamp base n) (extend y Fin.elim0)) ↔
        y = compressionStamp base (n + 1)) := by
    intro n y hy
    exact (BoundedFormula.realize_toFormula M (BoundedFormula.successorFormula 1 0)
      (extend (compressionStamp base n) (extend y Fin.elim0))
      (Fin.cases (values n) (Fin.cases hy (fun i => Fin.elim0 i)))).trans
        (BoundedFormula.truth_successorFormula 1 0 _)
  obtain ⟨stamps, hStamps, trace, entries, _⟩ :=
    M.exists_definableNaturalHistory formula Fin.elim0 (fun i => Fin.elim0 i)
      (compressionStamp base) values nextValue pairing unions separation collection infinite
  have valueEq (n : Nat) : trace.1.natValue n = compressionStamp base n :=
    (entries n _).1 (trace.1.natValue_entry n)
  have unionCode : NatUnionCode (compressionStamp base) (naturalFamilyUnion stamps) := by
    intro x
    simpa only [valueEq] using (naturalFamilyUnion_code trace.1 x)
  have stampBelow (n : Nat) : compressionStamp base n ∈ naturalFamilyUnion stamps :=
    unionCode.subset (n + 1) (ZFSet.mem_insert _ _)
  refine ⟨stamps, hStamps, naturalFamilyUnion stamps,
    M.naturalFamilyUnion_mem unions separation (M.omega_mem separation infinite) hStamps, rfl,
    ⟨⟨?_, ?_⟩, entries, unionCode, compressionStamp_union_ordinal ordinal unionCode⟩⟩
  · intro z hz
    obtain ⟨i, hi, y, rfl⟩ := trace.1.shape z hz
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode i).1 hi
    exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, (entries n y).1 hz ▸ stampBelow n⟩
  · obtain ⟨_, function⟩ := trace.1
    exact function.2

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace CompressionStampCode
variable {base stamps limit K : ZFSet.{u}} (code : CompressionStampCode base stamps limit)
include code

theorem function_into_bound (values : ∀ n, compressionStamp base n ∈ K) :
    ZFSet.IsFunc ZFSet.omega K stamps := by
  refine ⟨?_, code.function.2⟩
  intro z hz
  obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
  exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, (code.entries n y).1 hz ▸ values n⟩

theorem successor_mem_limit {a : ZFSet.{u}} (ha : a ∈ limit) : insert a a ∈ limit := by
  obtain ⟨n, member⟩ := (code.union a).1 ha
  rw [ordinalSetProperty_eq_code_rank a (ordinalSetProperty_member code.ordinal ha),
    ← ordinalCode_succ, ordinalSetProperty_eq_code_rank limit code.ordinal, mem_ordinalCode_iff]
  exact (Order.succ_le_iff.2 (ZFSet.rank_lt_of_mem member)).trans_lt
    (ZFSet.rank_lt_of_mem (code.stamp_mem_limit n))

theorem rank_isLimit : Order.IsSuccLimit (ZFSet.rank limit) := by
  apply Order.isSuccLimit_iff_of_orderBot.2
  refine ⟨ne_of_gt (bot_le.trans_lt (ZFSet.rank_lt_of_mem code.base_mem_limit)), ?_⟩
  rw [Order.isSuccPrelimit_iff_succ_lt]
  intro a ha
  have member : ordinalCode a ∈ limit := by
    rw [ordinalSetProperty_eq_code_rank limit code.ordinal, mem_ordinalCode_iff]
    exact ha
  have bound := ZFSet.rank_lt_of_mem (code.successor_mem_limit member)
  rw [← ordinalCode_succ, rank_ordinalCode] at bound
  exact bound

end CompressionStampCode

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
include conditions pairing unions powers separation infinite hK

theorem compressionStamp_mem {base : ZFSet.{u}} (hBase : base ∈ K) (n : Nat) :
    compressionStamp base n ∈ K := by
  induction n with
  | zero => exact conditions.successor_mem pairing unions powers separation infinite hK hBase
  | succ n ih => exact conditions.successor_mem pairing unions powers separation infinite hK ih

theorem compressionStamp_limit_mem {base stamps limit : ZFSet.{u}}
    (code : CompressionStampCode base stamps limit) (hBase : base ∈ K)
    (hStamps : stamps ∈ M.sets) : limit ∈ K := by
  have values := conditions.compressionStamp_mem pairing unions powers separation infinite hK hBase
  obtain ⟨δ, hδ, bounded⟩ := conditions.2.2.1 ZFSet.omega conditions.2.1 stamps hStamps
    (code.function_into_bound values)
  have subset : limit ⊆ δ := by
    intro x hx
    obtain ⟨n, member⟩ := (code.union x).1 hx
    exact (ordinalSetProperty_member conditions.1 hδ).1 (compressionStamp base n)
      (bounded _ _ ((code.entries n _).2 rfl)) x member
  obtain ⟨l, eqLimit⟩ := (ordinalSetProperty_iff limit).1 code.ordinal
  obtain ⟨d, eqDelta⟩ := (ordinalSetProperty_iff δ).1 (ordinalSetProperty_member conditions.1 hδ)
  obtain ⟨k, eqK⟩ := (ordinalSetProperty_iff K).1 conditions.1
  rw [eqLimit, eqDelta, ordinalCode_subset_iff] at subset
  rw [eqDelta, eqK, mem_ordinalCode_iff] at hδ
  rw [eqLimit, eqK, mem_ordinalCode_iff]
  exact subset.trans_lt hδ

end GroundInaccessibleConditions

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundCompressionStamps_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K base : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hBase : base ∈ K) :
    ∃ stamps ∈ M.sets, ∃ limit ∈ M.sets,
      limit = naturalFamilyUnion stamps ∧ CompressionStampCode base stamps limit ∧
        limit ∈ K ∧ Order.IsSuccLimit (ZFSet.rank limit) ∧ base ∈ limit := by
  obtain ⟨stamps, hStamps, limit, hLimit, equal, code⟩ :=
    M.exists_groundCompressionStamps pairing unions separation collection infinite
      (M.transitive hK hBase) (ordinalSetProperty_member conditions.1 hBase)
  exact ⟨stamps, hStamps, limit, hLimit, equal, code,
    conditions.compressionStamp_limit_mem pairing unions powers separation infinite hK code hBase hStamps,
    code.rank_isLimit, code.base_mem_limit⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
