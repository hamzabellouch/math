import OAI.SetTheory.PartitionPrinciple.Definability.HistoryFieldFormulas

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundStateFieldFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    {history : ZFSet.{u}} (hHistory : history ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔ y = (states n).code)
    (j : Fin 13) :
    ∃ family ∈ M.sets, FunctionGraphOn ZFSet.omega family ∧
      ∀ n y, ZFSet.pair (natSetCode n) y ∈ family ↔ y = (states n).field j := by
  let params := extend history Fin.elim0
  have paramsM : ∀ i, params i ∈ M.sets := Fin.cases hHistory (fun i => Fin.elim0 i)
  have fieldsM (n : Nat) : (states n).field j ∈ M.sets :=
    M.recursiveStateData_field_mem (states n)
      (M.pair_right (M.transitive hHistory ((entries n _).2 rfl))) j
  have naturalM (n : Nat) : natSetCode n ∈ M.sets := M.transitive hω (natSetCode_mem_omega n)
  have total : ∀ x ∈ M.sets, x ∈ ZFSet.omega → ∃ z ∈ M.sets,
      Realize M.sets (historyFieldPairFormula 0 1 2 j) (extend x (extend z params)) ∧
      ∀ w ∈ M.sets,
        Realize M.sets (historyFieldPairFormula 0 1 2 j) (extend x (extend w params)) → w = z := by
    intro x hx hxω
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hxω
    have pairM := M.orderedPair_mem pairing hx (fieldsM n)
    refine ⟨ZFSet.pair (natSetCode n) ((states n).field j), pairM, ?_, ?_⟩
    · exact (M.realize_historyFieldPairFormula 0 1 2 j _
        (Fin.cases hx (Fin.cases pairM paramsM)) states entries n rfl).2 rfl
    · intro w hw specified
      exact (M.realize_historyFieldPairFormula 0 1 2 j _
        (Fin.cases hx (Fin.cases hw paramsM)) states entries n rfl).1 specified
  obtain ⟨family, hFamily, image⟩ := replacement_of_collection_separation M.sets collection separation
    (historyFieldPairFormula 0 1 2 j) params paramsM ZFSet.omega hω total
  have allEntries (z : ZFSet.{u}) :
      z ∈ family ↔ ∃ n, z = ZFSet.pair (natSetCode n) ((states n).field j) := by
    constructor
    · intro member
      have hz := M.transitive hFamily member
      obtain ⟨x, hx, hxω, specified⟩ := (image z hz).1 member
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hxω
      exact ⟨n, (M.realize_historyFieldPairFormula 0 1 2 j _
        (Fin.cases hx (Fin.cases hz paramsM)) states entries n rfl).1 specified⟩
    · rintro ⟨n, rfl⟩
      have pairM := M.orderedPair_mem pairing (naturalM n) (fieldsM n)
      apply (image _ pairM).2
      exact ⟨natSetCode n, naturalM n, natSetCode_mem_omega n,
        (M.realize_historyFieldPairFormula 0 1 2 j _
          (Fin.cases (naturalM n) (Fin.cases pairM paramsM)) states entries n rfl).2 rfl⟩
  have exactEntries (n : Nat) (y : ZFSet.{u}) :
      ZFSet.pair (natSetCode n) y ∈ family ↔ y = (states n).field j := by
    rw [allEntries]
    constructor
    · rintro ⟨m, equal⟩
      obtain ⟨index, value⟩ := ZFSet.pair_inj.1 equal
      have same : n = m := natSetCode_injective index
      exact same ▸ value
    · intro equal
      exact ⟨n, congrArg (ZFSet.pair (natSetCode n)) equal⟩
  refine ⟨family, hFamily, ⟨⋃₀ ⋃₀ family, ?_, ?_⟩, exactEntries⟩
  · intro z member
    obtain ⟨n, rfl⟩ := (allEntries z).1 member
    exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, pair_second_mem_doubleUnion member⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
    refine ⟨(states n).field j, (exactEntries n _).2 rfl, ?_⟩
    intro y hy
    exact (exactEntries n y).1 hy

theorem exists_groundStateFieldUnion
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    {history : ZFSet.{u}} (hHistory : history ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔ y = (states n).code)
    (j : Fin 13) :
    ∃ family ∈ M.sets, ∃ range ∈ M.sets, ∃ union ∈ M.sets,
      FunctionGraphOn ZFSet.omega family ∧
      (∀ n y, ZFSet.pair (natSetCode n) y ∈ family ↔ y = (states n).field j) ∧
      (∀ y, y ∈ range ↔ ∃ n, y = (states n).field j) ∧
      union = ⋃₀ range ∧ (∀ x, x ∈ union ↔ ∃ n, x ∈ (states n).field j) := by
  obtain ⟨family, hFamily, function, exactEntries⟩ :=
    M.exists_groundStateFieldFamily pairing separation collection hω hHistory states entries j
  let range := relationImage ZFSet.omega (⋃₀ ⋃₀ family) family
  have hRange := M.relationImage_mem separation hω (M.union_mem unions (M.union_mem unions hFamily)) hFamily
  have exactRange (y : ZFSet.{u}) : y ∈ range ↔ ∃ n, y = (states n).field j := by
    rw [mem_relationImage]
    constructor
    · rintro ⟨_, x, hx, entry⟩
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
      exact ⟨n, (exactEntries n y).1 entry⟩
    · rintro ⟨n, equal⟩
      have entry := (exactEntries n y).2 equal
      exact ⟨pair_second_mem_doubleUnion entry, natSetCode n, natSetCode_mem_omega n, entry⟩
  refine ⟨family, hFamily, range, hRange, ⋃₀ range, M.union_mem unions hRange,
    function, exactEntries, exactRange, rfl, ?_⟩
  intro x
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨field, member, hx⟩
    obtain ⟨n, equal⟩ := (exactRange field).1 member
    exact ⟨n, equal ▸ hx⟩
  · rintro ⟨n, hx⟩
    exact ⟨(states n).field j, (exactRange _).2 ⟨n, rfl⟩, hx⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
