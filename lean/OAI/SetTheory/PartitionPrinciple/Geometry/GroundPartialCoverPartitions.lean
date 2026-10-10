import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundOrdinalImagePartitions

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def partialCoverOccurrence (delta T X h : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ delta, ∃ x ∈ X, ∃ hi ∈ ⋃₀ ⋃₀ h,
    z = ZFSet.pair i x ∧ ZFSet.pair i hi ∈ h ∧ ∃ u ∈ T, ZFSet.pair u x ∈ hi)
    (ZFSet.prod delta X)

theorem pair_mem_partialCoverOccurrence (delta T X h i x : ZFSet.{u}) :
    ZFSet.pair i x ∈ partialCoverOccurrence delta T X h ↔
      i ∈ delta ∧ x ∈ X ∧ ∃ hi, ZFSet.pair i hi ∈ h ∧ ∃ u ∈ T, ZFSet.pair u x ∈ hi := by
  rw [partialCoverOccurrence, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, y, hy, hi, _, equal, entry, covered⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hy, hi, entry, covered⟩
  · rintro ⟨hi, hx, graph, entry, covered⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, i, hi, x, hx, graph,
      pair_second_mem_doubleUnion entry, rfl, entry, covered⟩

namespace BoundedFormula
private def partialCoverOccurrenceFormula {n} (z delta T X H h : Fin n) : BoundedFormula n :=
  exMem delta (exMem X.succ (exMem H.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (.conj (pairMembershipFormula 2 0 h.succ.succ.succ)
        (exMem T.succ.succ.succ (pairMembershipFormula 0 2 1))))))

private theorem partialCoverOccurrence_meaning {n} (z delta T X H h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (partialCoverOccurrenceFormula z delta T X H h) env ↔
      ∃ i ∈ env delta, ∃ x ∈ env X, ∃ hi ∈ env H,
        env z = ZFSet.pair i x ∧ ZFSet.pair i hi ∈ env h ∧ ∃ u ∈ env T, ZFSet.pair u x ∈ hi := by
  simp only [partialCoverOccurrenceFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (N : TransitiveGround.{u})

theorem partialCoverOccurrence_mem
    (pairing : Realize N.sets SetFormula.pairing Fin.elim0)
    (unions : Realize N.sets SetFormula.union Fin.elim0)
    (powers : Realize N.sets powerSet Fin.elim0) (separation : SeparationSchema N.sets)
    {delta T X h : ZFSet.{u}} (hDelta : delta ∈ N.sets) (hT : T ∈ N.sets)
    (hX : X ∈ N.sets) (hh : h ∈ N.sets) : partialCoverOccurrence delta T X h ∈ N.sets := by
  have hH := N.union_mem unions (N.union_mem unions hh)
  let params := extend delta (extend T (extend X (extend (⋃₀ ⋃₀ h) (extend h Fin.elim0))))
  have selected := N.bounded_separation_mem separation
    (BoundedFormula.partialCoverOccurrenceFormula 0 1 2 3 4 5) params
    (Fin.cases hDelta (Fin.cases hT (Fin.cases hX (Fin.cases hH (Fin.cases hh (fun j => Fin.elim0 j))))))
    (N.prod_mem pairing unions powers separation hDelta hX)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.partialCoverOccurrenceFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod delta X) = partialCoverOccurrence delta T X h := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, partialCoverOccurrence, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.partialCoverOccurrence_meaning _ _ _ _ _ _ _)
  exact equal ▸ selected

theorem partialCover_ordinal_partitions
    (zf : ZFRealization N.sets) {delta T X Y h f : ZFSet.{u}}
    (hDelta : delta ∈ N.sets) (ordinal : ordinalSetProperty delta)
    (hT : T ∈ N.sets) (hX : X ∈ N.sets) (hY : Y ∈ N.sets)
    (hh : h ∈ N.sets) (hf : f ∈ N.sets) (family : FunctionGraphOn delta h)
    (function : ZFSet.IsFunc X Y f) (onto : ∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f)
    (cover : ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧ ∃ u ∈ T, ZFSet.pair u x ∈ hi) :
    ∃ full ∈ N.sets, ∃ p ∈ N.sets, ∃ q ∈ N.sets,
      FunctionGraphOn delta full ∧ FunctionGraphOn delta p ∧ FunctionGraphOn delta q ∧
      (∀ i U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q → U ⊆ Y ∧ V ⊆ X) ∧
      (∀ y ∈ Y, ∃ i ∈ delta, ∃ U, ZFSet.pair i U ∈ p ∧ y ∈ U) ∧
      (∀ i k U V y, ZFSet.pair i U ∈ p → ZFSet.pair k V ∈ p → y ∈ U → y ∈ V → i = k) ∧
      (∀ i k U V x, ZFSet.pair i U ∈ q → ZFSet.pair k V ∈ q → x ∈ U → x ∈ V → i = k) ∧
      ∀ i hi A U V, ZFSet.pair i hi ∈ h → ZFSet.pair i A ∈ full →
        ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q →
        (∀ x, x ∈ A ↔ x ∈ X ∧ ∃ u ∈ T, ZFSet.pair u x ∈ hi) ∧
        (∀ y, y ∈ U ↔ y ∈ Y ∧ (∃ x ∈ A, ZFSet.pair x y ∈ f) ∧
          ∀ k ∈ i, ∀ B, ZFSet.pair k B ∈ full → ¬ ∃ x ∈ B, ZFSet.pair x y ∈ f) ∧
        (∀ x, x ∈ V ↔ x ∈ A ∧ ∃ y ∈ U, ZFSet.pair x y ∈ f) ∧
        graphRestriction V f ∈ N.sets ∧ ZFSet.IsFunc V U (graphRestriction V f) ∧
        (∀ y ∈ U, ∃ x ∈ V, ZFSet.pair x y ∈ graphRestriction V f) ∧
        ∀ x ∈ V, ∃ u ∈ T, ZFSet.pair u x ∈ hi := by
  have pairing := zf.1.2.2.2.1
  have unions := zf.1.2.2.2.2.1
  have powers := zf.1.2.2.2.2.2.1
  have separation : SeparationSchema N.sets := zf.2.1
  let R := partialCoverOccurrence delta T X h
  have hR : R ∈ N.sets := N.partialCoverOccurrence_mem pairing unions powers separation hDelta hT hX hh
  have relation : R ⊆ ZFSet.prod delta X := fun _ hz => (ZFSet.mem_sep.1 hz).1
  have covering : ∀ x ∈ X, ∃ i ∈ delta, ZFSet.pair i x ∈ R := by
    intro x hx
    obtain ⟨i, hi, g, entry, covered⟩ := cover x hx
    exact ⟨i, hi, (pair_mem_partialCoverOccurrence delta T X h i x).2 ⟨hi, hx, g, entry, covered⟩⟩
  obtain ⟨p, hp, q, hq, pFunction, qFunction, bounds, coverY, disjointY, disjointX, pieces⟩ :=
    N.ordinal_image_partitions zf hDelta ordinal hX hY hR hf relation function onto covering
  let full := N.relationFiberFamily delta X R
  have hFull : full ∈ N.sets := N.relationFiberFamily_mem pairing unions powers separation hDelta hX hR
  have fullFunction : FunctionGraphOn delta full :=
    ⟨N.groundPower X, N.relationFiberFamily_function separation hDelta hX hR⟩
  have fullEntries (i A : ZFSet.{u}) (entry : ZFSet.pair i A ∈ full) (x : ZFSet.{u}) :
      x ∈ A ↔ x ∈ X ∧ ZFSet.pair i x ∈ R := by
    have equal := ((N.pair_mem_relationFiberFamily delta X R i A).1 entry).2.2
    rw [equal, mem_relationFiber]
  refine ⟨full, hFull, p, hp, q, hq, fullFunction, pFunction, qFunction,
    bounds, coverY, disjointY, disjointX, ?_⟩
  intro i hi A U V inH inFull ip iq
  obtain ⟨target, source, hRestrict, restrictFunction, restrictOnto⟩ := pieces i U V ip iq
  have original (x : ZFSet.{u}) : x ∈ A ↔ x ∈ X ∧ ∃ u ∈ T, ZFSet.pair u x ∈ hi := by
    rw [fullEntries i A inFull x]
    constructor
    · rintro ⟨hx, entry⟩
      obtain ⟨_, _, g, inH', covered⟩ := (pair_mem_partialCoverOccurrence delta T X h i x).1 entry
      have equal := family.unique inH' inH
      exact ⟨hx, equal ▸ covered⟩
    · rintro ⟨hx, covered⟩
      exact ⟨hx, (pair_mem_partialCoverOccurrence delta T X h i x).2
        ⟨family.pair_source inH, hx, hi, inH, covered⟩⟩
  have selected (x : ZFSet.{u}) : x ∈ V ↔ x ∈ A ∧ ∃ y ∈ U, ZFSet.pair x y ∈ f := by
    rw [source x]
    constructor
    · rintro ⟨entry, image⟩
      exact ⟨(fullEntries i A inFull x).2 ⟨(ZFSet.pair_mem_prod.1 (relation entry)).2, entry⟩, image⟩
    · rintro ⟨member, image⟩
      exact ⟨((fullEntries i A inFull x).1 member).2, image⟩
  refine ⟨original, ?_, selected, hRestrict, restrictFunction, restrictOnto, ?_⟩
  · intro y
    rw [target y]
    constructor
    · rintro ⟨hy, ⟨x, hx, ix, xy⟩, least⟩
      refine ⟨hy, ⟨x, (fullEntries i A inFull x).2 ⟨hx, ix⟩, xy⟩, ?_⟩
      intro k ki B inFullB witness
      obtain ⟨v, hv, vy⟩ := witness
      have coordinates := (fullEntries k B inFullB v).1 hv
      exact least k ki ⟨v, coordinates.1, coordinates.2, vy⟩
    · rintro ⟨hy, ⟨x, hx, xy⟩, least⟩
      have coordinates := (fullEntries i A inFull x).1 hx
      refine ⟨hy, ⟨x, coordinates.1, coordinates.2, xy⟩, ?_⟩
      intro k ki witness
      obtain ⟨B, inFullB⟩ := fullFunction.total (ordinal.1 i (family.pair_source inH) k ki)
      obtain ⟨v, hv, kv, vy⟩ := witness
      exact least k ki B inFullB ⟨v, (fullEntries k B inFullB v).2 ⟨hv, kv⟩, vy⟩
  · intro x hx
    exact ((original x).1 ((selected x).1 hx).1).2

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
