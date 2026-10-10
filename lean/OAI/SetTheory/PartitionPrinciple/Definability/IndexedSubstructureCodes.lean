import OAI.SetTheory.PartitionPrinciple.Geometry.SeparationTileCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

def indexedSuborderGraph (I B R domains : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ v ∈ R, ∃ x ∈ B, ∃ y ∈ B,
    z = ZFSet.pair i v ∧ v = ZFSet.pair x y ∧
      ZFSet.pair i x ∈ domains ∧ ZFSet.pair i y ∈ domains) (ZFSet.prod I R)

def indexedSubmeetGraph (I B μ domains : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ v ∈ μ, ∃ x ∈ B, ∃ y ∈ B, ∃ w ∈ B,
    z = ZFSet.pair i v ∧ v = ZFSet.pair (ZFSet.pair x y) w ∧
      ZFSet.pair i x ∈ domains ∧ ZFSet.pair i y ∈ domains ∧ ZFSet.pair i w ∈ domains)
    (ZFSet.prod I μ)

theorem pair_mem_indexedSuborderGraph (I B R domains i v : ZFSet.{u}) :
    ZFSet.pair i v ∈ indexedSuborderGraph I B R domains ↔
      i ∈ I ∧ v ∈ R ∧ ∃ x ∈ relationFiber B domains i, ∃ y ∈ relationFiber B domains i,
        v = ZFSet.pair x y := by
  rw [indexedSuborderGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, w, hw, x, hx, y, hy, equal, value, first, second⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hw, x, (mem_relationFiber _ _ _ _).2 ⟨hx, first⟩,
      y, (mem_relationFiber _ _ _ _).2 ⟨hy, second⟩, value⟩
  · rintro ⟨hi, hv, x, hx, y, hy, equal⟩
    obtain ⟨hx, first⟩ := (mem_relationFiber _ _ _ _).1 hx
    obtain ⟨hy, second⟩ := (mem_relationFiber _ _ _ _).1 hy
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hv⟩, i, hi, v, hv, x, hx, y, hy, rfl, equal, first, second⟩

theorem pair_mem_indexedSubmeetGraph (I B μ domains i v : ZFSet.{u}) :
    ZFSet.pair i v ∈ indexedSubmeetGraph I B μ domains ↔
      i ∈ I ∧ v ∈ μ ∧ ∃ x ∈ relationFiber B domains i, ∃ y ∈ relationFiber B domains i,
        ∃ w ∈ relationFiber B domains i, v = ZFSet.pair (ZFSet.pair x y) w := by
  rw [indexedSubmeetGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, v', hv, x, hx, y, hy, w, hw, equal, value, first, second, third⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hv, x, (mem_relationFiber _ _ _ _).2 ⟨hx, first⟩,
      y, (mem_relationFiber _ _ _ _).2 ⟨hy, second⟩,
      w, (mem_relationFiber _ _ _ _).2 ⟨hw, third⟩, value⟩
  · rintro ⟨hi, hv, x, hx, y, hy, w, hw, equal⟩
    obtain ⟨hx, first⟩ := (mem_relationFiber _ _ _ _).1 hx
    obtain ⟨hy, second⟩ := (mem_relationFiber _ _ _ _).1 hy
    obtain ⟨hw, third⟩ := (mem_relationFiber _ _ _ _).1 hw
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hv⟩, i, hi, v, hv, x, hx, y, hy,
      w, hw, rfl, equal, first, second, third⟩

theorem suborderFiber_pair_iff {I B R domains i x y : ZFSet.{u}} (hi : i ∈ I) :
    ZFSet.pair x y ∈ relationFiber R (indexedSuborderGraph I B R domains) i ↔
      ZFSet.pair x y ∈ R ∧ x ∈ relationFiber B domains i ∧ y ∈ relationFiber B domains i := by
  rw [mem_relationFiber, pair_mem_indexedSuborderGraph]
  constructor
  · rintro ⟨hxy, _, _, a, ha, b, hb, equal⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hxy, ha, hb⟩
  · rintro ⟨hxy, hx, hy⟩
    exact ⟨hxy, hi, hxy, x, hx, y, hy, rfl⟩

theorem submeetFiber_triple_iff {I B μ domains i x y w : ZFSet.{u}} (hi : i ∈ I) :
    ZFSet.pair (ZFSet.pair x y) w ∈ relationFiber μ (indexedSubmeetGraph I B μ domains) i ↔
      ZFSet.pair (ZFSet.pair x y) w ∈ μ ∧ x ∈ relationFiber B domains i ∧
        y ∈ relationFiber B domains i ∧ w ∈ relationFiber B domains i := by
  rw [mem_relationFiber, pair_mem_indexedSubmeetGraph]
  constructor
  · rintro ⟨hxy, _, _, a, ha, b, hb, c, hc, equal⟩
    obtain ⟨ab, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ab
    exact ⟨hxy, ha, hb, hc⟩
  · rintro ⟨hxy, hx, hy, hw⟩
    exact ⟨hxy, hi, hxy, x, hx, y, hy, w, hw, rfl⟩

namespace BoundedFormula
def indexedSuborderEntryFormula {n} (z I B R domains : Fin n) : BoundedFormula n :=
  exMem I (exMem R.succ (exMem B.succ.succ (exMem B.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ 3 2)
      (.conj (orderedPairFormula 2 1 0)
        (.conj (pairMembershipFormula 3 1 domains.succ.succ.succ.succ)
          (pairMembershipFormula 3 0 domains.succ.succ.succ.succ)))))))

def indexedSubmeetEntryFormula {n} (z I B μ domains : Fin n) : BoundedFormula n :=
  exMem I (exMem μ.succ (exMem B.succ.succ (exMem B.succ.succ.succ (exMem B.succ.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ.succ 4 3)
      (.conj (orderedTripleFormula 3 2 1 0)
        (.conj (pairMembershipFormula 4 2 domains.succ.succ.succ.succ.succ)
          (.conj (pairMembershipFormula 4 1 domains.succ.succ.succ.succ.succ)
            (pairMembershipFormula 4 0 domains.succ.succ.succ.succ.succ)))))))))

theorem truth_indexedSuborderEntryFormula {n} (z I B R domains : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (indexedSuborderEntryFormula z I B R domains) env ↔
      env z ∈ indexedSuborderGraph (env I) (env B) (env R) (env domains) := by
  simp only [indexedSuborderEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, indexedSuborderGraph, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨i, hi, v, hv, _, _, _, _, equal, _⟩ := h
  change env z = ZFSet.pair i v at equal
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hi, hv⟩

theorem truth_indexedSubmeetEntryFormula {n} (z I B μ domains : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (indexedSubmeetEntryFormula z I B μ domains) env ↔
      env z ∈ indexedSubmeetGraph (env I) (env B) (env μ) (env domains) := by
  simp only [indexedSubmeetEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_orderedTripleFormula, truth_pairMembershipFormula, indexedSubmeetGraph, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨i, hi, v, hv, _, _, _, _, _, _, equal, _⟩ := h
  change env z = ZFSet.pair i v at equal
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hi, hv⟩
end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
