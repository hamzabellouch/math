import OAI.SetTheory.PartitionPrinciple.Geometry.SeparationTileCodes

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem fixedTopCarrier_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {P : ZFSet.{u}} (hP : P ∈ M.sets) : fixedTopCarrier P ∈ M.sets :=
  M.insert_mem pairing unions hP hP

theorem fixedTopOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) : fixedTopOrder P r ∈ M.sets := by
  have singleton : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  exact M.binary_union_mem pairing unions hr (M.prod_mem pairing unions powers separation
    (M.fixedTopCarrier_mem pairing unions hP) singleton)

theorem fixedTopMeet_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) : fixedTopMeet P r ∈ M.sets :=
  M.canonicalMeetGraph_mem pairing unions powers separation
    (M.fixedTopCarrier_mem pairing unions hP) (M.fixedTopOrder_mem pairing unions powers separation hP hr)

theorem fixedTop_ground_codes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) :
    fixedTopCarrier P ∈ M.sets ∧ fixedTopOrder P r ∈ M.sets ∧ fixedTopMeet P r ∈ M.sets ∧
      attachmentOldEmbeddingGraph P ∈ M.sets :=
  ⟨M.fixedTopCarrier_mem pairing unions hP, M.fixedTopOrder_mem pairing unions powers separation hP hr,
    M.fixedTopMeet_mem pairing unions powers separation hP hr,
    M.attachmentOldEmbeddingGraph_mem pairing unions powers separation hP⟩

theorem exists_fixedTopOrder
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r μ : ZFSet.{u}} (old : MeetOrderCode P r μ)
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) :
    ∃ L ∈ M.sets, ∃ s ∈ M.sets, ∃ ν ∈ M.sets, ∃ e ∈ M.sets,
      L = fixedTopCarrier P ∧ s = fixedTopOrder P r ∧ ν = fixedTopMeet P r ∧
      e = attachmentOldEmbeddingGraph P ∧ MeetOrderCode L s ν ∧
      MeetEmbeddingCode P L r s μ ν e ∧ P ∈ L ∧ P ∉ P ∧
      P ⊆ L ∧ r ⊆ s ∧ μ ⊆ ν ∧
      (∀ x ∈ L, ZFSet.pair x P ∈ s) ∧
      (∀ x ∈ P, ZFSet.pair P x ∉ s) ∧
      (∀ x y, y ∈ P → (ZFSet.pair x y ∈ s ↔ ZFSet.pair x y ∈ r)) ∧
      (∀ x ∈ P, ∀ y ∈ P, ∀ z, ZFSet.pair (ZFSet.pair x y) z ∈ ν ↔
        ZFSet.pair (ZFSet.pair x y) z ∈ μ) ∧
      (∀ x y, y ∈ P → ZFSet.pair x y ∈ s → x ∈ P) := by
  obtain ⟨hL, hs, hν, he⟩ := M.fixedTop_ground_codes pairing unions powers separation hP hr
  exact ⟨fixedTopCarrier P, hL, fixedTopOrder P r, hs, fixedTopMeet P r, hν,
    attachmentOldEmbeddingGraph P, he, rfl, rfl, rfl, rfl, fixedTopMeet_code old,
    fixedTopOldEmbedding_code old, fixedTopCarrier_top P, ZFSet.mem_irrefl P,
    fixedTopCarrier_subset P, fixedTopOrder_subset P r, fixedTopMeet_subset old,
    fun _ hx => fixedTopOrder_greatest hx,
    fun _ hx => (fixedTopOrder_strict_top old.order hx).2,
    fun _ _ hy => fixedTopOrder_old_iff hy,
    fun _ hx _ hy _ => fixedTopMeet_old_iff old hx hy,
    fun _ _ hy entry => fixedTopOrder_no_new_below old.order hy entry⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
