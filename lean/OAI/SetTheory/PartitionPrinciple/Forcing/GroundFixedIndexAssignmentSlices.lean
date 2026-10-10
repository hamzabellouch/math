import OAI.SetTheory.PartitionPrinciple.Geometry.RepresentativeIndexSteps

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

noncomputable def fixedIndexAssignmentPairs (idx T A : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (assignmentOnIndices {idx} T A) (ZFSet.prod T T)
    (productSecond {idx} (ZFSet.prod T T))

theorem mem_fixedIndexAssignmentPairs (idx T A v w : ZFSet.{u}) :
    ZFSet.pair v w ∈ fixedIndexAssignmentPairs idx T A ↔
      v ∈ T ∧ w ∈ T ∧ stageOneAssignment idx v w ∈ A := by
  rw [fixedIndexAssignmentPairs, mem_relationImage]
  constructor
  · rintro ⟨bound, x, hx, edge⟩
    obtain ⟨i, hi, pair, _, equal⟩ := (mem_productSecond _ _ _).1 edge
    have ei : i = idx := ZFSet.mem_singleton.1 hi
    obtain ⟨ex, ep⟩ := ZFSet.pair_inj.1 equal
    subst i
    subst pair
    exact ⟨(ZFSet.pair_mem_prod.1 bound).1, (ZFSet.pair_mem_prod.1 bound).2,
      ex ▸ (mem_assignmentOnIndices _ _ _ _).1 hx |>.1⟩
  · rintro ⟨hv, hw, old⟩
    have bounds := ZFSet.pair_mem_prod.2 ⟨hv, hw⟩
    exact ⟨bounds, stageOneAssignment idx v w,
      (assignmentOnIndices_entry _ _ _ _ _ _).2 ⟨old, ZFSet.mem_singleton.2 rfl, hv, hw⟩,
      (mem_productSecond _ _ _).2 ⟨idx, ZFSet.mem_singleton.2 rfl, _, bounds, rfl⟩⟩

noncomputable def fixedIndexAssignmentClassGraph (idx T A B graph : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (fixedIndexAssignmentPairs idx T A) (stageOneAssignments {idx} T) B
    (relationConverse (stageOneAssignments {idx} T) (ZFSet.prod T T)
      (productSecond {idx} (ZFSet.prod T T))) graph

theorem fixedIndexAssignmentClassGraph_entry (idx T A B graph v w y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair v w) y ∈ fixedIndexAssignmentClassGraph idx T A B graph ↔
      v ∈ T ∧ w ∈ T ∧ stageOneAssignment idx v w ∈ A ∧ y ∈ B ∧
        ZFSet.pair (stageOneAssignment idx v w) y ∈ graph := by
  rw [fixedIndexAssignmentClassGraph, pair_mem_relationCompose, mem_fixedIndexAssignmentPairs]
  constructor
  · rintro ⟨⟨hv, hw, old⟩, hy, x, _, inverse, edge⟩
    have projection := ((pair_mem_relationConverse _ _ _ x (ZFSet.pair v w)).1 inverse).2.2
    obtain ⟨i, hi, pair, _, equal⟩ := (mem_productSecond _ _ _).1 projection
    have ei : i = idx := ZFSet.mem_singleton.1 hi
    obtain ⟨ex, ep⟩ := ZFSet.pair_inj.1 equal
    subst i
    subst pair
    subst x
    exact ⟨hv, hw, old, hy, edge⟩
  · rintro ⟨hv, hw, old, hy, edge⟩
    have bound := ZFSet.pair_mem_prod.2 ⟨hv, hw⟩
    have triple := (stageOneAssignment_mem_assignments {idx} T idx v w).2
      ⟨ZFSet.mem_singleton.2 rfl, hv, hw⟩
    exact ⟨⟨hv, hw, old⟩, hy, _, triple,
      (pair_mem_relationConverse _ _ _ _ _).2 ⟨triple, bound,
        (mem_productSecond _ _ _).2 ⟨idx, ZFSet.mem_singleton.2 rfl, _, bound, rfl⟩⟩, edge⟩

theorem fixedIndexAssignmentClassGraph_function {idx T A B graph D : ZFSet.{u}}
    (function : ZFSet.IsFunc D B graph)
    (covered : ∀ v ∈ T, ∀ w ∈ T, stageOneAssignment idx v w ∈ A →
      stageOneAssignment idx v w ∈ D) :
    ZFSet.IsFunc (fixedIndexAssignmentPairs idx T A) B
      (fixedIndexAssignmentClassGraph idx T A B graph) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    unfold fixedIndexAssignmentClassGraph relationCompose at hz
    exact (ZFSet.mem_sep.1 hz).1
  · intro pair member
    have pairBound := (mem_relationImage _ _ _ pair).1 member |>.1
    obtain ⟨v, hv, w, hw, rfl⟩ := ZFSet.mem_prod.1 pairBound
    have old := (mem_fixedIndexAssignmentPairs idx T A v w).1 member |>.2.2
    obtain ⟨y, edge, unique⟩ := function.2 _ (covered v hv w hw old)
    have hy := (ZFSet.pair_mem_prod.1 (function.1 edge)).2
    exact ⟨y, (fixedIndexAssignmentClassGraph_entry _ _ _ _ _ _ _ _).2 ⟨hv, hw, old, hy, edge⟩,
      fun z hz => unique z ((fixedIndexAssignmentClassGraph_entry _ _ _ _ _ _ _ _).1 hz).2.2.2.2⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem fixedIndexAssignmentPairs_mem_small
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {idx T A N : ZFSet.{u}} (hIdx : idx ∈ M.sets) (hT : T ∈ M.sets)
    (hA : A ∈ M.sets) (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    fixedIndexAssignmentPairs idx T A ∈ M.sets ∧
      M.groundEmbeddable (fixedIndexAssignmentPairs idx T A) N := by
  have singleton : ({idx} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hIdx hIdx
  have slice := M.assignmentOnIndices_mem pairing unions powers separation singleton hT hA
  have sliceSmall := M.assignmentOnIndices_small pairing unions powers separation singleton hT hA hN small
  have bound := M.prod_mem pairing unions powers separation hT hT
  have graph := M.productSecond_mem pairing unions powers separation singleton bound
  exact ⟨M.relationImage_mem separation slice bound graph,
    M.groundEmbeddable_function_image pairing unions powers separation choice slice bound hN
      graph (productSecond_function {idx} (ZFSet.prod T T)) sliceSmall⟩

theorem fixedIndexAssignmentClassGraph_mem
    {idx T A B graph : ZFSet.{u}} (hIdx : idx ∈ M.sets) (hT : T ∈ M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hGraph : graph ∈ M.sets) :
    fixedIndexAssignmentClassGraph idx T A B graph ∈ M.sets := by
  have singleton : ({idx} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hIdx hIdx
  have pairs := M.prod_mem pairing unions powers separation hT hT
  have slice := M.assignmentOnIndices_mem pairing unions powers separation singleton hT hA
  have projection := M.productSecond_mem pairing unions powers separation singleton pairs
  have domain := M.relationImage_mem separation slice pairs projection
  have triples := M.stageOneAssignments_mem pairing unions powers separation singleton hT
  exact M.relationCompose_mem pairing unions powers separation domain triples hB
    (M.relationConverse_mem pairing unions powers separation triples pairs projection) hGraph

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
