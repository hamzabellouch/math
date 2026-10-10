import OAI.SetTheory.PartitionPrinciple.Definability.GroundRegularFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundAssignmentIndexLevels

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem small_assignmentCuts_bounded
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U J K levels : ZFSet.{u}} (hU : U ∈ M.sets) (hK : K ∈ M.sets)
    (hLevels : levels ∈ M.sets) (regular : GroundRegular M K)
    (small : GroundBelow M U K) (function : ZFSet.IsFunc J K levels) (subset : U ⊆ J) :
    ∃ beta ∈ K, ∀ A, A ⊆ U → assignmentCut levels beta A = A := by
  have restricted : ZFSet.IsFunc U K (graphRestriction U levels) := by
    refine ⟨?_, ?_⟩
    · intro z member
      obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 member
      exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.pair_mem_prod.1 (function.1 entry)).2⟩
    · intro x hx
      obtain ⟨y, entry, unique⟩ := function.2 x (subset hx)
      exact ⟨y, pair_mem_graphRestriction.2 ⟨entry, hx⟩,
        fun z hz => unique z (pair_mem_graphRestriction.1 hz).1⟩
  obtain ⟨beta, hBeta, bound⟩ := regular.bound_small_domain pairing unions powers separation
    hU hK (M.graphRestriction_mem unions separation hU hLevels) small restricted
  refine ⟨beta, hBeta, fun A contained => assignmentCut_eq_of_lower ?_⟩
  intro z hz
  obtain ⟨level, entry, _⟩ := function.2 z (subset (contained hz))
  exact ⟨level, bound z level (pair_mem_graphRestriction.2 ⟨entry, contained hz⟩), entry⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
