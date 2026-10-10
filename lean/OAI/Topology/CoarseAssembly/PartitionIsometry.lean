import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RoeCalculus

namespace OAI

/-! # The Hilbert-space isometry of a finite square partition -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
@[simp] theorem coordinate_partitionMap (a : X → H →L[ℂ] H) (x : X) :
    (coordinate x).comp (partitionMap a) = a x := by
  ext v
  simp [partitionMap, ContinuousLinearMap.comp_apply, coordinate_apply, insert_apply,
    lp.single_apply]

theorem partitionMap_adjoint (a : X → H →L[ℂ] H) :
    (partitionMap a).adjoint = ∑ x, (a x).adjoint.comp (coordinate x) := by
  simp only [partitionMap, map_sum, ContinuousLinearMap.adjoint_comp, insert_adjoint]

theorem partitionMap_adjoint_comp (a : X → H →L[ℂ] H) :
    (partitionMap a).adjoint.comp (partitionMap a) = ∑ x, (a x).adjoint.comp (a x) := by
  rw [partitionMap_adjoint, ContinuousLinearMap.finsetSum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [ContinuousLinearMap.comp_assoc, coordinate_partitionMap]

@[simp] theorem partitionIsometry_toContinuousLinearMap (a : X → H →L[ℂ] H)
    (hpart : ∑ x, (a x).adjoint.comp (a x) = 1) :
    (partitionIsometry a hpart).toContinuousLinearMap = partitionMap a := rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
