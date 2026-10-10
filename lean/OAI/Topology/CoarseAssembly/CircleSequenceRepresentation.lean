import OAI.Topology.CoarseAssembly.NegativeProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.Complex.Circle

namespace OAI

/-! # Continuous circle functions represented by the bilateral shift -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped CStarAlgebra

def circleCoordinate : C(Circle, ℂ) := ⟨fun z => (z : ℂ), continuous_subtype_val⟩

theorem bilateralShift_mem_unitary : bilateralShift ∈ unitary (End circleSequenceSpace) :=
  Unitary.mem_iff.mpr bilateralShift_unitary

theorem bilateralShift_spectrum_circle : spectrum ℂ bilateralShift ⊆
    (Submonoid.unitSphere ℂ : Set ℂ) := by
  intro z hz
  exact mem_sphere_zero_iff_norm.mpr (CStarRing.norm_of_mem_unitary
    (spectrum_subset_unitary_of_mem_unitary bilateralShift_mem_unitary hz))

/-- Continuous functional calculus of the actual bilateral shift. -/
def circleRepresentation : C(Circle, ℂ) →⋆ₐ[ℂ] End circleSequenceSpace :=
  cfcHomSuperset (isStarNormal_of_mem_unitary bilateralShift_mem_unitary) bilateralShift_spectrum_circle

@[simp] theorem circleRepresentation_coordinate : circleRepresentation circleCoordinate = bilateralShift :=
  cfcHomSuperset_id _ _

end CoarseAssembly.Analytic

end

end OAI
