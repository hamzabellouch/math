import OAI.Topology.CoarseAssembly.BoundedTransform
import OAI.Topology.CoarseAssembly.CayleyNaturality
import OAI.Topology.CoarseAssembly.ScalarCutDown

namespace OAI

/-! # Naturality of the path-compatible rational normalization -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem boundedTransform_congr {F G : A} (h : F = G)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    boundedTransform F hF = boundedTransform G hG := by
  subst G
  rfl

theorem map_boundedTransform (φ : A →⋆ₐ[ℂ] B) (F : A) (hF : IsSelfAdjoint F) :
    φ (boundedTransform F hF) = boundedTransform (φ F) (hF.map φ) := by
  simp only [boundedTransform, map_smul, map_sub, map_star, map_cayleyUnitary]

variable {H K : HilbertSpace}

theorem map_symmetricCutDown (φ : End H →⋆ₐ[ℂ] End K) (P F : End H) :
    φ (symmetricCutDown P F) = symmetricCutDown (φ P) (φ F) := by
  unfold symmetricCutDown
  have hs (T : End H) : φ ((1 / 2 : ℝ) • T) = (1 / 2 : ℝ) • φ T :=
    φ.toAlgHom.map_smul_of_tower _ _
  rw [map_add, hs]
  simp only [map_add, map_mul, map_star, map_sub, map_one]

end CoarseAssembly.Analytic

end

end OAI
