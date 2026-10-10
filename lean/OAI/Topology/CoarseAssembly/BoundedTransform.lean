import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.CayleyContinuity
import OAI.Topology.CoarseAssembly.CayleyNormControl
import OAI.Topology.CoarseAssembly.CycleCompactPerturbation
import Mathlib.Tactic.Module

namespace OAI

/-! # A continuous bounded transform of self-adjoint Fredholm operators

The imaginary part of the Cayley transform is the rational function
`2x / (1 + x²)`. It is contractive and varies continuously even when the
original family has no uniform norm bound.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem boundedTransform_selfAdjoint (F : A) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (boundedTransform F hF) := by
  change star (boundedTransform F hF) = boundedTransform F hF
  simp only [boundedTransform, star_smul, star_sub, star_star, Complex.star_def,
    map_div₀, Complex.conj_I, map_ofNat, neg_div, neg_smul]
  module

theorem boundedTransform_norm_le (F : A) (hF : IsSelfAdjoint F) :
    ‖boundedTransform F hF‖ ≤ 1 := by
  nontriviality A
  unfold boundedTransform
  rw [norm_smul, norm_div, Complex.norm_I, Complex.norm_ofNat]
  have hn := norm_sub_le (cayleyUnitary F hF : A) (star (cayleyUnitary F hF : A))
  rw [norm_star, CStarRing.norm_coe_unitary] at hn
  nlinarith

theorem continuous_boundedTransform {T : Type*} [TopologicalSpace T]
    (F : T → A) (hF : ∀ t, IsSelfAdjoint (F t)) (hc : Continuous F) :
    Continuous (fun t => boundedTransform (F t) (hF t)) := by
  have hu := continuous_cayleyUnitary F hF hc
  exact continuous_const.smul (hu.sub hu.star)

end CoarseAssembly.Analytic

end

end OAI
