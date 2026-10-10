import OAI.Topology.CoarseAssembly.MultiplierBoundaryHomotopy

namespace OAI

/-! # Roe perturbations do not change the analytic boundary class -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance roePerturbationScalarTower : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance roePerturbationScalarComm : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp
local instance roePerturbationContinuousStar : ContinuousStar (Operator X H) := ⟨operator_star_continuous⟩

theorem multiplierBoundaryClass_roePerturbation
    (F G : multiplierAlgebra (X := X) (H := H))
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hGd : G.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hGF : G.val - F.val ∈ algebra (X := X) (H := H)) :
    multiplierBoundaryClass F hF hFd = multiplierBoundaryClass G hG hGd := by
  let L : Interval → multiplierAlgebra (X := X) (H := H) :=
    fun t => F + (t.val : ℂ) • (G - F)
  have hL : ∀ t, IsSelfAdjoint (L t) := by
    intro t
    change star (F + (t.val : ℂ) • (G - F)) = F + (t.val : ℂ) • (G - F)
    simp only [star_add, star_smul, star_sub, hF.star_eq, hG.star_eq,
      Complex.star_def, Complex.conj_ofReal]
  have hLd : ∀ t, (L t).val ^ 2 - 1 ∈ algebra (X := X) (H := H) := by
    intro t
    let K : Operator X H := (t.val : ℂ) • (G.val - F.val)
    have hK : K ∈ algebra (X := X) (H := H) := (algebra (X := X) (H := H)).smul_mem _ hGF
    have hm := F.property ⟨K, hK⟩
    have he : (L t).val ^ 2 - 1 = (F.val ^ 2 - 1) + F.val * K + K * F.val + K * K := by
      change (F.val + K) ^ 2 - 1 = _
      noncomm_ring
    rw [he]
    exact add_mem (add_mem (add_mem hFd hm.1) hm.2) (mul_mem hK hK)
  have hc : Continuous L := by
    exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_subtype_val).smul
      continuous_const)
  have h0 : L start = F := by simp [L, start]
  have h1 : L finish = G := by simp [L, finish]
  have h := multiplierBoundaryClass_homotopy L hL hLd hc
  simpa only [h0, h1] using h

end CoarseAssembly.DiscreteRoe

end

end OAI
