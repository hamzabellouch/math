import OAI.Topology.CoarseAssembly.InvolutiveNormalization
import Mathlib.Analysis.Normed.Operator.Fredholm.Open

namespace OAI

/-! # Compact parametrices and finite-dimensional defects

These are the finite-dimensional analytic ingredients for the scalar-unitary
index pairing. No index-pairing conclusion is assumed here.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem finiteDimensional_ker_of_compact_parametrix (S T : End H)
    (hc : IsCompactOperator (S * T - 1 : End H)) : FiniteDimensional ℂ T.ker := by
  let K : End H := S * T - 1
  let V : Submodule ℂ H := Module.End.eigenspace K.toLinearMap (-1)
  have hv : FiniteDimensional ℂ V :=
    ContinuousLinearMap.finite_dimensional_eigenspace hc (-1) (by norm_num)
  have hi : T.ker ≤ V := by
    intro x hx
    have hx' : T x = 0 := hx
    rw [Module.End.mem_eigenspace_iff]
    simp [K, hx']
  let := hv
  exact FiniteDimensional.of_injective (Submodule.inclusion hi) (Submodule.inclusion_injective hi)

theorem compact_idempotent_finiteRange (P : End H) (hp : P * P = P)
    (hc : IsCompactOperator P) : LinearMap.HasFiniteRange P.toLinearMap := by
  let V : Submodule ℂ H := Module.End.eigenspace P.toLinearMap 1
  have hv : FiniteDimensional ℂ V :=
    ContinuousLinearMap.finite_dimensional_eigenspace hc 1 one_ne_zero
  have hi : P.range ≤ V := by
    rintro y ⟨x, rfl⟩
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact congrArg (fun T : End H => T x) hp
  let := hv
  apply (Submodule.fg_iff_finiteDimensional _).mpr
  exact FiniteDimensional.of_injective (Submodule.inclusion hi) (Submodule.inclusion_injective hi)

theorem fredholm_of_finite_parametrix (S T : End H)
    (hl : LinearMap.HasFiniteRange (S * T - 1 : End H).toLinearMap)
    (hr : LinearMap.HasFiniteRange (T * S - 1 : End H).toLinearMap) : T.IsFredholm := by
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := S)
  constructor
  · rw [LinearMap.IsLeftQuasiInverse, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    exact hl
  · rw [LinearMap.IsRightQuasiInverse, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    exact hr

theorem isFredholm_of_compact_essential_unitary (T : End H)
    (hl : IsCompactOperator (star T * T - 1 : End H))
    (hr : IsCompactOperator (T * star T - 1 : End H)) : T.IsFredholm := by
  let G : End H := star T * T
  have hG : IsSelfAdjoint G := IsSelfAdjoint.star_mul_self T
  have hcG : IsCompactOperator (G * G - 1 : End H) := by
    have he : G * G - 1 = G * (G - 1) + (G - 1) := by noncomm_ring
    rw [he]
    exact (compact_mul_left hl G).add hl
  let P := kernelProjection G
  have hP := kernelProjection_compact G hcG
  have hPP : P * P = P := kernelProjection_sq G
  have hTP : T * P = 0 := by
    ext x
    have hx : G (P x) = 0 := congrArg (fun A : End H => A x) (mul_kernelProjection G)
    have he : G.ker = T.ker := ContinuousLinearMap.ker_adjoint_comp_self T
    have hx' : P x ∈ G.ker := hx
    exact (show P x ∈ T.ker from he ▸ hx')
  have hu : IsUnit (G + P) := kernel_corrected_isUnit G hG hcG
  let V : End H := ↑(hu.unit⁻¹)
  have hVA : V * (G + P) = 1 := by
    rw [← hu.unit_spec]
    exact Units.inv_mul hu.unit
  have hVP : V * P = P := by
    have hAP : (G + P) * P = P := by
      rw [add_mul, mul_kernelProjection G, hPP, zero_add]
    calc
      V * P = V * ((G + P) * P) := by rw [hAP]
      _ = (V * (G + P)) * P := (mul_assoc _ _ _).symm
      _ = P := by rw [hVA, one_mul]
  let S : End H := V * star T
  have hST : S * T = 1 - P := by
    calc
      S * T = V * (G + P) - V * P := by dsimp only [S, G]; noncomm_ring
      _ = 1 - P := by rw [hVA, hVP]
  have hVm : IsCompactOperator (V - 1 : End H) := by
    have he : V - 1 = -(V * ((G - 1) + P)) := by
      calc
        V - 1 = V - V * (G + P) := by rw [hVA]
        _ = -(V * ((G - 1) + P)) := by noncomm_ring
    rw [he]
    exact (compact_mul_left (hl.add hP) V).neg
  have hTS : IsCompactOperator (T * S - 1 : End H) := by
    have he : T * S - 1 = (T * star T - 1) + (T * (V - 1)) * star T := by
      dsimp only [S]
      noncomm_ring
    rw [he]
    exact hr.add (compact_mul_right (compact_mul_left hVm T) (star T))
  have hTSsq : (T * S) * (T * S) = T * S := by
    calc
      (T * S) * (T * S) = T * (S * T) * S := by noncomm_ring
      _ = T * S := by rw [hST, mul_sub, mul_one, hTP, sub_zero]
  have hQsq : (1 - T * S) * (1 - T * S) = 1 - T * S := by
    calc
      _ = 1 - T * S - T * S + (T * S) * (T * S) := by noncomm_ring
      _ = 1 - T * S := by rw [hTSsq]; abel
  have hQ : IsCompactOperator (1 - T * S : End H) := by
    rw [show (1 : End H) - T * S = -(T * S - 1) by abel]
    exact hTS.neg
  have hlfin : LinearMap.HasFiniteRange (S * T - 1 : End H).toLinearMap := by
    rw [hST, show (1 : End H) - P - 1 = -P by abel]
    exact (compact_idempotent_finiteRange P hPP hP).neg
  have hrfin : LinearMap.HasFiniteRange (T * S - 1 : End H).toLinearMap := by
    rw [show T * S - (1 : End H) = -(1 - T * S) by abel]
    exact (compact_idempotent_finiteRange _ hQsq hQ).neg
  exact fredholm_of_finite_parametrix S T hlfin hrfin

end CoarseAssembly.Analytic

end

end OAI
