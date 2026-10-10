import OAI.Topology.CoarseAssembly.FredholmSquare
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

namespace OAI

/-! # The finite-rank kernel correction

For a self-adjoint operator with compact square defect, the orthogonal
projection onto its kernel is compact. Adding that projection removes the
kernel and preserves self-adjointness and the compact square defect.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

def kernelClosedSubmodule (F : End H) : ClosedSubmodule ℂ H :=
  ⟨F.ker, F.isClosed_ker⟩

def kernelProjection (F : End H) : End H := (kernelClosedSubmodule F).starProjection

theorem kernelProjection_selfAdjoint (F : End H) : IsSelfAdjoint (kernelProjection F) :=
  isSelfAdjoint_starProjection _

theorem mul_kernelProjection (F : End H) : F * kernelProjection F = 0 := by
  ext x
  exact (kernelClosedSubmodule F).starProjection_apply_mem x

theorem kernelProjection_mul (F : End H) (hF : IsSelfAdjoint F) :
    kernelProjection F * F = 0 := by
  have h := congrArg star (mul_kernelProjection F)
  simpa only [star_mul, star_zero, hF.star_eq, (kernelProjection_selfAdjoint F).star_eq] using h

theorem kernelProjection_sq (F : End H) :
    kernelProjection F * kernelProjection F = kernelProjection F :=
  (kernelClosedSubmodule F).isIdempotentElem_starProjection

theorem kernelProjection_compact (F : End H)
    (hF : IsCompactOperator (F * F - 1 : End H)) :
    IsCompactOperator (kernelProjection F) := by
  let V := kernelClosedSubmodule F
  let : FiniteDimensional ℂ V := finiteDimensional_ker_of_compact_square F hF
  have hi : IsCompactOperator (id : V → V) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ)).2 inferInstance
  have hp : IsCompactOperator V.orthogonalProjectionOnto := hi.comp_clm _
  exact hp.clm_comp V.subtypeL

theorem kernel_corrected_eq_zero (F : End H) (hF : IsSelfAdjoint F)
    (x : H) (hx : (F + kernelProjection F) x = 0) : x = 0 := by
  have hprod : kernelProjection F * (F + kernelProjection F) = kernelProjection F := by
    rw [mul_add, kernelProjection_mul F hF, kernelProjection_sq, zero_add]
  have hp : kernelProjection F x = 0 := by
    calc
      kernelProjection F x = (kernelProjection F * (F + kernelProjection F)) x :=
        congrArg (fun T : End H => T x) hprod.symm
      _ = kernelProjection F ((F + kernelProjection F) x) := rfl
      _ = 0 := by rw [hx, map_zero]
  have hf : F x = 0 := by
    change F x + kernelProjection F x = 0 at hx
    simpa only [hp, add_zero] using hx
  have he : kernelProjection F x = x :=
    (kernelClosedSubmodule F).starProjection_eq_self_iff.mpr hf
  exact he.symm.trans hp

theorem kernel_corrected_injective (F : End H) (hF : IsSelfAdjoint F) :
    Function.Injective (F + kernelProjection F) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply kernel_corrected_eq_zero F hF
  rw [map_sub, hxy, sub_self]

theorem kernel_corrected_selfAdjoint (F : End H) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (F + kernelProjection F) :=
  hF.add (kernelProjection_selfAdjoint F)

theorem kernel_corrected_compact_square (F : End H) (hF : IsSelfAdjoint F)
    (hc : IsCompactOperator (F * F - 1 : End H)) :
    IsCompactOperator ((F + kernelProjection F) * (F + kernelProjection F) - 1 : End H) := by
  have he : (F + kernelProjection F) * (F + kernelProjection F) - 1 =
      (F * F - 1) + kernelProjection F := by
    rw [add_mul, mul_add, mul_add, mul_kernelProjection,
      kernelProjection_mul F hF, kernelProjection_sq]
    abel
  rw [he]
  exact hc.add (kernelProjection_compact F hc)

end CoarseAssembly.Analytic

end

end OAI
