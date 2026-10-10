import OAI.RepresentationTheory.VertexAlgebra.ModuleGrading

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {A : CFTTypeVOA V} {W : Type v} [AddCommGroup W] [Module ℂ W]
  (M : A.GradingRestrictedModule W)
theorem virasoro_one_physical_commutator {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (m : ℤ) :
    M.virasoroMode 1 * M.physicalMode a d m - M.physicalMode a d m * M.virasoroMode 1 =
      ((d : ℂ) - 1 - m) • M.physicalMode a d (m + 1) := by
  ext v
  have h := M.toWeakModule.mode_commutator_nat A.conformalVector a v 2 (m + (d : ℤ) - 1)
  have h0 : mode A.fields A.conformalVector 0 a = A.toVertexAlgebra.translation a :=
    by rw [A.conformal_translation]
  have h1 : mode A.fields A.conformalVector 1 a = (d : ℂ) • a :=
    A.virasoro_zero_on_grade ha
  have h2 : mode A.fields A.conformalVector 2 a = 0 := hq
  have ht := congrArg (fun f : Module.End ℂ W => f v)
    (M.toWeakModule.translation_covariance a (m + d + 1))
  simp only [LinearMap.smul_apply] at ht
  norm_num [Finset.sum_range_succ, h0, h1, h2, mode_zero, mode_smul] at h
  rw [show (2 : ℤ) + (m + d - 1) = m + d + 1 by omega] at h
  rw [ht] at h
  simp only [show m + (d : ℤ) + 1 - 1 = m + d by omega] at h
  change M.virasoroMode 1 (M.physicalMode a d m v) -
    M.physicalMode a d m (M.virasoroMode 1 v) =
      ((d : ℂ) - 1 - m) • M.physicalMode a d (m + 1) v
  change mode M.fields A.conformalVector 2 (mode M.fields a (m + d - 1) v) -
    mode M.fields a (m + d - 1) (mode M.fields A.conformalVector 2 v) =
      ((d : ℂ) - 1 - m) • mode M.fields a (m + 1 + d - 1) v
  rw [show m + 1 + (d : ℤ) - 1 = m + d by omega, h]
  push_cast
  module

 
theorem virasoro_neg_one_physical_commutator (a : V) (d : ℕ) (m : ℤ) :
    M.virasoroMode (-1) * M.physicalMode a d m -
      M.physicalMode a d m * M.virasoroMode (-1) =
        (-((d : ℂ) - 1 + m)) • M.physicalMode a d (m - 1) := by
  ext v
  have h := M.toWeakModule.mode_commutator_nat A.conformalVector a v 0 (m + (d : ℤ) - 1)
  have h0 : mode A.fields A.conformalVector 0 a = A.toVertexAlgebra.translation a :=
    by rw [A.conformal_translation]
  norm_num [Finset.sum_range_succ, h0] at h
  have ht := congrArg (fun f : Module.End ℂ W => f v)
    (M.toWeakModule.translation_covariance a (m + d - 1))
  simp only [LinearMap.smul_apply] at ht
  change mode M.fields A.conformalVector 0 (mode M.fields a (m + d - 1) v) -
    mode M.fields a (m + d - 1) (mode M.fields A.conformalVector 0 v) =
      (-((d : ℂ) - 1 + m)) • mode M.fields a (m - 1 + d - 1) v
  rw [h, ht, show m + (d : ℤ) - 1 - 1 = m - 1 + d - 1 by omega]
  push_cast
  congr 1
  ring

 
theorem sl2_commutator (x : W) :
    M.virasoroMode 1 (M.virasoroMode (-1) x)-
      M.virasoroMode (-1) (M.virasoroMode 1 x)= (2 : ℂ) • M.virasoroMode 0 x := by
  have h := congrArg (fun f : Module.End ℂ W => f x)
    (M.virasoro_one_physical_commutator A.conformal_mem A.conformal_quasiPrimary (-1))
  norm_num [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  exact h
end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
