import OAI.RepresentationTheory.VertexAlgebra.ModuleCreationEstimates

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)

def creationTerm (a : W) (n : ℤ) (v : V) (j : ℕ) : W :=
  (((-1:ℂ)^(n+(j:ℤ)+1))/(j.factorial:ℂ)) •
    ((M.virasoroMode (-1)^j) (mode M.fields v (n+j) a))

theorem creationTerm_finiteSupport (a : W) (n : ℤ) (v : V) :
    (Function.support (M.creationTerm a n v)).Finite := by
  apply (mode_shift_hasFiniteSupport M.fields v a n).subset
  intro j hj
  contrapose! hj
  simp only [Function.mem_support] at hj ⊢
  simp only [not_not] at hj ⊢
  simp only [creationTerm, hj, map_zero, smul_zero]

def creationMode (a : W) (n : ℤ) : V →ₗ[ℂ] W where
  toFun v := ∑ᶠ j : ℕ, M.creationTerm a n v j
  map_add' v w := by
    have he : M.creationTerm a n (v+w) = fun j =>
        M.creationTerm a n v j + M.creationTerm a n w j := by
      funext j
      simp [creationTerm, map_add, smul_add]
    rw [he, finsum_add_distrib (M.creationTerm_finiteSupport a n v)
      (M.creationTerm_finiteSupport a n w)]
  map_smul' z v := by
    simp only [creationTerm, mode_smul, LinearMap.smul_apply, map_smul]
    simp_rw [smul_comm (_ / _) z]
    rw [← smul_finsum]
    rfl

@[simp] theorem creationMode_apply (a : W) (n : ℤ) (v : V) :
    M.creationMode a n v = ∑ᶠ j : ℕ, M.creationTerm a n v j := rfl

theorem creationMode_vacuum_nonneg (a : W) (n : ℤ) (hn : 0 ≤ n) :
    M.creationMode a n A.vacuum = 0 := by
  rw [creationMode_apply]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  simp only [creationTerm, M.vacuum_mode, ite_eq_right (by omega : n+(j:ℤ) ≠ -1),
    LinearMap.zero_apply, map_zero, smul_zero]

theorem creationMode_vacuum (a : W) (k : ℕ) :
    M.creationMode a (-(k:ℤ)-1) A.vacuum =
      (k.factorial:ℂ)⁻¹ • ((M.virasoroMode (-1)^k) a) := by
  rw [creationMode_apply, finsum_eq_single _ k]
  · have he : -(k:ℤ)-1+(k:ℤ) = -1 := by omega
    simp [creationTerm, M.vacuum_mode, he]
  · intro j hj
    have he : -(k:ℤ)-1+(j:ℤ) ≠ -1 := by omega
    simp [creationTerm, M.vacuum_mode, he]

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
