import OAI.RepresentationTheory.VertexAlgebra.ModuleAdjoints

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)

namespace UnitaryStructure
variable {M} (Q : M.UnitaryStructure U)
include Q
theorem normal_product_quadratic {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (b : W) :
    (inner ℂ (mode M.fields (mode A.fields a (-1) a) (2 * (d : ℤ) - 1) b) b).re =
      ∑ᶠ j : ℕ,
        (‖M.physicalMode a d (d + j) b‖ ^ 2 +
         ‖M.physicalMode a d (j + 1 - d) b‖ ^ 2) := by
  let L : W →+ ℝ :=
    { toFun := fun x => (inner ℂ x b).re
      map_zero' := by simp
      map_add' := by intro x y; simp }
  change L _ = _
  rw [M.mode_normal_product,
    L.map_finsum (M.mode_normal_product_hasFiniteSupport a a b (2 * (d : ℤ) - 1))]
  apply finsum_congr
  intro j
  have h₁ : mode M.fields a (-1 - j) = M.physicalMode a d (-(d + (j : ℤ))) := by
    dsimp [physicalMode]
    congr 1
    omega
  have h₂ : mode M.fields a (2 * (d : ℤ) - 1 + j) = M.physicalMode a d (d + j) := by
    dsimp [physicalMode]
    congr 1
    omega
  have h₃ : mode M.fields a (2 * (d : ℤ) - 1 - 1 - j) =
      M.physicalMode a d (-(j + 1 - d)) := by
    dsimp [physicalMode]
    congr 1
    omega
  have h₄ : mode M.fields a j = M.physicalMode a d (j + 1 - d) := by
    dsimp [physicalMode]
    congr 1
    omega
  dsimp [L]
  rw [inner_add_left, Complex.add_re, h₁, h₂, h₃, h₄,
    Q.physicalMode_adjoint ha hq hh (-(d + j)),
    Q.physicalMode_adjoint ha hq hh (-(j + 1 - d))]
  simp only [neg_neg]
  exact congrArg₂ (· + ·) (inner_self_eq_norm_sq (𝕜 := ℂ) _) (inner_self_eq_norm_sq (𝕜 := ℂ) _)

omit Q in
 

theorem normal_product_norms_hasFiniteSupport (a : V) (b : W) (d : ℕ) :
    Function.HasFiniteSupport (fun j : ℕ =>
        ‖M.physicalMode a d (d + j) b‖ ^ 2 +
        ‖M.physicalMode a d (j + 1 - d) b‖ ^ 2) := by
  have h₁ := mode_shift_hasFiniteSupport M.fields a b (2 * (d : ℤ) - 1)
  have h₂ := mode_shift_hasFiniteSupport M.fields a b 0
  apply (h₁.union h₂).subset
  intro j hj
  by_contra h
  have he₁ : mode M.fields a (2 * (d : ℤ) - 1 + j) b = 0 := by
    by_contra hn
    exact h (Or.inl hn)
  have he₂ : mode M.fields a (0 + j) b = 0 := by
    by_contra hn
    exact h (Or.inr hn)
  apply hj
  change ‖mode M.fields a (d + j + d - 1) b‖ ^ 2 +
        ‖mode M.fields a (j + 1 - d + d - 1) b‖ ^ 2 = 0
  rw [show (d : ℤ) + j + d - 1 = 2 * d - 1 + j by omega,
    show (j : ℤ) + 1 - d + d - 1 = 0 + j by omega, he₁, he₂]
  simp

 

theorem positive_column {a : V} {d : ℕ} (hd : 1 ≤ d) (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (b : W) :
    (∑ᶠ m : ℕ, ‖M.physicalMode a d m b‖ ^ 2) ≤
      (inner ℂ (mode M.fields (mode A.fields a (-1) a) (2 * (d : ℤ) - 1) b) b).re := by
  rw [Q.normal_product_quadratic ha hq hh]
  have hf : Function.HasFiniteSupport (fun m : ℕ => ‖M.physicalMode a d m b‖ ^ 2) := by
    have h := mode_shift_hasFiniteSupport M.fields a b ((d : ℤ) - 1)
    have h' := Function.HasFiniteSupport.comp h (g := fun x : W => ‖x‖ ^ 2) (by simp)
    have he (m : ℕ) : (m : ℤ) + d - 1 = d - 1 + m := by omega
    simpa only [Function.comp_def, physicalMode, he] using h' 
  have hg := normal_product_norms_hasFiniteSupport (M := M) a b d
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ℕ) hf,
    ← tsum_eq_finsum (L := SummationFilter.unconditional ℕ) hg]
  apply Summable.tsum_le_tsum_of_inj (fun m => m + (d - 1))
    (by intro x y h; dsimp at h; omega) (by intro i hi; positivity) _
    (summable_of_hasFiniteSupport hf) (summable_of_hasFiniteSupport hg)
  intro m
  have he : ((m + (d - 1) : ℕ) : ℤ) + 1 - d = m := by omega
  rw [he]
  exact le_add_of_nonneg_left (sq_nonneg _)

end UnitaryStructure

end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
