import OAI.RepresentationTheory.RowColumn.Multiplicity
import OAI.LinearAlgebra.MatrixState.HilbertSchmidt

namespace OAI

section
noncomputable section

namespace RowColumn
open scoped BigOperators ComplexConjugate Classical

section HilbertSchmidt
variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- Ordinary squared Hilbert--Schmidt norm on a possibly rectangular map. -/
def hilbertSchmidtSq (B : V →L[ℂ] W) : ℝ :=
  (LinearMap.trace ℂ V (B.adjoint.comp B).toLinearMap).re

lemma hilbertSchmidtSq_eq_sum (B : V →L[ℂ] W)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ V) :
    hilbertSchmidtSq B = ∑ i, ‖B (b i)‖ ^ 2 := by
  rw [hilbertSchmidtSq, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa using (B.apply_norm_sq_eq_inner_adjoint_right (b i)).symm

lemma norm_sq_le_hilbertSchmidtSq (B : V →L[ℂ] W) :
    ‖B‖ ^ 2 ≤ hilbertSchmidtSq B := by
  let b := stdOrthonormalBasis ℂ V
  have hn : 0 ≤ hilbertSchmidtSq B := by
    rw [hilbertSchmidtSq_eq_sum B b]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh : ‖B‖ ≤ Real.sqrt (hilbertSchmidtSq B) := by
    apply B.opNorm_le_bound (Real.sqrt_nonneg _)
    intro x
    have ha : ‖B x‖ ≤ ∑ i, ‖inner ℂ (b i) x‖ * ‖B (b i)‖ := by
      nth_rw 1 [← b.sum_repr' x]
      rw [map_sum]
      apply (norm_sum_le _ _).trans
      simp only [map_smul, norm_smul]
      exact le_rfl
    have hb := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => ‖inner ℂ (b i) x‖) (fun i => ‖B (b i)‖)
    rw [b.sum_sq_norm_inner_right, Real.sqrt_sq (norm_nonneg x),
      ← hilbertSchmidtSq_eq_sum B b, mul_comm] at hb
    exact ha.trans hb
  exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (Real.sq_sqrt hn)

end HilbertSchmidt

section CopyTrace
variable {V W X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  {u v : ℕ}

/-- Sum of the genuine range projections for the given isometric copies. -/
def copyProjection (I : Fin u → V →ₗᵢ[ℂ] X) : X →L[ℂ] X :=
  ∑ i, (I i).toContinuousLinearMap.comp (I i).toContinuousLinearMap.adjoint

lemma hilbertSchmidtSq_overlap (I : V →ₗᵢ[ℂ] X) (J : W →ₗᵢ[ℂ] X) :
    hilbertSchmidtSq (I.toContinuousLinearMap.adjoint.comp J.toContinuousLinearMap) =
      (LinearMap.trace ℂ X
        ((I.toContinuousLinearMap.comp I.toContinuousLinearMap.adjoint).comp
          (J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint)).toLinearMap).re := by
  unfold hilbertSchmidtSq
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.toLinearMap_comp]
  congr 1
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

/-- The all-copy identity in weighted.tex:126–133, for the actual embeddings.
No overlap bound is an assumption. -/
lemma allCopy_hilbertSchmidt_identity (I : Fin u → V →ₗᵢ[ℂ] X)
    (J : Fin v → W →ₗᵢ[ℂ] X) :
    ∑ i, ∑ j, hilbertSchmidtSq
      ((I i).toContinuousLinearMap.adjoint.comp (J j).toContinuousLinearMap) =
    (LinearMap.trace ℂ X ((copyProjection I).comp (copyProjection J)).toLinearMap).re := by
  change _ = (LinearMap.trace ℂ X
    ((∑ i, (I i).toContinuousLinearMap.comp (I i).toContinuousLinearMap.adjoint) *
      (∑ j, (J j).toContinuousLinearMap.comp (J j).toContinuousLinearMap.adjoint)).toLinearMap).re
  simp only [Finset.sum_mul, Finset.mul_sum, ContinuousLinearMap.toLinearMap_sum,
    map_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact hilbertSchmidtSq_overlap (I i) (J j)

lemma allCopyOverlap_le_trace (I : Fin u → V →ₗᵢ[ℂ] X)
    (J : Fin v → W →ₗᵢ[ℂ] X) :
    allCopyOverlap I J ≤
      (LinearMap.trace ℂ X ((copyProjection I).comp (copyProjection J)).toLinearMap).re := by
  rw [← allCopy_hilbertSchmidt_identity I J]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact norm_sq_le_hilbertSchmidtSq _

end CopyTrace
end RowColumn

end
end

section

noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace RowColumn
open CubeShuffle.UnitaryFinite
variable {V W X E G : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {u v : ℕ}

lemma isometry_adjoint_apply (I : V →ₗᵢ[ℂ] X) (x : V) :
    I.toContinuousLinearMap.adjoint (I x) = x := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact I.inner_map_map y x

lemma isometry_adjoint_comp (I : V →ₗᵢ[ℂ] X) :
    I.toContinuousLinearMap.adjoint.comp I.toContinuousLinearMap = 1 := by
  ext x
  exact isometry_adjoint_apply I x

lemma copyProjection_positive (I : Fin u → V →ₗᵢ[ℂ] X) :
    (copyProjection I).IsPositive := by
  apply ContinuousLinearMap.isPositive_sum
  intro i _
  exact ContinuousLinearMap.isPositive_self_comp_adjoint _

lemma copyProjection_trace (I : Fin u → V →ₗᵢ[ℂ] X) :
    LinearMap.trace ℂ X (copyProjection I).toLinearMap = (u * Module.finrank ℂ V : ℕ) := by
  simp only [copyProjection, ContinuousLinearMap.toLinearMap_sum, map_sum,
    ContinuousLinearMap.toLinearMap_comp]
  have h (i : Fin u) : LinearMap.trace ℂ X
      ((I i).toContinuousLinearMap.toLinearMap.comp (I i).toContinuousLinearMap.adjoint.toLinearMap) =
      (Module.finrank ℂ V : ℂ) := by
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace ℂ V ((I i).toContinuousLinearMap.adjoint.comp
      (I i).toContinuousLinearMap).toLinearMap = _
    rw [isometry_adjoint_comp]
    exact LinearMap.trace_id ℂ V
  simp_rw [h]
  simp [Nat.cast_mul]

lemma copyProjection_intertwines [Group G] (ρ : Representation ℂ G V) (τ : Representation ℂ G X)
    (hρ : IsUnitary ρ) (hτ : IsUnitary τ) (I : Fin u → V →ₗᵢ[ℂ] X)
    (hI : ∀ i, Intertwines ρ τ (I i).toLinearMap) :
    Intertwines τ τ (copyProjection I).toLinearMap := by
  intro g x
  simp only [copyProjection, ContinuousLinearMap.coe_coe, sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (I i).toContinuousLinearMap.adjoint (τ g x) =
    ρ g ((I i).toContinuousLinearMap.adjoint x) from
    adjoint_intertwines (I i).toLinearMap (hI i) hρ hτ g x]
  exact hI i g _

lemma allCopyOverlap_comp_isometry (I : Fin u → V →ₗᵢ[ℂ] X)
    (J : Fin v → W →ₗᵢ[ℂ] X) (K : X →ₗᵢ[ℂ] E) :
    allCopyOverlap (fun i => K.comp (I i)) (fun j => K.comp (J j)) = allCopyOverlap I J := by
  unfold allCopyOverlap
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun T : W →L[ℂ] V => ‖T‖^2)
  ext x
  change (K.toContinuousLinearMap.comp (I i).toContinuousLinearMap).adjoint
    (K (J j x)) = _
  rw [ContinuousLinearMap.adjoint_comp]
  change (I i).toContinuousLinearMap.adjoint (K.toContinuousLinearMap.adjoint (K (J j x))) = _
  rw [isometry_adjoint_apply]
  rfl

lemma allCopyOverlap_le_count (I : Fin u → V →ₗᵢ[ℂ] X)
    (J : Fin v → W →ₗᵢ[ℂ] X) : allCopyOverlap I J ≤ (u : ℝ) * v := by
  unfold allCopyOverlap
  have h (i : Fin u) (j : Fin v) :
      ‖(I i).toContinuousLinearMap.adjoint.comp (J j).toContinuousLinearMap‖^2 ≤ 1 := by
    have hn := ContinuousLinearMap.opNorm_comp_le (I i).toContinuousLinearMap.adjoint
      (J j).toContinuousLinearMap
    rw [ContinuousLinearMap.adjoint.norm_map] at hn
    have hb := mul_le_mul (I i).norm_toContinuousLinearMap_le (J j).norm_toContinuousLinearMap_le
      (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have hz : ‖(I i).toContinuousLinearMap.adjoint.comp (J j).toContinuousLinearMap‖ ≤ 1 :=
      hn.trans (by simpa using hb)
    nlinarith [norm_nonneg ((I i).toContinuousLinearMap.adjoint.comp (J j).toContinuousLinearMap)]
  calc
    _ ≤ ∑ _i : Fin u, ∑ _j : Fin v, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = _ := by simp

end RowColumn

end
end


section
noncomputable section
open scoped BigOperators Classical
namespace RowColumn
open CubeShuffle.UnitaryFinite
variable {G V E : Type*} [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (ρ : Representation ℂ G V) (τ : Representation ℂ G E)
  (hρ : IsUnitary ρ) (hτ : IsUnitary τ)

include hρ hτ
lemma isometric_adjoint_intertwines (f : Representation.IntertwiningMap ρ τ) (g : G) (x : E) :
    LinearMap.adjoint f.toLinearMap (τ g x) = ρ g (LinearMap.adjoint f.toLinearMap x) := by
  have hf : Intertwines ρ τ f.toLinearMap := by
    intro g y
    exact Representation.IntertwiningMap.isIntertwining ρ τ f g y
  have hh := adjoint_intertwines f.toLinearMap hf hρ hτ g x
  simpa only [LinearMap.adjoint_eq_toCLM_adjoint] using hh

def gramIntertwiner (f : Representation.IntertwiningMap ρ τ) : Representation.IntertwiningMap ρ ρ where
  toLinearMap := (LinearMap.adjoint f.toLinearMap).comp f.toLinearMap
  isIntertwining' g := by
    ext x
    change (LinearMap.adjoint f.toLinearMap) (f (ρ g x)) =
      ρ g ((LinearMap.adjoint f.toLinearMap) (f x))
    rw [Representation.IntertwiningMap.isIntertwining]
    exact isometric_adjoint_intertwines ρ τ hρ hτ f g (f x)

/-- Every actual nonzero algebraic embedding of irreducible unitary carriers
normalizes to an isometric intertwiner. No normalized embedding is assumed. -/
theorem isometric_intertwiner_of_injective [Representation.IsIrreducible ρ]
    (f : Representation.IntertwiningMap ρ τ) (hf : Function.Injective f) :
    ∃ I : V →ₗᵢ[ℂ] E, ∀ g x, I (ρ g x)=τ g (I x) := by
  let : Nontrivial V := by
    let := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
    exact ρ.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨c,hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective
      (gramIntertwiner ρ τ hρ hτ f)
  have hgram : (LinearMap.adjoint f.toLinearMap).comp f.toLinearMap = c • LinearMap.id := by
    change (gramIntertwiner ρ τ hρ hτ f).toLinearMap = _
    rw [← hc]
    rfl
  have hn (x : V) : ‖f x‖^2 = c.re * ‖x‖^2 := by
    have hh := congrArg (fun T : V →ₗ[ℂ] V => inner ℂ x (T x)) hgram
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, LinearMap.smul_apply,
      LinearMap.id_apply, inner_smul_right, inner_self_eq_norm_sq_to_K] at hh
    change ‖f.toLinearMap x‖^2 = c.re * ‖x‖^2
    have he := congrArg Complex.re hh
    simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_zero] using he
  obtain ⟨x,hx⟩ := exists_ne (0 : V)
  have hfx : f x ≠ 0 := by intro h; exact hx (hf (h.trans (map_zero f).symm))
  have hcpos : 0 < c.re := by
    have hh := hn x
    have hp : 0 < ‖f x‖^2 := sq_pos_of_ne_zero ((norm_ne_zero_iff).mpr hfx)
    have hxnon : 0 ≤ ‖x‖^2 := sq_nonneg _
    nlinarith
  let a : ℂ := (Real.sqrt c.re)⁻¹
  let F : V →ₗ[ℂ] E := a • f.toLinearMap
  have ha : ‖a‖^2 * c.re = 1 := by
    simp only [a, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [inv_pow, Real.sq_sqrt hcpos.le, inv_mul_cancel₀ (ne_of_gt hcpos)]
  have hnorm (y : V) : ‖F y‖ = ‖y‖ := by
    change ‖a • f y‖=‖y‖
    rw [norm_smul]
    have hh : (‖a‖*‖f y‖)^2=‖y‖^2 := by rw [mul_pow, hn, ← mul_assoc, ha, one_mul]
    exact (sq_eq_sq₀ (mul_nonneg (norm_nonneg a) (norm_nonneg (f y))) (norm_nonneg y)).mp hh
  let I : V →ₗᵢ[ℂ] E := { F with norm_map' := hnorm }
  refine ⟨I,?_⟩
  intro g y
  change a • f (ρ g y)=τ g (a • f y)
  rw [Representation.IntertwiningMap.isIntertwining, map_smul]
end RowColumn

end
end

end OAI
