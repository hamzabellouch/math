import OAI.RepresentationTheory.SpinAngle.Core

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder








noncomputable section
open scoped BigOperators
namespace SpinAngle.Analytic

variable {A : Type*} [contextInstance35_21 : CStarAlgebra A] [contextInstance35_38 : PartialOrder A] [contextInstance35_55 : StarOrderedRing A]
  [contextInstance36_2 : NonnegSpectrumClass ℝ A]

lemma norm_mul_projection_sq
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonnegSpectrumClass ℝ A] (a p : A) (hp : IsStarProjection p) :
    ‖a * p‖ ^ 2 = ‖a * p * star a‖ := by
  rw [sq, ← CStarRing.norm_self_mul_star, star_mul, hp.isSelfAdjoint.star_eq]
  congr 1
  calc
    a * p * (p * star a) = a * (p * p) * star a := by simp only [mul_assoc]
    _ = a * p * star a := by rw [hp.isIdempotentElem.eq]

lemma norm_projection_mul_sq
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonnegSpectrumClass ℝ A] (p a : A) (hp : IsStarProjection p) :
    ‖p * a‖ ^ 2 = ‖star a * p * a‖ := by
  rw [sq, ← CStarRing.norm_star_mul_self, star_mul, hp.isSelfAdjoint.star_eq]
  congr 1
  calc
    star a * p * (p * a) = star a * (p * p) * a := by simp only [mul_assoc]
    _ = star a * p * a := by rw [hp.isIdempotentElem.eq]



lemma norm_mul_projection_sq_le_sum {ι : Type*} [Fintype ι]
    (a p : A) (hp : IsStarProjection p) (w : ι → ℝ) (r : ι → A)
    (hw : ∀ i, 0 ≤ w i) (hdom : p ≤ ∑ i, w i • (r i * star (r i))) :
    ‖a * p‖ ^ 2 ≤ ∑ i, w i * ‖a * r i‖ ^ 2 := by
  rw [norm_mul_projection_sq a p hp]
  have hcomp := star_right_conjugate_le_conjugate hdom a
  have hpos : 0 ≤ a * p * star a :=
    star_right_conjugate_nonneg hp.nonneg a
  calc
    ‖a * p * star a‖ ≤ ‖a * (∑ i, w i • (r i * star (r i))) * star a‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hcomp hpos
    _ = ‖∑ i, w i • ((a * r i) * star (a * r i))‖ := by
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
        star_mul, mul_assoc]
    _ ≤ ∑ i, ‖w i • ((a * r i) * star (a * r i))‖ := norm_sum_le _ _
    _ = ∑ i, w i * ‖a * r i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_of_nonneg (hw i), CStarRing.norm_self_mul_star, sq]

lemma norm_projection_mul_sq_le_sum {ι : Type*} [Fintype ι]
    (p a : A) (hp : IsStarProjection p) (w : ι → ℝ) (r : ι → A)
    (hw : ∀ i, 0 ≤ w i) (hdom : p ≤ ∑ i, w i • (star (r i) * r i)) :
    ‖p * a‖ ^ 2 ≤ ∑ i, w i * ‖r i * a‖ ^ 2 := by
  have h := norm_mul_projection_sq_le_sum (star a) p hp w (fun i => star (r i)) hw
    (by simpa using hdom)
  have hab : ‖star a * p‖ = ‖p * a‖ := by
    calc
      ‖star a * p‖ = ‖star (p * a)‖ := by rw [star_mul, hp.isSelfAdjoint.star_eq]
      _ = ‖p * a‖ := norm_star _
  have hr (i : ι) : ‖star a * star (r i)‖ = ‖r i * a‖ := by
    rw [← star_mul, norm_star]
  simpa only [hab, hr] using h




lemma support_inverse_factorization
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonnegSpectrumClass ℝ A] (r v t q k p : A)
    (hvt : v * t = q) (hrq : r * q = r)
    (htk : Commute t k) (htp : Commute t p) :
    r * k * p = (r * v * k) * (p * t) := by
  calc
    r * k * p = (r * q) * k * p := by rw [hrq]
    _ = (r * (v * t)) * k * p := by rw [hvt]
    _ = (r * v * k) * (p * t) := by
      simp only [mul_assoc]
      rw [← mul_assoc t k, htk.eq, mul_assoc k, htp.eq]


lemma norm_support_inverse_le (r v t q k p : A)
    (hvt : v * t = q) (hrq : r * q = r)
    (htk : Commute t k) (htp : Commute t p) :
    ‖r * k * p‖ ^ 2 ≤ ‖r * v * k‖ ^ 2 * ‖p * t‖ ^ 2 := by
  rw [support_inverse_factorization r v t q k p hvt hrq htk htp]
  calc
    ‖(r * v * k) * (p * t)‖ ^ 2 ≤ (‖r * v * k‖ * ‖p * t‖) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_mul_le _ _) 2
    _ = _ := mul_pow _ _ _



lemma norm_projection_sqrt_sq (p t : A) (hp : IsStarProjection p)
    (ht : IsSelfAdjoint t) (htp : Commute t p) :
    ‖p * t‖ ^ 2 = ‖(t * t) * p‖ := by
  rw [norm_projection_mul_sq p t hp, ht.star_eq]
  congr 1
  calc
    t * p * t = t * (p * t) := mul_assoc _ _ _
    _ = t * (t * p) := by rw [htp.eq]
    _ = t * t * p := (mul_assoc _ _ _).symm

lemma norm_three_projections_sq_le_one
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonnegSpectrumClass ℝ A] (h k p : A)
    (hh : IsStarProjection h) (hk : IsStarProjection k) (hp : IsStarProjection p) :
    ‖h * k * p‖ ^ 2 ≤ 1 := by
  have hn : ‖h * k * p‖ ≤ 1 := calc
    _ ≤ (‖h‖ * ‖k‖) * ‖p‖ := (norm_mul_le _ _).trans <|
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * 1) * 1 := mul_le_mul
      (mul_le_mul hh.norm_le hk.norm_le (norm_nonneg _) zero_le_one)
      hp.norm_le (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num
  calc
    _ ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = 1 := by norm_num







theorem three_projection_angle_of_density_mixtures
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (h k p : A) (hh : IsStarProjection h) (hk : IsStarProjection k)
    (hp : IsStarProjection p)
    (w : ι → ℝ) (z : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hz : ∀ j, 0 ≤ z j)
    (r v t q : ι → A) (s : κ → A)
    (hH : h ≤ ∑ i, w i • (star (r i) * r i))
    (hK : k ≤ ∑ j, z j • (s j * star (s j)))
    (hvt : ∀ i, v i * t i = q i) (hrq : ∀ i, r i * q i = r i)
    (htk : ∀ i, Commute (t i) k) (htp : ∀ i, Commute (t i) p)
    (g phi : ℝ) (hg : 0 ≤ g) (hphi : 0 ≤ phi)
    (hglobal : ∀ i, ‖p * t i‖ ^ 2 ≤ g)
    (hcell : ∀ i j, ‖r i * v i * s j‖ ^ 2 ≤ phi) :
    ‖h * k * p‖ ^ 2 ≤ min 1 ((∑ i, w i) * (∑ j, z j) * g * phi) := by
  apply le_min (norm_three_projections_sq_le_one h k p hh hk hp)
  have hs (i : ι) : ‖r i * v i * k‖ ^ 2 ≤ (∑ j, z j) * phi := by
    calc
      _ ≤ ∑ j, z j * ‖r i * v i * s j‖ ^ 2 :=
        norm_mul_projection_sq_le_sum (r i * v i) k hk z s hz hK
      _ ≤ ∑ j, z j * phi := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hcell i j) (hz j)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hb (i : ι) : ‖r i * k * p‖ ^ 2 ≤ ((∑ j, z j) * phi) * g := calc
    _ ≤ ‖r i * v i * k‖ ^ 2 * ‖p * t i‖ ^ 2 :=
      norm_support_inverse_le (r i) (v i) (t i) (q i) k p
        (hvt i) (hrq i) (htk i) (htp i)
    _ ≤ ((∑ j, z j) * phi) * g := by
      by_cases hzero : ‖p * t i‖ ^ 2 = 0
      · rw [hzero, mul_zero]
        exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => hz j) hphi) hg
      · exact mul_le_mul (hs i) (hglobal i) (sq_nonneg _)
          (mul_nonneg (Finset.sum_nonneg fun j _ => hz j) hphi)
  calc
    ‖h * k * p‖ ^ 2 = ‖h * (k * p)‖ ^ 2 := by rw [mul_assoc]
    _ ≤ ∑ i, w i * ‖r i * (k * p)‖ ^ 2 :=
      norm_projection_mul_sq_le_sum h (k * p) hh w r hw hH
    _ = ∑ i, w i * ‖r i * k * p‖ ^ 2 := by simp only [mul_assoc]
    _ ≤ ∑ i, w i * (((∑ j, z j) * phi) * g) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i)
    _ = (∑ i, w i) * (∑ j, z j) * g * phi := by rw [← Finset.sum_mul]; ring

end SpinAngle.Analytic

end
end

end OAI
