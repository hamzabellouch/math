import Mathlib
import OAI.RingTheory.Multiplicity.FiniteGradedQuotient

namespace OAI

noncomputable section
open DirectSum
namespace Lech.LinearNormalization
universe u v
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

lemma homogeneous_span_coefficients (G : ℕ → Submodule k A) [GradedAlgebra G]
    {s n : ℕ} (z : Fin s → A) (hz : ∀ i,z i ∈ G 1)
    {a : A} (ha : a ∈ G (n+1)) (hi : a ∈ Ideal.span (Set.range z)) :
    ∃ c : Fin s → A,(∀ i,c i ∈ G n) ∧ ∑ i,c i*z i = a := by
  obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hi
  let π : A →ₗ[k] A := (G (n+1)).subtype.comp
    ((DFinsupp.lapply (n+1)).comp (decomposeLinearEquiv G).toLinearMap)
  have hπ : π a = a := decompose_of_mem_same G ha
  have hsum := congrArg π hc
  rw [map_sum,hπ] at hsum
  refine ⟨fun i => (decompose G (c i) n : A),fun i => (decompose G (c i) n).property,?_⟩
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro i _
  exact (coe_decompose_mul_add_of_right_mem G (hz i)).symm
end Lech.LinearNormalization

namespace Lech.IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def initialForm (n : ℕ) : ↥(I^n) →ₗ[R] Ring I := (quotientR I).comp (monomial I n)

lemma initialForm_mem (n : ℕ) (a : ↥(I^n)) : initialForm I n a ∈ grade I n :=
  ⟨monomial I n a,⟨a,rfl⟩,rfl⟩

lemma exists_initialForm {n : ℕ} {a : Ring I} (ha : a ∈ grade I n) :
    ∃ b : ↥(I^n),initialForm I n b = a := by
  obtain ⟨_,⟨b,rfl⟩,rfl⟩ := ha
  exact ⟨b,rfl⟩

lemma initialForm_mul {n m : ℕ} (a : ↥(I^n)) (b : ↥(I^m)) :
    initialForm I (n+m) ⟨(a:R)*(b:R),by rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2⟩ =
      initialForm I n a * initialForm I m b := by
  change Ideal.Quotient.mk (shifted I) _ =
    Ideal.Quotient.mk (shifted I) (monomial I n a) *
    Ideal.Quotient.mk (shifted I) (monomial I m b)
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  exact (Polynomial.monomial_mul_monomial _ _ _ _).symm

lemma initialForm_eq_zero_iff (n : ℕ) (a : ↥(I^n)) :
    initialForm I n a = 0 ↔ (a:R) ∈ I^(n+1) :=
  Ideal.Quotient.eq_zero_iff_mem.trans (monomial_mem_shifted_iff I n a)

lemma initialForm_eq_iff (n : ℕ) (a b : ↥(I^n)) :
    initialForm I n a = initialForm I n b ↔ (a:R)-(b:R) ∈ I^(n+1) := by
  rw [← sub_eq_zero,← map_sub,initialForm_eq_zero_iff]
  rfl

lemma power_le_reduction_sup {s n : ℕ} (z : Fin s → ↥I)
    (h : ∀ a ∈ grade I (n+1),a ∈ Ideal.span (Set.range
      (fun i => initialForm I 1 ⟨(z i:R),by simp⟩)))
    [I.IsMaximal] :
    I^(n+1) ≤ (Ideal.span (Set.range (fun i => (z i:R)))) * I^n ⊔ I^(n+2) := by
  let k := R ⧸ I
  let : Field k := Ideal.Quotient.field I
  let Z : Fin s → Ring I := fun i => initialForm I 1 ⟨(z i:R),by simp⟩
  have hZ (i) : Z i ∈ grade I 1 := initialForm_mem I 1 _
  intro a ha
  let a' : ↥(I^(n+1)) := ⟨a,ha⟩
  obtain ⟨c,hc,hce⟩ := LinearNormalization.homogeneous_span_coefficients
    (grade I) Z hZ (initialForm_mem I (n+1) a') (h _ (initialForm_mem I (n+1) a'))
  choose b hb using fun i => exists_initialForm I (hc i)
  let t : Fin s → ↥(I^(n+1)) := fun i => ⟨(b i:R)*(z i:R),by
    rw [pow_add]
    exact Ideal.mul_mem_mul (b i).2 (by simp)⟩
  have he : initialForm I (n+1) (∑ i,t i) = initialForm I (n+1) a' := by
    rw [map_sum]
    convert hce using 1
    apply Finset.sum_congr rfl
    intro i _
    exact (initialForm_mul I (b i) ⟨(z i:R),by simp⟩).trans
      (congrArg (·*Z i) (hb i))
  have hdiff : a - ∑ i,(b i:R)*(z i:R) ∈ I^(n+2) := by
    have hh := (initialForm_eq_iff I (n+1) a' (∑ i,t i)).mp he.symm
    simpa [a',t,Submodule.coe_sum,Nat.add_assoc] using hh
  have ht : ∑ i,(b i:R)*(z i:R) ∈
      (Ideal.span (Set.range (fun i => (z i:R)))) * I^n := by
    apply Ideal.sum_mem
    intro i _
    rw [mul_comm (b i:R) (z i:R)]
    exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_range_self i)) (b i).2
  rw [← sub_add_cancel a (∑ i,(b i:R)*(z i:R))]
  exact Ideal.add_mem _
    ((show I^(n+2) ≤ _ ⊔ I^(n+2) from le_sup_right) hdiff)
    ((show (Ideal.span (Set.range (fun i => (z i:R)))) * I^n ≤
      (Ideal.span (Set.range (fun i => (z i:R)))) * I^n ⊔ I^(n+2) from le_sup_left) ht)

lemma reduction_of_high_grades [IsLocalRing R] [IsNoetherianRing R]
    {s c : ℕ} (z : Fin s → ↥(IsLocalRing.maximalIdeal R))
    (h : ∀ a ∈ grade (IsLocalRing.maximalIdeal R) (c+1),a ∈ Ideal.span (Set.range
      (fun i => initialForm (IsLocalRing.maximalIdeal R) 1
        ⟨(z i:R),by simp⟩))) :
    (IsLocalRing.maximalIdeal R)^(c+1) =
      Ideal.span (Set.range (fun i => (z i:R))) * (IsLocalRing.maximalIdeal R)^c := by
  let m := IsLocalRing.maximalIdeal R
  let J := Ideal.span (Set.range (fun i => (z i:R)))
  have hJ : J ≤ m := Ideal.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact (z i).2)
  apply le_antisymm
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian (m^(c+1))) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    have H := power_le_reduction_sup m z h
    convert H using 1
    change J*m^c ⊔ m*m^(c+1) = J*m^c ⊔ m^(c+2)
    rw [← pow_succ']
  · exact (Ideal.mul_mono hJ le_rfl).trans_eq (pow_succ' m c).symm
end Lech.IdealGraded

end

end OAI
