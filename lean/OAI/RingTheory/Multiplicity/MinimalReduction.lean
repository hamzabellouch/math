import Mathlib
import OAI.RingTheory.Multiplicity.AssociatedGradedReduction
import OAI.RingTheory.Multiplicity.LinearNormalizationDimension

namespace OAI

noncomputable section
open IsLocalRing MvPolynomial
namespace Lech.MinimalReduction
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma associatedGraded_nontrivial [IsNoetherianRing R] [IsLocalRing R] :
    Nontrivial (IdealGraded.Ring (maximalIdeal R)) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  have h1 : (1 : reesAlgebra (maximalIdeal R)) ∈ IdealGraded.shifted (maximalIdeal R) := by
    rw [h]; trivial
  have hm := h1 0
  change (1 : Polynomial R).coeff 0 ∈ (maximalIdeal R)^(0+1) at hm
  simp at hm

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma pad_generators [IsNoetherianRing R] [IsLocalRing R]
    {s d : ℕ} (hs : s≤d) (z : Fin s → ↥(maximalIdeal R)) :
    ∃ w : Fin d → ↥(maximalIdeal R),
      Ideal.span (Set.range (fun i => (w i:R))) =
        Ideal.span (Set.range (fun i => (z i:R))) := by
  classical
  let w : Fin d → ↥(maximalIdeal R) := fun i => if hi : i.val<s then z ⟨i.val,hi⟩ else 0
  refine ⟨w,le_antisymm ?_ ?_⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : i.val<s
    · simpa only [w,dite_eq_left hi] using
        (Ideal.subset_span (Set.mem_range_self (⟨i.val,hi⟩ : Fin s)) :
          (z ⟨i.val,hi⟩:R) ∈ Ideal.span (Set.range (fun j => (z j:R))))
    · simp only [w,dite_eq_right hi,ZeroMemClass.coe_zero]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    let j : Fin d := ⟨i.val,i.isLt.trans_le hs⟩
    have he : w j = z i := by simp [w,j,i.isLt]
    have H := Ideal.subset_span (s:=Set.range (fun i => (w i:R))) (Set.mem_range_self j)
    simpa only [he] using H

 

theorem exists_reduction [Infinite (ResidueField R)] :
    ∃ z : Fin (dimension R) → R, (∀ i,z i ∈ maximalIdeal R) ∧
      ∃ c : ℕ,(maximalIdeal R)^(c+1) =
        Ideal.span (Set.range z) * (maximalIdeal R)^c := by
  let m := maximalIdeal R
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let : Infinite (R ⧸ m) := inferInstanceAs (Infinite (ResidueField R))
  let : Nontrivial (IdealGraded.Ring m) := associatedGraded_nontrivial
  obtain ⟨N,x,hx,hxG⟩ := IdealGraded.exists_generators m
  obtain ⟨s,_,Z,hZspan,hZi,hxI⟩ :=
    @LinearNormalization.exists_linear_normalization (R ⧸ m) (Ideal.Quotient.field m)
      (IdealGraded.Ring m) inferInstance (IdealGraded.gradedAlgebra m) inferInstance
      inferInstance (IdealGraded.grade m) (IdealGraded.gradeGradedAlgebra m) N x hxG
  have hZG (i) : Z i ∈ IdealGraded.grade m 1 := by
    apply (show Submodule.span (R ⧸ m) (Set.range x) ≤ IdealGraded.grade m 1 from
      Submodule.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hxG j))
    exact hZspan i
  have hs : s ≤ dimension R := LinearNormalization.generator_number_le_dimension Z hZG hZi
  obtain ⟨c,hc⟩ := @LinearNormalization.high_grades_in_span (R ⧸ m) (Ideal.Quotient.field m)
    (IdealGraded.Ring m) inferInstance (IdealGraded.gradedAlgebra m) N s
    (IdealGraded.grade m) (IdealGraded.gradeGradedAlgebra m) x Z hx hZG hxI
  choose z hz using fun i => IdealGraded.exists_initialForm m (hZG i)
  let zr : Fin s → ↥m := fun i => ⟨(z i:R),by simpa using (z i).2⟩
  have hr : m^(c+1) = Ideal.span (Set.range (fun i => (zr i:R))) * m^c := by
    apply IdealGraded.reduction_of_high_grades zr
    intro a ha
    have he : (fun i => IdealGraded.initialForm m 1
        ⟨(zr i:R),by simp⟩) = Z := by
      funext i
      exact hz i
    rw [he]
    exact hc (c+1) (Nat.le_succ c) a ha
  obtain ⟨w,hw⟩ := pad_generators hs zr
  refine ⟨fun i => (w i:R),fun i => (w i).2,c,?_⟩
  rw [hw]
  exact hr

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma reduction_powers [IsNoetherianRing R] [IsLocalRing R]
    {I J : Ideal R} {c : ℕ} (h : I^(c+1)=J*I^c) (n : ℕ) :
    I^(n+c)=J^n*I^c := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      I^(n+1+c) = I^n*I^(c+1) := by rw [← pow_add]; congr 1; omega
      _ = I^n*(J*I^c) := by rw [h]
      _ = J*(I^n*I^c) := by ac_rfl
      _ = J*I^(n+c) := by rw [pow_add]
      _ = J*(J^n*I^c) := by rw [ih]
      _ = J^(n+1)*I^c := by simp only [pow_succ',mul_assoc]

lemma reduction_power_le {I J : Ideal R} {c : ℕ} (h : I^(c+1)=J*I^c) (n : ℕ) :
    I^(n+c) ≤ J^n := by
  rw [reduction_powers h n]
  exact Ideal.mul_le_left

lemma reduction_primary {J : Ideal R} {c : ℕ}
    (hJ : J ≤ maximalIdeal R) (h : (maximalIdeal R)^(c+1)=J*(maximalIdeal R)^c) :
    J.radical = maximalIdeal R := by
  apply le_antisymm
  · exact (Ideal.radical_mono hJ).trans_eq (Ideal.IsPrime.radical (inferInstance : (maximalIdeal R).IsPrime))
  · have he : ((maximalIdeal R)^(c+1)).radical = maximalIdeal R := by
      rw [Ideal.radical_pow _ (by omega),Ideal.IsPrime.radical (inferInstance : (maximalIdeal R).IsPrime)]
    rw [← he]
    apply Ideal.radical_mono
    simpa only [Nat.add_comm 1 c,pow_one] using reduction_power_le h 1
end Lech.MinimalReduction

end

end OAI
