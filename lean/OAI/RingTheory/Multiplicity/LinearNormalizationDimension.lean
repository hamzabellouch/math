import Mathlib
import OAI.RingTheory.Multiplicity.GradedLinearNormalization
import OAI.RingTheory.Multiplicity.LechLengthLe

namespace OAI

noncomputable section
open DirectSum MvPolynomial
namespace Lech.LinearNormalization
universe u v
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

lemma degree_finrank_lower (G : ℕ → Submodule k A) [GradedAlgebra G]
    {s : ℕ} (z : Fin s → A) (hz : ∀ i,z i ∈ G 1)
    (hi : Function.Injective (aeval (R:=k) z)) (n : ℕ) [Module.Finite k (G n)] :
    s.multichoose n ≤ Module.finrank k (G n) := by
  let f : homogeneousSubmodule (Fin s) k n →ₗ[k] G n :=
    (aeval (R:=k) z).toLinearMap.domRestrict
      (homogeneousSubmodule (Fin s) k n) |>.codRestrict (G n)
        (fun p => Grading.aeval_mem G z hz p.property)
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply hi
    exact congrArg Subtype.val he
  have H := f.finrank_le_finrank_of_injective hf
  have he : Module.finrank k (homogeneousSubmodule (Fin s) k n) = s.multichoose n := by
    rw [(Grading.homogeneousEquiv k s n).finrank_eq,Module.finrank_pi,Grading.index_card]
  rwa [he] at H

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
local instance residueField : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _

lemma polynomial_rank_le_colength {s : ℕ}
    (z : Fin s → IdealGraded.Ring (IsLocalRing.maximalIdeal R))
    (hz : ∀ i,z i ∈ IdealGraded.grade (IsLocalRing.maximalIdeal R) 1)
    (hi : Function.Injective (aeval (R:=R ⧸ IsLocalRing.maximalIdeal R) z)) (N : ℕ) :
    ∑ n ∈ Finset.range N,s.multichoose n ≤ colength R N := by
  let m := IsLocalRing.maximalIdeal R
  have H : (∑ n ∈ Finset.range N,(s.multichoose n : ℕ∞)) ≤
      Module.length R (R ⧸ m^N) := by
    rw [IdealGraded.length_eq_sum]
    apply Finset.sum_le_sum
    intro n _
    rw [IdealGraded.length_piece_eq_finrank]
    have hdeg : s.multichoose n ≤ Module.finrank (R ⧸ m) (IdealGraded.grade m n) :=
      @degree_finrank_lower (R ⧸ m) (Ideal.Quotient.field m)
        (IdealGraded.Ring m) inferInstance (IdealGraded.gradedAlgebra m)
        (IdealGraded.grade m) (IdealGraded.gradeGradedAlgebra m)
        s z hz hi n (IdealGraded.gradeFinite m n)
    have hp : Module.finrank (R ⧸ m) (IdealGraded.Piece m n) =
        Module.finrank (R ⧸ m) (IdealGraded.grade m n) :=
      (IdealGraded.pieceEquiv m n).finrank_eq
    exact ENat.natCast_le_natCast.mpr (hdeg.trans_eq hp.symm)
  rw [← colength_cast R N,← Nat.cast_sum] at H
  exact_mod_cast H

lemma generator_number_le_dimension {s : ℕ}
    (z : Fin s → IdealGraded.Ring (IsLocalRing.maximalIdeal R))
    (hz : ∀ i,z i ∈ IdealGraded.grade (IsLocalRing.maximalIdeal R) 1)
    (hi : Function.Injective (aeval (R:=R ⧸ IsLocalRing.maximalIdeal R) z)) :
    s ≤ dimension R := by
  obtain ⟨C,hC⟩ := colength_polynomial_bound R
  by_contra hs
  have hsd : dimension R+1 ≤ s := by omega
  let N := s.factorial*C+1
  have hN : 0<N := by dsimp [N]; omega
  have hchoose : (N+s-1).choose s ≤ colength R N := by
    have H := polynomial_rank_le_colength z hz hi N
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [ht,Nat.sum_range_multichoose] at H
    simpa only [ht,Nat.add_right_comm t 1 s,Nat.add_sub_cancel] using H
  have hpow : N^s ≤ s.factorial*colength R N :=
    (Nat.pow_succ_le_ascFactorial N s).trans (by
      rw [Nat.ascFactorial_eq_factorial_mul_choose']
      exact Nat.mul_le_mul_left _ hchoose)
  have htotal : N^(dimension R+1) ≤ N^dimension R*(s.factorial*C) := by
    calc
      N^(dimension R+1) ≤ N^s := Nat.pow_le_pow_right hN hsd
      _ ≤ s.factorial*colength R N := hpow
      _ ≤ s.factorial*(N^dimension R*C) := Nat.mul_le_mul_left _ (hC N)
      _ = N^dimension R*(s.factorial*C) := by ac_rfl
  rw [pow_succ] at htotal
  have hbad : N ≤ s.factorial*C := Nat.le_of_mul_le_mul_left htotal (Nat.pow_pos hN)
  dsimp [N] at hbad
  omega
end Lech.LinearNormalization

end

end OAI
