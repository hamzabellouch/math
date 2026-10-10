import Mathlib
import OAI.RingTheory.Multiplicity.RobertsSeparable

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
lemma frobenius_scalar_quotient_homology_tendsto_zero
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (g : R) (hg : g ≠ 0) (i : ℤ) :
    Tendsto (fun n : ℕ => ((Module.length R (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj
      (frobeniusComplex R p n F)).homology i)).toNat : ℝ) / ((p:ℝ)^n)^(dimension R)) atTop (𝓝 0) := by
  by_cases hu : IsUnit g
  · have hz (n : ℕ) : Module.length R (((complexQuotient (Ideal.span {g}) (.up ℤ)).obj
        (frobeniusComplex R p n F)).homology i) = 0 := by
      let Q := (complexQuotient (Ideal.span {g}) (.up ℤ)).obj (frobeniusComplex R p n F)
      have he : g • 𝟙 Q = 0 := complexQuotient_annihilated (Ideal.span {g}) g
        (Ideal.subset_span (Set.mem_singleton g)) (frobeniusComplex R p n F)
      have hQ : IsZero Q := (IsZero.iff_id_eq_zero Q).mpr (hu.smul_eq_zero.mp he)
      have : Subsingleton (Q.homology i) := ModuleCat.isZero_iff_subsingleton.mp
        ((homologyFunctor (ModuleCat R) (.up ℤ) i).map_isZero hQ)
      exact Module.length_eq_zero (R:=R) (M:=Q.homology i)
    simpa only [hz,ENat.toNat_zero,Nat.cast_zero,zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · obtain ⟨zs,hd,hzs,hprim⟩ := exists_small_quotient_parameters g
      (mem_nonZeroDivisors_of_ne_zero hg) hu
    exact frobenius_quotient_homology_tendsto_zero p F hF (Ideal.span {g}) zs hzs hprim hd i

lemma tendsto_frobenius_shift_zero (p d e : ℕ) (hp : 0 < p) (a : ℕ → ℝ)
    (ha : Tendsto (fun n => a n / ((p:ℝ)^n)^d) atTop (𝓝 0)) :
    Tendsto (fun n => a (e+n) / ((p:ℝ)^n)^d) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => e+n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat e
  have ht := ha.comp hn
  have hc := ht.const_mul (((p:ℝ)^e)^d)
  simp only [mul_zero] at hc
  apply hc.congr
  intro n
  dsimp only [Function.comp_apply]
  rw [pow_add,mul_pow]
  have h0 : ((p:ℝ)^e)^d ≠ 0 := by positivity
  rw [← mul_div_assoc]
  exact mul_div_mul_left _ _ h0

lemma tendsto_frobenius_unshift_zero (p d e : ℕ) (_hp : 0 < p) (a : ℕ → ℝ)
    (ha : Tendsto (fun n => a (e+n) / ((p:ℝ)^n)^d) atTop (𝓝 0)) :
    Tendsto (fun n => a n / ((p:ℝ)^n)^d) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat e).mp
  have ht := ha.div_const (((p:ℝ)^e)^d)
  simp only [zero_div] at ht
  apply ht.congr
  intro n
  rw [Nat.add_comm n e,pow_add,mul_pow]
  ring
end Lech

end

end OAI
