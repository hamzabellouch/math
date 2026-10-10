import Mathlib
import OAI.RingTheory.Multiplicity.ZeroHomologyScalarExtension

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
lemma frobenius_weight_eq (p d n : ℕ) :
    (p:ℝ)^(-(n*d:ℤ)) = (((p:ℝ)^n)^d)⁻¹ := by
  rw [← Nat.cast_mul,zpow_neg,zpow_natCast,pow_mul]

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma duttaSequence_tendsto_of_homology_limits
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (L : ℝ)
    (hzero : Tendsto (fun n : ℕ => ((Module.length R ((frobeniusComplex R p n F).homology 0)).toNat : ℝ) /
      ((p:ℝ)^n)^(dimension R)) atTop (𝓝 L))
    (hneg : ∀ i : ℤ,i < 0 → Tendsto (fun n : ℕ =>
      ((Module.length R ((frobeniusComplex R p n F).homology i)).toNat : ℝ) /
        ((p:ℝ)^n)^(dimension R)) atTop (𝓝 0)) :
    Tendsto (duttaSequence R p F) atTop (𝓝 L) := by
  classical
  have hi (i : ℕ) : Tendsto (fun n : ℕ => (-1:ℝ)^i *
      (((Module.length R ((frobeniusComplex R p n F).homology (-(i:ℤ)))).toNat : ℝ) /
        ((p:ℝ)^n)^(dimension R))) atTop (𝓝 (if i=0 then L else 0)) := by
    by_cases h : i=0
    · subst i
      simpa using hzero
    · have hlt : -(i:ℤ) < 0 := by omega
      simpa only [h,ite_false,mul_zero] using (hneg (-(i:ℤ)) hlt).const_mul ((-1:ℝ)^i)
  have hsum := tendsto_finsetSum (Finset.range (dimension R+1)) (fun i _ => hi i)
  simp only [Finset.sum_ite_eq',Finset.mem_range,Nat.succ_pos,ite_true] at hsum
  apply hsum.congr
  intro n
  unfold duttaSequence shortEuler
  rw [frobenius_weight_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_eq_mul_inv]
  ring

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma duttaMultiplicity_eq_of_tendsto (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (L : ℝ)
    (hL : Tendsto (duttaSequence R p F) atTop (𝓝 L)) :
    duttaMultiplicity R p F = L := hL.limUnder_eq
end Lech

end

end OAI
