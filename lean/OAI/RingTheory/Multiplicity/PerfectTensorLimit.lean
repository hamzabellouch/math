import Mathlib
import OAI.RingTheory.Multiplicity.FiniteLengthPrimary
import OAI.RingTheory.Multiplicity.FrobeniusTensorStage
import OAI.RingTheory.Multiplicity.LechLengthLe

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal nonZeroDivisors Topology
open Filter
namespace Lech.PerfectDomainStages
open Lech.RootTower
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [CharP K p] [CharP L p]
local instance perfectTensorLimitPowerSeriesIsDomain : IsDomain (MvPowerSeries (Fin h) k) :=
  NoZeroDivisors.to_isDomain _

include K L in
 

theorem stage_tensor_length_tendsto
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (M : ModuleCat.{u} D) (hM : IsFiniteLength D M) :
    letI : ∀ n, Algebra D (stage (MvPowerSeries (Fin h) k) D p n) :=
      fun n => (originalToStage (MvPowerSeries (Fin h) k) D p n).toAlgebra
    Tendsto (fun n => normalizedLength (Fin h) k p
      ((stage (MvPowerSeries (Fin h) k) D p n) ⊗[D] M)) atTop
      (𝓝 (normalizedLength (Fin h) k p ((PerfectClosure D p) ⊗[D] M))) := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let : ∀ n, Algebra D (stage A D p n) := fun n => (originalToStage A D p n).toAlgebra
  let : ∀ n, IsScalarTower D (stage A D p n) (PerfectClosure D p) := fun n =>
    IsScalarTower.of_algebraMap_eq fun d => rfl
  obtain ⟨hno,hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  let := hno
  let := hart
  obtain ⟨b,f,hfgen⟩ := Module.Finite.exists_fin' D M
  obtain ⟨H,hH,hHM⟩ := Lech.finiteLength_primary_annihilator hM
  have hflat := perfectClosure_flat (Fin h) k p
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_flat_frobenius A p
    (fun n => iterateFrobenius_flat (σ := Fin h) (R := k) p n)
  have hi (n : ℕ) := tensorMap_injective A D p L K hflat n
  have hdim : Lech.dimension D = h := by
    have hd := Lech.ringKrullDim_eq_of_integral_injective (algebraMap A D)
      (Algebra.IsIntegral.isIntegral : (algebraMap A D).IsIntegral) hf
    rw [Lech.PowerSeries.fin_dimension k h] at hd
    have hh := Lech.dimension_cast D
    rw [hd] at hh
    exact_mod_cast hh
  obtain ⟨g,hg,hgc⟩ := exists_conductor A D p L K
  have hgn : algebraMap A D g ∈ D⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr
    (fun hz => hg (hf (by simpa using hz)))
  have herr := Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal H hH hgn p
  rw [hdim] at herr
  have hfiniteQuot (n : ℕ) :
      normalizedLength (Fin h) k p ((stage A D p n) ⧸ H.map (originalToStage A D p n)) ≠ ⊤ := by
    rw [normalizedLength_actual_stage_quotient (Fin h) k D p hres H n (hi n)]
    obtain ⟨c,hc⟩ := Lech.FrobeniusGrowth.linear_power_containment H hH
    have hl := Lech.length_quotient_le D (hc (p^n) (Nat.one_le_pow n p (Fact.out : p.Prime).pos))
    have hlfin := ne_top_of_le_ne_top (Lech.quotient_length_ne_top D (c*p^n)) hl
    rw [Lech.FrobeniusGrowth.powerIdeal_eq_map H p n] at hlfin
    apply ENNReal.mul_ne_top
    · apply ENNReal.inv_ne_top.mpr
      exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    · simpa using hlfin
  have hfinite (n : ℕ) : normalizedLength (Fin h) k p ((stage A D p n) ⊗[D] M) ≠ ⊤ := by
    have hb : (b : ℝ≥0∞) ≠ ⊤ := by simp
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hb (hfiniteQuot n))
      (Lech.TensorGenerator.length_le f (stage A D p n) (regularTower (Fin h) k p)
        hfgen H hHM)
  apply Lech.TensorConductor.length_tendsto (D := D) (stage A D p) M
    (regularTower (Fin h) k p) (stage_mono A D p) (stage_exhaustive A D p)
    (fun n => rootMap A p n g) hgc hfinite
  have ht : Tendsto (fun n => (b : ℝ≥0∞) * normalizedLength (Fin h) k p
      ((stage A D p n) ⧸ (H.map (originalToStage A D p n) ⊔
        Ideal.span {algebraMap P (stage A D p n) (rootMap A p n g)}))) atTop (𝓝 0) := by
    have hb := ENNReal.Tendsto.const_mul herr (a := (b : ℝ≥0∞)) (Or.inr (by simp))
    simp only [mul_zero] at hb
    apply hb.congr
    intro n
    congr 1
    symm
    simpa only [Fintype.card_fin] using
      normalizedLength_scalar_stage_quotient (Fin h) k D p hres H n (hi n) g
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro n
    exact zero_le
  · intro n
    exact Lech.TensorGenerator.scalar_cokernel_le f (stage A D p n)
      (regularTower (Fin h) k p) hfgen H hHM (rootMap A p n g)

include K L in
 

theorem frobenius_module_length_tendsto
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (M : ModuleCat.{u} D) (hM : IsFiniteLength D M) :
    Tendsto (fun n => ((p : ℝ≥0∞)^(n*h))⁻¹ *
      (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal) atTop
      (𝓝 (normalizedLength (Fin h) k p ((PerfectClosure D p) ⊗[D] M))) := by
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  let A := MvPowerSeries (Fin h) k
  have hflat := perfectClosure_flat (Fin h) k p
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_flat_frobenius A p
    (fun n => iterateFrobenius_flat (σ := Fin h) (R := k) p n)
  have hi (n : ℕ) := tensorMap_injective A D p L K hflat n
  have ht := stage_tensor_length_tendsto h k D p K L hf hres M hM
  apply ht.congr
  intro n
  simpa only [Fintype.card_fin] using
    normalizedLength_original_stage_tensor (Fin h) k D p hres M n (hi n)

include K L in
 

theorem perfection_finite_length
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D)))
    (M : ModuleCat.{u} D) (hM : IsFiniteLength D M) (v : ℝ≥0∞)
    (hv : Tendsto (fun n => ((p : ℝ≥0∞)^(n*h))⁻¹ *
      (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal) atTop (𝓝 v)) :
    normalizedLength (Fin h) k p ((PerfectClosure D p) ⊗[D] M) = v :=
  tendsto_nhds_unique (frobenius_module_length_tendsto h k D p K L hf hres M hM) hv

end Lech.PerfectDomainStages

end

end OAI
