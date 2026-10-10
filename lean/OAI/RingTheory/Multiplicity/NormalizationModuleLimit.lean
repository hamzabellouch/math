import Mathlib
import OAI.RingTheory.Multiplicity.IntermediateTensorLength

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Filter
open scoped ENNReal Topology
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
  [FiniteDimensional K L] [CharP K p] [CharP L p]

local instance normalizationModuleLimitPowerSeriesIsDomain : IsDomain (MvPowerSeries (Fin h) k) :=
  NoZeroDivisors.to_isDomain _

include K L in
 

theorem exists_normalization_frobenius_module_limit
    (hf : Function.Injective (algebraMap (MvPowerSeries (Fin h) k) D))
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries (Fin h) k))
      (IsLocalRing.ResidueField D))) :
    ∃ r : ℕ, 0 < r ∧ ∀ (M : ModuleCat.{u} D), IsFiniteLength D M →
      Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞) * normalizedLength (Fin h) k p
          ((PerfectClosure D p) ⊗[D] M))) := by
  let A := MvPowerSeries (Fin h) k
  let B := order A D K L
  let E := separableClosure K L
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let : IsNoetherianRing B.toSubring := inferInstanceAs (IsNoetherianRing B)
  let : IsLocalRing B.toSubring := inferInstanceAs (IsLocalRing B)
  let : IsLocalHom B.toSubring.subtype := inferInstanceAs (IsLocalHom (algebraMap B D))
  let : CharP B p := B.val.toRingHom.charP Subtype.val_injective p
  let : CharP E p := (algebraMap E L).charP (algebraMap E L).injective p
  let : IsLocalHom (algebraMap A B) := ⟨fun x hx =>
    isUnit_of_map_unit (algebraMap A D) x (by
      simpa only [← IsScalarTower.algebraMap_apply A B D] using hx.map (algebraMap B D))⟩
  let : Module.Finite B D := Module.Finite.of_restrictScalars_finite A B D
  have hfb : Function.Injective (algebraMap A B) := by
    intro x y hxy
    exact hf (by simpa only [← IsScalarTower.algebraMap_apply A B D] using
      (congrArg (algebraMap B D) hxy))
  have hresBD : Function.Surjective (algebraMap (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField D)) := by
    intro x
    obtain ⟨a,ha⟩ := hres x
    exact ⟨algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a,
      (IsScalarTower.algebraMap_apply _ _ _ a).symm.trans ha⟩
  have hresAB : Function.Surjective (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)) := by
    intro b
    obtain ⟨a,ha⟩ := hres (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D) b)
    refine ⟨a,(algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)).injective ?_⟩
    exact (IsScalarTower.algebraMap_apply _ _ _ a).symm.trans ha
  have hdim : Lech.dimension B = h := by
    have hd := Lech.ringKrullDim_eq_of_integral_injective (algebraMap A B)
      (Algebra.IsIntegral.isIntegral : (algebraMap A B).IsIntegral) hfb
    rw [Lech.PowerSeries.fin_dimension k h] at hd
    have hh := Lech.dimension_cast B
    rw [hd] at hh
    exact_mod_cast hh
  have hdimSub : Lech.dimension B.toSubring = h := hdim
  obtain ⟨e,he⟩ := uniform_power A D K L p
  obtain ⟨r,hr,hlim⟩ := Lech.FrobeniusIntermediate.exists_positive_module_rank_transfer p B.toSubring
  refine ⟨r,hr,fun M hM => ?_⟩
  let N := (ModuleCat.extendScalars (Lech.FrobeniusIntermediate.powerMap p B.toSubring e he)).obj M
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  obtain ⟨I,hI,hIM⟩ := Lech.finiteLength_primary_annihilator hM
  have hN : IsFiniteLength B N :=
    Lech.finiteLength_extendScalars_of_primary (Lech.FrobeniusIntermediate.powerMap p B.toSubring e he)
      M I hIM (Lech.FrobeniusIntermediate.map_radical_primary p B.toSubring e he I hI)
  have ht := frobenius_module_length_tendsto h k B p K E hfb hresAB N hN
  have hout := hlim e he hresBD M hM
    (normalizedLength (Fin h) k p ((PerfectClosure B p) ⊗[B] N))
    (by
      rw [hdimSub]
      apply ht.congr
      intro n
      rfl)
  have heq := Lech.FrobeniusIntermediate.normalizedLength_intermediate_tensor
    (Fin h) k D p B e he M
  simp only [Fintype.card_fin] at heq
  rw [heq]
  simpa only [hdim,hdimSub,mul_left_comm] using hout
end Lech.SeparableOrder

end

end OAI
