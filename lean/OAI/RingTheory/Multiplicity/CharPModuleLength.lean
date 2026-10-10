import Mathlib
import OAI.RingTheory.Multiplicity.NormalizationModuleLimit
import OAI.RingTheory.Multiplicity.QuotientExtension

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace Lech.CharP
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul IsLocalRing Filter
open scoped ENNReal Topology nonZeroDivisors
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

theorem exists_length_with_module_limit (hh : 0 < Lech.dimension D) :
    ∃ ell : Lech.AllModuleLength (PerfectClosure D p),
      (∀ (M : ModuleCat.{u} D), IsFiniteLength D M →
        Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension D))⁻¹ *
          (Module.length D (Lech.FrobeniusModule D p n M)).toENNReal)
          atTop (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M)))) ∧
      (∀ (H : Ideal D), H.radical = maximalIdeal D →
        Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension D))⁻¹ *
          (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
          atTop (𝓝 (ell.value (ModuleCat.of (PerfectClosure D p)
            ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))))) ∧
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
        ∀ a : ℕ, 0 < a →
          ell.value (ModuleCat.of (PerfectClosure D p) ((PerfectClosure D p) ⧸
            (parameterIdeal D z a).map (PerfectClosure.of D p))) =
              (a : ℝ≥0∞)^(Lech.dimension D) *
                ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z)))) ∧
      (∀ (ys : List D), ys.length = Lech.dimension D →
        (entryIdeal ys).radical = maximalIdeal D → ∀ i : ℤ, i < 0 →
          ell.value ((unit (ys.map (PerfectClosure.of D p))).homology i) = 0) ∧
      (∀ (z : Fin (Lech.dimension D) → D),
        (Ideal.span (Set.range z)).radical = maximalIdeal D →
          0 < Lech.Primary.multiplicity (Ideal.span (Set.range z))) := by
  obtain ⟨h,ψ,hψ,hfin,hloc,hres,hd⟩ :=
    Lech.Normalization.exists_finite_powerSeries_normalization D p
  have hdim : Lech.dimension D = h := by
    have hd' := Lech.dimension_cast D
    rw [hd] at hd'
    exact_mod_cast hd'
  let k := ResidueField D
  let : CharP k p := CharP.of_ringHom_of_ne_zero (residue D) p
    (Nat.Prime.ne_zero Fact.out)
  let A := MvPowerSeries (Fin h) k
  let C := PerfectClosure D p
  let P := PerfectClosure A p
  let : IsDomain A := NoZeroDivisors.to_isDomain _
  let : Algebra A D := ψ.toAlgebra
  let : Module.Finite A D := hfin
  let : IsLocalHom (algebraMap A D) := hloc
  have hf : Function.Injective (algebraMap A D) := hψ
  have hres' : Function.Surjective (algebraMap (ResidueField A) (ResidueField D)) := by
    intro b
    obtain ⟨a,ha⟩ := hres b
    refine ⟨residue A a,?_⟩
    rw [ResidueField.algebraMap_residue]
    exact ha
  let : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hf
  let K := FractionRing A
  let L := FractionRing D
  let : Algebra K L := FractionRing.liftAlgebra A L
  let : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  let : FiniteDimensional K L := Module.Finite.of_isLocalization A D A⁰
  obtain ⟨r,hr,hlimmod⟩ :=
    Lech.SeparableOrder.exists_normalization_frobenius_module_limit h k D p K L hf hres'
  have hlim (H : Ideal D) (hH : H.radical = maximalIdeal D) :
      Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞) * normalizedLength (Fin h) k p
          ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))) := by
    have ht := hlimmod (ModuleCat.of D (D ⧸ H)) (Lech.finiteLength_primary_quotient H hH)
    have heq := (regularTower (Fin h) k p).length_eq_of_equiv
      ((ModuleCat.restrictScalars (algebraMap P C)).mapIso
        (Lech.quotientExtensionEquiv (PerfectClosure.of D p) H).toModuleIso).toLinearEquiv
    change normalizedLength (Fin h) k p ((PerfectClosure D p) ⊗[D] (D ⧸ H)) =
      normalizedLength (Fin h) k p ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)) at heq
    rw [heq] at ht
    apply ht.congr
    intro n
    congr 1
    exact congrArg ENat.toENNReal (Lech.quotientExtensionEquiv (iterateFrobenius D p n) H).length_eq
  let ell := (regularTower (Fin h) k p).allModuleLength (algebraMap P C) r
    (by exact_mod_cast (Nat.ne_of_gt hr))
  let φ := Lech.CoefficientField.localSection D p
  have hφ : Function.Surjective ((residue D).comp φ) :=
    fun a => ⟨a,Lech.CoefficientField.localSection_rightInverse D p a⟩
  refine ⟨ell,?_,?_,?_,?_,?_⟩
  · intro M hM
    rw [hdim]
    exact hlimmod M hM
  · intro H hH
    rw [hdim]
    exact hlim H hH
  · intro z hz a ha
    have hprim : (parameterIdeal D z a).radical = maximalIdeal D :=
      (Lech.Normalization.radical_span_powers z a (Nat.ne_of_gt ha)).trans hz
    have ht := hlim (parameterIdeal D z a) hprim
    have hp := Lech.Normalization.parameter_frobenius_multiplicity_enn
      (Lech.dimension D) hh rfl φ hφ z hz a ha p
    have hp' : Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*h))⁻¹ *
        (Module.length D (D ⧸ (parameterIdeal D z a).map (iterateFrobenius D p n))).toENNReal)
        atTop (𝓝 ((a : ℝ≥0∞)^(Lech.dimension D) *
          ENNReal.ofReal (Lech.Primary.multiplicity (Ideal.span (Set.range z))))) := by
      convert hp using 1
      ext n
      apply congrArg (fun b : ℝ≥0∞ => b *
        (Module.length D (D ⧸ (parameterIdeal D z a).map (iterateFrobenius D p n))).toENNReal)
      rw [hdim]
    exact tendsto_nhds_unique ht hp'
  · intro ys hlen hys i hi
    have hz := Lech.SeparableOrder.normalizedLength_parameter_koszul
      h k D p K L ys (hlen.trans hdim) hys i hi
    change (r : ℝ≥0∞) * _ = 0
    change (regularTower (Fin h) k p).length _ = 0 at hz
    rw [hz,mul_zero]
  · intro z hz
    exact Lech.Normalization.parameter_multiplicity_pos
      (Lech.dimension D) hh rfl φ hφ z hz
end Lech.CharP

end

end OAI
