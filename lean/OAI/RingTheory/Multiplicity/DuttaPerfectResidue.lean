import Mathlib
import OAI.RingTheory.Multiplicity.DuttaEulerLimit
import OAI.RingTheory.Multiplicity.PerfectionModuleLengthFinite
import OAI.RingTheory.Multiplicity.RobertsPerfectResidue

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology ENNReal
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (IsLocalRing.ResidueField D) p]

omit [IsDomain D] [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  [PerfectRing (IsLocalRing.ResidueField D) p] in
lemma real_frobeniusModule_limit (M : ModuleCat.{u} D) (hM : IsFiniteLength D M)
    (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*dimension D))⁻¹ *
      (Module.length D (FrobeniusModule D p n M)).toENNReal) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ((Module.length D (FrobeniusModule D p n M)).toNat : ℝ) /
      ((p:ℝ)^n)^dimension D) atTop (𝓝 L.toReal) := by
  apply ((ENNReal.tendsto_toReal hL).comp hlim).congr
  intro n
  have hn : Module.length D (FrobeniusModule D p n M) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (frobeniusModule_finiteLength D p M hM n)
  simp only [Function.comp_apply,ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_natCast]
  rw [← ENat.natCast_toNat hn,ENat.toENNReal_coe,ENNReal.toReal_natCast]
  rw [pow_mul,div_eq_mul_inv,mul_comm]
  simp only [ENat.toNat_natCast]

lemma dutta_limit_from_perfection (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hF : IsFiniteHomologyComplex D F) (ell : AllModuleLength (PerfectClosure D p))
    (hfinite : ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj
      (F.homology 0)) ≠ ⊤)
    (hlim : Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*dimension D))⁻¹ *
      (Module.length D (FrobeniusModule D p n (F.homology 0))).toENNReal) atTop
      (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj (F.homology 0))))) :
    Tendsto (duttaSequence D p F) atTop
      (𝓝 ((ell.value ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex
        (.up ℤ)).obj F).homology 0)).toReal)) := by
  have hz := hF.d_zero_one_eq_zero
  rw [ell.value_eq_of_linearEquiv (scalarExtensionZeroHomologyIso (PerfectClosure.of D p) F hz).toLinearEquiv]
  apply duttaSequence_tendsto_of_homology_limits p F
  · apply (real_frobeniusModule_limit D p (F.homology 0) (hF.homology_finite_length 0)
      _ hfinite hlim).congr
    intro n
    have he := (scalarExtensionZeroHomologyIso (iterateFrobenius D p n) F hz).toLinearEquiv.length_eq
    change ((Module.length D (FrobeniusModule D p n (F.homology 0))).toNat : ℝ) / _ = _
    change Module.length D ((frobeniusComplex D p n F).homology 0) =
      Module.length D (FrobeniusModule D p n (F.homology 0)) at he
    rw [he]
  · exact frobenius_homology_tendsto_zero D p F hF

lemma exists_dutta_limit (hh : 0 < dimension D)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F) :
    Tendsto (duttaSequence D p F) atTop (𝓝 (duttaMultiplicity D p F)) := by
  obtain ⟨ell,hlim,hcyc,hparam,hK,hpos⟩ := exists_length_with_module_limit D p hh
  have hfinite := normalized_perfection_module_finite D p ell hparam (F.homology 0)
    (hF.homology_finite_length 0)
  have hl := dutta_limit_from_perfection D p F hF ell hfinite
    (hlim (F.homology 0) (hF.homology_finite_length 0))
  rw [duttaMultiplicity_eq_of_tendsto p F _ hl]
  exact hl
end Lech.CharP

end

end OAI
