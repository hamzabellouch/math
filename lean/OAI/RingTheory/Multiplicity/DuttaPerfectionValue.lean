import Mathlib
import OAI.RingTheory.Multiplicity.DuttaFrobeniusShift

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology ENNReal
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (IsLocalRing.ResidueField D) p]

lemma perfection_complex_value (ell : AllModuleLength (PerfectClosure D p))
    (hlim : ∀ (M : ModuleCat.{u} D),IsFiniteLength D M →
      Tendsto (fun n : ℕ => ((p:ℝ≥0∞)^(n*dimension D))⁻¹*
        (Module.length D (FrobeniusModule D p n M)).toENNReal) atTop
        (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M))))
    (hparam : ∀ (z : Fin (dimension D) → D),
      (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D →
      ∀ a : ℕ,0<a → ell.value (ModuleCat.of (PerfectClosure D p)
        ((PerfectClosure D p) ⧸ (parameterIdeal D z a).map (PerfectClosure.of D p))) =
        (a:ℝ≥0∞)^dimension D*ENNReal.ofReal (Primary.multiplicity (Ideal.span (Set.range z))))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F) (n : ℕ) :
    (ell.value ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex _).obj
      (frobeniusComplex D p n F)).homology 0)).toReal =
        ((p:ℝ)^n)^dimension D*duttaMultiplicity D p F := by
  have H (G : CochainComplex (ModuleCat.{u} D) ℤ) (hG : IsFiniteHomologyComplex D G) :=
    dutta_limit_from_perfection D p G hG ell
      (normalized_perfection_module_finite D p ell hparam (G.homology 0) (hG.homology_finite_length 0))
      (hlim (G.homology 0) (hG.homology_finite_length 0))
  have hFval := duttaMultiplicity_eq_of_tendsto p F _ (H F hF)
  have hshift := duttaLimit_frobenius p F _ (H F hF) n
  rw [← hFval] at hshift
  exact tendsto_nhds_unique (H (frobeniusComplex D p n F) (frobenius_finiteHomology p F hF n)) hshift
end Lech.CharP

end

end OAI
