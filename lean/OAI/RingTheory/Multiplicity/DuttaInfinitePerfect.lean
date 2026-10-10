import Mathlib
import OAI.RingTheory.Multiplicity.DuttaEstimateLimit
import OAI.RingTheory.Multiplicity.DuttaMinimalEstimate

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]
  [Infinite (ResidueField D)]

 

theorem dutta_lower_bound_infinite_perfect (hd : 0 < dimension D)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsShortComplex D F) :
    multiplicity D ≤ duttaMultiplicity D p F := by
  obtain ⟨G,hG,hm,⟨e⟩⟩ := hF.exists_minimal
  rw [duttaMultiplicity_eq_of_homotopyEquiv p e]
  obtain ⟨A,c,_,H⟩ := dutta_minimal_estimate D p hd G hG.finiteHomology hm
  have hbound := dutta_estimate_limit p (dimension D) c (Fact.out : p.Prime).one_lt
    (multiplicity D) A (Module.finrank D (G.X 0))
    (∑ i∈Finset.range (dimension D+1),(Module.finrank D (G.X (-(i:ℤ))):ℝ))
    (duttaMultiplicity D p G) H
  have hpos : 0 < Module.finrank D (G.X 0) := by
    let := hG.term_free 0
    let := hG.term_finite 0
    apply (Module.finrank_pos_iff_of_free D (G.X 0)).mpr
    apply not_subsingleton_iff_nontrivial.mp
    intro hh
    exact hG.homology_zero_nonzero
      (ExactAt.of_isZero (ModuleCat.isZero_iff_subsingleton.mpr hh)).isZero_homology
  have hposR : (1:ℝ) ≤ Module.finrank D (G.X 0) := by exact_mod_cast hpos
  have hepos : 0 ≤ multiplicity D := by
    rw [← Primary.maximal_multiplicity_eq]
    exact Primary.multiplicity_nonneg _ (Ideal.IsPrime.radical inferInstance)
  exact le_trans (by nlinarith) hbound
end Lech.CharP

end

end OAI
