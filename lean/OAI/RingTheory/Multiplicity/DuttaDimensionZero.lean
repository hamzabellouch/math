import Mathlib
import OAI.RingTheory.Multiplicity.ArtinianSupport
import OAI.RingTheory.Multiplicity.DuttaFrobeniusShift

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology
namespace Lech
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]

lemma isField_of_dimension_zero (hd : dimension D=0) : IsField D := by
  have hk : Ring.KrullDimLE 0 D := Ring.krullDimLE_iff.mpr (by
    rw [← dimension_cast D,hd])
  exact Ring.KrullDimLE.isField_of_isDomain

 

lemma duttaSequence_dimension_zero (p : ℕ) [Fact p.Prime] [CharP D p]
    (hd : dimension D=0) (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hF : IsFiniteHomologyComplex D F) (n : ℕ) :
    duttaSequence D p F n = (Module.finrank D (F.X 0) : ℝ) := by
  let := (isField_of_dimension_zero hd).toField
  let G := frobeniusComplex D p n F
  have hG := frobenius_finiteHomology p F hF n
  have he : G.homology 0 ≅ G.X 0 :=
    G.homologyIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
      ((ShortComplex.HomologyData.ofZeros (G.sc' (-1) 0 1)
        ((hG.bounded (-1) (by left; rw [hd]; norm_num)).eq_of_src _ _)
        (hG.d_zero_one_eq_zero)).left.homologyIso)
  have := hG.term_finite 0
  have := hF.term_free 0
  have := hF.term_finite 0
  unfold duttaSequence shortEuler
  simp only [hd,mul_zero,neg_zero,zpow_zero,one_mul,zero_add,Finset.range_one,
    Finset.sum_singleton,pow_zero,Nat.cast_zero]
  change ((Module.length D (G.homology 0)).toNat : ℝ)=_
  rw [he.toLinearEquiv.length_eq,Module.length_eq_finrank,ENat.toNat_natCast]
  change ((Module.finrank D ((ModuleCat.extendScalars (iterateFrobenius D p n)).obj (F.X 0))):ℝ)=_
  rw [finrank_extendScalars]

theorem dutta_dimension_zero (p : ℕ) [Fact p.Prime] [CharP D p]
    (hd : dimension D=0) (F : CochainComplex (ModuleCat.{u} D) ℤ)
    (hF : IsShortComplex D F) :
    Tendsto (duttaSequence D p F) atTop (𝓝 (duttaMultiplicity D p F)) ∧
    multiplicity D ≤ duttaMultiplicity D p F := by
  have hl : Tendsto (duttaSequence D p F) atTop (𝓝 (Module.finrank D (F.X 0):ℝ)) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (Module.finrank D (F.X 0):ℝ)) atTop _) using 1
    funext n
    exact duttaSequence_dimension_zero p hd F hF.finiteHomology n
  have he : duttaMultiplicity D p F = (Module.finrank D (F.X 0):ℝ) := hl.limUnder_eq
  rw [he]
  refine ⟨hl,?_⟩
  let := (isField_of_dimension_zero hd).toField
  rw [multiplicity_eq_length_of_artinian D,Module.length_eq_finrank]
  simp only [Module.finrank_self,Nat.cast_one]
  have hp : 0 < Module.finrank D (F.X 0) := by
    let := hF.term_free 0
    let := hF.term_finite 0
    apply (Module.finrank_pos_iff_of_free D (F.X 0)).mpr
    apply not_subsingleton_iff_nontrivial.mp
    intro hh
    exact hF.homology_zero_nonzero
      (ExactAt.of_isZero (ModuleCat.isZero_iff_subsingleton.mpr hh)).isZero_homology
  exact_mod_cast hp
end Lech

end

end OAI
