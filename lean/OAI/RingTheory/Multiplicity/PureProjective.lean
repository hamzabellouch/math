import Mathlib

namespace OAI

noncomputable section
namespace Lech.PureProjective
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : CochainComplex C ℤ) (d : ℤ) [Projective (K.homology d)]

def sectionCycles : K.homology d ⟶ K.cycles d :=
  Projective.factorThru (𝟙 (K.homology d)) (K.homologyπ d)

lemma sectionCycles_π : sectionCycles K d ≫ K.homologyπ d = 𝟙 _ :=
  Projective.factorThru_comp _ _

def inclusion : (single C (.up ℤ) d).obj (K.homology d) ⟶ K :=
  mkHomFromSingle (sectionCycles K d ≫ K.iCycles d)
    (by intro k _; simp only [Category.assoc, iCycles_d, comp_zero])

lemma cycles_inclusion : cyclesMap (inclusion K d) d =
    (singleObjCyclesSelfIso (.up ℤ) d (K.homology d)).hom ≫ sectionCycles K d := by
  rw [←cancel_mono (K.iCycles d), cyclesMap_i]
  simp only [inclusion, mkHomFromSingle_f, Category.assoc, singleObjCyclesSelfIso_hom]

lemma homology_inclusion : homologyMap (inclusion K d) d =
    (singleObjHomologySelfIso (.up ℤ) d (K.homology d)).hom := by
  rw [←cancel_epi (((single C (.up ℤ) d).obj (K.homology d)).homologyπ d),
    homologyπ_naturality, cycles_inclusion, Category.assoc, sectionCycles_π,
    Category.comp_id, homologyπ_singleObjHomologySelfIso_hom]

lemma inclusion_quasiIso (hpure : ∀ j, j≠d → IsZero (K.homology j)) :
    QuasiIso (inclusion K d) := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hj : j=d
  · subst j
    rw [homology_inclusion]
    infer_instance
  · exact (isZero_single_obj_homology (.up ℤ) d (K.homology d) j hj).isIso
      (hpure j hj) _

 

def homotopyEquiv (N : ℤ) [K.IsStrictlyLE N] [∀ j, Projective (K.X j)]
    (hpure : ∀ j, j≠d → IsZero (K.homology j)) :
    HomotopyEquiv ((single C (.up ℤ) d).obj (K.homology d)) K := by
  let S : CochainComplex C ℤ := (single C (.up ℤ) d).obj (K.homology d)
  have : S.IsStrictlyLE d := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact isZero_single_obj_X (.up ℤ) d (K.homology d) j (by omega)
  letI := CochainComplex.isKProjective_of_projective S d
  letI := CochainComplex.isKProjective_of_projective K N
  exact Classical.choose ((CochainComplex.IsKProjective.quasiIso_iff (inclusion K d)).mp
    (inclusion_quasiIso K d hpure))
end Lech.PureProjective

end

end OAI
