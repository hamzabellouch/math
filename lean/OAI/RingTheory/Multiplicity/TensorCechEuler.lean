import Mathlib
import OAI.RingTheory.Multiplicity.CechProducts
import OAI.RingTheory.Multiplicity.ReesRootUnfiltered

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]

 
def positiveZ (D : Diagram R ι) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (positiveComplex D).extend ComplexShape.embeddingUpNat

lemma positiveZ_bounded (D : Diagram R ι) (q : ℤ)
    (hq : q < 0 ∨ (Fintype.card ι:ℤ) ≤ q) : IsZero ((positiveZ D).X q) := by
  by_cases hq0 : 0 ≤ q
  · have he : ComplexShape.embeddingUpNat.f q.toNat=q := Int.toNat_of_nonneg hq0
    exact (positiveComplex_bounded D q.toNat (by omega)).of_iso
      ((positiveComplex D).extendXIso ComplexShape.embeddingUpNat he)
  · apply (positiveComplex D).isZero_extend_X
    intro j hj
    change (j:ℤ)=q at hj
    omega

 
def tensorCech (F : CochainComplex (ModuleCat.{u} R) ℤ) (D : Diagram R ι) :=
  (TensorTotal.Right.functor F).obj (positiveZ D)

lemma tensorCech_bounded (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p)) (D : Diagram R ι)
    (q : ℤ) (hq : q < -(h:ℤ) ∨ (Fintype.card ι:ℤ) ≤ q) :
    IsZero ((tensorCech F D).X q) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply mapBifunctor.hom_ext
  intro p r hpr
  have hz : IsZero ((F.X p) ⊗ (positiveZ D).X r) := by
    by_cases hp : p < -(h:ℤ) ∨ 0<p
    · exact (tensorRight ((positiveZ D).X r)).map_isZero (hb p hp)
    · exact (tensorLeft (F.X p)).map_isZero
        (positiveZ_bounded D r (by change p+r=q at hpr; omega))
  exact hz.eq_of_src _ _

lemma tensorCech_homology_bounded (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p)) (D : Diagram R ι)
    (q : ℤ) (hq : q < -(h:ℤ) ∨ (Fintype.card ι:ℤ) ≤ q) :
    IsZero ((tensorCech F D).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (tensorCech_bounded F h hb D q hq)

variable {D E G : Diagram R ι} (φ : Map D E) (ψ : Map E G)
  (hzero : ∀ s,φ.app s ≫ ψ.app s=0)

 
def tensorShortComplex (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((positiveShortComplex φ ψ hzero).map
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R))).map (TensorTotal.Right.functor F)

lemma tensorShortComplex_shortExact (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ p,Module.Flat R (F.X p))
    (hs : ∀ s,(diagramShortComplex φ ψ hzero s).ShortExact) :
    (tensorShortComplex φ ψ hzero F).ShortExact :=
  TensorTotal.Right.shortExact F hflat _
    (extend_shortExact _ (positive_shortExact φ ψ hzero hs) _)

variable {I : Ideal R} (ell : TorsionLength I)

def tensorEuler (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ) (D : Diagram R ι) : ℝ :=
  (-1:ℝ)^h * finiteHomologyEuler ell (tensorCech F D) (-(h:ℤ)) (h+Fintype.card ι)

lemma tensorEuler_additive (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (hflat : ∀ p,Module.Flat R (F.X p))
    (hs : ∀ s,(diagramShortComplex φ ψ hzero s).ShortExact)
    (hD : ∀ q,ell.finiteClass ((tensorCech F D).homology q))
    (hG : ∀ q,ell.finiteClass ((tensorCech F G).homology q)) :
    tensorEuler ell F h E=tensorEuler ell F h D+tensorEuler ell F h G := by
  have hS := tensorShortComplex_shortExact φ ψ hzero F hflat hs
  have hE (q : ℤ) : ell.finiteClass ((tensorCech F E).homology q) :=
    ell.finiteClass.prop_X₂_of_exact (hS.homology_exact₂ q) (hD q) (hG q)
  have he := finiteHomologyEuler_additive ell _ hS (-(h:ℤ)) (h+Fintype.card ι)
    hD hE hG (tensorCech_homology_bounded F h hb G _ (by omega))
    (tensorCech_homology_bounded F h hb D _ (by omega))
  change finiteHomologyEuler ell (tensorCech F E) _ _ = _ at he
  unfold tensorEuler
  rw [he,mul_add]
  rfl

lemma tensorEuler_prod (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (hflat : ∀ p,Module.Flat R (F.X p))
    (D E : Diagram R ι)
    (hD : ∀ q,ell.finiteClass ((tensorCech F D).homology q))
    (hE : ∀ q,ell.finiteClass ((tensorCech F E).homology q)) :
    tensorEuler ell F h (prodDiagram D E)=tensorEuler ell F h D+tensorEuler ell F h E :=
  tensorEuler_additive (prodInl D E) (prodSnd D E) (prod_comp_zero D E)
    ell F h hb hflat (prod_shortExact D E) hD hE

lemma tensorEuler_iso (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    {D E : Diagram R ι} (e : positiveComplex D ≅ positiveComplex E)
    (hD : ∀ q,ell.finiteClass ((tensorCech F D).homology q)) :
    tensorEuler ell F h D=tensorEuler ell F h E := by
  apply congrArg ((-1:ℝ)^h * ·)
  exact finiteHomologyEuler_iso ell _ _
    ((TensorTotal.Right.functor F).mapIso
      ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso e)) (fun q => (hD q).1) _ _
end Lech.FiniteModuleCech

end

end OAI
