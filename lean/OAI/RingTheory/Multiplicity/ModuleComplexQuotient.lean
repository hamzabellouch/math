import Mathlib
import OAI.RingTheory.Multiplicity.IdealFilteredComplex

namespace OAI

noncomputable section
namespace Lech.ModuleComplexQuotient
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} R) c)
  (P : ∀ p,Submodule R (K.X p))
  (hP : ∀ p q,P p ≤ (P q).comap (K.d p q).hom)

 
def complex : HomologicalComplex (ModuleCat.{u} R) c where
  X p := ModuleCat.of R ((K.X p) ⧸ P p)
  d p q := ModuleCat.ofHom ((P p).mapQ (P q) (K.d p q).hom (hP p q))
  shape p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change Submodule.Quotient.mk ((K.d p q).hom x)=0
        rw [K.shape p q hpq]
        exact Submodule.Quotient.mk_zero _
  d_comp_d' p q r _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change Submodule.Quotient.mk ((K.d q r).hom ((K.d p q).hom x))=0
        have he := congrArg (fun f : K.X p ⟶ K.X r => f.hom x) (K.d_comp_d p q r)
        change (K.d q r).hom ((K.d p q).hom x)=0 at he
        rw [he]
        exact Submodule.Quotient.mk_zero _

def projection : K ⟶ complex K P hP where
  f p := ModuleCat.ofHom (P p).mkQ
  comm' _ _ _ := rfl

def inclusion : IdealFiltered.subcomplex K P hP ⟶ K where
  f p := ModuleCat.ofHom (P p).subtype
  comm' _ _ _ := rfl

lemma inclusion_projection : inclusion K P hP ≫ projection K P hP=0 := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Submodule.Quotient.mk_eq_zero (P p)).mpr x.property

def shortComplex : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c) :=
  ShortComplex.mk (inclusion K P hP) (projection K P hP) (inclusion_projection K P hP)

lemma shortComplex_exact : (shortComplex K P hP).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro p
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change Submodule.Quotient.mk x=0 at hx
    exact ⟨⟨x,(Submodule.Quotient.mk_eq_zero (P p)).mp hx⟩,rfl⟩
  · exact (ModuleCat.mono_iff_injective _).mpr (P p).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).mpr (P p).mkQ_surjective

variable {K} {P hP}
  {L : HomologicalComplex (ModuleCat.{u} R) c}
  {Q : ∀ p,Submodule R (L.X p)} {hQ : ∀ p q,Q p ≤ (Q q).comap (L.d p q).hom}
  (f : K ⟶ L) (hf : ∀ p,P p ≤ (Q p).comap (f.f p).hom)

def map : complex K P hP ⟶ complex L Q hQ where
  f p := ModuleCat.ofHom ((P p).mapQ (Q p) (f.f p).hom (hf p))
  comm' p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change Submodule.Quotient.mk ((L.d p q).hom ((f.f p).hom x))=
          Submodule.Quotient.mk ((f.f q).hom ((K.d p q).hom x))
        exact congrArg (fun g : K.X p ⟶ L.X q => Submodule.Quotient.mk (g.hom x)) (f.comm p q)

lemma projection_natural : f ≫ projection L Q hQ=projection K P hP ≫ map f hf := by
  apply Hom.ext
  funext p
  rfl
end Lech.ModuleComplexQuotient

end

end OAI
