import Mathlib
import OAI.RingTheory.Multiplicity.BicomplexEuler
import OAI.RingTheory.Multiplicity.IdealFilteredQuotient

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)

 
def quotientAt : TotalGhost.Bic (R:=R) :=
  flip (((IdealFiltered.quotientFunctor I F h s hd).mapHomologicalComplex (.up ℤ)).obj (cechZ I z hz m))

def ambientInclusion : enlargedAt I z hz F h s hd m ⟶ unfilteredAt I z hz F m where
  f p := { f q := (IdealFiltered.ambientInclusion I F h s hd ((cechZ I z hz m).X q)).f p
           comm' _ _ _ := rfl }
  comm' _ _ _ := by apply Hom.ext; funext q; rfl

def quotientProjection : unfilteredAt I z hz F m ⟶ quotientAt I z hz F h s hd m where
  f p := { f q := ModuleCat.ofHom (IdealFiltered.term I F h s ((cechZ I z hz m).X q) p).mkQ
           comm' _ _ _ := rfl }
  comm' _ _ _ := by apply Hom.ext; funext q; rfl

lemma ambient_quotient_zero : ambientInclusion I z hz F h s hd m ≫ quotientProjection I z hz F h s hd m=0 := by
  apply Hom.ext
  funext p
  apply Hom.ext
  funext q
  exact congrArg (fun f => f.f p) (ModuleComplexQuotient.inclusion_projection
    (IdealFiltered.tensorComplex F ((cechZ I z hz m).X q))
    (IdealFiltered.term I F h s ((cechZ I z hz m).X q))
    (IdealFiltered.term_d I F h s hd ((cechZ I z hz m).X q)))

 
def quotientShortComplex : ShortComplex (TotalGhost.Bic (R:=R)) :=
  ShortComplex.mk (ambientInclusion I z hz F h s hd m) (quotientProjection I z hz F h s hd m)
    (ambient_quotient_zero I z hz F h s hd m)

lemma quotientShortComplex_exact : (quotientShortComplex I z hz F h s hd m).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro p
  apply shortExact_of_degreewise_shortExact
  intro q
  have hs := ModuleComplexQuotient.shortComplex_exact
    (IdealFiltered.tensorComplex F ((cechZ I z hz m).X q))
    (IdealFiltered.term I F h s ((cechZ I z hz m).X q))
    (IdealFiltered.term_d I F h s hd ((cechZ I z hz m).X q))
  have := hs.mono_f
  have := hs.epi_g
  exact hs.map (HomologicalComplex.eval _ _ p)

 
def quotientAtRowIso (p : ℤ) :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).obj
      (((TensorIdeal.quotientFunctor (I^(IdealFiltered.order h s p))).mapHomologicalComplex (.up ℤ)).obj
        (cechZ I z hz m)) ≅ (quotientAt I z hz F h s hd m).X p :=
  IdealFiltered.quotientRowIso I F h s hd (cechZ I z hz m) p

lemma quotientAt_isZero (p : ℤ) (hp : IsZero (F.X p)) :
    IsZero ((quotientAt I z hz F h s hd m).X p) := by
  apply FiniteComplex.isZero_of_X
  intro q
  let Q := (cechZ I z hz m).X q
  exact (TensorIdeal.quotientFunctor (I^(IdealFiltered.order h s p))).map_isZero
    ((tensorRight Q).map_isZero hp)

lemma quotientAt_row_bounded (p q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) :
    IsZero (((quotientAt I z hz F h s hd m).X p).X q) := by
  have hzK : IsZero ((cechZ I z hz m).X q) :=
    FiniteModuleCech.positiveZ_bounded (cechDiagram I z hz m) q (by simpa using hq)
  exact (TensorIdeal.quotientFunctor (I^(IdealFiltered.order h s p))).map_isZero
    ((tensorLeft (F.X p)).map_isZero hzK)
end Lech.ReesRoot

end

end OAI
