import Mathlib
import OAI.RingTheory.Multiplicity.CechCartierZRange
import OAI.RingTheory.Multiplicity.ComplexReduction
import OAI.RingTheory.Multiplicity.ExceptionalRootCohomology
import OAI.RingTheory.Multiplicity.IdealFilteredLayers
import OAI.RingTheory.Multiplicity.ReesRootRows

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)

 
def layerAt : TotalGhost.Bic (R:=R) :=
  (((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj
    (enlargedAt I z hz F h s hd m)

def layerAtProjection : enlargedAt I z hz F h s hd m ⟶ layerAt I z hz F h s hd m :=
  (TensorIdeal.bicomplexQuotientNat I (.up ℤ) (.up ℤ)).app (enlargedAt I z hz F h s hd m)

lemma layerAtProjection_f (p q : ℤ) :
    ((layerAtProjection I z hz F h s hd m).f p).f q =
      (TensorIdeal.quotientNat I).app (((enlargedAt I z hz F h s hd m).X p).X q) :=
  TensorIdeal.bicomplexQuotientNat_f I (.up ℤ) (.up ℤ) _ p q

variable (hgen : Ideal.span (Set.range z)=I)
include hgen in
lemma enlarged_first_range (p q : ℤ) :
    (((enlargedMap I z hz F h s hd (cechInclusionZ I z hz m 1)).f p).f q).hom.range =
      I • (⊤ : Submodule R (((enlargedAt I z hz F h s hd m).X p).X q)) := by
  exact IdealFiltered.rowMap_range I F h s hd p ((cechInclusionZ I z hz m 1).f q)
    (by simpa only [pow_one] using cechInclusionZ_range I z hz m hgen 1 q)

lemma enlarged_first_injective (p q : ℤ) [Module.Flat R (F.X p)] :
    Function.Injective (((enlargedMap I z hz F h s hd (cechInclusionZ I z hz m 1)).f p).f q).hom :=
  IdealFiltered.rowMap_injective I F h s hd p _ (cechInclusionZ_injective I z hz m 1 q)

include hgen in
lemma layerAt_zero :
    enlargedMap I z hz F h s hd (cechInclusionZ I z hz m 1) ≫
      layerAtProjection I z hz F h s hd m=0 := by
  apply Hom.ext
  funext p
  apply Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f,HomologicalComplex.zero_f,layerAtProjection_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Submodule.Quotient.mk
    ((((enlargedMap I z hz F h s hd (cechInclusionZ I z hz m 1)).f p).f q).hom x)=0
  rw [Submodule.Quotient.mk_eq_zero,←enlarged_first_range I z hz F h s hd m hgen p q]
  exact LinearMap.mem_range_self _ _

 
def enlargedLayerShortComplex : ShortComplex (TotalGhost.Bic (R:=R)) :=
  ShortComplex.mk (enlargedMap I z hz F h s hd (cechInclusionZ I z hz m 1))
    (layerAtProjection I z hz F h s hd m) (layerAt_zero I z hz F h s hd m hgen)

lemma enlargedLayerShortComplex_exact (hflat : ∀ p,Module.Flat R (F.X p)) :
    (enlargedLayerShortComplex I z hz F h s hd m hgen).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro p
  apply shortExact_of_degreewise_shortExact
  intro q
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    change (((layerAtProjection I z hz F h s hd m).f p).f q).hom y=0 at hy
    rw [layerAtProjection_f] at hy
    change Submodule.Quotient.mk y=0 at hy
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hy
    rw [←enlarged_first_range I z hz F h s hd m hgen p q] at hm
    exact hm
  · apply (ModuleCat.mono_iff_injective _).mpr
    let := hflat p
    exact enlarged_first_injective I z hz F h s hd m p q
  · apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (((layerAtProjection I z hz F h s hd m).f p).f q).hom
    rw [layerAtProjection_f]
    exact Submodule.mkQ_surjective _

 
def exceptionalCechZIso :
    ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℤ)).obj (cechZ I z hz m) ≅
      (FiniteModuleCech.positiveComplex (exceptionalDiagram I z hz m)).extend
        ComplexShape.embeddingUpNat :=
  ComplexExtension.mapExtendIso (TensorIdeal.quotientFunctor I) (cech I z hz m) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso
      (FiniteModuleCech.reductionPositiveIso (cechDiagram I z hz m) I)

 

def layerAtRowIso (p : ℤ) [Module.Flat R (F.X p)] :
    (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).obj
      ((FiniteModuleCech.positiveComplex
        (exceptionalDiagram I z hz (raise m (IdealFiltered.order h s p)))).extend
          ComplexShape.embeddingUpNat) ≅ (layerAt I z hz F h s hd m).X p :=
  (((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).mapHomologicalComplex (.up ℤ)).mapIso
      (exceptionalCechZIso I z hz (raise m (IdealFiltered.order h s p))).symm ≪≫
    (NatIso.mapHomologicalComplex (TensorIdeal.tensorReductionIso I (F.X p)) (.up ℤ)).app
      (cechZ I z hz (raise m (IdealFiltered.order h s p))) ≪≫
    ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℤ)).mapIso
      (enlargedRowIso I z hz F h s hd m hgen p)
end Lech.ReesRoot

end

end OAI
