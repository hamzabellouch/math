import Mathlib
import OAI.RingTheory.Multiplicity.IdealQuotientFunctor
import OAI.RingTheory.Multiplicity.ReesRootCech

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]
variable (D : Diagram R ι) (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)

def coefficients : Diagram R ι where
  obj s := F.obj (D.obj s)
  res h := F.map (D.res h)
  res_self s := by rw [D.res_self,F.map_id]
  res_comp h h' := by rw [←F.map_comp,D.res_comp]

def Map.coefficients {E : Diagram R ι} (φ : Map D E) :
    Map (coefficients D F) (coefficients E F) where
  app s := F.map (φ.app s)
  naturality h := by
    change F.map (D.res h) ≫ F.map (φ.app _) = F.map (φ.app _) ≫ F.map (E.res h)
    rw [←F.map_comp,←F.map_comp,φ.naturality]

variable (I : Ideal R)
abbrev reduction := coefficients D (TensorIdeal.quotientFunctor I)

lemma quotientPiEquiv_d (q : ℕ) (x : cochains D q) :
    TensorIdeal.quotientPiEquiv I (fun s : Set.powersetCard ι (q+1) => D.obj s.val)
      (Submodule.Quotient.mk (d D q x)) =
    d (reduction D I) q
      (TensorIdeal.quotientPiEquiv I (fun s : Set.powersetCard ι q => D.obj s.val)
        (Submodule.Quotient.mk x)) := by
  rw [TensorIdeal.quotientPiEquiv_mk,TensorIdeal.quotientPiEquiv_mk]
  funext s
  change (Submodule.mkQ (I • (⊤ : Submodule R (D.obj s.val))))
    (∑ j : Fin (q+1), (-1:ℤ)^j.val • (D.res (AlternatingCech.delete_subset s j)).hom
      (x (AlternatingCech.delete s j))) = _
  rw [map_sum]
  change (∑ j : Fin (q+1), (Submodule.mkQ (I • (⊤ : Submodule R (D.obj s.val))))
    ((-1:ℤ)^j.val • (D.res (AlternatingCech.delete_subset s j)).hom
      (x (AlternatingCech.delete s j)))) = _
  simp only [map_zsmul]
  rfl

 

def reductionComplexIso :
    ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℕ)).obj (complex D) ≅
      complex (reduction D I) :=
  Hom.isoOfComponents (fun q => (TensorIdeal.quotientPiEquiv I
    (fun s : Set.powersetCard ι q => D.obj s.val)).toModuleIso) (by
      intro q r h
      obtain rfl : q+1=r := h
      rw [complex_d]
      change _ ≫ ModuleCat.ofHom (d (reduction D I) q) =
        (TensorIdeal.quotientFunctor I).map ((complex D).d q (q+1)) ≫ _
      rw [complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x => exact (quotientPiEquiv_d D I q x).symm)

 
def reductionPositiveIso :
    ((TensorIdeal.quotientFunctor I).mapHomologicalComplex (.up ℕ)).obj (positiveComplex D) ≅
      positiveComplex (reduction D I) :=
  Hom.isoOfComponents (fun q => (TensorIdeal.quotientPiEquiv I
    (fun s : Set.powersetCard ι (q+1) => D.obj s.val)).toModuleIso) (by
      intro q r h
      obtain rfl : q+1=r := h
      rw [positiveComplex_d]
      change _ ≫ ModuleCat.ofHom (d (reduction D I) (q+1)) =
        (TensorIdeal.quotientFunctor I).map ((positiveComplex D).d q (q+1)) ≫ _
      rw [positiveComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x => exact (quotientPiEquiv_d D I (q+1) x).symm)

 
omit [LinearOrder ι] in
lemma reduction_cochains_torsion (q : ℕ) :
    powerTorsion I (ModuleCat.of R (cochains (reduction D I) q)) :=
  (powerTorsion I).prop_of_iso
    (TensorIdeal.quotientPiEquiv I (fun s : Set.powersetCard ι q => D.obj s.val)).toModuleIso
    (TensorIdeal.quotient_torsion I (cochains D q))

lemma reduction_homology_torsion (q : ℕ) :
    powerTorsion I ((complex (reduction D I)).homology q) :=
  powerTorsion_epi I ((complex (reduction D I)).homologyπ q)
    (powerTorsion_mono I ((complex (reduction D I)).iCycles q)
      (reduction_cochains_torsion D I q))

lemma reduction_positiveHomology_torsion (q : ℕ) :
    powerTorsion I ((positiveComplex (reduction D I)).homology q) :=
  powerTorsion_epi I ((positiveComplex (reduction D I)).homologyπ q)
    (powerTorsion_mono I ((positiveComplex (reduction D I)).iCycles q)
      (reduction_cochains_torsion D I (q+1)))

namespace Map
variable {D} {E : Diagram R ι} (φ : Map D E)
variable (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]

omit [LinearOrder ι] in
lemma cochains_isoModSerre (hφ : ∀ s,P.isoModSerre (φ.app s)) (q : ℕ) :
    P.isoModSerre (ModuleCat.ofHom (φ.cochains q)) :=
  piLinear_isoModSerre (fun s : Set.powersetCard ι q => (φ.app s.val).hom) P
    (fun s => hφ s.val)

lemma homology_isoModSerre (hφ : ∀ s,P.isoModSerre (φ.app s)) (q : ℕ) :
    P.isoModSerre (HomologicalComplex.homologyMap φ.complex q) :=
  homology_isoModSerre_of_termwise P φ.complex (φ.cochains_isoModSerre P hφ) q

lemma positiveHomology_isoModSerre (hφ : ∀ s,P.isoModSerre (φ.app s)) (q : ℕ) :
    P.isoModSerre (HomologicalComplex.homologyMap φ.positiveComplex q) :=
  homology_isoModSerre_of_termwise P φ.positiveComplex
    (fun q => φ.cochains_isoModSerre P hφ (q+1)) q
end Map
end Lech.FiniteModuleCech

end

end OAI
