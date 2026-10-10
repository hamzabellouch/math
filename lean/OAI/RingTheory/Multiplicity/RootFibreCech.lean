import Mathlib
import OAI.RingTheory.Multiplicity.CechReduction
import OAI.RingTheory.Multiplicity.ExceptionalFibreRestriction
import OAI.RingTheory.Multiplicity.RootSectionDiagram

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance reesRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance reesModule (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance reesBaseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance reesPModule (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
private local instance reesScalarComm (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _
private local instance sectionGroup (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
private local instance sectionModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule
private local instance indexFinite (s : Finset (Fin (n+1))) : Fintype (PLift s.Nonempty) := Fintype.ofFinite _

private local instance projectiveSectionModule (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (m : Fin n → ℤ) : Module R (ProjectiveRoot.Sections R n s hs m) :=
  (ProjectiveRoot.Sections R n s hs m).module'
private local instance sourceFibreModule (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (m : Fin n → ℤ) : Module R (RootFibreSections I s hs m) :=
  Submodule.Quotient.module _

variable (m : Fin n → ℤ)
def unitCech (s : Finset (Fin (n+1))) : ProjectiveRoot.cechObj R n m s ⟶ cechObj I z hz m s :=
  ModuleCat.ofHom (LinearMap.pi (fun hs : PLift s.Nonempty =>
    (TensorIdeal.unitMap (A:=ProjectiveRoot.Ring R n s) (B:=Ring I z hz s)
      (ProjectiveRoot.Sections R n s hs.down m)).comp (LinearMap.proj hs)))

lemma unitCech_natural {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    ProjectiveRoot.cechRes R n m hst ≫ unitCech I z hz m t =
      unitCech I z hz m s ≫ cechRes I z hz m hst := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext ht
  by_cases hs : s.Nonempty
  · change (1 ⊗ₜ[ProjectiveRoot.Ring R n t] ((ProjectiveRoot.cechRes R n m hst).hom x ht)) =
      (cechRes I z hz m hst).hom ((unitCech I z hz m s).hom x) ht
    rw [ProjectiveRoot.cechRes_apply R n m hst hs ht.down,
      cechRes_apply I z hz m hst hs ht.down]
    change _ = sectionsRestriction I z hz hs ht.down m hst
      (1 ⊗ₜ[ProjectiveRoot.Ring R n s] x ⟨hs⟩)
    rw [sectionsRestriction_tmul,map_one]
    rfl
  · change (1 ⊗ₜ[ProjectiveRoot.Ring R n t] (if hs : s.Nonempty then _ else 0)) =
      if hs : s.Nonempty then _ else 0
    simp only [dite_eq_right hs,TensorProduct.tmul_zero]

def unitCechMap : FiniteModuleCech.Map (ProjectiveRoot.cechDiagram R n m) (cechDiagram I z hz m) where
  app := unitCech I z hz m
  naturality := unitCech_natural I z hz m

abbrev rootReductionDiagram := FiniteModuleCech.reduction (ProjectiveRoot.cechDiagram R n m) I
abbrev exceptionalDiagram := FiniteModuleCech.reduction (cechDiagram I z hz m) I

def fibreCechMap : FiniteModuleCech.Map (rootReductionDiagram I m) (exceptionalDiagram I z hz m) :=
  FiniteModuleCech.Map.coefficients (ProjectiveRoot.cechDiagram R n m)
    (TensorIdeal.quotientFunctor I) (unitCechMap I z hz m)

variable (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

include hgen hds hmu ha in
lemma fibreCechMap_isoModSerre (s : Finset (Fin (n+1))) :
    ell.zeroClass.isoModSerre ((fibreCechMap I z hz m).app s) := by
  change ell.zeroClass.isoModSerre ((TensorIdeal.quotientFunctor I).map (unitCech I z hz m s))
  apply TensorIdeal.quotientPi_isoModSerre I
    (fun hs : PLift s.Nonempty => ProjectiveRoot.Sections R n s hs.down m)
    (fun hs : PLift s.Nonempty => Sections I z hz s hs.down m)
    (fun hs => TensorIdeal.unitMap (A:=ProjectiveRoot.Ring R n s) (B:=Ring I z hz s)
      (ProjectiveRoot.Sections R n s hs.down m)) ell.zeroClass
  intro hs
  change ell.zeroClass.isoModSerre (ModuleCat.ofHom (rootFibreMap I z hz s hs.down m))
  apply isoModSerre_of_surjective_kernel ell.zeroClass
  · exact rootFibreMap_surjective I z hz hgen s hs.down m
  · exact ⟨powerTorsion_submodule I _ (TensorIdeal.quotient_torsion I _),
      rootFibreMap_kernel_zero I z hz hgen ell hds hmu ha s hs.down m⟩

include hgen hds hmu ha in
 

theorem fibreCech_homology (q : ℕ) :
    ell.zeroClass.isoModSerre
      (homologyMap (fibreCechMap I z hz m).positiveComplex q) :=
  (fibreCechMap I z hz m).positiveHomology_isoModSerre ell.zeroClass
    (fibreCechMap_isoModSerre I z hz m hgen ell hds hmu ha) q

include hgen hds hmu ha in
lemma fibreCech_cardinality_homology (q : ℕ) :
    ell.zeroClass.isoModSerre (homologyMap (fibreCechMap I z hz m).complex q) :=
  (fibreCechMap I z hz m).homology_isoModSerre ell.zeroClass
    (fibreCechMap_isoModSerre I z hz m hgen ell hds hmu ha) q

end Lech.ReesRoot

end

end OAI
