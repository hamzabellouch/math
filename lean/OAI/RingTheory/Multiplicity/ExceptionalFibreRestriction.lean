import Mathlib
import OAI.RingTheory.Multiplicity.ExceptionalFibre
import OAI.RingTheory.Multiplicity.RootSectionBase

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory HomogeneousLocalization
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

variable {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty) (m : Fin n → ℤ)

def rootFibreRestriction (hst : s ⊆ t) :
    RootFibreSections I s hs m →ₗ[R] RootFibreSections I t ht m :=
  TensorIdeal.idealQuotientMap I (ProjectiveRoot.sectionsRestrictionBase R n hs ht m hst)

def exceptionalRestriction (hst : s ⊆ t) :
    ExceptionalSections I z hz s hs m →ₗ[R] ExceptionalSections I z hz t ht m :=
  TensorIdeal.idealQuotientMap I (sectionsRestriction I z hz hs ht m hst)

lemma rootFibreMap_mk (x : ProjectiveRoot.Sections R n s hs m) :
    rootFibreMap I z hz s hs m (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (1 ⊗ₜ[ProjectiveRoot.Ring R n s] x) := rfl

lemma rootFibreMap_restriction (hst : s ⊆ t) (x : RootFibreSections I s hs m) :
    exceptionalRestriction I z hz hs ht m hst (rootFibreMap I z hz s hs m x) =
      rootFibreMap I z hz t ht m (rootFibreRestriction I hs ht m hst x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change Submodule.Quotient.mk (sectionsRestriction I z hz hs ht m hst
      (1 ⊗ₜ[ProjectiveRoot.Ring R n s] x)) = _
    rw [sectionsRestriction_tmul,map_one]
    rfl

end Lech.ReesRoot

end

end OAI
