import Mathlib
import OAI.RingTheory.Multiplicity.ReesUlrichCech
import OAI.RingTheory.Multiplicity.RootPermutation

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits ProductSourceCover
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance baseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance sectionChartModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := inferInstance

 
def permuteSections (σ : Equiv.Perm (Fin n)) (s : Finset (Fin (n+1)))
    (hs : s.Nonempty) (m : Fin n → ℤ) :
    Sections I z hz s hs m ≃ₗ[Ring I z hz s] Sections I z hz s hs (permuteWeight n σ m) :=
  LinearEquiv.baseChange (ProjectiveRoot.Ring R n s) (Ring I z hz s) _ _
    (ProjectiveRoot.permuteSections R n σ s hs m)

lemma permuteSections_natural (σ : Equiv.Perm (Fin n))
    {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (m : Fin n → ℤ) (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz hs ht (permuteWeight n σ m) hst (permuteSections I z hz σ s hs m x)=
      permuteSections I z hz σ t ht m (sectionsRestriction I z hz hs ht m hst x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      change sectionsRestriction I z hz hs ht _ hst
        (a ⊗ₜ[ProjectiveRoot.Ring R n s] ProjectiveRoot.permuteSections R n σ s hs m x)=_
      rw [sectionsRestriction_tmul,ProjectiveRoot.permuteSections_natural,sectionsRestriction_tmul]
      rfl
  | add x y hx hy => simp only [map_add,hx,hy]

private local instance baseModule (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance projectiveModule (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
private local instance scalarComm (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _
private local instance sectionGroup (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
private local instance sectionModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

def permuteCechEquiv (σ : Equiv.Perm (Fin n)) (m : Fin n → ℤ) (s : Finset (Fin (n+1))) :
    cechObj I z hz m s ≃ₗ[R] cechObj I z hz (permuteWeight n σ m) s where
  toFun x hs := permuteSections I z hz σ s hs.down m (x hs)
  invFun x hs := (permuteSections I z hz σ s hs.down m).symm (x hs)
  left_inv x := by funext hs; exact LinearEquiv.symm_apply_apply _ _
  right_inv x := by funext hs; exact LinearEquiv.apply_symm_apply _ _
  map_add' x y := by funext hs; exact map_add _ _ _
  map_smul' r x := by
    funext hs
    exact map_smul ((permuteSections I z hz σ s hs.down m).restrictScalars R) r (x hs)

lemma permuteCechEquiv_natural (σ : Equiv.Perm (Fin n)) (m : Fin n → ℤ)
    {s t : Finset (Fin (n+1))} (hst : s ⊆ t) (x : cechObj I z hz m s) :
    permuteCechEquiv I z hz σ m t ((cechRes I z hz m hst).hom x)=
      (cechRes I z hz (permuteWeight n σ m) hst).hom (permuteCechEquiv I z hz σ m s x) := by
  funext ht
  by_cases hs : s.Nonempty
  · change permuteSections I z hz σ t ht.down m ((cechRes I z hz m hst).hom x ht)=
      (cechRes I z hz _ hst).hom (fun hs => permuteSections I z hz σ s hs.down m (x hs)) ht
    rw [cechRes_apply I z hz m hst hs ht.down,cechRes_apply I z hz _ hst hs ht.down,
      permuteSections_natural]
  · change permuteSections I z hz σ t ht.down m (if hs : s.Nonempty then _ else 0)=
      if hs : s.Nonempty then _ else 0
    simp only [dite_eq_right hs,map_zero]

 

def permuteCechIso (σ : Equiv.Perm (Fin n)) (m : Fin n → ℤ) :
    cech I z hz m ≅ cech I z hz (permuteWeight n σ m) :=
  FiniteModuleCech.positiveIso (permuteCechEquiv I z hz σ m)
    (fun _ => permuteCechEquiv_natural I z hz σ m _)
end Lech.ReesRoot

end

end OAI
