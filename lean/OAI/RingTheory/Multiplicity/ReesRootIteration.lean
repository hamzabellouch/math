import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootLayers

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance baseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance baseModule (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz s))
private local instance projectiveModule (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
private local instance scalarComm (s : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n s) R (Ring I z hz s) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _
private local instance sectionGroup (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz s hs m) := TensorProduct.addCommGroup
private local instance sectionChartModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := TensorProduct.leftModule
private local instance sectionBaseModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule

private local instance sectionTower (t : Finset (Fin (n+1))) (ht : t.Nonempty) (m : Fin n → ℤ) :
    IsScalarTower R (Ring I z hz t) (Sections I z hz t ht m) := TensorProduct.isScalarTower_left

variable (t : Finset (Fin (n+1))) (ht : t.Nonempty) (k : Fin (n+1)) (hk : k ∈ t)

 
def downIter (m : Fin n → ℤ) (N : ℕ) :
    Sections I z hz t ht (raise m N) ≃ₗ[Ring I z hz t] Sections I z hz t ht m :=
  match N with
  | 0 => LinearEquiv.refl _ _
  | N+1 => (downIter (fun j => m j+1) N).trans (downEquiv I z hz t ht m k hk)

lemma inclusionIter_coordinate (m : Fin n → ℤ) (N : ℕ)
    (x : Sections I z hz t ht (raise m N)) :
    inclusionIter I z hz t ht m N x = z k^N • downIter I z hz t ht k hk m N x := by
  induction N generalizing m with
  | zero => simp only [inclusionIter,downIter,pow_zero,one_smul]; rfl
  | succ N ih =>
      change Sections I z hz t ht (raise (fun j => m j+1) N) at x
      change inclusion I z hz t ht m (inclusionIter I z hz t ht (fun j => m j+1) N x) = _
      rw [inclusion_eq I z hz t ht m k hk,ih]
      change algebraMap R (Ring I z hz t) (z k) •
        downEquiv I z hz t ht m k hk (z k^N • downIter I z hz t ht k hk (fun j => m j+1) N x) = _
      rw [IsScalarTower.algebraMap_smul]
      rw [←IsScalarTower.algebraMap_smul (Ring I z hz t) (z k^N),map_smul,
        IsScalarTower.algebraMap_smul,smul_smul,pow_succ']
      rfl

open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable (m : Fin n → ℤ)

 

def cechInclusionIterApp (N : ℕ) (s : Finset (Fin (n+1))) :
    cechObj I z hz (raise m N) s ⟶ cechObj I z hz m s :=
  ModuleCat.ofHom {
    toFun x hs := inclusionIter I z hz s hs.down m N (x hs)
    map_add' x y := by funext hs; exact map_add _ _ _
    map_smul' r x := by funext hs; exact map_smul (inclusionIter I z hz s hs.down m N) r (x hs) }

lemma cechInclusionIter_natural (N : ℕ) {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    cechRes I z hz (raise m N) hst ≫ cechInclusionIterApp I z hz m N t =
      cechInclusionIterApp I z hz m N s ≫ cechRes I z hz m hst := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext ht
  by_cases hs : s.Nonempty
  · change inclusionIter I z hz t ht.down m N
      ((cechRes I z hz (raise m N) hst).hom x ht) =
        (cechRes I z hz m hst).hom ((cechInclusionIterApp I z hz m N s).hom x) ht
    rw [cechRes_apply I z hz (raise m N) hst hs ht.down,
      cechRes_apply I z hz m hst hs ht.down]
    exact (inclusionIter_restriction I z hz s hs m ht.down hst N (x ⟨hs⟩)).symm
  · change inclusionIter I z hz t ht.down m N (if hs : s.Nonempty then _ else 0) =
      if hs : s.Nonempty then _ else 0
    simp only [dite_eq_right hs,map_zero]

def cechInclusionIterDiagram (N : ℕ) : FiniteModuleCech.Map
    (cechDiagram I z hz (raise m N)) (cechDiagram I z hz m) where
  app := cechInclusionIterApp I z hz m N
  naturality := cechInclusionIter_natural I z hz m N

 
def cechInclusionIter (N : ℕ) : cech I z hz (raise m N) ⟶ cech I z hz m :=
  (cechInclusionIterDiagram I z hz m N).positiveComplex

end Lech.ReesRoot

end

end OAI
