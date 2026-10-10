import Mathlib
import OAI.RingTheory.Multiplicity.IdealQuotientFunctor
import OAI.RingTheory.Multiplicity.ReesRootIteration

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] (J : Ideal R) {ι : Type} [Fintype ι]
  (M N : ι → Type u) [∀ i,AddCommGroup (M i)] [∀ i,Module R (M i)]
  [∀ i,AddCommGroup (N i)] [∀ i,Module R (N i)] (f : ∀ i,M i →ₗ[R] N i)
lemma piMap_range (hf : ∀ i,(f i).range=J • (⊤ : Submodule R (N i))) :
    (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).range =
      J • (⊤ : Submodule R (∀ i,N i)) := by
  ext x
  rw [mem_smul_pi_iff]
  constructor
  · rintro ⟨y,rfl⟩ i
    rw [←hf i]
    exact LinearMap.mem_range_self _ _
  · intro hx
    have hy (i : ι) : x i ∈ (f i).range := (hf i).symm ▸ hx i
    choose y hy using hy
    exact ⟨y,funext hy⟩
end Lech.TensorIdeal

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
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
private local instance sectionModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule
private local instance proofFinite (s : Finset (Fin (n+1))) : Fintype (PLift s.Nonempty) := Fintype.ofFinite _

lemma cechInclusionIterApp_range (hgen : Ideal.span (Set.range z)=I)
    (a : ℕ) (t : Finset (Fin (n+1))) :
    (cechInclusionIterApp I z hz m a t).hom.range =
      I^a • (⊤ : Submodule R (cechObj I z hz m t)) :=
  TensorIdeal.piMap_range (I^a)
    (fun ht : PLift t.Nonempty => Sections I z hz t ht.down (raise m a))
    (fun ht : PLift t.Nonempty => Sections I z hz t ht.down m)
    (fun ht => inclusionIter I z hz t ht.down m a)
    (fun ht => inclusionIter_range I z hz t ht.down m hgen a)

lemma cechInclusionIter_range (hgen : Ideal.span (Set.range z)=I) (a q : ℕ) :
    ((cechInclusionIter I z hz m a).f q).hom.range =
      I^a • (⊤ : Submodule R ((cech I z hz m).X q)) :=
  TensorIdeal.piMap_range (I^a)
    (fun t : Set.powersetCard (Fin (n+1)) (q+1) => cechObj I z hz (raise m a) t.val)
    (fun t : Set.powersetCard (Fin (n+1)) (q+1) => cechObj I z hz m t.val)
    (fun t => (cechInclusionIterApp I z hz m a t.val).hom)
    (fun t => cechInclusionIterApp_range I z hz m hgen a t.val)

lemma cechInclusionIter_injective (a q : ℕ) :
    Function.Injective ((cechInclusionIter I z hz m a).f q).hom := by
  intro x y hxy
  funext t ht
  exact inclusionIter_injective I z hz t.val ht.down m a (congrFun (congrFun hxy t) ht)

instance cechInclusionIter_mono (a : ℕ) : Mono (cechInclusionIter I z hz m a) :=
  mono_of_mono_f _ (fun q => (ModuleCat.mono_iff_injective _).mpr
    (cechInclusionIter_injective I z hz m a q))
end Lech.ReesRoot

end

end OAI
