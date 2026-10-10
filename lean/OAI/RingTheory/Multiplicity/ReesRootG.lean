import Mathlib
import OAI.RingTheory.Multiplicity.IdealFilteredComplex
import OAI.RingTheory.Multiplicity.ReesRootLayers
import OAI.RingTheory.Multiplicity.TensorIdealRange

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance concreteRing (t : Finset (Fin (n+1))) : CommRing (Ring I z hz t) := inferInstance
private local instance baseAlgebra (t : Finset (Fin (n+1))) : Algebra R (Ring I z hz t) :=
  Homogeneous.algebra (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz t))
private local instance baseModule (t : Finset (Fin (n+1))) : Module R (Ring I z hz t) :=
  Homogeneous.module (IdealGraded.reesGrade I) (Submonoid.powers (denominator I z hz t))
private local instance projectiveModule (t : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n t) (Ring I z hz t) := (projectiveAlgebra I z hz t).toModule
private local instance scalarComm (t : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n t) R (Ring I z hz t) where
  smul_comm a r b := by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _
private local instance sectionGroup (t : Finset (Fin (n+1))) (ht : t.Nonempty) (m : Fin n → ℤ) :
    AddCommGroup (Sections I z hz t ht m) := TensorProduct.addCommGroup
private local instance sectionBaseModule (t : Finset (Fin (n+1))) (ht : t.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz t ht m) := TensorProduct.leftModule

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)

 

def baseTwist : Fin n → ℤ := fun j => m j-(h*s:ℕ)

def enlargedOn (t : Finset (Fin (n+1))) (ht : t.Nonempty) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  IdealFiltered.complex I F h s hd
    (ModuleCat.of R (Sections I z hz t ht (baseTwist h s m)))

 

lemma enlarged_twist (i : ℕ) (hi : i ≤ h) :
    raise (baseTwist h s m) (IdealFiltered.order h s (-(i:ℤ))) = fun j => m j-(i*s:ℕ) := by
  funext j
  rw [raise_apply,baseTwist,IdealFiltered.order_source h s i hi,Nat.sub_mul,Nat.cast_sub (Nat.mul_le_mul_right s hi)]
  push_cast
  ring

 

def enlargedTermEquiv (t : Finset (Fin (n+1))) (ht : t.Nonempty)
    (hgen : Ideal.span (Set.range z)=I) (p : ℤ) [Module.Flat R (F.X p)] :
    ((F.X p) ⊗[R] Sections I z hz t ht
      (raise (baseTwist h s m) (IdealFiltered.order h s p))) ≃ₗ[R]
        ((enlargedOn I z hz F h s hd m t ht).X p) :=
  TensorIdeal.equiv I
    (inclusionIter I z hz t ht (baseTwist h s m) (IdealFiltered.order h s p))
    (IdealFiltered.order h s p)
    (inclusionIter_range I z hz t ht (baseTwist h s m) hgen (IdealFiltered.order h s p))
    (F.X p)
    (inclusionIter_injective I z hz t ht (baseTwist h s m) (IdealFiltered.order h s p))

lemma enlargedTermEquiv_val (t : Finset (Fin (n+1))) (ht : t.Nonempty)
    (hgen : Ideal.span (Set.range z)=I) (p : ℤ) [Module.Flat R (F.X p)]
    (x : (F.X p) ⊗[R] Sections I z hz t ht
      (raise (baseTwist h s m) (IdealFiltered.order h s p))) :
    (enlargedTermEquiv I z hz F h s hd m t ht hgen p x).val =
      (inclusionIter I z hz t ht (baseTwist h s m) (IdealFiltered.order h s p)).lTensor (F.X p) x := rfl

 

def cechZ : CochainComplex (ModuleCat.{u} R) ℤ :=
  (cech I z hz m).extend ComplexShape.embeddingUpNat

lemma cechZ_negative (q : ℤ) (hq : q < 0) : IsZero ((cechZ I z hz m).X q) := by
  apply (cech I z hz m).isZero_extend_X
  intro j hj
  change (j:ℤ)=q at hj
  omega

 

def enlargedBicomplex :
    CochainComplex (CochainComplex (ModuleCat.{u} R) ℤ) ℤ :=
  ((IdealFiltered.functor I F h s hd).mapHomologicalComplex (.up ℤ)).obj
    (cechZ I z hz (baseTwist h s m))

end Lech.ReesRoot

end

end OAI
