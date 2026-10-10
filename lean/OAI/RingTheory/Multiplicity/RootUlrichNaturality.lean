import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootCech
import OAI.RingTheory.Multiplicity.RootChartUlrich

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech
universe u v w w' z
lemma basis_coordinates_semilinear {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    {ι : Type z} [Fintype ι] (b : Module.Basis ι A M) (c : Module.Basis ι B N)
    (φ : A →+* B) (f : M →ₛₗ[φ] N) (hb : ∀ i,f (b i)=c i) (x : M) :
    c.equivFun (f x)=fun i => φ (b.equivFun x i) := by
  classical
  apply c.equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply,Module.Basis.equivFun_symm_apply]
  conv_lhs => rw [←b.sum_repr x,map_sum]
  simp only [map_smulₛₗ,hb,Module.Basis.equivFun_apply]
end Lech

namespace Lech.ProjectiveRoot
open ProductSourceCover UniversalSplitting
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
lemma powerSectionBasis_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (e : PowerIndex n) :
    sectionsRestriction R n hs ht (fun i => (powerWeight n i:ℤ)) hst
      (powerSectionBasis R n s hs e)=powerSectionBasis R n t ht e := by
  apply Subtype.ext
  change (powerSectionBasis R n s hs e : GridAmbient R n)=
    (powerSectionBasis R n t ht e : GridAmbient R n)
  rw [powerSectionBasis_val,powerSectionBasis_val]
end Lech.ProjectiveRoot

namespace Lech.ReesRoot
open UniversalSplitting ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance baseAlgebra (s : Finset (Fin (n+1))) : Algebra R (Ring I z hz s) := inferInstance
private local instance sectionModule (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module (Ring I z hz s) (Sections I z hz s hs m) := inferInstance

lemma sectionsRestriction_smul {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (m : Fin n → ℤ) (hst : s ⊆ t) (a : Ring I z hz s) (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz hs ht m hst (a • x)=
      restriction I z hz hst a • sectionsRestriction I z hz hs ht m hst x := by
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
      simp only [TensorProduct.smul_tmul',smul_eq_mul,sectionsRestriction_tmul,map_mul]
  | add x y hx hy => rw [smul_add,map_add,map_add,hx,hy,smul_add]

 
def sectionsRestrictionRing {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (m : Fin n → ℤ) (hst : s ⊆ t) :
    Sections I z hz s hs m →ₛₗ[restriction I z hz hst] Sections I z hz t ht m where
  toFun := sectionsRestriction I z hz hs ht m hst
  map_add' := map_add _
  map_smul' := sectionsRestriction_smul I z hz hs ht m hst

def powerSectionBasis (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    Module.Basis (PowerIndex n) (Ring I z hz s)
      (Sections I z hz s hs (fun i => (powerWeight n i:ℤ))) :=
  (ProjectiveRoot.powerSectionBasis R n s hs).baseChange (Ring I z hz s)

lemma powerSectionBasis_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (e : PowerIndex n) :
    sectionsRestriction I z hz hs ht (fun i => (powerWeight n i:ℤ)) hst
      (powerSectionBasis I z hz s hs e)=powerSectionBasis I z hz t ht e := by
  simp only [powerSectionBasis,Module.Basis.baseChange_apply,sectionsRestriction_tmul,map_one,
    ProjectiveRoot.powerSectionBasis_natural]

lemma powerSectionCoordinates_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (x : Sections I z hz s hs (fun i => (powerWeight n i:ℤ))) :
    (powerSectionBasis I z hz t ht).equivFun
      (sectionsRestriction I z hz hs ht (fun i => (powerWeight n i:ℤ)) hst x)=
        fun e => restriction I z hz hst ((powerSectionBasis I z hz s hs).equivFun x e) :=
  basis_coordinates_semilinear (A := Ring I z hz s) (B := Ring I z hz t)
    (M := Sections I z hz s hs (fun i => (powerWeight n i:ℤ)))
    (N := Sections I z hz t ht (fun i => (powerWeight n i:ℤ)))
    (powerSectionBasis I z hz s hs) (powerSectionBasis I z hz t ht)
    (restriction I z hz hst) (sectionsRestrictionRing I z hz hs ht _ hst)
    (powerSectionBasis_natural I z hz hs ht hst) x
end Lech.ReesRoot

end

end OAI
