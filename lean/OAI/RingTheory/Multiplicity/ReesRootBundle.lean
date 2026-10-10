import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootMap

namespace OAI

noncomputable section

namespace Lech.HomogeneousEval
open HomogeneousLocalization
universe u v
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
lemma awayMap_algebraMap {f g x : A} {e : ℕ} (hg : g ∈ G e) (hx : x = f*g) (r : R) :
    awayMap G hg hx (algebraMap R (Away G f) r) = algebraMap R (Away G x) r := by
  apply HomogeneousLocalization.val_injective
  rw [val_awayMap,Homogeneous.val_algebraMap,Homogeneous.val_algebraMap]
  rw [IsScalarTower.algebraMap_apply R A (Localization.Away f),IsLocalization.Away.lift_eq,
    ←IsScalarTower.algebraMap_apply R A (Localization.Away x)]
end Lech.HomogeneousEval

namespace Lech.ProjectiveRoot
open MvPolynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
lemma ringRestriction_algebraMap {s t : Finset (Fin (n+1))} (hst : s ⊆ t) (r : R) :
    ringRestriction R n hst (algebraMap R (Ring R n s) r) = algebraMap R (Ring R n t) r :=
  HomogeneousEval.awayMap_algebraMap _ _ _ r
end Lech.ProjectiveRoot

namespace Lech.ReesRoot
open MvPolynomial HomogeneousLocalization IdealGraded
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j, z j ∈ I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

lemma gradedMap_smul (r : R) (a : MvPolynomial (Fin (n+1)) R) :
    gradedMap I z hz (r • a) = r • gradedMap I z hz a :=
  (MvPolynomial.aeval (R:=R) (generator I z hz)).toLinearMap.map_smul r a

def mapAlg (s : Finset (Fin (n+1))) : ProjectiveRoot.Ring R n s →ₐ[R] Ring I z hz s where
  __ := map I z hz s
  commutes' r := by
    change map I z hz s (algebraMap R (ProjectiveRoot.Ring R n s) r) = algebraMap R (Ring I z hz s) r
    have he := (Homogeneous.awayMap (ProjectiveCoefficientChart.grading R n) (reesGrade I)
      (gradedMap I z hz) (gradedMap_smul I z hz) (ProjectiveRoot.product R n s)).map_smul r 1
    change map I z hz s (r • 1) = r • map I z hz s 1 at he
    simpa only [Algebra.algebraMap_eq_smul_one,map_one] using he

def restrictionAlg {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    Ring I z hz s →ₐ[R] Ring I z hz t where
  __ := restriction I z hz hst
  commutes' r := HomogeneousEval.awayMap_algebraMap _ _ _ r

instance projectiveAlgebra (s : Finset (Fin (n+1))) :
    Algebra (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (map I z hz s).toAlgebra
instance projectiveTower (s : Finset (Fin (n+1))) :
    IsScalarTower R (ProjectiveRoot.Ring R n s) (Ring I z hz s) :=
  IsScalarTower.of_algebraMap_eq' (mapAlg I z hz s).comp_algebraMap.symm


abbrev Sections (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :=
  Ring I z hz s ⊗[ProjectiveRoot.Ring R n s] ProjectiveRoot.Sections R n s hs m

private local instance bundleConcreteRing (support : Finset (Fin (n+1))) :
    CommRing (Ring I z hz support) := inferInstance
private local instance bundleBaseAlgebra (support : Finset (Fin (n+1))) :
    Algebra R (Ring I z hz support) :=
  Homogeneous.algebra (reesGrade I) (Submonoid.powers (denominator I z hz support))
private local instance bundleBaseModule (support : Finset (Fin (n+1))) :
    Module R (Ring I z hz support) :=
  Homogeneous.module (reesGrade I) (Submonoid.powers (denominator I z hz support))
private local instance bundleProjectiveModule (support : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n support) (Ring I z hz support) :=
  (projectiveAlgebra I z hz support).toModule
private local instance bundleScalarComm (support : Finset (Fin (n+1))) :
    SMulCommClass (ProjectiveRoot.Ring R n support) R (Ring I z hz support) where
  smul_comm coefficient scalar element := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _
private local instance bundleSectionGroup (support : Finset (Fin (n+1)))
    (h_support : support.Nonempty) (weight : Fin n → ℤ) :
    AddCommGroup (Sections I z hz support h_support weight) := TensorProduct.addCommGroup
private local instance bundleSectionBaseModule (support : Finset (Fin (n+1)))
    (h_support : support.Nonempty) (weight : Fin n → ℤ) :
    Module R (Sections I z hz support h_support weight) := TensorProduct.leftModule

variable {s t v : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
  (hv : v.Nonempty) (m : Fin n → ℤ)

def coefficientRestriction (hst : s ⊆ t) :
    Ring I z hz s →ₛₗ[ProjectiveRoot.ringRestriction R n hst] Ring I z hz t where
  toFun := restriction I z hz hst
  map_add' := map_add _
  map_smul' a b := by
    change restriction I z hz hst (map I z hz s a * b) =
      map I z hz t (ProjectiveRoot.ringRestriction R n hst a) * restriction I z hz hst b
    rw [map_mul,map_restriction]

def sectionsRestrictionSemi (hst : s ⊆ t) :
    Sections I z hz s hs m →ₛₗ[ProjectiveRoot.ringRestriction R n hst] Sections I z hz t ht m :=
  TensorProduct.map (coefficientRestriction I z hz hst)
    (ProjectiveRoot.sectionsRestriction R n hs ht m hst)


def sectionsRestriction (hst : s ⊆ t) : Sections I z hz s hs m →ₗ[R] Sections I z hz t ht m where
  toFun := sectionsRestrictionSemi I z hz hs ht m hst
  map_add' := map_add _
  map_smul' r x := by
    change sectionsRestrictionSemi I z hz hs ht m hst (r • x) =
      r • sectionsRestrictionSemi I z hz hs ht m hst x
    induction x using TensorProduct.inductionOn with
    | tmul coefficient element =>
        change (restrictionAlg I z hz hst).toLinearMap (r • coefficient) ⊗ₜ
            ProjectiveRoot.sectionsRestriction R n hs ht m hst element =
          (r • (restrictionAlg I z hz hst).toLinearMap coefficient) ⊗ₜ
            ProjectiveRoot.sectionsRestriction R n hs ht m hst element
        rw [(restrictionAlg I z hz hst).toLinearMap.map_smul r coefficient]
    | add first second hfirst hsecond =>
        rw [smul_add,map_add,map_add,hfirst,hsecond,smul_add]

lemma sectionsRestriction_tmul (hst : s ⊆ t) (b : Ring I z hz s)
    (x : ProjectiveRoot.Sections R n s hs m) :
    sectionsRestriction I z hz hs ht m hst (b ⊗ₜ x) =
      restriction I z hz hst b ⊗ₜ ProjectiveRoot.sectionsRestriction R n hs ht m hst x := rfl

lemma sectionsRestriction_self (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz hs hs m (Finset.Subset.refl s) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul b x => rw [sectionsRestriction_tmul,restriction_self,ProjectiveRoot.sectionsRestriction_self]
  | add x y hx hy => rw [map_add,hx,hy]

lemma sectionsRestriction_comp (hst : s ⊆ t) (htv : t ⊆ v) (x : Sections I z hz s hs m) :
    sectionsRestriction I z hz ht hv m htv (sectionsRestriction I z hz hs ht m hst x) =
      sectionsRestriction I z hz hs hv m (hst.trans htv) x := by
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
      rw [sectionsRestriction_tmul,sectionsRestriction_tmul,sectionsRestriction_tmul,
        restriction_comp,ProjectiveRoot.sectionsRestriction_comp]
  | add x y hx hy => simp only [map_add,hx,hy]


theorem sections_properties :
    Module.FinitePresentation (Ring I z hz s) (Sections I z hz s hs m) ∧
    Module.Projective (Ring I z hz s) (Sections I z hz s hs m) ∧
    ∀ p : PrimeSpectrum (Ring I z hz s),
      Module.rankAtStalk (Sections I z hz s hs m) p = n.factorial := by
  obtain ⟨hfp,hpr,hr⟩ := ProjectiveRoot.sections_properties R n hs m
  let := hfp
  let := hpr
  refine ⟨inferInstance,inferInstance,?_⟩
  intro p
  rw [Module.rankAtStalk_baseChange]
  exact hr _

end Lech.ReesRoot

end

end OAI
