import Mathlib
import OAI.RingTheory.Multiplicity.ReesCoordinate
import OAI.RingTheory.Multiplicity.ReesRegular
import OAI.RingTheory.Multiplicity.ReesRootCech

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
variable (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ)

def downEquiv (k : Fin (n+1)) (hk : k ∈ s) :
    Sections R n s hs (fun i => m i+1) ≃ₗ[Ring R n s] Sections R n s hs m :=
  twistEquiv R n k s hk hs _ m (-1) (by intro i; omega)

lemma downEquiv_change (k j : Fin (n+1)) (hk : k ∈ s) (hj : j ∈ s)
    (x : Sections R n s hs (fun i => m i+1)) :
    downEquiv R n s hs m k hk x = ratio R n s k j hk • downEquiv R n s hs m j hj x := by
  apply Subtype.ext
  change (↑((targetUnit R n k)^(-1:ℤ)) : GridAmbient R n) * x.val =
    scalarMap R n s (ratio R n s k j hk) *
      ((↑((targetUnit R n j)^(-1:ℤ)) : GridAmbient R n) * x.val)
  rw [scalarMap_ratio]
  simp only [zpow_neg_one]
  rw [mul_assoc,←mul_assoc (↑(targetUnit R n j) : GridAmbient R n),Units.mul_inv,one_mul]

lemma downEquiv_restriction {t : Finset (Fin (n+1))} (ht : t.Nonempty) (hst : s ⊆ t)
    (k : Fin (n+1)) (hk : k ∈ s) (x : Sections R n s hs (fun i => m i+1)) :
    sectionsRestriction R n hs ht m hst (downEquiv R n s hs m k hk x) =
      downEquiv R n t ht m k (hst hk) (sectionsRestriction R n hs ht _ hst x) := rfl
end Lech.ProjectiveRoot

namespace Lech.ReesRoot
open ProductSourceCover
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

variable (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ)

def downEquiv (k : Fin (n+1)) (hk : k ∈ s) :
    Sections I z hz s hs (fun i => m i+1) ≃ₗ[Ring I z hz s] Sections I z hz s hs m :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Ring I z hz s) _)
    (ProjectiveRoot.downEquiv R n s hs m k hk)

 

def localInclusion (k : Fin (n+1)) (hk : k ∈ s) :
    Sections I z hz s hs (fun i => m i+1) →ₗ[Ring I z hz s] Sections I z hz s hs m :=
  (algebraMap R (Ring I z hz s) (z k)) • (downEquiv I z hz s hs m k hk).toLinearMap

lemma localInclusion_tmul (k : Fin (n+1)) (hk : k ∈ s)
    (b : Ring I z hz s) (x : ProjectiveRoot.Sections R n s hs (fun i => m i+1)) :
    localInclusion I z hz s hs m k hk (b ⊗ₜ x) =
      (algebraMap R (Ring I z hz s) (z k)*b) ⊗ₜ ProjectiveRoot.downEquiv R n s hs m k hk x := by
  change (algebraMap R (Ring I z hz s) (z k)) • (b ⊗ₜ[ProjectiveRoot.Ring R n s] ProjectiveRoot.downEquiv R n s hs m k hk x) = _
  rw [TensorProduct.smul_tmul']
  rfl

 

lemma localInclusion_independent (k j : Fin (n+1)) (hk : k ∈ s) (hj : j ∈ s)
    (x : Sections I z hz s hs (fun i => m i+1)) :
    localInclusion I z hz s hs m k hk x = localInclusion I z hz s hs m j hj x := by
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
      rw [localInclusion_tmul,localInclusion_tmul,ProjectiveRoot.downEquiv_change R n s hs m k j hk hj,
        ←TensorProduct.smul_tmul (R := ProjectiveRoot.Ring R n s)
          (ProjectiveRoot.ratio R n s k j hk)
          (algebraMap R (Ring I z hz s) (z k)*b)
          (ProjectiveRoot.downEquiv R n s hs m j hj x)]
      congr 1
      change map I z hz s (ProjectiveRoot.ratio R n s k j hk) *
        (algebraMap R (Ring I z hz s) (z k)*b) = algebraMap R (Ring I z hz s) (z j)*b
      rw [←mul_assoc,mul_comm _ (algebraMap R (Ring I z hz s) (z k)),ratio_relation]
  | add x y hx hy => simp only [map_add,hx,hy]

lemma localInclusion_restriction {t : Finset (Fin (n+1))} (ht : t.Nonempty) (hst : s ⊆ t)
    (k : Fin (n+1)) (hk : k ∈ s) (x : Sections I z hz s hs (fun i => m i+1)) :
    sectionsRestriction I z hz hs ht m hst (localInclusion I z hz s hs m k hk x) =
      localInclusion I z hz t ht m k (hst hk) (sectionsRestriction I z hz hs ht _ hst x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
      rw [localInclusion_tmul,sectionsRestriction_tmul,sectionsRestriction_tmul,localInclusion_tmul,
        map_mul,ProjectiveRoot.downEquiv_restriction]
      congr 2
      exact (restrictionAlg I z hz hst).commutes (z k)
  | add x y hx hy => simp only [map_add,hx,hy]

 

def inclusion : Sections I z hz s hs (fun i => m i+1) →ₗ[R] Sections I z hz s hs m :=
  (localInclusion I z hz s hs m hs.choose hs.choose_spec).restrictScalars R

lemma inclusion_eq (k : Fin (n+1)) (hk : k ∈ s) (x : Sections I z hz s hs (fun i => m i+1)) :
    inclusion I z hz s hs m x = localInclusion I z hz s hs m k hk x :=
  localInclusion_independent I z hz s hs m hs.choose k hs.choose_spec hk x

lemma inclusion_restriction {t : Finset (Fin (n+1))} (ht : t.Nonempty) (hst : s ⊆ t)
    (x : Sections I z hz s hs (fun i => m i+1)) :
    sectionsRestriction I z hz hs ht m hst (inclusion I z hz s hs m x) =
      inclusion I z hz t ht m (sectionsRestriction I z hz hs ht _ hst x) := by
  rw [inclusion_eq I z hz s hs m hs.choose hs.choose_spec,
    inclusion_eq I z hz t ht m hs.choose (hst hs.choose_spec)]
  exact localInclusion_restriction I z hz s hs m ht hst hs.choose hs.choose_spec x

 

lemma localInclusion_injective (k : Fin (n+1)) (hk : k ∈ s) :
    Function.Injective (localInclusion I z hz s hs m k hk) := by
  let : Module.Projective (Ring I z hz s) (Sections I z hz s hs m) :=
    (sections_properties I z hz hs m).2.1
  let : Module.Flat (Ring I z hz s) (Sections I z hz s hs m) := Module.Flat.of_projective
  have hr : IsRegular (algebraMap R (Ring I z hz s) (z k)) := by
    apply (Commute.isRegular_iff (fun b => mul_comm _ b)).2
    simpa only [IsLeftRegular, Algebra.smul_def] using coordinate_smul_injective I z hz s k hk
  have hinj := Module.Flat.isSMulRegular_of_isRegular (M := Sections I z hz s hs m) hr
  exact hinj.comp (downEquiv I z hz s hs m k hk).injective

lemma inclusion_injective : Function.Injective (inclusion I z hz s hs m) :=
  localInclusion_injective I z hz s hs m hs.choose hs.choose_spec

open CategoryTheory CategoryTheory.Limits
 
def cechInclusionApp (s : Finset (Fin (n+1))) :
    cechObj I z hz (fun i => m i+1) s ⟶ cechObj I z hz m s :=
  ModuleCat.ofHom {
    toFun x hs := inclusion I z hz s hs.down m (x hs)
    map_add' x y := by funext hs; exact map_add _ _ _
    map_smul' r x := by funext hs; exact map_smul (inclusion I z hz s hs.down m) r (x hs) }

lemma cechInclusion_natural {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    cechRes I z hz (fun i => m i+1) hst ≫ cechInclusionApp I z hz m t =
      cechInclusionApp I z hz m s ≫ cechRes I z hz m hst := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext ht
  by_cases hs : s.Nonempty
  · change inclusion I z hz t ht.down m
      ((cechRes I z hz (fun i => m i+1) hst).hom x ht) =
        (cechRes I z hz m hst).hom ((cechInclusionApp I z hz m s).hom x) ht
    rw [cechRes_apply I z hz (fun i => m i+1) hst hs ht.down,
      cechRes_apply I z hz m hst hs ht.down]
    exact (inclusion_restriction I z hz s hs m ht.down hst (x ⟨hs⟩)).symm
  · change inclusion I z hz t ht.down m (if hs : s.Nonempty then _ else 0) =
      if hs : s.Nonempty then _ else 0
    simp only [dite_eq_right hs,map_zero]

 
def cechInclusionDiagram : FiniteModuleCech.Map
    (cechDiagram I z hz (fun i => m i+1)) (cechDiagram I z hz m) where
  app := cechInclusionApp I z hz m
  naturality := cechInclusion_natural I z hz m

 
def cechInclusion : cech I z hz (fun i => m i+1) ⟶ cech I z hz m :=
  (cechInclusionDiagram I z hz m).positiveComplex

end Lech.ReesRoot

end

end OAI
