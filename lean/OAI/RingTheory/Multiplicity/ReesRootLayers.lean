import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootInclusion

namespace OAI

noncomputable section
namespace Lech.LocalPrincipal
universe u v w
variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {M : Type w} [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M]
  (I : Ideal R) {ι : Type*} (z : ι → R) (hz : Ideal.span (Set.range z)=I)
  (k : ι) (q : ι → B) (hq : ∀ j, algebraMap R B (z k)*q j=algebraMap R B (z j))

include hz hq in
lemma smul_top_eq_range :
    I • (⊤ : Submodule R M) = ((z k) • (LinearMap.id : M →ₗ[R] M)).range := by
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro a ha x _
    rw [←hz] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨j,rfl⟩ := ha
        refine ⟨q j • x,?_⟩
        change z k • (q j • x) = z j • x
        rw [←IsScalarTower.algebraMap_smul B (z k),←mul_smul,hq,IsScalarTower.algebraMap_smul]
    | zero => simpa only [zero_smul] using (LinearMap.range ((z k) • (LinearMap.id : M →ₗ[R] M))).zero_mem
    | add a b ha hb ia ib =>
        rw [add_smul]
        exact Submodule.add_mem _ ia ib
    | smul a b hb ib =>
        rw [smul_eq_mul,mul_smul]
        exact Submodule.smul_mem _ a ib
  · rintro _ ⟨x,rfl⟩
    exact Submodule.smul_mem_smul (hz ▸ Ideal.subset_span ⟨k,rfl⟩) Submodule.mem_top
end Lech.LocalPrincipal

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

variable (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ)

lemma inclusion_range (hgen : Ideal.span (Set.range z)=I) :
    (inclusion I z hz s hs m).range = I • (⊤ : Submodule R (Sections I z hz s hs m)) := by
  classical
  let k := hs.choose
  have hk : k ∈ s := hs.choose_spec
  rw [LocalPrincipal.smul_top_eq_range I z hgen k
    (fun j => map I z hz s (ProjectiveRoot.ratio R n s k j hk)) (ratio_relation I z hz s k · hk)]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨downEquiv I z hz s hs m k hk y,?_⟩
    rw [inclusion_eq I z hz s hs m k hk]
    change z k • (downEquiv I z hz s hs m k hk) y =
      algebraMap R (Ring I z hz s) (z k) • (downEquiv I z hz s hs m k hk) y
    exact (IsScalarTower.algebraMap_smul (Ring I z hz s) (z k) _).symm
  · rintro ⟨y,rfl⟩
    refine ⟨(downEquiv I z hz s hs m k hk).symm y,?_⟩
    rw [inclusion_eq I z hz s hs m k hk]
    change algebraMap R (Ring I z hz s) (z k) •
      (downEquiv I z hz s hs m k hk) ((downEquiv I z hz s hs m k hk).symm y) = z k • y
    rw [LinearEquiv.apply_symm_apply,IsScalarTower.algebraMap_smul]

 
abbrev ExceptionalSections :=
  Sections I z hz s hs m ⧸ (I • (⊤ : Submodule R (Sections I z hz s hs m)))

 
def layerEquiv (hgen : Ideal.span (Set.range z)=I) :
    (Sections I z hz s hs m ⧸ (inclusion I z hz s hs m).range) ≃ₗ[R]
      ExceptionalSections I z hz s hs m :=
  Submodule.quotEquivOfEq _ _ (inclusion_range I z hz s hs m hgen)

 

def raise (m : Fin n → ℤ) : ℕ → Fin n → ℤ
  | 0 => m
  | N+1 => raise (fun i => m i+1) N

lemma raise_apply (m : Fin n → ℤ) (N : ℕ) (i : Fin n) : raise m N i = m i+N := by
  induction N generalizing m with
  | zero => simp only [raise,Nat.cast_zero,add_zero]
  | succ N ih => rw [raise,ih,Nat.cast_succ]; ring

 

def inclusionIter (m : Fin n → ℤ) (N : ℕ) :
    Sections I z hz s hs (raise m N) →ₗ[R] Sections I z hz s hs m :=
  match N with
  | 0 => LinearMap.id
  | N+1 => (inclusion I z hz s hs m).comp (inclusionIter (fun i => m i+1) N)

lemma inclusionIter_injective (N : ℕ) :
    Function.Injective (inclusionIter I z hz s hs m N) := by
  induction N generalizing m with
  | zero => exact Function.injective_id
  | succ N ih => exact (inclusion_injective I z hz s hs m).comp (ih _)

 

lemma inclusionIter_range (hgen : Ideal.span (Set.range z)=I) (N : ℕ) :
    (inclusionIter I z hz s hs m N).range = I^N • (⊤ : Submodule R (Sections I z hz s hs m)) := by
  induction N generalizing m with
  | zero =>
      change (LinearMap.id : Sections I z hz s hs m →ₗ[R] Sections I z hz s hs m).range = _
      simp only [LinearMap.range_id,pow_zero,Ideal.one_eq_top,Submodule.top_smul]
  | succ N ih =>
      change ((inclusion I z hz s hs m).comp
        (inclusionIter I z hz s hs (fun i => m i+1) N)).range = _
      rw [LinearMap.range_comp,ih,Submodule.map_smul'',Submodule.map_top,
        inclusion_range I z hz s hs m hgen,
        ←Submodule.mul_smul,pow_succ]

lemma inclusionIter_restriction {t : Finset (Fin (n+1))} (ht : t.Nonempty) (hst : s ⊆ t)
    (N : ℕ) (x : Sections I z hz s hs (raise m N)) :
    sectionsRestriction I z hz hs ht m hst (inclusionIter I z hz s hs m N x) =
      inclusionIter I z hz t ht m N (sectionsRestriction I z hz hs ht (raise m N) hst x) := by
  induction N generalizing m with
  | zero => rfl
  | succ N ih =>
      change Sections I z hz s hs (raise (fun i => m i+1) N) at x
      change sectionsRestriction I z hz hs ht m hst
        (inclusion I z hz s hs m (inclusionIter I z hz s hs (fun i => m i+1) N x)) = _
      refine (inclusion_restriction I z hz s hs m ht hst _).trans ?_
      exact congrArg (inclusion I z hz t ht m) (ih (fun i => m i+1) x)

 

def thickeningEquiv (hgen : Ideal.span (Set.range z)=I) (N : ℕ) :
    (Sections I z hz s hs m ⧸ (inclusionIter I z hz s hs m N).range) ≃ₗ[R]
      (Sections I z hz s hs m ⧸ (I^N • (⊤ : Submodule R (Sections I z hz s hs m)))) :=
  Submodule.quotEquivOfEq _ _ (inclusionIter_range I z hz s hs m hgen N)

end Lech.ReesRoot

end

end OAI
