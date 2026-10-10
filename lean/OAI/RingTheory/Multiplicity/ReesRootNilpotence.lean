import Mathlib
import OAI.RingTheory.Multiplicity.IdealFilteredHomotopy
import OAI.RingTheory.Multiplicity.KoszulHomologyMap
import OAI.RingTheory.Multiplicity.ReesRootG
import OAI.RingTheory.Multiplicity.ReesRootIteration

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

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℕ)
  (H : ∀ k, Homotopy (z k^a • 𝟙 F) 0)

def intersectionTensorHomotopy (t : Finset (Fin (n+1))) (ht : t.Nonempty)
    (m : Fin n → ℤ) :
    Homotopy (termTensorMap F (ModuleCat.of R (Sections I z hz t ht (raise m a)))
      (ModuleCat.ofHom (inclusionIter I z hz t ht m a))) 0 := by
  let k := ht.choose
  have hk : k ∈ t := ht.choose_spec
  apply tensorDivisionHomotopy F (z k^a)
    (ModuleCat.ofHom ((downIter I z hz t ht k hk m a).toLinearMap.restrictScalars R)) _ _ (H k)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (inclusionIter_coordinate I z hz t ht k hk m a x).symm

 

def intersectionCechHomotopy (t : Finset (Fin (n+1))) (m : Fin n → ℤ) :
    Homotopy (termTensorMap F (cechObj I z hz (raise m a) t)
      (cechInclusionIterApp I z hz m a t)) 0 := by
  classical
  letI : Fintype (PLift t.Nonempty) := Fintype.ofFinite _
  let Q : PLift t.Nonempty → ModuleCat.{u} R := fun ht =>
    ModuleCat.of R (Sections I z hz t ht.down (raise m a))
  let Q' : PLift t.Nonempty → ModuleCat.{u} R := fun ht =>
    ModuleCat.of R (Sections I z hz t ht.down m)
  exact TensorPi.homotopy (Q := Q) (Q' := Q') F
    (fun ht => ModuleCat.ofHom (inclusionIter I z hz t ht.down m a))
    (fun ht => intersectionTensorHomotopy I z hz F a H t ht.down m)

 

def cechNatTensorHomotopy (m : Fin n → ℤ) (q : ℕ) :
    Homotopy (termTensorMap F ((cech I z hz (raise m a)).X q)
      ((cechInclusionIter I z hz m a).f q)) 0 := by
  classical
  let Q : Set.powersetCard (Fin (n+1)) (q+1) → ModuleCat.{u} R := fun t =>
    cechObj I z hz (raise m a) t.val
  let Q' : Set.powersetCard (Fin (n+1)) (q+1) → ModuleCat.{u} R := fun t =>
    cechObj I z hz m t.val
  exact TensorPi.homotopy (Q := Q) (Q' := Q') F
    (fun t => cechInclusionIterApp I z hz m a t.val)
    (fun t => intersectionCechHomotopy I z hz F a H t.val m)

def cechInclusionZ (m : Fin n → ℤ) (a : ℕ) :
    cechZ I z hz (raise m a) ⟶ cechZ I z hz m :=
  extendMap (cechInclusionIter I z hz m a) ComplexShape.embeddingUpNat

def cechZTensorHomotopy (m : Fin n → ℤ) (q : ℤ) :
    Homotopy (termTensorMap F ((cechZ I z hz (raise m a)).X q)
      ((cechInclusionZ I z hz m a).f q)) 0 := by
  by_cases hq : q < 0
  · apply Homotopy.ofEq
    have hzQ := cechZ_negative I z hz (raise m a) q hq
    have he : (cechInclusionZ I z hz m a).f q=0 := hzQ.eq_of_src _ _
    rw [he,termTensorMap_zero]
  · have heq : (q.toNat:ℤ)=q := by omega
    let e := (cech I z hz (raise m a)).extendXIso ComplexShape.embeddingUpNat heq
    let e' := (cech I z hz m).extendXIso ComplexShape.embeddingUpNat heq
    apply coefficientHomotopyOfIso F e e' _ _ _ (cechNatTensorHomotopy I z hz F a H m q.toNat)
    change e.hom ≫ (cechInclusionIter I z hz m a).f q.toNat =
      (extendMap (cechInclusionIter I z hz m a) ComplexShape.embeddingUpNat).f q ≫ e'.hom
    rw [extendMap_f _ _ heq]
    dsimp only [e,e']
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

variable (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))

 

def enlargedAt (m : Fin n → ℤ) : TotalGhost.Bic (R:=R) :=
  HomologicalComplex₂.flip (((IdealFiltered.functor I F h s hd).mapHomologicalComplex (.up ℤ)).obj
    (cechZ I z hz m))

def enlargedMap {m m' : Fin n → ℤ} (f : cechZ I z hz m ⟶ cechZ I z hz m') :
    enlargedAt I z hz F h s hd m ⟶ enlargedAt I z hz F h s hd m' :=
  (HomologicalComplex₂.flipFunctor _ _ _).map
    (((IdealFiltered.functor I F h s hd).mapHomologicalComplex (.up ℤ)).map f)

 

def enlargedRowHomotopy (m : Fin n → ℤ) :
    TotalGhost.RowHomotopy (enlargedMap I z hz F h s hd (cechInclusionZ I z hz m a)) :=
  TotalGhost.RowHomotopy.ofRows (fun q =>
    IdealFiltered.coefficientNullHomotopy I F h s hd ((cechInclusionZ I z hz m a).f q)
      (cechZTensorHomotopy I z hz F a H m q))

 
lemma enlargedAt_isZero (m : Fin n → ℤ) (p q : ℤ) (hp : IsZero (F.X p)) :
    IsZero (((enlargedAt I z hz F h s hd m).X p).X q) := by
  let Q := (cechZ I z hz m).X q
  exact @IsZero.of_mono (ModuleCat.{u} R) _ _ _ _
    ((IdealFiltered.ambientInclusion I F h s hd Q).f p)
    (IdealFiltered.ambientInclusion_mono I F h s hd Q p)
    (((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R)).flip.obj Q).map_isZero hp)

 
def twistSequence (m : Fin n → ℤ) (a : ℕ) : ℕ → (Fin n → ℤ)
  | 0 => m
  | N+1 => raise (twistSequence m a N) a

lemma twistSequence_apply (m : Fin n → ℤ) (a N : ℕ) (j : Fin n) :
    twistSequence m a N j=m j+(a*N:ℕ) := by
  induction N with
  | zero => simp [twistSequence]
  | succ N ih =>
    simp only [twistSequence,raise_apply,ih,Nat.mul_succ,Nat.cast_add]
    ring

 
def enlargedStep (m : Fin n → ℤ) (a N : ℕ) :
    enlargedAt I z hz F h s hd (twistSequence m a (N+1)) ⟶
      enlargedAt I z hz F h s hd (twistSequence m a N) :=
  enlargedMap I z hz F h s hd (cechInclusionZ I z hz (twistSequence m a N) a)

include H in
 

lemma enlargedPath_homology_zero (m : Fin n → ℤ) (l b : ℤ)
    (hb : ∀ p, p<l ∨ b<p → IsZero (F.X p)) (N : ℕ) (hN : b-l<(N:ℤ)) (i : ℤ) :
    homologyMap (HomologicalComplex₂.total.map
      (TotalGhost.towerPath (X:=fun N => enlargedAt I z hz F h s hd (twistSequence m a N))
        (enlargedStep I z hz F h s hd m a) N) (.up ℤ)) i=0 := by
  exact TotalGhost.homologyMap_path_eq_zero
    (X:=fun N => enlargedAt I z hz F h s hd (twistSequence m a N))
    (enlargedStep I z hz F h s hd m a)
    (fun N => enlargedRowHomotopy I z hz F a H h s hd (twistSequence m a N)) N l b hN
    (fun p q hp => enlargedAt_isZero I z hz F h s hd _ p q (hb p (Or.inr hp)))
    (fun p q hp => enlargedAt_isZero I z hz F h s hd _ p q (hb p (Or.inl hp))) i

 

theorem uniform_enlarged_nilpotence
    (hp : ∀ p,Module.Projective R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (ha : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ a : ℕ, 0<a ∧ ∀ m : Fin n → ℤ, ∀ i : ℤ,
      homologyMap (HomologicalComplex₂.total.map
        (TotalGhost.towerPath (X:=fun N => enlargedAt I z hz F h s hd (twistSequence m a N))
          (enlargedStep I z hz F h s hd m a) (h+1)) (.up ℤ)) i=0 := by
  obtain ⟨a,Ha⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F (-(h:ℤ)) 0 hp hfin hb ha
  let H : ∀ k,Homotopy (z k^(a+1) • 𝟙 F) 0 := fun k =>
    Koszul.scalarPowerHomotopy F (z k) a (a+1) (by omega) (Ha k).some
  exact ⟨a+1,by omega,fun m i => enlargedPath_homology_zero I z hz F (a+1) H h s hd
    m (-(h:ℤ)) 0 hb (h+1) (by omega) i⟩

end Lech.ReesRoot

end

end OAI
