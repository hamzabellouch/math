import Mathlib
import OAI.RingTheory.Multiplicity.FilteredCechAugmented
import OAI.RingTheory.Multiplicity.HomogeneousRegradeIdentity

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable {K L : Bic (R := R)} {f : K ⟶ L}

lemma row_hom_transport (q r s t : ℤ) (hst : s=t)
    (H : Homotopy (((HomologicalComplex₂.flipFunctor _ _ _).map f).f q) 0) :
    H.hom r s ≫ (L.XXIsoOfEq _ _ _ hst rfl).hom = H.hom r t := by
  subst t
  simp only [XXIsoOfEq_rfl,Iso.refl_hom]
  exact Category.comp_id _

 

def RowHomotopy.ofRows
    (H : ∀ q, Homotopy (((HomologicalComplex₂.flipFunctor _ _ _).map f).f q) 0) : RowHomotopy f where
  h p q := (H q).hom p (p-1)
  equation p q := by
    have hh := (H q).comm p
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p-1) p by change p-1+1=p; omega),
      zero_f,add_zero] at hh
    exact hh.trans (congrArg (fun t : (K.X (p+1)).X q ⟶ (L.X p).X q =>
      (K.d p (p+1)).f q ≫ t +
      (show (K.X p).X q ⟶ (L.X (p-1)).X q from (H q).hom p (p-1)) ≫ (L.d (p-1) p).f q)
        (row_hom_transport q (p+1) (p+1-1) p (by omega) (H q)).symm)
end Lech.TotalGhost


namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable {K L M : Bic (R := R)}

 

def Shifted (n : ℕ) (f : K.total (ComplexShape.up ℤ) ⟶ L.total (ComplexShape.up ℤ)) : Prop :=
  ∀ p q i : ℤ, ∀ hpq : p+q=i,
    ∃ p' q' : ℤ, p'+(n:ℤ)=p ∧ q'=q+(n:ℤ) ∧
      ∃ hp'q' : p'+q'=i, ∃ a : (K.X p).X q ⟶ (L.X p').X q',
        K.ιTotal (ComplexShape.up ℤ) p q i hpq ≫ f.f i =
          a ≫ L.ιTotal (ComplexShape.up ℤ) p' q' i hp'q'

lemma shifted_identity (K : Bic (R := R)) : Shifted 0 (𝟙 (K.total (ComplexShape.up ℤ))) := by
  intro p q i hpq
  refine ⟨p,q,by simp,by simp,hpq,𝟙 _,?_⟩
  simp

lemma shifted_comp {f : K.total (ComplexShape.up ℤ) ⟶ L.total (ComplexShape.up ℤ)}
    {g : L.total (ComplexShape.up ℤ) ⟶ M.total (ComplexShape.up ℤ)}
    {n m : ℕ} (hf : Shifted n f) (hg : Shifted m g) : Shifted (n+m) (f≫g) := by
  intro p q i hpq
  obtain ⟨p',q',hp',hq',hp'q',a,ha⟩ := hf p q i hpq
  obtain ⟨p'',q'',hp'',hq'',hp''q'',b,hb⟩ := hg p' q' i hp'q'
  refine ⟨p'',q'',by push_cast; omega,by push_cast; omega,hp''q'',a≫b,?_⟩
  rw [comp_f,←Category.assoc,ha,Category.assoc,hb,Category.assoc]

lemma shifted_correction {f : K ⟶ L} (h : RowHomotopy f) : Shifted 1 (correction h) := by
  intro p q i hpq
  obtain ⟨a,ha⟩ := correction_lowers h p q i hpq
  exact ⟨p-1,q+1,by norm_num,by norm_num,by omega,a,ha⟩

 

lemma shifted_eq_zero {f : K.total (ComplexShape.up ℤ) ⟶ L.total (ComplexShape.up ℤ)}
    {n : ℕ} (hf : Shifted n f) (l b : ℤ)
    (hK : ∀ p q, b<p → IsZero ((K.X p).X q))
    (hL : ∀ p q, p<l → IsZero ((L.X p).X q)) (hn : b-l<(n:ℤ)) : f=0 := by
  apply HomologicalComplex.hom_ext
  intro i
  apply total.hom_ext
  intro p q hpq
  change p+q=i at hpq
  by_cases hp : b<p
  · exact (hK p q hp).eq_of_src _ _
  obtain ⟨p',q',hp',_,hp'q',a,ha⟩ := hf p q i hpq
  have hp'l : p'<l := by omega
  rw [ha,(hL p' q' hp'l).eq_of_tgt a 0]
  simp

 
def towerPath {C : Type*} [Category C] {X : ℕ → C} (f : ∀ n, X (n+1) ⟶ X n) : ∀ n, X n ⟶ X 0
  | 0 => 𝟙 _
  | n+1 => f n ≫ towerPath f n

lemma homologyMap_path {X : ℕ → Bic (R := R)} (f : ∀ n, X (n+1) ⟶ X n)
    (h : ∀ n, RowHomotopy (f n)) (n : ℕ) (i : ℤ) :
    homologyMap (towerPath (X := fun n => (X n).total (ComplexShape.up ℤ)) (fun n => correction (h n)) n) i =
      homologyMap (total.map (towerPath f n) (ComplexShape.up ℤ)) i := by
  induction n with
  | zero => simp [towerPath]
  | succ n ih =>
    simp only [towerPath,homologyMap_comp,homologyMap_correction,ih,total.map_comp]

lemma shifted_path {X : ℕ → Bic (R := R)} (f : ∀ n, X (n+1) ⟶ X n)
    (h : ∀ n, RowHomotopy (f n)) (n : ℕ) :
    Shifted n (towerPath (X := fun n => (X n).total (ComplexShape.up ℤ)) (fun n => correction (h n)) n) := by
  induction n with
  | zero => exact shifted_identity _
  | succ n ih =>
    simpa only [towerPath,Nat.add_comm 1 n] using shifted_comp (shifted_correction (h n)) ih

 

lemma homologyMap_path_eq_zero {X : ℕ → Bic (R := R)} (f : ∀ n, X (n+1) ⟶ X n)
    (h : ∀ n, RowHomotopy (f n)) (n : ℕ) (l b : ℤ)
    (hn : b-l<(n:ℤ))
    (hXn : ∀ p q, b<p → IsZero (((X n).X p).X q))
    (hX0 : ∀ p q, p<l → IsZero (((X 0).X p).X q)) (i : ℤ) :
    homologyMap (total.map (towerPath f n) (ComplexShape.up ℤ)) i=0 := by
  rw [←homologyMap_path f h n i,shifted_eq_zero (shifted_path f h n) l b hXn hX0 hn]
  simp only [homologyMap_zero]
end Lech.TotalGhost


namespace Lech.TotalGhost
open CategoryTheory
universe u v w u' v' w'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

lemma towerPath_map {X : ℕ → C} (f : ∀ n, X (n+1) ⟶ X n) (G : C ⥤ D) (n : ℕ) :
    towerPath (X := fun n => G.obj (X n)) (fun n => G.map (f n)) n=G.map (towerPath f n) := by
  induction n with
  | zero => exact (G.map_id _).symm
  | succ n ih => simpa only [towerPath,Functor.map_comp] using congrArg (fun g => G.map (f n) ≫ g) ih
end Lech.TotalGhost


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

def tensorBic : CochainComplex (ModuleCat.{u} R) ℤ ⥤ TotalGhost.Bic (R := R) :=
  ((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj F

lemma tensorBic_total_map {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    HomologicalComplex₂.total.map ((tensorBic F).map f) (.up ℤ)=
      (TensorTotal.Right.functor F).map f := by
  unfold tensorBic
  change _ = HomologicalComplex₂.total.map (_ ≫ _) _
  rw [((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).map_id F]
  rw [NatTrans.id_app,Category.id_comp]

lemma tensorBic_isZero (K : CochainComplex (ModuleCat.{u} R) ℤ) (p q : ℤ)
    (hp : IsZero (F.X p)) : IsZero ((((tensorBic F).obj K).X p).X q) :=
  ((curriedTensor (ModuleCat.{u} R)).flip.obj (K.X q)).map_isZero hp

variable (m : ℕ) (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)

def bicRowHomotopy (t : ℕ) :
    TotalGhost.RowHomotopy ((tensorBic F).map (positiveInclusion I z hz (Nat.le_add_right t m))) :=
  TotalGhost.RowHomotopy.ofRows (positiveRowHomotopy I z hz F m H t)

def bicRowHomotopyAt (s t : ℕ) (he : t=s+m) :
    TotalGhost.RowHomotopy ((tensorBic F).map
      (positiveInclusion I z hz (by omega : s ≤ t))) := by
  subst t
  exact bicRowHomotopy I z hz F m H s

def twistStep (t n : ℕ) : positive I z hz (t+m*(n+1)) ⟶ positive I z hz (t+m*n) :=
  positiveInclusion I z hz (by rw [Nat.mul_succ]; omega)

lemma twistPath (t N : ℕ) :
    TotalGhost.towerPath (X := fun n => positive I z hz (t+m*n))
      (twistStep I z hz m t) N =
      positiveInclusion I z hz (show t ≤ t+m*N by omega) := by
  induction N with
  | zero =>
    simp only [Nat.mul_zero,Nat.add_zero,TotalGhost.towerPath,positiveInclusion_refl]
  | succ N ih =>
    rw [TotalGhost.towerPath,ih]
    exact positiveInclusion_comp I z hz _ _

include H in
 

lemma positive_homologyMap_zero (l b : ℤ)
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j)) (N : ℕ) (hN : b-l<(N:ℤ))
    (t : ℕ) (i : ℤ) :
    homologyMap ((TensorTotal.Right.functor F).map
      (positiveInclusion I z hz (show t≤t+m*N by omega))) i=0 := by
  let X : ℕ → TotalGhost.Bic (R := R) := fun n => (tensorBic F).obj (positive I z hz (t+m*n))
  let f : ∀ n, X (n+1) ⟶ X n := fun n => (tensorBic F).map (twistStep I z hz m t n)
  have hrow : ∀ n, TotalGhost.RowHomotopy (f n) := by
    intro n
    exact bicRowHomotopyAt I z hz F m H (t+m*n) (t+m*(n+1))
      (by rw [Nat.mul_succ,Nat.add_assoc])
  have hh := TotalGhost.homologyMap_path_eq_zero f hrow N l b hN
    (fun p q hp => tensorBic_isZero F _ p q (hb p (Or.inr hp)))
    (fun p q hp => tensorBic_isZero F _ p q (hb p (Or.inl hp))) i
  dsimp only [f] at hh
  have he := TotalGhost.towerPath_map (X := fun n => positive I z hz (t+m*n))
    (twistStep I z hz m t) (tensorBic F) N
  rw [he,twistPath,tensorBic_total_map] at hh
  exact hh
end Lech.FilteredCech

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace Lech
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

 
noncomputable def baseChangeFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id _ := by apply ModuleCat.hom_ext; simp
  map_comp _ _ := by apply ModuleCat.hom_ext; exact LinearMap.baseChange_comp _ _

instance baseChangeFunctor_additive : (baseChangeFunctor R S).Additive where
  map_add := by intros; apply ModuleCat.hom_ext; exact LinearMap.baseChange_add _ _

 
noncomputable def baseChangeHomEquiv (M N : ModuleCat.{u} R) :
    (S ⊗[R] M →ₗ[S] S ⊗[R] N) ≃ₗ[R]
      ((baseChangeFunctor R S).obj M ⟶ (baseChangeFunctor R S).obj N) where
  toFun f := ModuleCat.ofHom f
  invFun f := f.hom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (IsScalarTower.algebraMap_smul S r (f x)).symm

instance baseChangeFunctor_linear : (baseChangeFunctor R S).Linear R where
  map_smul {M N} f r := by
    change baseChangeHomEquiv R S M N ((r • f.hom).baseChange S) = _
    rw [LinearMap.baseChange_smul, map_smul]
    rfl

variable {R S}
lemma baseChangeHom_isBaseChange (M N : ModuleCat.{u} R)
    [Module.Free R M] [Module.Finite R M] :
    IsBaseChange S (LinearMap.baseChangeHom R S M N) := by
  have h := (TensorProduct.isBaseChange R M S).linearMapLeftRight
    (TensorProduct.isBaseChange R N S)
  convert h using 1
  apply LinearMap.ext
  intro f
  apply (TensorProduct.isBaseChange R M S).algHom_ext
  intro m
  exact (IsBaseChange.linearMapLeftRightHom_comp_apply (TensorProduct.isBaseChange R M S) (TensorProduct.mk R S N 1) f m).symm

instance baseChangeFunctor_map_localized (U : Submonoid R) [IsLocalization U S]
    (M N : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    IsLocalizedModule U ((baseChangeFunctor R S).mapLinearMap R (X := M) (Y := N)) := by
  have : IsLocalizedModule U (LinearMap.baseChangeHom R S M N) :=
    (isLocalizedModule_iff_isBaseChange U S _).mpr (baseChangeHom_isBaseChange M N)
  change IsLocalizedModule U ((baseChangeHomEquiv R S M N).toLinearMap ∘ₗ
    LinearMap.baseChangeHom R S M N ∘ₗ
      (ModuleCat.homLinearEquiv (M := M) (N := N) (S := R)).toLinearMap)
  infer_instance

end Lech

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
namespace Lech
universe u
variable {R : Type u} [CommRing R]

 
lemma baseChange_contractible (S : Type u) [CommRing S] [Algebra R S]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hf : ∀ j, Module.Free R (F.X j))
    (hb : ∀ j, b < j → IsZero (F.X j))
    (ha : ((baseChangeFunctor R S).mapHomologicalComplex _ |>.obj F).Acyclic) :
    Nonempty (Homotopy (𝟙 ((baseChangeFunctor R S).mapHomologicalComplex _ |>.obj F)) 0) := by
  let T := baseChangeFunctor R S
  let L : CochainComplex (ModuleCat.{u} S) ℤ := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  have : L.IsStrictlyLE b := by
    rw [isStrictlyLE_iff]
    intro i hi
    exact T.map_isZero (hb i hi)
  have (i : ℤ) : Projective (L.X i) := by
    have := hf i
    change Projective (ModuleCat.of S (S ⊗[R] F.X i))
    infer_instance
  have : L.IsKProjective := isKProjective_of_projective L b
  exact IsKProjective.nonempty_homotopy_zero (𝟙 L) ha

end Lech


namespace Lech
open scoped TensorProduct
section Retract
variable {R : Type*} [CommRing R] (S : Submonoid R)
  {M N M' N' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  (f : M →ₗ[R] M') (g : N →ₗ[R] N')
  (i : M →ₗ[R] N) (p : N →ₗ[R] M)
  (i' : M' →ₗ[R] N') (p' : N' →ₗ[R] M')
  (hpi : p.comp i = LinearMap.id) (hp'i' : p'.comp i' = LinearMap.id)
  (hgi : g.comp i = i'.comp f) (hfp : f.comp p = p'.comp g)
  [IsLocalizedModule S g]

include hpi hp'i' hgi hfp in
 
lemma localizedModule_retract : IsLocalizedModule S f where
  map_units s := by
    apply (Module.End.isUnit_iff _).mpr
    have hs := (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)
    have hi := LinearMap.injective_of_comp_eq_id i' p' hp'i'
    constructor
    · intro x y h
      apply hi
      apply hs.1
      simpa only [Module.algebraMap_end_apply,←map_smul] using congrArg i' h
    · intro x
      obtain ⟨n,hn⟩ := hs.2 (i' x)
      refine ⟨p' n,?_⟩
      change (s : R) • p' n = x
      have hh := congrArg p' hn
      simp only [Module.algebraMap_end_apply, map_smul] at hh
      exact hh.trans (LinearMap.congr_fun hp'i' x)
  surj x := by
    obtain ⟨⟨n,s⟩,hn⟩ := IsLocalizedModule.surj S g (i' x)
    refine ⟨⟨p n,s⟩,?_⟩
    have hh := congrArg p' hn
    simpa only [Submonoid.smul_def,map_smul,←LinearMap.comp_apply,hp'i',
      LinearMap.id_apply,←hfp] using hh
  exists_of_eq {x y} h := by
    have hh : g (i x) = g (i y) := by
      change (g.comp i) x = (g.comp i) y
      rw [hgi]
      exact congrArg i' h
    obtain ⟨s,hs⟩ := IsLocalizedModule.exists_of_eq (S := S) hh
    refine ⟨s,?_⟩
    have he := congrArg p hs
    simpa only [Submonoid.smul_def,map_smul,←LinearMap.comp_apply,hpi,
      LinearMap.id_apply] using he
end Retract

open CategoryTheory
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (M : Type*) [AddCommGroup M] [Module R M]
  [Module.Projective R M] [Module.Finite R M]

lemma projective_baseChange : Module.Projective A (A ⊗[R] M) := by
  obtain ⟨n,p,i,_,_,hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact Module.Projective.of_split (i.baseChange A) (p.baseChange A)
    (by rw [←LinearMap.baseChange_comp,hpi,LinearMap.baseChange_id])

end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

def precompLinear {M N P : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) : (N →ₗ[R] P) →ₗ[R] (M →ₗ[R] P) where
  toFun g := g.comp f
  map_add' g h := by ext; rfl
  map_smul' r g := by ext; rfl

lemma baseChangeHom_localized_projective (U : Submonoid R) [IsLocalization U A]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R M] [Module.Finite R M] :
    IsLocalizedModule U (LinearMap.baseChangeHom R A M N) := by
  obtain ⟨n,p,i,_,_,hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hfree : IsLocalizedModule U (LinearMap.baseChangeHom R A (Fin n → R) N) :=
    (isLocalizedModule_iff_isBaseChange U A _).mpr
      (baseChangeHom_isBaseChange (ModuleCat.of R (Fin n → R)) (ModuleCat.of R N))
  apply localizedModule_retract U (LinearMap.baseChangeHom R A M N)
    (LinearMap.baseChangeHom R A (Fin n → R) N)
    (precompLinear p) (precompLinear i)
    ((precompLinear (p.baseChange A)).restrictScalars R)
    ((precompLinear (i.baseChange A)).restrictScalars R)
  · ext f x
    change f (p (i x)) = f x
    exact congrArg f (LinearMap.congr_fun hpi x)
  · apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    change f ((p.baseChange A) ((i.baseChange A) x)) = f x
    have h : (p.baseChange A).comp (i.baseChange A) = LinearMap.id := by
      rw [←LinearMap.baseChange_comp,hpi,LinearMap.baseChange_id]
    exact congrArg f (LinearMap.congr_fun h x)
  · apply LinearMap.ext
    intro f
    change (f.comp p).baseChange A = (f.baseChange A).comp (p.baseChange A)
    exact LinearMap.baseChange_comp p f
  · apply LinearMap.ext
    intro f
    change (f.comp i).baseChange A = (f.baseChange A).comp (i.baseChange A)
    exact LinearMap.baseChange_comp i f

lemma baseChangeFunctor_map_localized_projective (U : Submonoid R) [IsLocalization U A]
    (M N : ModuleCat.{u} R) [Module.Projective R M] [Module.Finite R M] :
    IsLocalizedModule U ((baseChangeFunctor R A).mapLinearMap R (X := M) (Y := N)) := by
  have := baseChangeHom_localized_projective (A := A) U M N
  change IsLocalizedModule U ((baseChangeHomEquiv R A M N).toLinearMap ∘ₗ
    LinearMap.baseChangeHom R A M N ∘ₗ
      (ModuleCat.homLinearEquiv (M := M) (N := N) (S := R)).toLinearMap)
  infer_instance

 

lemma baseChange_projective_contractible (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : ℤ) (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, b < j → IsZero (F.X j))
    (ha : ((baseChangeFunctor R A).mapHomologicalComplex _ |>.obj F).Acyclic) :
    Nonempty (Homotopy (𝟙 ((baseChangeFunctor R A).mapHomologicalComplex _ |>.obj F)) 0) := by
  let T := baseChangeFunctor R A
  let L : CochainComplex (ModuleCat.{u} A) ℤ := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  have : L.IsStrictlyLE b := by
    rw [isStrictlyLE_iff]
    intro i hi
    exact T.map_isZero (hb i hi)
  have (i : ℤ) : Projective (L.X i) := by
    have := hp i
    have := hfin i
    have := projective_baseChange (R := R) (A := A) (F.X i)
    change Projective (ModuleCat.of A (A ⊗[R] F.X i))
    infer_instance
  have : L.IsKProjective := isKProjective_of_projective L b
  exact IsKProjective.nonempty_homotopy_zero (𝟙 L) ha
end Lech
end

end OAI
