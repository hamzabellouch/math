import OAI.RingTheory.Tachikawa.Triangular

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P Q : ChainComplex (ModuleCat R) ℤ)

namespace CokerAt

def mapLinear (n : ℤ) : (P ⟶ Q) →ₗ[k] (CokerAt P n →ₗ[R] CokerAt Q n) where
  toFun f := map f n
  map_add' f g := by
    ext x
    obtain ⟨y,rfl⟩ := π_surjective P n x
    rfl
  map_smul' c f := by
    ext x
    obtain ⟨y,rfl⟩ := π_surjective P n x
    rfl

end CokerAt

namespace FullHomComparison

def toStable : (P ⟶ Q) →ₗ[k]
    StableHom (k := k) (R := R) (M := CokerAt P 0) (N := CokerAt Q 0) :=
  (projectiveFactors (k := k)).mkQ.comp (CokerAt.mapLinear P Q 0)

def toHomotopy : (P ⟶ Q) →ₗ[k]
    ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.down ℤ)).obj P ⟶
      (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.down ℤ)).obj Q) :=
  (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.down ℤ)).mapLinearMap k

lemma toStable_surjective (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j)) :
    Function.Surjective (toStable P Q (k := k)) := by
  intro x
  obtain ⟨u,rfl⟩ := (projectiveFactors (k := k)).mkQ_surjective x
  obtain ⟨f,hf⟩ := exists_complete_lift P Q hp hq pproj qfin qproj u
  exact ⟨f,congrArg (projectiveFactors (k := k)).mkQ hf⟩

lemma kernel_eq (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (pfin : Module.Finite R (P.X (-1)))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j)) :
    LinearMap.ker (toHomotopy P Q (k := k)) = LinearMap.ker (toStable P Q (k := k)) := by
  ext f
  change (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.down ℤ)).map f = 0 ↔
    (projectiveFactors (k := k)).mkQ (CokerAt.map f 0) = 0
  rw [HomotopyCategory.quotient_map_eq_zero_iff]
  change Nonempty (Homotopy f 0) ↔ Submodule.Quotient.mk (CokerAt.map f 0) = (0 : StableHom (k := k))
  erw [Submodule.Quotient.mk_eq_zero]
  exact nullhomotopic_iff_coker_factors f hp hq pproj pfin qfin qproj

def equiv (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (pfin : Module.Finite R (P.X (-1)))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j)) :
    ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.down ℤ)).obj P ⟶
      (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.down ℤ)).obj Q) ≃ₗ[k]
      StableHom (k := k) (R := R) (M := CokerAt P 0) (N := CokerAt Q 0) := by
  let e := (toHomotopy P Q (k := k)).quotKerEquivOfSurjective
    (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.down ℤ)).map_surjective
  let e' := (toStable P Q (k := k)).quotKerEquivOfSurjective
    (toStable_surjective P Q hp hq pproj qfin qproj)
  have hk := kernel_eq (k := k) P Q hp hq pproj pfin qfin qproj
  exact e.symm.trans ((Submodule.quotEquivOfEq _ _ hk).trans e')

end FullHomComparison
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace CompleteTranslate

abbrev complex (P : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ) :
    ChainComplex (ModuleCat.{0} R) ℤ where
  X i := P.X (i+a)
  d i j := P.d (i+a) (j+a)
  shape i j h := P.shape _ _ (by
    intro he
    apply h
    change j+1=i
    change j+a+1=i+a at he
    omega)
  d_comp_d' i j l _ _ := P.d_comp_d _ _ _

lemma exact (P : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ)
    (hP : ComplexExact P) : ComplexExact (complex P a) := by
  intro j
  change Function.Exact (P.d (j+1+a) (j+a)) (P.d (j+a) (j-1+a))
  rw [show j+1+a=j+a+1 by omega, show j-1+a=j+a-1 by omega]
  exact hP (j+a)
lemma totallyAcyclic (P : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ)
    (hP : TotallyAcyclic P) : TotallyAcyclic (complex P a) := by
  refine ⟨exact P a hP.1,?_⟩
  intro j f hf
  change f.comp (P.d (j+1+a) (j+a)).hom = 0 at hf
  change ∃ g : P.X (j-1+a) →ₗ[R] R, g.comp (P.d (j+a) (j-1+a)).hom = f
  rw [show j+1+a=j+a+1 by omega] at hf
  rw [show j-1+a=j+a-1 by omega]
  exact hP.2 (j+a) f hf

def map {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q) (a : ℤ) :
    complex P a ⟶ complex Q a where
  f j := f.f (j+a)
  comm' i j _ := f.comm (i+a) (j+a)

def cokerEquiv (P : ChainComplex (ModuleCat.{0} R) ℤ) (a : ℤ) :
    CokerAt (complex P a) 0 ≃ₗ[R] CokerAt P a := by
  change (P.X (0+a) ⧸ LinearMap.range (P.d (0+1+a) (0+a)).hom) ≃ₗ[R]
    (P.X a ⧸ LinearMap.range (P.d (a+1) a).hom)
  rw [show (0:ℤ)+a=a by omega, show (0:ℤ)+1+a=a+1 by omega]

end CompleteTranslate
end Tachikawa



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P Q : ChainComplex (ModuleCat.{0} R) ℤ)

abbrev Cochain (a : ℤ) := ∀ (i j : ℤ), i = j+a → (P.X i ⟶ Q.X j)

variable {P Q}
def Closed {a : ℤ} (f : Cochain P Q a) : Prop :=
  ∀ i j l m (hij : i=j+a) (hlm : l=m+a),
    f i j hij ≫ Q.d j m = P.d i l ≫ f l m hlm

lemma transport_left {a i i' j : ℤ} (f : Cochain P Q a) (h : i=i') (he : i'=j+a) :
    (P.XIsoOfEq h).hom ≫ f i' j he = f i j (h.trans he) := by
  subst i'; simp
lemma transport_right {a i j j' : ℤ} (f : Cochain P Q a) (h : j=j') (he : i=j+a) :
    f i j he ≫ (Q.XIsoOfEq h).hom = f i j' (by omega) := by
  subst j'; simp

lemma d_pre_eq {a : ℤ} (f : Cochain P Q a) (p i i' j : ℤ)
    (he : i=i') (hi : i=j+a) (hi' : i'=j+a) :
    P.d p i ≫ f i j hi = P.d p i' ≫ f i' j hi' := by
  subst i'; rfl
lemma d_post_eq {a : ℤ} (f : Cochain P Q a) (i j j' q : ℤ)
    (he : j=j') (hi : i=j+a) (hi' : i=j'+a) :
    f i j hi ≫ Q.d j q = f i j' hi' ≫ Q.d j' q := by
  subst j'; rfl

variable (P Q) in
def ofChain {a : ℤ} (f : CompleteTranslate.complex P a ⟶ Q) : Cochain P Q a :=
  fun _i j h => (P.XIsoOfEq h).hom ≫ f.f j

lemma ofChain_closed {a : ℤ} (f : CompleteTranslate.complex P a ⟶ Q) :
    Closed (ofChain P Q f) := by
  intro i j l m hij hlm
  subst i; subst l
  change (P.XIsoOfEq rfl).hom ≫ f.f j ≫ Q.d j m =
    P.d (j+a) (m+a) ≫ (P.XIsoOfEq rfl).hom ≫ f.f m
  simpa only [XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp] using f.comm j m

def toChain {a : ℤ} (f : Cochain P Q a) (hf : Closed f) :
    CompleteTranslate.complex P a ⟶ Q where
  f j := f (j+a) j rfl
  comm' i j _ := hf (i+a) i (j+a) j rfl rfl

@[simp] lemma to_ofChain {a : ℤ} (f : CompleteTranslate.complex P a ⟶ Q) :
    toChain (ofChain P Q f) (ofChain_closed f) = f := by
  ext j; simp [toChain,ofChain]
@[simp] lemma of_toChain {a : ℤ} (f : Cochain P Q a) (hf : Closed f) :
    ofChain P Q (toChain f hf) = f := by
  funext i j h
  subst i
  simp [ofChain,toChain]

def Boundary {a : ℤ} (f : Cochain P Q a) : Prop :=
  ∃ h : Cochain P Q (a-1), ∀ i j (he : i=j+a),
    f i j he = P.d i (i-1) ≫ h (i-1) j (by omega) +
      h i (j+1) (by omega) ≫ Q.d (j+1) j

lemma ofHomotopy_boundary {a : ℤ} {f : CompleteTranslate.complex P a ⟶ Q}
    (h : Homotopy f 0) : Boundary (ofChain P Q f) := by
  let c : Cochain P Q (a-1) := fun i j he =>
    (P.XIsoOfEq (show i=(j-1)+a by omega)).hom ≫ h.hom (j-1) j
  refine ⟨c,?_⟩
  intro i j he
  subst i
  simp only [ofChain,XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp]
  have hh := h.comm j
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)] at hh
  simp only [zero_f,add_zero] at hh
  dsimp only [CompleteTranslate.complex] at hh
  change f.f j = P.d (j+a) (j-1+a) ≫ h.hom (j-1) j + h.hom j (j+1) ≫ Q.d (j+1) j at hh
  have ht (p p' q : ℤ) (he : p=p') :
      (P.XIsoOfEq (congrArg (fun t => t+a) he)).hom ≫ h.hom p' q = h.hom p q := by
    subst p'; simp
  dsimp only [c]
  rw [← Category.assoc,HomologicalComplex.d_comp_XIsoOfEq_hom]
  rw [ht j (j+1-1) (j+1) (by omega)]
  exact hh

lemma boundary_homotopy {a : ℤ} (f : Cochain P Q a) (hf : Closed f)
    (hb : Boundary f) : Nonempty (Homotopy (toChain f hf) 0) := by
  obtain ⟨c,hc⟩ := hb
  classical
  let h : ∀ p q, (CompleteTranslate.complex P a).X p ⟶ Q.X q :=
    fun p q => if he : q=p+1 then c (p+a) q (by omega) else 0
  refine ⟨{ hom := h, zero := ?_, comm := ?_ }⟩
  · intro p q hpq
    change ¬ p+1=q at hpq
    simp only [h,dite_eq_right (Ne.symm hpq)]
  · intro j
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)]
    simp only [toChain,zero_f,add_zero,h,dite_eq_left (show j=j-1+1 by omega),dite_eq_left rfl]
    have hr := hc (j+a) j rfl
    rw [d_pre_eq c (j+a) (j+a-1) (j-1+a) j (by omega) _ _] at hr
    exact hr

end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {P Q S : ChainComplex (ModuleCat.{0} R) ℤ}
structure Index (a : ℤ) where
  i : ℤ
  j : ℤ
  h : i=j+a

def indexEquiv (a : ℤ) : Cochain P Q a ≃ (∀ t : Index a, P.X t.i ⟶ Q.X t.j) where
  toFun f t := f t.i t.j t.h
  invFun f i j h := f ⟨i,j,h⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance (a : ℤ) : AddCommGroup (Cochain P Q a) := (indexEquiv a).addCommGroup
instance (a : ℤ) : Module k (Cochain P Q a) :=
  AddEquiv.module k { toEquiv := indexEquiv a, map_add' := fun _ _ => rfl }

@[simp] lemma zero_apply {a : ℤ} (i j : ℤ) (h : i=j+a) :
    (0 : Cochain P Q a) i j h = 0 := rfl
@[simp] lemma add_apply {a : ℤ} (f g : Cochain P Q a) (i j : ℤ) (h : i=j+a) :
    (f+g) i j h = f i j h+g i j h := rfl

lemma twice {V : Type*} [AddCommGroup V] [Module k V] (v : V) : v+v=0 := by
  rw [← two_smul k]
  have hz : (2:k)=0 := CharP.cast_eq_zero k 2
  rw [hz,zero_smul]
lemma negative {V : Type*} [AddCommGroup V] [Module k V] (v : V) : -v=v :=
  (neg_eq_iff_add_eq_zero).mpr (twice (k := k) v)

lemma closed_zero (a : ℤ) : Closed (0 : Cochain P Q a) := by
  intro i j l m hij hlm; simp
lemma closed_add {a : ℤ} {f g : Cochain P Q a} (hf : Closed f) (hg : Closed g) :
    Closed (f+g) := by
  intro i j l m hij hlm
  change (f i j hij+g i j hij) ≫ _ = _ ≫ (f l m hlm+g l m hlm)
  rw [add_comp,comp_add,hf,hg]
lemma closed_of_adjacent {a : ℤ} (f : Cochain P Q a)
    (hf : ∀ i j (h : i=j+a), f i j h ≫ Q.d j (j-1) = P.d i (i-1) ≫ f (i-1) (j-1) (by omega)) :
    Closed f := by
  intro i j l m hij hlm
  by_cases he : m+1=j
  · have hl : l=i-1 := by omega
    subst l
    have hm : m=j-1 := by omega
    subst m
    exact (hf i j hij).trans (d_pre_eq f i (i-1) (j-1+a) (j-1) (by omega) _ _)
  · rw [Q.shape _ _ he,P.shape _ _ (by change ¬ l+1=i; omega),comp_zero,zero_comp]

def diff {a : ℤ} (f : Cochain P Q (a-1)) : Cochain P Q a := fun i j he =>
  P.d i (i-1) ≫ f (i-1) j (by omega) + f i (j+1) (by omega) ≫ Q.d (j+1) j

lemma diff_add {a : ℤ} (f g : Cochain P Q (a-1)) : diff (f+g) = diff f+diff g := by
  funext i j he
  simp only [add_apply,diff,comp_add,add_comp]
  abel
lemma diff_closed {a : ℤ} (f : Cochain P Q (a-1)) : Closed (diff f) := by
  apply closed_of_adjacent
  intro i j he
  dsimp only [diff]
  rw [add_comp,comp_add,Category.assoc,Category.assoc,Q.d_comp_d,comp_zero,
    ← Category.assoc (P.d i (i-1)) (P.d (i-1) (i-1-1)),P.d_comp_d,zero_comp,add_zero,zero_add]
  exact congrArg (fun t => P.d i (i-1) ≫ t)
    (d_post_eq f (i-1) j (j-1+1) (j-1) (by omega) _ _)

lemma boundary_diff {a : ℤ} (f : Cochain P Q (a-1)) : Boundary (diff f) := by
  refine ⟨fun i j he => f i j (by omega),?_⟩
  intros; rfl
lemma boundary_add {a : ℤ} {f g : Cochain P Q a} (hf : Boundary f) (hg : Boundary g) :
    Boundary (f+g) := by
  obtain ⟨s,hs⟩ := hf
  obtain ⟨t,ht⟩ := hg
  refine ⟨s+t,?_⟩
  intro i j he
  change f i j he+g i j he = _ ≫ (s _ _ _+t _ _ _) + (s _ _ _+t _ _ _) ≫ _
  rw [hs,ht,comp_add,add_comp]
  abel
lemma boundary_zero (a : ℤ) : Boundary (0 : Cochain P Q a) := by
  refine ⟨0,?_⟩; intros; simp

lemma boundary_iff_diff {a : ℤ} (f : Cochain P Q a) :
    Boundary f ↔ ∃ h : Cochain P Q (a-1), f = diff h := by
  constructor
  · rintro ⟨h,hh⟩
    exact ⟨h,funext fun i => funext fun j => funext fun he => hh i j he⟩
  · rintro ⟨h,rfl⟩; exact boundary_diff h

include k in
lemma closed_iff_diff_zero {a : ℤ} (f : Cochain P Q (a-1)) :
    Closed f ↔ diff f = 0 := by
  constructor
  · intro hf
    funext i j he
    change P.d i (i-1) ≫ f (i-1) j _ + f i (j+1) _ ≫ Q.d (j+1) j = 0
    rw [hf i (j+1) (i-1) j (by omega) (by omega)]
    exact twice (k := k) _
  · intro hf
    apply closed_of_adjacent
    intro i j he
    have hh := congrFun (congrFun (congrFun hf i) (j-1)) (by omega)
    change P.d i (i-1) ≫ f (i-1) (j-1) _ + f i (j-1+1) _ ≫ Q.d (j-1+1) (j-1) = 0 at hh
    rw [d_post_eq f i (j-1+1) j (j-1) (by omega) _ he] at hh
    exact (eq_neg_of_add_eq_zero_right hh).trans (negative (k := k) _)

def pre (u : S ⟶ P) {a : ℤ} (f : Cochain P Q a) : Cochain S Q a :=
  fun i j he => u.f i ≫ f i j he

def post {a : ℤ} (f : Cochain P Q a) (u : Q ⟶ S) : Cochain P S a :=
  fun i j he => f i j he ≫ u.f j
lemma pre_closed (u : S ⟶ P) {a : ℤ} {f : Cochain P Q a} (hf : Closed f) : Closed (pre u f) := by
  intro i j l m hij hlm
  dsimp only [pre]
  rw [Category.assoc,hf,← Category.assoc,u.comm,Category.assoc]
lemma post_closed {a : ℤ} {f : Cochain P Q a} (hf : Closed f) (u : Q ⟶ S) : Closed (post f u) := by
  intro i j l m hij hlm
  dsimp only [post]
  rw [Category.assoc,u.comm,← Category.assoc,hf,Category.assoc]
end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {P' Q' : ChainComplex (ModuleCat.{0} S) ℤ}
variable (e : ∀ i j, (P.X i ⟶ Q.X j) ≃ₗ[k] (P'.X i ⟶ Q'.X j))

def cochainEquiv (a : ℤ) : Cochain P Q a ≃ₗ[k] Cochain P' Q' a where
  toFun f i j h := e i j (f i j h)
  invFun f i j h := (e i j).symm (f i j h)
  left_inv f := by funext i j h; exact (e i j).symm_apply_apply _
  right_inv f := by funext i j h; exact (e i j).apply_symm_apply _
  map_add' f g := by funext i j h; exact (e i j).map_add _ _
  map_smul' c f := by funext i j h; exact (e i j).map_smul c _

variable (hpre : ∀ i l j (f : P.X l ⟶ Q.X j),
    e i j (P.d i l ≫ f) = P'.d i l ≫ e l j f)
  (hpost : ∀ i j m (f : P.X i ⟶ Q.X j),
    e i m (f ≫ Q.d j m) = e i j f ≫ Q'.d j m)
include hpre hpost
lemma cochainEquiv_closed_iff {a : ℤ} (f : Cochain P Q a) :
    Closed (cochainEquiv e a f) ↔ Closed f := by
  constructor
  · intro hf i j l m hij hlm
    apply (e i m).injective
    rw [hpre,hpost]
    exact hf i j l m hij hlm
  · intro hf i j l m hij hlm
    change e i j (f i j hij) ≫ Q'.d j m = P'.d i l ≫ e l m (f l m hlm)
    rw [← hpre,← hpost,hf]

lemma cochainEquiv_diff {a : ℤ} (f : Cochain P Q (a-1)) :
    cochainEquiv e a (diff f) = diff (cochainEquiv e (a-1) f) := by
  funext i j h
  change e i j (_+_) = _+_
  rw [map_add,hpre,hpost]
  rfl

lemma cochainEquiv_boundary_iff {a : ℤ} (f : Cochain P Q a) :
    Boundary (cochainEquiv e a f) ↔ Boundary f := by
  rw [boundary_iff_diff,boundary_iff_diff]
  constructor
  · rintro ⟨h,hh⟩
    refine ⟨(cochainEquiv e (a-1)).symm h,?_⟩
    apply (cochainEquiv e a).injective
    rw [cochainEquiv_diff e hpre hpost,LinearEquiv.apply_symm_apply,hh]
  · rintro ⟨h,rfl⟩
    exact ⟨cochainEquiv e (a-1) h,cochainEquiv_diff e hpre hpost h⟩
end Tachikawa.DownHom



namespace Tachikawa
open CategoryTheory
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (hp : TotallyAcyclic P) (hq : ComplexExact Q)
  (pproj : ∀ j, Module.Projective R (P.X j))
  (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
  {N : ModuleCat.{0} R} (ε : Q.X 0 ⟶ N)
  (he : Function.Exact (Q.d 1 0) ε) (hs : Function.Surjective ε)
include hp hq pproj qfin qproj he hs
lemma exists_augmented_complete_lift (g : P.X 0 ⟶ N) (hg : P.d 1 0 ≫ g = 0) :
    ∃ f : P ⟶ Q, f.f 0 ≫ ε = g := by
  let e := CokerAt.augmentationEquiv Q N 0 ε.hom he hs
  let u := e.symm.toLinearMap.comp (CokerAt.descend P 0 g.hom (ModuleCat.hom_ext_iff.mp hg))
  obtain ⟨f,hf⟩ := exists_complete_lift P Q hp hq pproj qfin qproj u
  refine ⟨f,?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have hy := congrArg e (LinearMap.congr_fun hf (CokerAt.π P 0 y))
  change ε (f.f 0 y) = e (e.symm (g y)) at hy
  change ε (f.f 0 y) = g y
  simpa only [LinearEquiv.apply_symm_apply] using hy
end Tachikawa



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {N : ModuleCat.{0} R}
  (ε : Q.X 0 ⟶ N) (hε : Q.d 1 0 ≫ ε = 0)

def evalCycle {a : ℤ} (f : Cochain P Q a) (hf : Closed f) :
    VectorSplit.Z (completeHom (k := k) P N) a :=
  ⟨f a 0 (by omega) ≫ ε, by
    apply (completeHom_memZ P N a _).mpr
    erw [← Category.assoc,← hf (a+1) 1 a 0 (by omega) (by omega),
      Category.assoc,hε,Limits.comp_zero]⟩

def evalClass {a : ℤ} (f : Cochain P Q a) (hf : Closed f) :
    VectorSplit.H (completeHom (k := k) P N) a :=
  VectorSplit.quotient _ a (evalCycle ε hε f hf)

lemma eval_boundary {a : ℤ} (f : Cochain P Q a) (hf : Closed f) (hb : Boundary f) :
    evalClass (k := k) ε hε f hf = 0 := by
  obtain ⟨h,hh⟩ := hb
  apply (VectorSplit.quotient_zero_iff_predecessor a _).mpr
  refine ⟨h (a-1) 0 (by omega) ≫ ε,?_⟩
  change P.d a (a-1) ≫ h (a-1) 0 _ ≫ ε = f a 0 _ ≫ ε
  rw [hh a 0,add_comp,Category.assoc,Category.assoc,show Q.d (0+1) 0 ≫ ε = 0 from hε,Limits.comp_zero,add_zero]

variable (hP : TotallyAcyclic P) (hQ : ComplexExact Q)
  (pP : ∀ j, Module.Projective R (P.X j))
  (fP : ∀ j, Module.Finite R (P.X j))
  (fQ : ∀ j, Module.Finite R (Q.X j)) (pQ : ∀ j, Module.Projective R (Q.X j))
  (he : Function.Exact (Q.d 1 0) ε) (hs : Function.Surjective ε)

include hP hQ pP fP fQ pQ he hs in
lemma boundary_of_eval_zero {a : ℤ} (f : Cochain P Q a) (hf : Closed f)
    (hz : evalClass (k := k) ε hε f hf = 0) : Boundary f := by
  obtain ⟨g,hg⟩ := (VectorSplit.quotient_zero_iff_predecessor a _).mp hz
  change P.X (a-1) ⟶ N at g
  change P.d a (a-1) ≫ g = f a 0 _ ≫ ε at hg
  let P' := CompleteTranslate.complex P a
  let e := CokerAt.augmentationEquiv Q N 0 ε.hom he hs
  let g' : P'.X (-1) →ₗ[R] N :=
    g.hom.comp (P.XIsoOfEq (show -1+a=a-1 by omega)).hom.hom
  have hfac : CokerAt.map (toChain f hf) 0 ∈ projectiveFactors (k := k) := by
    refine ⟨P'.X (-1), ?_, ?_, CokerAt.δ P' 0 (-1), e.symm.toLinearMap.comp g', ?_⟩
    · exact fP (-1+a)
    · exact pP (-1+a)
    · apply LinearMap.ext
      intro x
      obtain ⟨y,rfl⟩ := CokerAt.π_surjective P' 0 x
      apply e.injective
      change e (e.symm (g' (P'.d 0 (-1) y))) = e (CokerAt.π Q 0 (f (0+a) 0 rfl y))
      rw [LinearEquiv.apply_symm_apply]
      change g ((P.XIsoOfEq (show -1+a=a-1 by omega)).hom (P.d (0+a) (-1+a) y)) =
        ε (f (0+a) 0 rfl y)
      have hm : P.d (0+a) (-1+a) ≫ (P.XIsoOfEq (show -1+a=a-1 by omega)).hom ≫ g =
          f (0+a) 0 rfl ≫ ε := by
        rw [← Category.assoc,P.d_comp_XIsoOfEq_hom]
        have hx := congrArg (fun z => (P.XIsoOfEq (show 0+a=a by omega)).hom ≫ z) hg
        rw [← Category.assoc,P.XIsoOfEq_hom_comp_d,← Category.assoc,transport_left] at hx
        exact hx
      exact congrArg (fun z => z y) hm
  obtain ⟨h⟩ := nullhomotopic_of_coker_factors (k := k) (toChain f hf)
    (CompleteTranslate.totallyAcyclic P a hP) hQ (fun j => pP (j+a)) fQ pQ hfac
  simpa only [of_toChain] using ofHomotopy_boundary h

include hP hQ pP fQ pQ he hs in
lemma eval_surjective (a : ℤ) (x : VectorSplit.H (completeHom (k := k) P N) a) :
    ∃ (f : Cochain P Q a) (hf : Closed f), evalClass (k := k) ε hε f hf = x := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective a x
  let g : (CompleteTranslate.complex P a).X 0 ⟶ N :=
    (P.XIsoOfEq (show 0+a=a by omega)).hom ≫ z.val
  have hg : (CompleteTranslate.complex P a).d 1 0 ≫ g = 0 := by
    dsimp only [g,CompleteTranslate.complex]
    erw [← Category.assoc,P.d_comp_XIsoOfEq_hom]
    have hz := (completeHom_memZ P N a z.val).mp z.property
    have hx := congrArg (fun t => (P.XIsoOfEq (show 1+a=a+1 by omega)).hom ≫ t) hz
    erw [← Category.assoc,P.XIsoOfEq_hom_comp_d,Limits.comp_zero] at hx
    exact hx
  obtain ⟨f,hf⟩ := exists_augmented_complete_lift
    (CompleteTranslate.totallyAcyclic P a hP) hQ (fun j => pP (j+a)) fQ pQ ε he hs g hg
  refine ⟨ofChain P Q f, ofChain_closed f, ?_⟩
  apply congrArg (VectorSplit.quotient _ a)
  apply Subtype.ext
  change (P.XIsoOfEq (show a=0+a by omega)).hom ≫ f.f 0 ≫ ε = z.val
  rw [hf]
  dsimp only [g]
  erw [← Category.assoc]
  simp
  exact Category.id_comp (z.val : P.X a ⟶ N)

end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R]  [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {N : ModuleCat.{0} R}
  (ε : Q.X 0 ⟶ N) (hε : Q.d 1 0 ≫ ε = 0)
lemma eval_add {a : ℤ} (f g : Cochain P Q a) (hf : Closed f) (hg : Closed g) :
    evalClass (k := k) ε hε (f+g) (closed_add hf hg) =
      evalClass ε hε f hf + evalClass ε hε g hg := by
  change VectorSplit.quotient _ a _ = VectorSplit.quotient _ a _ + VectorSplit.quotient _ a _
  rw [← map_add]
  apply congrArg (VectorSplit.quotient _ a)
  apply Subtype.ext
  change (f a 0 (by omega)+g a 0 (by omega)) ≫ ε = _
  rw [add_comp]
  rfl

variable (F : ModuleCat.{0} R ⥤ ModuleCat.{0} R) [F.Additive]
abbrev mapComplex (P : ChainComplex (ModuleCat.{0} R) ℤ) :=
  (F.mapHomologicalComplex (.down ℤ)).obj P

def mapCochain {a : ℤ} (f : Cochain P Q a) : Cochain (mapComplex F P) (mapComplex F Q) a :=
  fun i j h => F.map (f i j h)
lemma map_closed {a : ℤ} {f : Cochain P Q a} (hf : Closed f) : Closed (mapCochain F f) := by
  intro i j l m hij hlm
  change F.map (f i j hij) ≫ F.map (Q.d j m) = F.map (P.d i l) ≫ F.map (f l m hlm)
  rw [← F.map_comp,← F.map_comp,hf]

variable [F.Linear k] (X : ModuleCat.{0} R) (εP : P.X 0 ⟶ X)
  (hεP : P.d 1 0 ≫ εP = 0) (u : P ⟶ mapComplex F P) (u₀ : X ⟶ F.obj X)
  (hu : u.f 0 ≫ F.map εP = εP ≫ u₀)
include hεP in
lemma map_augmentation_zero : (mapComplex F P).d 1 0 ≫ F.map εP = 0 := by
  change F.map (P.d 1 0) ≫ F.map εP = 0
  rw [← F.map_comp,hεP,F.map_zero]

def actionDelta {a : ℤ} (f g : Cochain P P a) : Cochain P (mapComplex F P) a :=
  pre u (mapCochain F f) + post g u
lemma actionDelta_closed {a : ℤ} {f g : Cochain P P a} (hf : Closed f) (hg : Closed g) :
    Closed (actionDelta F u f g) := closed_add (pre_closed u (map_closed F hf)) (post_closed hg u)

abbrev homologyDelta (a : ℤ) :
    (VectorSplit.H (completeHom (k := k) P X) a × VectorSplit.H (completeHom (k := k) P X) a) →ₗ[k]
    VectorSplit.H (completeHom (k := k) P (F.obj X)) a :=
  (VectorSplit.Hmap (completeFunctorHom F P P X u) a).coprod
    (VectorSplit.Hmap (completeHomMap P u₀) a)

include hu in
lemma eval_actionDelta {a : ℤ} (f g : Cochain P P a) (hf : Closed f) (hg : Closed g) :
    evalClass (k := k) (F.map εP) (map_augmentation_zero F X εP hεP)
      (actionDelta F u f g) (actionDelta_closed F u hf hg) =
    homologyDelta F X u u₀ a (evalClass εP hεP f hf,evalClass εP hεP g hg) := by
  dsimp only [actionDelta]
  rw [eval_add _ _ _ _ (pre_closed u (map_closed F hf)) (post_closed hg u)]
  change _ = VectorSplit.Hmap (completeFunctorHom F P P X u) a
    (VectorSplit.quotient _ a (evalCycle εP hεP f hf)) +
    VectorSplit.Hmap (completeHomMap (k := k) P u₀) a
    (VectorSplit.quotient _ a (evalCycle εP hεP g hg))
  rw [VectorSplit.Hmap_quotient,VectorSplit.Hmap_quotient]
  congr 1
  · apply congrArg (VectorSplit.quotient _ a)
    apply Subtype.ext
    change (u.f a ≫ F.map (f a 0 _)) ≫ F.map εP = u.f a ≫ F.map (f a 0 _ ≫ εP)
    rw [F.map_comp,Category.assoc]
  · apply congrArg (VectorSplit.quotient _ a)
    apply Subtype.ext
    change (g a 0 _ ≫ u.f 0) ≫ F.map εP = (g a 0 _ ≫ εP) ≫ u₀
    rw [Category.assoc,hu,Category.assoc]

end Tachikawa.DownHom



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
open DownHom
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
lemma diagonal₀_comp {L M N : ModuleCat.{0} R}
    (f : D₀Obj F L ⟶ D₀Obj F M) (g : D₀Obj F M ⟶ D₀Obj F N) :
    diagonal₀ (f ≫ g) = diagonal₀ f ≫ diagonal₀ g := by
  have hf : D₀Map F (diagonal₀ f) = f := diagonal₀.symm_apply_apply f
  rw [← hf,diagonal₀_pre]
  rfl
lemma diagonal₁_comp {L M N : ModuleCat.{0} R}
    (f : D₁Obj F L ⟶ D₁Obj F M) (g : D₁Obj F M ⟶ D₁Obj F N) :
    diagonal₁ (f ≫ g) = diagonal₁ f ≫ diagonal₁ g := by
  have hf : D₁Map F (diagonal₁ f) = f := diagonal₁.symm_apply_apply f
  rw [← hf,diagonal₁_pre]
  rfl
lemma diagonal₀_post {L M N : ModuleCat.{0} R}
    (f : D₀Obj F L ⟶ D₀Obj F M) (g : M ⟶ N) :
    diagonal₀ (f ≫ D₀Map F g) = diagonal₀ f ≫ g := diagonal₀_comp F f (D₀Map F g)
lemma diagonal₁_post {L M N : ModuleCat.{0} R}
    (f : D₁Obj F L ⟶ D₁Obj F M) (g : M ⟶ N) :
    diagonal₁ (f ≫ D₁Map F g) = diagonal₁ f ≫ g := diagonal₁_comp F f (D₁Map F g)
lemma cross₁₀_comp_right {L M N : ModuleCat.{0} R}
    (f : D₁Obj F L ⟶ D₀Obj F M) (g : D₀Obj F M ⟶ D₀Obj F N) :
    cross₁₀ (f ≫ g) = cross₁₀ f ≫ (Enveloping.tensorFunctor F).map (diagonal₀ g) := by
  have hg : D₀Map F (diagonal₀ g) = g := diagonal₀.symm_apply_apply g
  rw [← hg,cross₁₀_post]
  rfl
lemma cross₁₀_comp_left {L M N : ModuleCat.{0} R}
    (f : D₁Obj F L ⟶ D₁Obj F M) (g : D₁Obj F M ⟶ D₀Obj F N) :
    cross₁₀ (f ≫ g) = diagonal₁ f ≫ cross₁₀ g := by
  have hf : D₁Map F (diagonal₁ f) = f := diagonal₁.symm_apply_apply f
  rw [← hf,cross₁₀_pre]
  rfl

variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}
abbrev down₀ (a : ℤ) : Cochain (D₀Complex F P) (D₀Complex F Q) a ≃ₗ[k] Cochain P Q a :=
  cochainEquiv (fun _ _ => diagonal₀) a
abbrev down₁ (a : ℤ) : Cochain (D₁Complex F P) (D₁Complex F Q) a ≃ₗ[k] Cochain P Q a :=
  cochainEquiv (fun _ _ => diagonal₁) a
abbrev downCross (a : ℤ) : Cochain (D₁Complex F P) (D₀Complex F Q) a ≃ₗ[k]
    Cochain P (Enveloping.tensorComplex F Q) a :=
  cochainEquiv (fun _ _ => cross₁₀) a

lemma down₀_closed {a : ℤ} (f : Cochain (D₀Complex F P) (D₀Complex F Q) a) :
    Closed (down₀ F a f) ↔ Closed f :=
  cochainEquiv_closed_iff _ (fun _ _ _ _ => diagonal₀_pre F _ _)
    (fun _ _ _ _ => diagonal₀_post F _ _) f
lemma down₁_closed {a : ℤ} (f : Cochain (D₁Complex F P) (D₁Complex F Q) a) :
    Closed (down₁ F a f) ↔ Closed f :=
  cochainEquiv_closed_iff _ (fun _ _ _ _ => diagonal₁_pre F _ _)
    (fun _ _ _ _ => diagonal₁_post F _ _) f
lemma downCross_closed {a : ℤ} (f : Cochain (D₁Complex F P) (D₀Complex F Q) a) :
    Closed (downCross F a f) ↔ Closed f :=
  cochainEquiv_closed_iff _ (fun _ _ _ _ => cross₁₀_pre F _ _)
    (fun _ _ _ _ => cross₁₀_post F _ _) f
lemma down₀_boundary {a : ℤ} (f : Cochain (D₀Complex F P) (D₀Complex F Q) a) :
    Boundary (down₀ F a f) ↔ Boundary f :=
  cochainEquiv_boundary_iff _ (fun _ _ _ _ => diagonal₀_pre F _ _)
    (fun _ _ _ _ => diagonal₀_post F _ _) f
lemma down₁_boundary {a : ℤ} (f : Cochain (D₁Complex F P) (D₁Complex F Q) a) :
    Boundary (down₁ F a f) ↔ Boundary f :=
  cochainEquiv_boundary_iff _ (fun _ _ _ _ => diagonal₁_pre F _ _)
    (fun _ _ _ _ => diagonal₁_post F _ _) f
lemma downCross_boundary {a : ℤ} (f : Cochain (D₁Complex F P) (D₀Complex F Q) a) :
    Boundary (downCross F a f) ↔ Boundary f :=
  cochainEquiv_boundary_iff _ (fun _ _ _ _ => cross₁₀_pre F _ _)
    (fun _ _ _ _ => cross₁₀_post F _ _) f

lemma downCross_delta (u : P ⟶ Enveloping.tensorComplex F P) {a : ℤ}
    (f : Cochain (D₀Complex F P) (D₀Complex F P) a)
    (g : Cochain (D₁Complex F P) (D₁Complex F P) a) :
    downCross F a (pre (crossMap F u) f+post g (crossMap F u)) =
      actionDelta (Enveloping.tensorFunctor F) u (down₀ F a f) (down₁ F a g) := by
  funext i j h
  change cross₁₀ ((crossMap F u).f i ≫ f i j h + g i j h ≫ (crossMap F u).f j) = _
  erw [map_add,cross₁₀_comp_right,cross₁₀_comp_left]
  change cross₁₀ (cross₁₀.symm (u.f i)) ≫ _ + _ ≫ cross₁₀ (cross₁₀.symm (u.f j)) = _
  erw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  rfl
end Tachikawa.Triangular

end

end OAI
