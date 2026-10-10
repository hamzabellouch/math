import Mathlib
import OAI.RingTheory.Multiplicity.FilteredCechAugmentationRing

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

private lemma component_iso_square {C : Type*} [Category C]
    {X Y A B D E : C} (eA : A ≅ B) (eD : D ≅ E)
    (a : X ⟶ A) (b : Y ⟶ D) (h : X ⟶ Y) (f : B ⟶ E) (g : A ⟶ D)
    (hg : g = eA.hom ≫ f ≫ eD.inv) (ha : h ≫ b = a ≫ g) :
    (a ≫ eA.hom) ≫ f = h ≫ (b ≫ eD.hom) := by
  rw [← Category.assoc h b, ha, Category.assoc, hg]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

def augmented (t : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (complex I z hz t).extend ComplexShape.embeddingUpNat

lemma augmented_boundedBelow (t : ℕ) :
    ∀ i, i < (0 : ℤ) → IsZero ((augmented I z hz t).X i) := by
  intro i hi
  apply (complex I z hz t).isZero_extend_X
  intro n hn
  change (n : ℤ)=i at hn
  omega

 

def positive (t : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  FiniteComplex.dropBottom (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)

lemma positive_boundedBelow (t : ℕ) :
    ∀ q, q≤(0 : ℤ) → IsZero ((positive I z hz t).X q) := by
  intro q hq
  exact FiniteComplex.dropBottom_boundedBelow _ _ _ q (by omega)

def positiveInclusion {s t : ℕ} (hst : s ≤ t) : positive I z hz t ⟶ positive I z hz s :=
  FiniteComplex.dropBottomMap (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)
    (augmented_boundedBelow I z hz s) (extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat)

def positiveXIso (t n : ℕ) (hn : 0<n) :
    (positive I z hz t).X (n : ℤ) ≅ (complex I z hz t).X n :=
  FiniteComplex.dropBottomXIso _ _ _ (n : ℤ) (by omega) ≪≫
    (complex I z hz t).extendXIso ComplexShape.embeddingUpNat (i := n) rfl

@[reassoc] lemma positiveXIso_inclusion {s t : ℕ} (hst : s ≤ t) (n : ℕ) (hn : 0<n) :
    (positiveXIso I z hz t n hn).hom ≫ (inclusion I z hz hst).f n =
      (positiveInclusion I z hz hst).f (n : ℤ) ≫ (positiveXIso I z hz s n hn).hom := by
  have he := congrArg (fun f => f.f (n : ℤ))
    (FiniteComplex.dropBottomMap_ι (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)
      (augmented_boundedBelow I z hz s) (extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat))
  dsimp only [positiveXIso,Iso.trans_hom,FiniteComplex.dropBottomXIso,asIso_hom,positiveInclusion]
  exact component_iso_square
    ((complex I z hz t).extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
    ((complex I z hz s).extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
    _ _ _ _ _
    (extendMap_f (inclusion I z hz hst) ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)) he

lemma positiveInclusion_refl (t : ℕ) : positiveInclusion I z hz (le_refl t)=𝟙 _ := by
  simp only [positiveInclusion]
  apply (cancel_mono (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t)))).mp
  refine (FiniteComplex.dropBottomMap_ι (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t) (augmented_boundedBelow I z hz t)
    (extendMap (inclusion I z hz (le_refl t)) ComplexShape.embeddingUpNat)).trans ?_
  have he : extendMap (inclusion I z hz (le_refl t)) ComplexShape.embeddingUpNat =
      𝟙 (augmented I z hz t) := by
    rw [inclusion_refl, extendMap_id]
    rfl
  exact (congrArg (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t)) ≫ ·) he).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

lemma positiveInclusion_comp {r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) :
    positiveInclusion I z hz hst ≫ positiveInclusion I z hz hrs =
      positiveInclusion I z hz (hrs.trans hst) := by
  apply (cancel_mono (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz r) 0
    (augmented_boundedBelow I z hz r)))).mp
  let ι (j : ℕ) := kernel.ι (FiniteComplex.bottomProjection (augmented I z hz j) 0
    (augmented_boundedBelow I z hz j))
  have hι {a b : ℕ} (hab : a ≤ b) : positiveInclusion I z hz hab ≫ ι a =
      ι b ≫ extendMap (inclusion I z hz hab) ComplexShape.embeddingUpNat :=
    FiniteComplex.dropBottomMap_ι (augmented I z hz b) 0
      (augmented_boundedBelow I z hz b) (augmented_boundedBelow I z hz a) _
  have he : extendMap (inclusion I z hz hst) ComplexShape.embeddingUpNat ≫
      extendMap (inclusion I z hz hrs) ComplexShape.embeddingUpNat =
        extendMap (inclusion I z hz (hrs.trans hst)) ComplexShape.embeddingUpNat := by
    rw [← extendMap_comp, inclusion_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (positiveInclusion I z hz hst ≫ ·) (hι hrs)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ extendMap (inclusion I z hz hrs) ComplexShape.embeddingUpNat) (hι hst)).trans
          ((Category.assoc _ _ _).trans ((congrArg (ι t ≫ ·) he).trans (hι _).symm)))))
end Lech.FilteredCech


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
variable (F : CochainComplex (ModuleCat.{u} R) ℤ)
  {Q Q' : ModuleCat.{u} R} (a : R) (d inc : Q ⟶ Q')

lemma scalar_tensor_division (hd : a • d=inc) :
    (termTensor Q).map (a • 𝟙 F) ≫ termTensorMap F Q d = termTensorMap F Q inc := by
  apply Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  change (a • x) ⊗ₜ[R] d y = x ⊗ₜ[R] inc y
  rw [TensorProduct.smul_tmul]
  have hdy := congrArg (fun f : Q ⟶ Q' => f y) hd
  change a • d y=inc y at hdy
  rw [hdy]

 
def tensorDivisionHomotopy (hd : a • d=inc) (H : Homotopy (a • 𝟙 F) 0) :
    Homotopy (termTensorMap F Q inc) 0 := by
  have HH := (((curriedTensor (ModuleCat.{u} R)).flip.obj Q).mapHomotopy H).compRight
    (termTensorMap F Q d)
  rw [scalar_tensor_division F a d inc hd,Functor.map_zero,zero_comp] at HH
  exact HH
end Lech.TensorTotal


namespace Lech.TensorPi
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {J : Type} [Fintype J]
  {A B C : ModuleCat.{u} R} {Q Q' Q'' : J → ModuleCat.{u} R}
open scoped TensorProduct
local instance : DecidableEq J := Classical.decEq J

abbrev modulePi (Q : J → ModuleCat.{u} R) : ModuleCat.{u} R := ModuleCat.of R (∀ j, Q j)

 

def map (f : ∀ j, A ⊗ Q j ⟶ B ⊗ Q' j) : A ⊗ modulePi Q ⟶ B ⊗ modulePi Q' :=
  ModuleCat.ofHom ((TensorProduct.piRight R R B (fun j => Q' j)).symm.toLinearMap.comp
    ((LinearMap.pi (fun j => (f j).hom.comp (LinearMap.proj j))).comp
      (TensorProduct.piRight R R A (fun j => Q j)).toLinearMap))

@[simp] lemma map_apply (f : ∀ j, A ⊗ Q j ⟶ B ⊗ Q' j)
    (x : A ⊗[R] (∀ j, Q j)) (j : J) :
    TensorProduct.piRight R R B (fun j => Q' j) (map f x) j =
      f j (TensorProduct.piRight R R A (fun j => Q j) x j) := by
  change (TensorProduct.piRight R R B _)
    ((TensorProduct.piRight R R B _).symm _) j = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

lemma ext {f g : A ⊗ modulePi Q ⟶ B ⊗ modulePi Q'}
    (h : ∀ x j, TensorProduct.piRight R R B (fun j => Q' j) (f x) j =
      TensorProduct.piRight R R B (fun j => Q' j) (g x) j) : f=g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (TensorProduct.piRight R R B (fun j => Q' j)).injective
  funext j
  exact h x j

lemma map_comp (f : ∀ j, A ⊗ Q j ⟶ B ⊗ Q' j) (g : ∀ j, B ⊗ Q' j ⟶ C ⊗ Q'' j) :
    map (fun j => f j ≫ g j) = map f ≫ map g := by
  apply ext
  intro x j
  simp

lemma map_add (f g : ∀ j, A ⊗ Q j ⟶ B ⊗ Q' j) :
    map (fun j => f j+g j)=map f+map g := by
  apply ext
  intro x j
  change TensorProduct.piRight R R B _ (map (fun j => f j+g j) x) j =
    TensorProduct.piRight R R B _ (map f x + map g x) j
  simp only [LinearEquiv.map_add,Pi.add_apply,map_apply]
  rfl

lemma map_zero : map (fun j : J => (0 : A ⊗ Q j ⟶ B ⊗ Q' j))=0 := by
  apply ext
  intro x j
  simp

 
def piMap (g : ∀ j, Q j ⟶ Q' j) : modulePi Q ⟶ modulePi Q' :=
  ModuleCat.ofHom (LinearMap.pi (fun j => (g j).hom.comp (LinearMap.proj j)))

lemma map_tensor (f : A ⟶ B) (g : ∀ j, Q j ⟶ Q' j) :
    map (fun j => f ⊗ₘ g j) = f ⊗ₘ piMap g := by
  apply ext
  intro x j
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [map_apply,TensorProduct.piRight_apply,TensorProduct.piRightHom_tmul,
      ModuleCat.MonoidalCategory.tensorHom_tmul]
    rfl
  | add x y hx hy => simp only [LinearMap.map_add,LinearEquiv.map_add,Pi.add_apply,hx,hy]

omit [Fintype J] in
lemma piMap_id : piMap (fun j => 𝟙 (Q j))=𝟙 (modulePi Q) := rfl
end Lech.TensorPi


namespace Lech.TensorPi
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive MonoidalCategory HomologicalComplex
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] {J : Type} [Fintype J]
  (F : CochainComplex (ModuleCat.{u} R) ℤ) {Q Q' : J → ModuleCat.{u} R}

 

def homotopy (inc : ∀ j, Q j ⟶ Q' j)
    (H : ∀ j, Homotopy (termTensorMap F (Q j) (inc j)) 0) :
    Homotopy (termTensorMap F (modulePi Q) (piMap inc)) 0 where
  hom p q := map (fun j => (H j).hom p q)
  zero p q hpq := by
    have hh : (fun j => (H j).hom p q) = (fun _ => 0) := funext (fun j => (H j).zero p q hpq)
    rw [hh,map_zero]
  comm p := by
    have hh : (fun j => (termTensorMap F (Q j) (inc j)).f p) =
        (fun j => ((termTensor (Q j)).obj F).d p (p+1) ≫ (H j).hom (p+1) p +
          (H j).hom p (p-1) ≫ ((termTensor (Q' j)).obj F).d (p-1) p) := by
      funext j
      have hj := (H j).comm p
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (p-1) p by change p-1+1=p; omega),zero_f,add_zero] at hj
      exact hj
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p-1) p by change p-1+1=p; omega),zero_f,add_zero]
    change (𝟙 (F.X p) ⊗ₘ piMap inc) =
      (F.d p (p+1) ⊗ₘ 𝟙 (modulePi Q)) ≫ map (fun j => (H j).hom (p+1) p) +
        map (fun j => (H j).hom p (p-1)) ≫ (F.d (p-1) p ⊗ₘ 𝟙 (modulePi Q'))
    rw [←map_tensor]
    change map (fun j => (termTensorMap F (Q j) (inc j)).f p) = _
    rw [hh,map_add,map_comp,map_comp]
    change map (fun j => F.d p (p+1) ⊗ₘ 𝟙 (Q j)) ≫ _ +
      _ ≫ map (fun j => F.d (p-1) p ⊗ₘ 𝟙 (Q' j)) = _
    rw [map_tensor,map_tensor,piMap_id,piMap_id]
end Lech.TensorPi


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma termTensorMap_comp {Q Q' Q'' : ModuleCat.{u} R} (a : Q ⟶ Q') (b : Q' ⟶ Q'') :
    termTensorMap F Q (a≫b)=termTensorMap F Q a ≫ termTensorMap F Q' b := by
  apply Hom.ext
  funext p
  exact whiskerLeft_comp (F.X p) a b

lemma termTensorMap_zero {Q Q' : ModuleCat.{u} R} : termTensorMap F Q (0 : Q ⟶ Q')=0 := by
  apply Hom.ext
  funext p
  exact Functor.map_zero ((curriedTensor (ModuleCat.{u} R)).obj (F.X p)) Q Q'

 

def coefficientHomotopyOfIso {Q Q' A A' : ModuleCat.{u} R}
    (e : Q ≅ A) (e' : Q' ≅ A') (f : Q ⟶ Q') (g : A ⟶ A')
    (hf : e.hom ≫ g=f≫e'.hom) (H : Homotopy (termTensorMap F A g) 0) :
    Homotopy (termTensorMap F Q f) 0 := by
  have HH := (H.compLeft (termTensorMap F Q e.hom)).compRight
    (termTensorMap F A' e'.inv)
  rw [←termTensorMap_comp,←termTensorMap_comp,hf,Category.assoc,Iso.hom_inv_id,
    Category.comp_id,comp_zero,zero_comp] at HH
  exact HH
end Lech.TensorTotal


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℕ)
  (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)

 

def intersectionHomotopy (t n : ℕ) (hn : 0<n) (a : Fin n → Fin h) :
    Homotopy (termTensorMap F (ModuleCat.of R (term I z (t+m) (ActualCech.intersection a)))
      (ModuleCat.ofHom (Submodule.inclusion (FilteredFraction.antitone I _ _ (Nat.le_add_right t m))))) 0 := by
  let i : Fin h := a ⟨0,hn⟩
  have hi : i ∈ ActualCech.intersection a := (ActualCech.mem_intersection a i).mpr ⟨⟨0,hn⟩,rfl⟩
  apply tensorDivisionHomotopy F (z i ^ m)
    (ModuleCat.ofHom (divide I z hz i hi t m)) _ _ (H i)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact smul_divide I z hz i hi t m x

def cochainPiIso (t n : ℕ) :
    (complex I z hz t).X n ≅ TensorPi.modulePi (fun a : Fin n → Fin h =>
      ModuleCat.of R (term I z t (ActualCech.intersection a))) := Iso.refl _

lemma cochainPiIso_inclusion {s t : ℕ} (hst : s≤t) (n : ℕ) :
    (cochainPiIso I z hz t n).hom ≫ TensorPi.piMap (fun a : Fin n → Fin h =>
      ModuleCat.ofHom (Submodule.inclusion (FilteredFraction.antitone I
        (GradedChart.denominator z (ActualCech.intersection a))
        (ActualCech.intersection a).card hst))) =
      (inclusion I z hz hst).f n ≫ (cochainPiIso I z hz s n).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def cochainHomotopy (t n : ℕ) (hn : 0<n) :
    Homotopy (termTensorMap F ((complex I z hz (t+m)).X n)
      ((inclusion I z hz (Nat.le_add_right t m)).f n)) 0 := by
  let Q : (Fin n → Fin h) → ModuleCat.{u} R := fun a =>
    ModuleCat.of R (term I z (t+m) (ActualCech.intersection a))
  let Q' : (Fin n → Fin h) → ModuleCat.{u} R := fun a =>
    ModuleCat.of R (term I z t (ActualCech.intersection a))
  let inc : ∀ a, Q a ⟶ Q' a := fun _ =>
    ModuleCat.ofHom (Submodule.inclusion (FilteredFraction.antitone I _ _ (Nat.le_add_right t m)))
  have HH := TensorPi.homotopy (Q := Q) (Q' := Q') F inc
    (intersectionHomotopy I z hz F m H t n hn)
  exact coefficientHomotopyOfIso F (cochainPiIso I z hz (t+m) n) (cochainPiIso I z hz t n)
    _ _ (cochainPiIso_inclusion I z hz (Nat.le_add_right t m) n) HH

 

def positiveRowHomotopy (t : ℕ) (q : ℤ) :
    Homotopy (termTensorMap F ((positive I z hz (t+m)).X q)
      ((positiveInclusion I z hz (Nat.le_add_right t m)).f q)) 0 := by
  by_cases hq : q ≤ 0
  · have hf : (positiveInclusion I z hz (Nat.le_add_right t m)).f q=0 :=
      (positive_boundedBelow I z hz (t+m) q hq).eq_of_src _ _
    rw [hf,termTensorMap_zero]
  · have hn : 0<q.toNat := by omega
    have heq : (q.toNat:ℤ)=q := by omega
    have HH := coefficientHomotopyOfIso F (positiveXIso I z hz (t+m) q.toNat hn)
      (positiveXIso I z hz t q.toNat hn) _ _ (positiveXIso_inclusion I z hz _ q.toNat hn)
      (cochainHomotopy I z hz F m H t q.toNat hn)
    rw [heq] at HH
    exact HH
end Lech.FilteredCech


namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
abbrev Bic := HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
variable {K L M : Bic (R := R)}

 

structure RowHomotopy (f : K ⟶ L) where
  h : ∀ p q : ℤ, (K.X p).X q ⟶ (L.X (p-1)).X q
  equation : ∀ p q : ℤ, (f.f p).f q =
    (K.d p (p+1)).f q ≫ h (p+1) q ≫ (L.XXIsoOfEq _ _ _ (by omega) rfl).hom +
      h p q ≫ (L.d (p-1) p).f q

 
def homotopyTerm {f : K ⟶ L} (h : RowHomotopy f) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel j i) : (K.total (ComplexShape.up ℤ)).X i ⟶ (L.total (ComplexShape.up ℤ)).X j :=
  K.totalDesc (fun p q hpq => h.h p q ≫ L.ιTotal (ComplexShape.up ℤ) (p-1) q j (by
    change p+q=i at hpq
    change j+1=i at hij
    change p-1+q=j
    omega))

@[reassoc (attr := simp)] lemma ι_homotopyTerm {f : K ⟶ L} (h : RowHomotopy f)
    (p q i j : ℤ) (hpq : p+q=i) (hij : (ComplexShape.up ℤ).Rel j i) :
    K.ιTotal (ComplexShape.up ℤ) p q i hpq ≫ homotopyTerm h i j hij =
      h.h p q ≫ L.ιTotal (ComplexShape.up ℤ) (p-1) q j (by change j+1=i at hij; change p-1+q=j; omega) := by
  apply ι_totalDesc

def correction {f : K ⟶ L} (h : RowHomotopy f) : K.total (ComplexShape.up ℤ) ⟶ L.total (ComplexShape.up ℤ) :=
  total.map f (ComplexShape.up ℤ) - Homotopy.nullHomotopicMap' (homotopyTerm h)

lemma homologyMap_correction {f : K ⟶ L} (h : RowHomotopy f) (i : ℤ) :
    homologyMap (correction h) i = homologyMap (total.map f (ComplexShape.up ℤ)) i := by
  have hh := (Homotopy.nullHomotopy' (homotopyTerm h)).homologyMap_eq i
  simp only [homologyMap_zero] at hh
  simp only [correction,homologyMap_sub,hh,sub_zero]

lemma ι_d (K : Bic (R := R)) (p p' q q' i i' : ℤ) (hpq : p+q=i)
    (hp : p+1=p') (hq : q+1=q') (hi : i+1=i') :
    K.ιTotal (ComplexShape.up ℤ) p q i hpq ≫ (K.total (ComplexShape.up ℤ)).d i i' =
      (K.d p p').f q ≫ K.ιTotal (ComplexShape.up ℤ) p' q i' (by change p'+q=i'; omega) +
      ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p,q) •
        ((K.X p).d q q' ≫ K.ιTotal (ComplexShape.up ℤ) p q' i' (by change p+q'=i'; omega)) := by
  change _ ≫ (K.D₁ (ComplexShape.up ℤ) i i' + K.D₂ (ComplexShape.up ℤ) i i') = _
  rw [comp_add,ι_D₁,ι_D₂,
    d₁_eq K (ComplexShape.up ℤ) hp q i' (by change p'+q=i'; omega),
    d₂_eq K (ComplexShape.up ℤ) p hq i' (by change p+q'=i'; omega)]
  change (1 : ℤˣ) • _ + _ = _
  rw [one_smul]

 
lemma correction_lowers {f : K ⟶ L} (h : RowHomotopy f) (p q i : ℤ) (hpq : p+q=i) :
    ∃ a : (K.X p).X q ⟶ (L.X (p-1)).X (q+1),
    K.ιTotal (ComplexShape.up ℤ) p q i hpq ≫ (correction h).f i =
      a ≫ L.ιTotal (ComplexShape.up ℤ) (p-1) (q+1) i (by change p-1+(q+1)=i; omega) := by
  let e := ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  refine ⟨-(e (p,q) • ((K.X p).d q (q+1) ≫ h.h p (q+1)) +
    e (p-1,q) • (h.h p q ≫ (L.X (p-1)).d q (q+1))), ?_⟩
  have hm := Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (i-1) i by change i-1+1=i; omega)
    (show (ComplexShape.up ℤ).Rel i (i+1) from rfl) (homotopyTerm h)
  dsimp only [correction,sub_f_apply]
  rw [comp_sub,hm,comp_add,←Category.assoc,ι_d K p (p+1) q (q+1) i (i+1) hpq rfl rfl rfl]
  simp only [add_comp,Category.assoc,ι_homotopyTerm,ι_homotopyTerm_assoc,Linear.units_smul_comp]
  have hLd : L.ιTotal (ComplexShape.up ℤ) (p-1) q (i-1) (by change p-1+q=i-1; omega) ≫
      (L.total (ComplexShape.up ℤ)).d (i-1) i =
      (L.d (p-1) p).f q ≫ L.ιTotal (ComplexShape.up ℤ) p q i hpq +
      e (p-1,q) • ((L.X (p-1)).d q (q+1) ≫
        L.ιTotal (ComplexShape.up ℤ) (p-1) (q+1) i (by change p-1+(q+1)=i; omega)) := by
    exact ι_d L (p-1) p q (q+1) (i-1) i (by omega) (by omega) rfl (by omega)
  rw [hLd]
  simp only [comp_add,Linear.comp_units_smul]
  
  rw [ιTotal_map]
  rw [h.equation p q]
  simp only [add_comp,Category.assoc,XXIsoOfEq_hom_ιTotal]
  simp only [neg_comp,add_comp,Linear.units_smul_comp,Category.assoc]
  abel

end Lech.TotalGhost
end

end OAI
