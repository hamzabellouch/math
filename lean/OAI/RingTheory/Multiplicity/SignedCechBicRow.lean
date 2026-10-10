import Mathlib
import OAI.RingTheory.Multiplicity.SourceGradedCechHomology

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Lech.FilteredCech (tensorBic tensorBic_total_map tensorBic_isZero)
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℕ)
  (H : ∀ i, Homotopy (z i ^ m • 𝟙 F) 0)

def bicRowHomotopy (t : ℤ) :
    TotalGhost.RowHomotopy ((tensorBic F).map
      (positiveInclusion I z hz (by omega : t ≤ t+(m:ℤ)))) :=
  TotalGhost.RowHomotopy.ofRows (positiveRowHomotopy I z hz F m H t)

 
def twistIndex (t : ℤ) (m : ℕ) : ℕ → ℤ
  | 0 => t
  | n+1 => twistIndex t m n+(m:ℤ)

lemma twistIndex_eq (t : ℤ) (m N : ℕ) : twistIndex t m N=t+(m*N:ℕ) := by
  induction N with
  | zero => simp [twistIndex]
  | succ N ih =>
    rw [twistIndex,ih,Nat.mul_succ,Nat.cast_add,add_assoc]

lemma twistIndex_le (t : ℤ) (m N : ℕ) : t ≤ twistIndex t m N := by
  rw [twistIndex_eq]
  omega

def twistStep (t : ℤ) (n : ℕ) :
    positive I z hz (twistIndex t m (n+1)) ⟶ positive I z hz (twistIndex t m n) :=
  positiveInclusion I z hz (by dsimp only [twistIndex]; omega)

lemma twistPath (t : ℤ) (N : ℕ) :
    TotalGhost.towerPath (X := fun n => positive I z hz (twistIndex t m n))
      (twistStep I z hz m t) N =
      positiveInclusion I z hz (twistIndex_le t m N) := by
  induction N with
  | zero => simp only [twistIndex,TotalGhost.towerPath,positiveInclusion_refl]
  | succ N ih =>
    rw [TotalGhost.towerPath,ih]
    exact positiveInclusion_comp I z hz _ _

include H in
 

lemma positive_homologyMap_zero (l b : ℤ)
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j)) (N : ℕ) (hN : b-l<(N:ℤ))
    (t : ℤ) (i : ℤ) :
    homologyMap ((TensorTotal.Right.functor F).map
      (positiveInclusion I z hz (show t ≤ t+(m*N:ℕ) by omega))) i=0 := by
  let X : ℕ → TotalGhost.Bic (R := R) := fun n => (tensorBic F).obj (positive I z hz (twistIndex t m n))
  let f : ∀ n, X (n+1) ⟶ X n := fun n => (tensorBic F).map (twistStep I z hz m t n)
  have hrow : ∀ n, TotalGhost.RowHomotopy (f n) :=
    fun n => bicRowHomotopy I z hz F m H (twistIndex t m n)
  have hh := TotalGhost.homologyMap_path_eq_zero f hrow N l b hN
    (fun p q hp => tensorBic_isZero F _ p q (hb p (Or.inr hp)))
    (fun p q hp => tensorBic_isZero F _ p q (hb p (Or.inl hp))) i
  dsimp only [f] at hh
  have he := TotalGhost.towerPath_map (X := fun n => positive I z hz (twistIndex t m n))
    (twistStep I z hz m t) (tensorBic F) N
  rw [he,twistPath] at hh
  have hc := congrArg (fun k => homologyMap k i)
    (tensorBic_total_map F (positiveInclusion I z hz (twistIndex_le t m N)))
  have hh' : ∀ ht : t ≤ twistIndex t m N,
      homologyMap ((TensorTotal.Right.functor F).map (positiveInclusion I z hz ht)) i=0 :=
    fun _ => hc.symm.trans hh
  rw [twistIndex_eq t m N] at hh'
  exact hh' _
end Lech.SignedCech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma positive_homologyMap_zero_of_le (m : ℕ) (H : ∀ i, Homotopy (z i^m • 𝟙 F) 0)
    (l b : ℤ) (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (N : ℕ) (hN : b-l<(N:ℤ)) (t : ℤ) (M : ℕ) (hM : m*N≤M) (i : ℤ) :
    homologyMap ((TensorTotal.Right.functor F).map
      (positiveInclusion I z hz (show t≤t+(M:ℤ) by omega))) i=0 := by
  have h1 : t ≤ t+(m*N:ℕ) := by omega
  have h2 : t+(m*N:ℕ) ≤ t+(M:ℤ) := by omega
  rw [←positiveInclusion_comp I z hz h1 h2,Functor.map_comp,homologyMap_comp,
    positive_homologyMap_zero I z hz F m H l b hb N hN t i,comp_zero]

 

lemma exists_uniform_positive_nilpotence (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ MD : ℕ, ∀ t : ℤ, ∀ M : ℕ, MD≤M → ∀ i : ℤ,
      homologyMap ((TensorTotal.Right.functor F).map
        (positiveInclusion I z hz (show t≤t+(M:ℤ) by omega))) i=0 := by
  classical
  obtain ⟨m,H⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F l b hp hfin hb ha
  let N : ℕ := (b-l).toNat+1
  have hN : b-l<(N:ℤ) := by dsimp [N]; omega
  refine ⟨m*N,?_⟩
  intro t M hM i
  exact positive_homologyMap_zero_of_le I z hz F m (fun i => (H i).some) l b hb N hN t M hM i
end Lech.SignedCech


namespace Lech.SignedFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (w : R) (d : ℕ)

lemma order_mul_le (t : ℤ) (M n : ℕ) : order d (t+(M:ℤ)) n ≤ M+order d t n := by
  unfold order
  omega

variable (hw : w∈I^d)
include hw
lemma smul_mem_shift (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) (x : piece I w d t) :
    a • x.val ∈ piece I w d (t+(M:ℤ)) := by
  obtain ⟨n,b,hb⟩ := exists_fraction I w d hw t x
  have hab : a*(b:R) ∈ I^(order d (t+(M:ℤ)) n) := by
    apply Ideal.pow_le_pow_right (order_mul_le d t M n)
    rw [pow_add]
    exact Ideal.mul_mem_mul ha b.property
  rw [←hb]
  change a • Localization.mk (b:R) (⟨w^n,n,rfl⟩ : Submonoid.powers w) ∈ _
  rw [Localization.smul_mk]
  exact fraction_mem I w d (t+(M:ℤ)) n ⟨a*(b:R),hab⟩

 
def multiply (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) :
    piece I w d t →ₗ[R] piece I w d (t+(M:ℤ)) where
  toFun x := ⟨a • x.val,smul_mem_shift I w d hw t M a ha x⟩
  map_add' _ _ := Subtype.ext (smul_add _ _ _)
  map_smul' _ _ := Subtype.ext (smul_comm _ _ _)

lemma inclusion_multiply (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) (x : piece I w d t) :
    Submodule.inclusion (antitone I w d (by omega : t ≤ t+(M:ℤ)))
      (multiply I w d hw t M a ha x)=a • x := rfl
end Lech.SignedFraction


namespace Lech.ComplexLift
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

 

def lift (f : K ⟶ L) (a : L ⟶ L) [∀ i, Mono (f.f i)]
    (r : ∀ i, L.X i ⟶ K.X i) (hr : ∀ i, r i ≫ f.f i=a.f i) : L ⟶ K where
  f := r
  comm' i j _ := by
    apply (cancel_mono (f.f j)).mp
    rw [Category.assoc,←f.comm i j,←Category.assoc,hr,a.comm,Category.assoc,hr]

@[reassoc] lemma lift_comp (f : K ⟶ L) (a : L ⟶ L) [∀ i, Mono (f.f i)]
    (r : ∀ i, L.X i ⟶ K.X i) (hr : ∀ i, r i ≫ f.f i=a.f i) :
    lift f a r hr ≫ f=a := by
  apply Hom.ext
  funext i
  exact hr i
end Lech.ComplexLift


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
variable {R : Type u} [CommRing R] {ι : Type v} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c}

lemma homologyMap_smul (a : R) (f : K ⟶ L) (i : ι) :
    homologyMap (a • f) i=a • homologyMap f i := by
  change ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat.{u} R) c i).map (a • f))=
    a • ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat.{u} R) c i).map f)
  have he : (shortComplexFunctor (ModuleCat.{u} R) c i).map (a • f)=
      a • (shortComplexFunctor (ModuleCat.{u} R) c i).map f := rfl
  rw [he,ShortComplex.homologyMap_smul]
end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
variable {R : Type u} [CommRing R] {ι : Type v} {ι' : Type w}
  {c : ComplexShape ι} {c' : ComplexShape ι'}
  {K L : HomologicalComplex (ModuleCat.{u} R) c}

lemma extendMap_smul (r : R) (f : K ⟶ L) (e : c.Embedding c') :
    extendMap (r • f) e=r • extendMap f e := by
  apply Hom.ext
  funext j
  by_cases hj : ∃ i, e.f i=j
  · obtain ⟨i,hi⟩ := hj
    simp only [smul_f_apply,extendMap_f _ e hi,CategoryTheory.Linear.comp_smul,
      CategoryTheory.Linear.smul_comp]
  · exact (K.isZero_extend_X e j (by simpa only [not_exists] using hj)).eq_of_src _ _
end Lech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)

instance inclusion_f_mono {s t : ℤ} (hst : s ≤ t) (n : ℕ) :
    Mono ((inclusion I z hz hst).f n) :=
  (ModuleCat.mono_iff_injective _).mpr
    (LocalizationCech.inclusionLinear_injective z (term I z t) (term I z s)
      (fun _ => SignedFraction.antitone I _ _ hst) n)

 

def cochainMultiply (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) (n : ℕ) :
    (complex I z hz t).X n ⟶ (complex I z hz (t+(M:ℤ))).X n :=
  ModuleCat.ofHom
    { toFun x b := SignedFraction.multiply I _ _
        (FilteredCech.denominator_mem I z hz (ActualCech.intersection b)) t M a ha (x b)
      map_add' x y := by funext b; exact map_add _ _ _
      map_smul' r x := by
        funext b
        exact map_smul (SignedFraction.multiply I _ _
          (FilteredCech.denominator_mem I z hz (ActualCech.intersection b)) t M a ha) r (x b) }

lemma cochainMultiply_inclusion (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) (n : ℕ) :
    cochainMultiply I z hz t M a ha n ≫
      (inclusion I z hz (by omega : t ≤ t+(M:ℤ))).f n = a • 𝟙 ((complex I z hz t).X n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

def multiply (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) :
    complex I z hz t ⟶ complex I z hz (t+(M:ℤ)) :=
  ComplexLift.lift (inclusion I z hz (by omega : t ≤ t+(M:ℤ))) (a • 𝟙 _)
    (cochainMultiply I z hz t M a ha) (cochainMultiply_inclusion I z hz t M a ha)

@[reassoc] lemma multiply_inclusion (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) :
    multiply I z hz t M a ha ≫ inclusion I z hz (by omega : t ≤ t+(M:ℤ)) =
      a • 𝟙 (complex I z hz t) := ComplexLift.lift_comp _ _ _ _

 
def positiveMultiply (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) :
    positive I z hz t ⟶ positive I z hz (t+(M:ℤ)) :=
  FiniteComplex.dropBottomMap (augmented I z hz t) 0 (augmented_boundedBelow I z hz t)
    (augmented_boundedBelow I z hz (t+(M:ℤ)))
    (extendMap (multiply I z hz t M a ha) ComplexShape.embeddingUpNat)

@[reassoc] lemma positiveMultiply_inclusion (t : ℤ) (M : ℕ) (a : R) (ha : a∈I^M) :
    positiveMultiply I z hz t M a ha ≫ positiveInclusion I z hz (by omega : t ≤ t+(M:ℤ)) =
      a • 𝟙 (positive I z hz t) := by
  apply (cancel_mono (kernel.ι (FiniteComplex.bottomProjection (augmented I z hz t) 0
    (augmented_boundedBelow I z hz t)))).mp
  simp only [positiveMultiply, positiveInclusion]
  let ι (j : ℤ) := kernel.ι (FiniteComplex.bottomProjection (augmented I z hz j) 0
    (augmented_boundedBelow I z hz j))
  have hM : positiveMultiply I z hz t M a ha ≫ ι (t+(M:ℤ)) =
      ι t ≫ extendMap (multiply I z hz t M a ha) ComplexShape.embeddingUpNat :=
    FiniteComplex.dropBottomMap_ι (augmented I z hz t) 0
      (augmented_boundedBelow I z hz t) (augmented_boundedBelow I z hz (t+(M:ℤ))) _
  have hI : positiveInclusion I z hz (show t ≤ t+(M:ℤ) by omega) ≫ ι t =
      ι (t+(M:ℤ)) ≫ extendMap (inclusion I z hz (show t ≤ t+(M:ℤ) by omega))
        ComplexShape.embeddingUpNat :=
    FiniteComplex.dropBottomMap_ι (augmented I z hz (t+(M:ℤ))) 0
      (augmented_boundedBelow I z hz (t+(M:ℤ))) (augmented_boundedBelow I z hz t) _
  have he : extendMap (multiply I z hz t M a ha) ComplexShape.embeddingUpNat ≫
      extendMap (inclusion I z hz (show t ≤ t+(M:ℤ) by omega)) ComplexShape.embeddingUpNat =
        a • 𝟙 (augmented I z hz t) := by
    rw [← extendMap_comp, multiply_inclusion, Lech.extendMap_smul, extendMap_id]
    rfl
  refine (Category.assoc _ _ _).trans
    ((congrArg (positiveMultiply I z hz t M a ha ≫ ·) hI).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ extendMap (inclusion I z hz (show t ≤ t+(M:ℤ) by omega))
          ComplexShape.embeddingUpNat) hM).trans
          ((Category.assoc _ _ _).trans ((congrArg (ι t ≫ ·) he).trans ?_)))))
  exact (CategoryTheory.Linear.comp_smul _ _ _ (ι t) a (𝟙 (augmented I z hz t))).trans
    ((congrArg (a • ·) (Category.comp_id (ι t))).trans
      ((congrArg (a • ·) (Category.id_comp (ι t))).symm.trans
        (CategoryTheory.Linear.smul_comp _ _ _ a (𝟙 (positive I z hz t)) (ι t)).symm))

end Lech.SignedCech


namespace Lech.TensorTotal.Right
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)
  {F G : CochainComplex (ModuleCat.{u} R) ℤ}

lemma map_smul (a : R) (f : F ⟶ G) : (functor K).map (a • f)=a • (functor K).map f := by
  apply Hom.ext
  funext i
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [map_f, smul_f_apply]
  refine (ι_degreeMap K (fun j => a • f.f j) p q i hpq).trans ?_
  change (K.X p ◁ (a • f.f q)) ≫ ιMapBifunctor K G (curriedTensor (ModuleCat.{u} R))
    (.up ℤ) p q i hpq = _
  rw [MonoidalLinear.whiskerLeft_smul]
  exact (CategoryTheory.Linear.smul_comp _ _ _ a _ _).trans
    ((congrArg (a • ·) (ι_degreeMap K f.f p q i hpq).symm).trans
      (CategoryTheory.Linear.comp_smul _ _ _ _ a _).symm)

end Lech.TensorTotal.Right


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

 

lemma annihilator_of_positive_nilpotence (t : ℤ) (M : ℕ) (i : ℤ)
    (hnil : homologyMap ((TensorTotal.Right.functor F).map
      (positiveInclusion I z hz (show t≤t+(M:ℤ) by omega))) i=0) :
    I^M ≤ Module.annihilator R
      (((TensorTotal.Right.functor F).obj (positive I z hz t)).homology i) := by
  intro a ha
  rw [Module.mem_annihilator]
  have hf := congrArg (fun f => homologyMap ((TensorTotal.Right.functor F).map f) i)
    (positiveMultiply_inclusion I z hz t M a ha)
  rw [Functor.map_comp,homologyMap_comp,hnil,comp_zero,
    TensorTotal.Right.map_smul,CategoryTheory.Functor.map_id,Lech.homologyMap_smul,homologyMap_id] at hf
  intro x
  have hx := congrArg (fun f => f x) hf
  exact hx.symm

 

lemma exists_uniform_positive_annihilator (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ MD : ℕ, ∀ t : ℤ, ∀ i : ℤ,
      I^MD ≤ Module.annihilator R
        (((TensorTotal.Right.functor F).obj (positive I z hz t)).homology i) := by
  obtain ⟨MD,hMD⟩ := exists_uniform_positive_nilpotence I z hz F l b hp hfin hb ha
  exact ⟨MD,fun t i => annihilator_of_positive_nilpotence I z hz F t MD i (hMD t MD le_rfl i)⟩

lemma positive_homology_powerTorsion (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic)
    (t i : ℤ) :
    powerTorsion I (((TensorTotal.Right.functor F).obj (positive I z hz t)).homology i) := by
  obtain ⟨MD,hMD⟩ := exists_uniform_positive_annihilator I z hz F l b hp hfin hb ha
  exact ⟨MD,hMD t i⟩
end Lech.SignedCech


namespace Lech.SignedCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)

lemma complex_nat (t : ℕ) : complex I z hz (t:ℤ)=FilteredCech.complex I z hz t := by
  have hT : term I z (t:ℤ)=FilteredCech.term I z t := funext (term_nat I z t)
  unfold complex FilteredCech.complex
  congr 1

lemma positive_nat (t : ℕ) : positive I z hz (t:ℤ)=FilteredCech.positive I z hz t := by
  unfold positive FilteredCech.positive augmented FilteredCech.augmented
  simp only [complex_nat]
end Lech.SignedCech


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma positive_homology_powerTorsion (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic)
    (t : ℕ) (i : ℤ) :
    powerTorsion I (((TensorTotal.Right.functor F).obj (positive I z hz t)).homology i) := by
  rw [←SignedCech.positive_nat I z hz t]
  exact SignedCech.positive_homology_powerTorsion I z hz F l b hp hfin hb ha t i
end Lech.FilteredCech


namespace Lech
open CochainComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R]

lemma prop_tensor_free_single (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (zs : List R) (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M]
    (j i : ℤ)
    (h : P ((Koszul.tensor zs ((singleFunctor (ModuleCat R) 0).obj
      (ModuleCat.of R R))).homology (i - j))) :
    P ((Koszul.tensor zs ((singleFunctor (ModuleCat R) j).obj M)).homology i) := by
  apply P.prop_of_iso (Koszul.tensorSingleHomologyIso zs M j i).symm
  simpa only [Functor.comp_obj, Koszul.tensorFunctor_obj, homologyFunctor] using
    prop_additive_free P
    (singleFunctor (ModuleCat R) 0 ⋙ Koszul.tensorFunctor zs ⋙
      homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (i - j))
    (by simpa only [Functor.comp_obj, Koszul.tensorFunctor_obj, homologyFunctor] using h) M

 

theorem acyclicity_of_koszul (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (zs : List R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < -(zs.length : ℤ) ∨ 0 < j → IsZero (F.X j))
    (hz : ∀ a ∈ zs, Nonempty (Homotopy (a • 𝟙 F) 0))
    (hK : ∀ i < 0, P ((Koszul.tensor zs
      ((singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))).homology i))
    (i : ℤ) (hi : i < 0) : P (F.homology i) := by
  have ht : P ((Koszul.tensor zs F).homology (i - zs.length)) := by
    rw [← Koszul.tensorFunctor_obj]
    apply FiniteComplex.homology_devissage P (Koszul.tensorFunctor zs)
      (Koszul.tensorSplitting zs) (-(zs.length : ℤ)) (zs.length + 1) F
      (i - zs.length) (fun j hj => hb j (by omega))
    intro j
    by_cases hj : j < -(zs.length : ℤ) ∨ 0 < j
    · exact P.prop_of_isZero ((homologyFunctor (ModuleCat R) (ComplexShape.up ℤ)
        (i - zs.length)).map_isZero ((Koszul.tensorFunctor zs).map_isZero
          ((single (ModuleCat R) (ComplexShape.up ℤ) j).map_isZero (hb j hj))))
    · have := hf j
      have := hfin j
      rw [Koszul.tensorFunctor_obj]
      apply prop_tensor_free_single P zs (F.X j) j (i - zs.length)
      exact hK _ (by omega)
  simpa using Koszul.prop_homology_of_tensor P zs F hz (i - zs.length) ht

end Lech
end

end OAI
