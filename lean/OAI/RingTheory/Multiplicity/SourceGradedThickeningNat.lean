import Mathlib
import OAI.RingTheory.Multiplicity.LechMapCochain

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

def thickeningNatSequence (M : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk
    (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M))
    (cokernel.π _) (cokernel.condition _)

lemma thickeningNatSequence_shortExact (M : ℕ) : (thickeningNatSequence I z hz M).ShortExact :=
  { exact := ShortComplex.exact_cokernel _
    mono_f := by
      change Mono (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M))
      infer_instance
    epi_g := by
      change Epi (cokernel.π (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M)))
      infer_instance }

def thickeningAugSequence (M : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (thickeningNatSequence I z hz M).map (ComplexShape.embeddingUpNat.extendFunctor _)

lemma thickeningAugSequence_shortExact (M : ℕ) : (thickeningAugSequence I z hz M).ShortExact :=
  Lech.extend_shortExact _ (thickeningNatSequence_shortExact I z hz M) _

 

def thickeningPositiveSequence (M : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  FiniteComplex.dropShortComplex (thickeningAugSequence I z hz M) 0
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) (0+M))
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) 0)
    (augmentedThickening_boundedBelow I z hz M)

lemma thickeningPositiveSequence_shortExact (M : ℕ) :
    (thickeningPositiveSequence I z hz M).ShortExact :=
  FiniteComplex.dropShortComplex_shortExact _ _ _ _ _ (thickeningAugSequence_shortExact I z hz M)

lemma thickeningPositiveSequence_f (M : ℕ) :
    (thickeningPositiveSequence I z hz M).f =
      FilteredCech.positiveInclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M) := rfl

lemma thickeningPositiveSequence_X₂ (M : ℕ) :
    (thickeningPositiveSequence I z hz M).X₂ = FilteredCech.positive I z (coordinate_mem I z hz) 0 := rfl

lemma thickeningPositiveSequence_X₃ (M : ℕ) :
    (thickeningPositiveSequence I z hz M).X₃ = thickeningCech I z hz M := rfl

def thickeningNatSequenceMap {M N : ℕ} (hMN : M≤N) :
    thickeningNatSequence I z hz N ⟶ thickeningNatSequence I z hz M where
  τ₁ := FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.add_le_add_left hMN 0)
  τ₂ := 𝟙 _
  τ₃ := finiteThickeningTransition I z hz 0 hMN
  comm₁₂ := by simp only [thickeningNatSequence,Category.comp_id,FilteredCech.inclusion_comp]
  comm₂₃ := by simp only [thickeningNatSequence,finiteThickeningTransition,
    cokernel.map,cokernel.π_desc,Category.id_comp]

def thickeningPositiveSequenceMap {M N : ℕ} (hMN : M≤N) :
    thickeningPositiveSequence I z hz N ⟶ thickeningPositiveSequence I z hz M :=
  FiniteComplex.dropShortComplexMap 0
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) (0+N))
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) 0)
    (augmentedThickening_boundedBelow I z hz N)
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) (0+M))
    (FilteredCech.augmented_boundedBelow I z (coordinate_mem I z hz) 0)
    (augmentedThickening_boundedBelow I z hz M)
    ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapShortComplex.map
      (thickeningNatSequenceMap I z hz hMN))

instance thickeningPositiveSequenceMap_middleIso {M N : ℕ} (hMN : M≤N) :
    IsIso (thickeningPositiveSequenceMap I z hz hMN).τ₂ := by
  have hm : IsIso (thickeningNatSequenceMap I z hz hMN).τ₂ := by
    change IsIso (𝟙 _)
    infer_instance
  have he : IsIso (((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapShortComplex.map
      (thickeningNatSequenceMap I z hz hMN)).τ₂) := by
    change IsIso ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map
      (thickeningNatSequenceMap I z hz hMN).τ₂)
    infer_instance
  exact @FiniteComplex.isIso_dropShortComplexMap_τ₂ _ _ _ _ _ 0 _ _ _ _ _ _ _ he

lemma thickeningPositiveSequenceMap_τ₁ {M N : ℕ} (hMN : M≤N) :
    (thickeningPositiveSequenceMap I z hz hMN).τ₁ =
      FilteredCech.positiveInclusion I z (coordinate_mem I z hz) (Nat.add_le_add_left hMN 0) := rfl

lemma thickeningPositiveSequenceMap_τ₃ {M N : ℕ} (hMN : M≤N) :
    (thickeningPositiveSequenceMap I z hz hMN).τ₃=thickeningCechTransition I z hz hMN := rfl

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

def thickeningTensorSequence (M : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (thickeningPositiveSequence I z hz M).map (TensorTotal.Right.functor F)

lemma thickeningTensorSequence_shortExact (hF : ∀ j, Module.Flat R (F.X j)) (M : ℕ) :
    (thickeningTensorSequence I z hz F M).ShortExact :=
  TensorTotal.Right.shortExact F hF _ (thickeningPositiveSequence_shortExact I z hz M)

def thickeningTensorSequenceMap {M N : ℕ} (hMN : M≤N) :
    thickeningTensorSequence I z hz F N ⟶ thickeningTensorSequence I z hz F M :=
  (TensorTotal.Right.functor F).mapShortComplex.map (thickeningPositiveSequenceMap I z hz hMN)
end Lech.SourceGraded


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v
variable {R : Type*} [CommRing R]
 

lemma stableImage_isIso {A B C : ModuleCat.{v} R} (u : A ⟶ B) (v : A ⟶ C)
    (f : B ⟶ C) (h : u ≫ f = v) (hv : Function.Injective v)
    (hr : LinearMap.range f.hom = LinearMap.range v.hom) :
    IsIso (u ≫ factorThruImage f) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have he : u ≫ factorThruImage f ≫ Limits.image.ι f = v := by rw [Limits.image.fac, h]
  constructor
  · intro x y hxy
    apply hv
    have hx := congrArg (fun g => g x) he
    have hy := congrArg (fun g => g y) he
    exact hx.symm.trans ((congrArg (Limits.image.ι f) hxy).trans hy)
  · intro y
    have hy : (Limits.image.ι f) y ∈ LinearMap.range v.hom := by
      rw [← hr]
      have he' := congrArg (fun g => g y) (ModuleCat.imageIsoRange_hom_subtype f)
      exact he' ▸ ((ModuleCat.imageIsoRange f).hom y).property
    obtain ⟨x,hx⟩ := hy
    refine ⟨x, ?_⟩
    apply (ModuleCat.mono_iff_injective (Limits.image.ι f)).mp inferInstance
    have hx' := congrArg (fun g => g x) he
    exact hx'.trans hx

end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

 

lemma shortExactTransition_stableImage_isIso
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)}
    (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact) [IsIso φ.τ₂]
    (i : ℤ) (hleft : homologyMap T.f i=0) (htrans : homologyMap φ.τ₁ (i+1)=0) :
    IsIso (inv (homologyMap φ.τ₂ i) ≫ homologyMap S.g i ≫
      factorThruImage (homologyMap φ.τ₃ i)) := by
  let a := inv (homologyMap φ.τ₂ i) ≫ homologyMap S.g i
  let b := homologyMap T.g i
  let f := homologyMap φ.τ₃ i
  have hc : a ≫ f=b := by
    dsimp only [a,b,f]
    rw [Category.assoc,←homologyMap_comp,←φ.comm₂₃,homologyMap_comp,
      IsIso.inv_hom_id_assoc]
  have hb : Mono b := (hT.homology_exact₂ i).mono_g hleft
  have hδ : f ≫ hT.δ i (i+1) rfl=0 := by
    rw [←HomologySequence.δ_naturality φ hS hT i (i+1) rfl,htrans,comp_zero]
  have hr : LinearMap.range f.hom=LinearMap.range b.hom := by
    apply le_antisymm
    · rintro x ⟨y,rfl⟩
      have hy : (hT.δ i (i+1) rfl) (f y)=0 := by
        change (f ≫ hT.δ i (i+1) rfl) y=0
        rw [hδ]
        rfl
      exact (ShortComplex.moduleCat_exact_iff _).mp (hT.homology_exact₃ i (i+1) rfl) _ hy
    · rintro x ⟨y,rfl⟩
      exact ⟨a y,congrArg (fun g => g y) hc⟩
  have := stableImage_isIso a b f hc ((ModuleCat.mono_iff_injective b).mp hb) hr
  simpa only [a,Category.assoc] using this
end Lech


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

instance thickeningTensorSequenceMap_middleIso {M N : ℕ} (hMN : M≤N) :
    IsIso (thickeningTensorSequenceMap I z hz F hMN).τ₂ := by
  change IsIso ((TensorTotal.Right.functor F).map (thickeningPositiveSequenceMap I z hz hMN).τ₂)
  infer_instance

lemma thickeningTensorSequenceMap_τ₃ {M N : ℕ} (hMN : M≤N) :
    (thickeningTensorSequenceMap I z hz F hMN).τ₃=
      (TensorTotal.Right.functor F).map (thickeningCechTransition I z hz hMN) := rfl

 

def geometricStructureMap (M : ℕ) :
    (TensorTotal.Right.functor F).obj (FilteredCech.positive I z (coordinate_mem I z hz) 0) ⟶
      (TensorTotal.Right.functor F).obj (thickeningCech I z hz M) :=
  (thickeningTensorSequence I z hz F M).g

@[reassoc] lemma geometricStructureMap_transition {M N : ℕ} (hMN : M≤N) :
    geometricStructureMap I z hz F N ≫
      (TensorTotal.Right.functor F).map (thickeningCechTransition I z hz hMN) =
      (thickeningTensorSequenceMap I z hz F hMN).τ₂ ≫ geometricStructureMap I z hz F M := by
  exact (thickeningTensorSequenceMap I z hz F hMN).comm₂₃.symm

lemma uniform_step_to_gap (P : ∀ a b : ℕ, a≤b → Prop) (MD : ℕ)
    (hP : ∀ a d : ℕ, MD≤d → P a (a+d) (Nat.le_add_right a d))
    (a b : ℕ) (hab : a≤b) (hgap : MD≤b-a) : P a b hab := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hab
  exact hP a d (by omega)

 

lemma exists_uniform_geometric_stableImage (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ MD : ℕ, ∀ M N : ℕ, ∀ hMN : M≤N, MD≤M → MD≤N-M → ∀ i : ℤ,
      IsIso (homologyMap (geometricStructureMap I z hz F N) i ≫
        factorThruImage (homologyMap ((TensorTotal.Right.functor F).map
          (thickeningCechTransition I z hz hMN)) i)) := by
  obtain ⟨MD,hMD⟩ := FilteredCech.exists_uniform_positive_nilpotence I z (coordinate_mem I z hz)
    F l b hp hfin hb ha
  have hflat : ∀ j, Module.Flat R (F.X j) := fun j => by have := hp j; infer_instance
  refine ⟨MD,fun M N hMN hM hgap i => ?_⟩
  let φ := thickeningTensorSequenceMap I z hz F hMN
  have hi₂ : IsIso φ.τ₂ := thickeningTensorSequenceMap_middleIso I z hz F hMN
  have hleft : homologyMap (thickeningTensorSequence I z hz F M).f i=0 := by
    exact hMD 0 M hM i
  have htrans : homologyMap φ.τ₁ (i+1)=0 := by
    change homologyMap ((TensorTotal.Right.functor F).map
      (FilteredCech.positiveInclusion I z (coordinate_mem I z hz) (Nat.add_le_add_left hMN 0))) (i+1)=0
    exact uniform_step_to_gap
      (fun a b hab => homologyMap ((TensorTotal.Right.functor F).map
        (FilteredCech.positiveInclusion I z (coordinate_mem I z hz) hab)) (i+1)=0)
      MD (fun a d hd => hMD a d hd (i+1)) (0+M) (0+N)
      (Nat.add_le_add_left hMN 0) (by omega)
  have hh := shortExactTransition_stableImage_isIso φ
    (thickeningTensorSequence_shortExact I z hz F hflat N)
    (thickeningTensorSequence_shortExact I z hz F hflat M) i hleft htrans
  exact (isIso_comp_left_iff (inv (homologyMap φ.τ₂ i)) _).mp hh
end Lech.SourceGraded

open CochainComplex CochainComplex.HomComplex
namespace Lech.Koszul

variable {R : Type*} [CommRing R]
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryTheory.Linear R C]
variable {F G : CochainComplex C ℤ}

omit [HasBinaryBiproducts C] in
lemma ofHom_smul (a : R) (f : F ⟶ G) :
    Cochain.ofHom (a • f) = a • Cochain.ofHom f := by
  ext i
  simp

 
noncomputable def coneRetraction {f : F ⟶ G} (h : Homotopy f 0) :
    mappingCone f ⟶ G :=
  mappingCone.desc f (Cochain.ofHomotopy h) (𝟙 G) (by simp)

@[simp] lemma inr_coneRetraction {f : F ⟶ G} (h : Homotopy f 0) :
    mappingCone.inr f ≫ coneRetraction h = 𝟙 G := by
  simp [coneRetraction]

 
noncomputable def coneScalarHomotopy (a b : R) (h : Homotopy (a • 𝟙 F) 0) :
    Homotopy (a • 𝟙 (mappingCone (b • 𝟙 F))) 0 := by
  let φ : F ⟶ F := b • 𝟙 F
  let H := Cochain.ofHomotopy h
  let α : Cochain F (mappingCone φ) (-2) :=
    -(H.comp (mappingCone.inl φ) (by norm_num))
  let β : Cochain F (mappingCone φ) (-1) :=
    H.comp (Cochain.ofHom (mappingCone.inr φ)) (add_zero (-1))
  refine (Cochain.equivHomotopy _ _).symm
    ⟨mappingCone.descCochain φ α β (by norm_num), ?_⟩
  have hH : δ (-1) 0 H = a • Cochain.ofHom (𝟙 F) := by
    simp [H, ofHom_smul]
  have hβ : δ (-1) 0 β = a • Cochain.ofHom (mappingCone.inr φ) := by
    dsimp [β]
    rw [δ_comp_ofHom]
    simp [hH, Cochain.smul_comp]
  have hα : δ (-2) (-1) α =
      -(H.comp (Cochain.ofHom φ) (add_zero (-1))).comp
        (Cochain.ofHom (mappingCone.inr φ)) (add_zero (-1)) +
      a • mappingCone.inl φ := by
    dsimp [α]
    rw [δ_neg, δ_comp H (mappingCone.inl φ) (by norm_num) 0 0 (-1)
      (by norm_num) (by norm_num) (by norm_num)]
    simp [mappingCone.δ_inl, hH, Cochain.smul_comp,
      Cochain.comp_assoc_of_second_is_zero_cochain, add_comm]
  rw [Cochain.ofHom_zero, add_zero, mappingCone.δ_descCochain _ _ _ _ 0 (by norm_num),
    hα, hβ]
  have hc : (H.comp (Cochain.ofHom φ) (add_zero (-1))).comp
        (Cochain.ofHom (mappingCone.inr φ)) (add_zero (-1)) =
      (Cochain.ofHom φ).comp β (by norm_num) := by
    simp [φ, β, ofHom_smul, Cochain.comp_smul, Cochain.smul_comp]
  rw [hc]
  simp only [Int.reduceNeg, Int.negOnePow_zero, one_smul]
  rw [show -(Cochain.ofHom φ).comp β (zero_add (-1)) + a • mappingCone.inl φ +
    (Cochain.ofHom φ).comp β (zero_add (-1)) = a • mappingCone.inl φ by abel]
  simp only [Cochain.comp_smul, ← smul_add, mappingCone.id, ofHom_smul]
  rfl

 
noncomputable def coneEntryHomotopy (a : R) (F : CochainComplex C ℤ) :
    Homotopy (a • 𝟙 (mappingCone (a • 𝟙 F))) 0 := by
  let φ : F ⟶ F := a • 𝟙 F
  refine (Cochain.equivHomotopy _ _).symm
    ⟨mappingCone.descCochain φ (0 : Cochain F (mappingCone φ) (-2))
      (mappingCone.inl φ) (by norm_num), ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ 0 (by norm_num)]
  simp only [δ_zero, zero_add, Int.negOnePow_zero, one_smul, mappingCone.δ_inl,
    Cochain.ofHom_zero, add_zero]
  simp only [φ, Linear.smul_comp, Category.id_comp, ofHom_smul, Cochain.smul_comp, Cochain.id_comp, Cochain.comp_smul,
    ← smul_add, mappingCone.id]

 
noncomputable def tensor (zs : List R) (F : CochainComplex C ℤ) : CochainComplex C ℤ :=
  zs.foldr (fun a K => mappingCone (a • 𝟙 K)) F

@[simp] lemma tensor_nil (F : CochainComplex C ℤ) : tensor ([] : List R) F = F := rfl
@[simp] lemma tensor_cons (a : R) (zs : List R) (F : CochainComplex C ℤ) :
    tensor (a :: zs) F = mappingCone (a • 𝟙 (tensor zs F)) := rfl

 
noncomputable def tensorScalarHomotopy (a : R) (zs : List R)
    (h : Homotopy (a • 𝟙 F) 0) : Homotopy (a • 𝟙 (tensor zs F)) 0 := by
  induction zs with
  | nil => exact h
  | cons b zs ih => exact coneScalarHomotopy a b ih

lemma tensor_entry_nullhomotopic (zs : List R) (F : CochainComplex C ℤ)
    (a : R) (ha : a ∈ zs) : Nonempty (Homotopy (a • 𝟙 (tensor zs F)) 0) := by
  induction zs with
  | nil => simp at ha
  | cons b zs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨coneEntryHomotopy a (tensor zs F)⟩
    · obtain ⟨h⟩ := ih ha
      exact ⟨coneScalarHomotopy a b h⟩

 
noncomputable def coneFunctor (a : R) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj F := mappingCone (a • 𝟙 F)
  map f := mappingCone.map _ _ f f (by simp [Linear.smul_comp, Linear.comp_smul])
  map_id _ := mappingCone.map_id _
  map_comp _ _ := mappingCone.map_comp _ _ _ _ _ _ _ _ _

instance (a : R) : (coneFunctor (C := C) a).Additive where
  map_add {F G} f g := by
    change mappingCone.map (a • 𝟙 F) (a • 𝟙 G) (f + g) (f + g)
        (by simp [Linear.smul_comp, Linear.comp_smul]) =
      mappingCone.map (a • 𝟙 F) (a • 𝟙 G) f f (by simp [Linear.smul_comp, Linear.comp_smul]) +
        mappingCone.map (a • 𝟙 F) (a • 𝟙 G) g g (by simp [Linear.smul_comp, Linear.comp_smul])
    ext i
    rw [HomologicalComplex.add_f_apply]
    simp [mappingCone.ext_from_iff _ (i + 1) i rfl, mappingCone.map,
      HomologicalComplex.add_f_apply, Preadditive.add_comp, Preadditive.comp_add]

noncomputable def termIso (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    ((coneFunctor a).obj F).X i ≅ F.X (i + 1) ⊞ F.X i :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (a • 𝟙 F) i (i + 1) rfl

lemma coneFunctor_map_f (a : R) {F G : CochainComplex C ℤ} (f : F ⟶ G) (i : ℤ) :
    ((coneFunctor a).map f).f i = (termIso a F i).hom ≫
      biprod.map (f.f (i + 1)) (f.f i) ≫ (termIso a G i).inv := by
  apply (mappingCone.ext_from_iff _ (i + 1) i rfl _ _).mpr
  constructor
  · simp [coneFunctor, mappingCone.map]
    change _ = HomologicalComplex.homotopyCofiber.inlX _ _ _ _ ≫ _
    simp [termIso, mappingCone.inl]
    have hF := HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom (a • 𝟙 F) (i+1) i rfl
    have hG := HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv (a • 𝟙 G) (i+1) i rfl
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ biprod.map (f.f (i+1)) (f.f i) ≫ (termIso a G i).inv) hF).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (termIso a G i).inv) (biprod.inl_map (f.f (i+1)) (f.f i))).trans
            ((Category.assoc _ _ _).trans ((congrArg (f.f (i+1) ≫ ·) hG))))))).symm
  · simp [coneFunctor, mappingCone.map]
    change _ = HomologicalComplex.homotopyCofiber.inrX _ _ ≫ _
    simp [termIso, mappingCone.inr]
    have hF := HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom (a • 𝟙 F) (i+1) i rfl
    have hG := HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv (a • 𝟙 G) (i+1) i rfl
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ biprod.map (f.f (i+1)) (f.f i) ≫ (termIso a G i).inv) hF).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (termIso a G i).inv) (biprod.inr_map (f.f (i+1)) (f.f i))).trans
            ((Category.assoc _ _ _).trans ((congrArg (f.f i ≫ ·) hG))))))).symm

noncomputable def biprodShortComplex (S T : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g) (by
    ext <;> simp)

noncomputable def biprodSplitting {S T : ShortComplex C} (s : S.Splitting) (t : T.Splitting) :
    (biprodShortComplex S T).Splitting where
  r := biprod.map s.r t.r
  s := biprod.map s.s t.s
  f_r := by
    dsimp [biprodShortComplex]
    ext <;> simp
  s_g := by
    dsimp [biprodShortComplex]
    ext <;> simp
  id := by
    change biprod.map s.r t.r ≫ biprod.map S.f T.f +
      biprod.map S.g T.g ≫ biprod.map s.s t.s = 𝟙 (S.X₂ ⊞ T.X₂)
    apply biprod.hom_ext
    · simpa [Preadditive.comp_add, Preadditive.add_comp, Category.assoc] using
        (biprod.fst : S.X₂ ⊞ T.X₂ ⟶ S.X₂) ≫= s.id
    · simpa [Preadditive.comp_add, Preadditive.add_comp, Category.assoc] using
        (biprod.snd : S.X₂ ⊞ T.X₂ ⟶ T.X₂) ≫= t.id

noncomputable def coneShortComplexIso (a : R) (S : ShortComplex (CochainComplex C ℤ))
    (i : ℤ) : (S.map (coneFunctor a)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) i) ≅
      biprodShortComplex (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) (i + 1)))
        (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)) :=
  ShortComplex.isoMk (termIso a S.X₁ i) (termIso a S.X₂ i) (termIso a S.X₃ i)
    (by simp [biprodShortComplex, coneFunctor_map_f])
    (by simp [biprodShortComplex, coneFunctor_map_f])

noncomputable def coneSplitting (a : R) (S : ShortComplex (CochainComplex C ℤ))
    (hs : ∀ i, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting) (i : ℤ) :
    ((S.map (coneFunctor a)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting :=
  (biprodSplitting (hs (i + 1)) (hs i)).ofIso (coneShortComplexIso a S i).symm

 
noncomputable def tensorMap (zs : List R) {F G : CochainComplex C ℤ}
    (f : F ⟶ G) : tensor zs F ⟶ tensor zs G := by
  induction zs with
  | nil => exact f
  | cons a zs ih =>
    exact mappingCone.map (a • 𝟙 (tensor zs F)) (a • 𝟙 (tensor zs G)) ih ih
      (by simp [Linear.smul_comp, Linear.comp_smul])

lemma tensorMap_id (zs : List R) (F : CochainComplex C ℤ) :
    tensorMap zs (𝟙 F) = 𝟙 (tensor zs F) := by
  induction zs with
  | nil => rfl
  | cons a zs ih =>
    change mappingCone.map (a • 𝟙 (tensor zs F)) (a • 𝟙 (tensor zs F))
      (tensorMap zs (𝟙 F)) (tensorMap zs (𝟙 F))
      (by simp [Linear.smul_comp, Linear.comp_smul]) = _
    simp only [ih, mappingCone.map_id]
    rfl

lemma tensorMap_comp (zs : List R) {F G H : CochainComplex C ℤ}
    (f : F ⟶ G) (g : G ⟶ H) :
    tensorMap zs (f ≫ g) = tensorMap zs f ≫ tensorMap zs g := by
  induction zs with
  | nil => rfl
  | cons a zs ih =>
    change mappingCone.map (a • 𝟙 (tensor zs F)) (a • 𝟙 (tensor zs H))
      (tensorMap zs (f ≫ g)) (tensorMap zs (f ≫ g))
      (by simp [Linear.smul_comp, Linear.comp_smul]) = _
    simp only [ih]
    exact mappingCone.map_comp _ _ _ _ _
      (by simp [Linear.smul_comp, Linear.comp_smul]) _ _
      (by simp [Linear.smul_comp, Linear.comp_smul])

 
noncomputable def tensorFunctor (zs : List R) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := tensor zs
  map := tensorMap zs
  map_id := tensorMap_id zs
  map_comp := tensorMap_comp zs

instance (zs : List R) : (tensorFunctor (C := C) zs).Additive := by
  induction zs with
  | nil => exact inferInstanceAs (𝟭 (CochainComplex C ℤ)).Additive
  | cons a zs ih =>
    change (tensorFunctor zs ⋙ coneFunctor a).Additive
    infer_instance

 

noncomputable def tensorSplitting (zs : List R) (S : ShortComplex (CochainComplex C ℤ))
    (hs : ∀ i, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting)
    (i : ℤ) :
    ((S.map (tensorFunctor zs)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting := by
  induction zs generalizing i with
  | nil => exact hs i
  | cons a zs ih =>
    exact coneSplitting a (S.map (tensorFunctor zs)) ih i

@[simp] lemma tensorFunctor_obj (zs : List R) (F : CochainComplex C ℤ) :
    (tensorFunctor zs).obj F = tensor zs F := rfl

 
noncomputable def tensorShiftIso (zs : List R) (F : CochainComplex C ℤ) (n : ℤ) :
    (tensor zs F)⟦n⟧ ≅ tensor zs (F⟦n⟧) := by
  induction zs with
  | nil => exact Iso.refl _
  | cons a zs ih =>
    refine mappingCone.shiftIso (a • 𝟙 (tensor zs F)) n ≪≫ ?_ ≪≫
      (coneFunctor a).mapIso ih
    apply eqToIso
    congr 1

variable [HasZeroObject C]

 

lemma cone_triangleh_epi {f : F ⟶ G} (h : Homotopy f 0) :
    Epi (mappingCone.triangleh f).mor₃ := by
  apply CategoryTheory.Pretriangulated.Triangle.epi₃ _ (HomotopyCategory.mappingCone_triangleh_distinguished f)
  change (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f = 0
  simpa using HomotopyCategory.eq_of_homotopy _ _ h

variable [CategoryWithHomology C]

 
noncomputable def coneHomologyProjection (f : F ⟶ G) (i : ℤ) :
    (mappingCone f).homology i ⟶ F.homology (i + 1) :=
  ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app
    (mappingCone f)).inv ≫
  (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map
    (mappingCone.triangleh f).mor₃ ≫
  ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 i
    (i + 1) (by omega)).hom.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj F) ≫
  ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (i + 1)).app F).hom

lemma coneHomologyProjection_epi {f : F ⟶ G} (h : Homotopy f 0) (i : ℤ) :
    Epi (coneHomologyProjection f i) := by
  have := cone_triangleh_epi h
  have := CategoryTheory.isSplitEpi_of_epi (mappingCone.triangleh f).mor₃
  have : Epi ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map
      (mappingCone.triangleh f).mor₃) := inferInstance
  have : Epi (((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 i
      (i + 1) (by omega)).hom.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj F)) := inferInstance
  unfold coneHomologyProjection
  exact epi_comp' (inferInstanceAs (Epi
    ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app (mappingCone f)).inv))
      (epi_comp' (inferInstanceAs (Epi ((HomotopyCategory.homologyFunctor C
        (ComplexShape.up ℤ) i).map (mappingCone.triangleh f).mor₃)))
        (epi_comp' (inferInstanceAs (Epi (((HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftIso 1 i (i+1) (by omega)).hom.app
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj F))))
          (inferInstanceAs (Epi ((HomotopyCategory.homologyFunctorFactors C
            (ComplexShape.up ℤ) (i+1)).app F).hom))))

lemma prop_homology_of_cone (P : ObjectProperty C) [P.IsClosedUnderQuotients]
    {f : F ⟶ G} (h : Homotopy f 0) (i : ℤ)
    (hp : P ((mappingCone f).homology i)) : P (F.homology (i + 1)) := by
  have := coneHomologyProjection_epi h i
  exact P.prop_of_epi (coneHomologyProjection f i) hp

 

lemma prop_homology_of_tensor (P : ObjectProperty C) [P.IsClosedUnderQuotients]
    (zs : List R) (F : CochainComplex C ℤ)
    (hzs : ∀ a ∈ zs, Nonempty (Homotopy (a • 𝟙 F) 0)) (i : ℤ)
    (hp : P ((tensor zs F).homology i)) : P (F.homology (i + zs.length)) := by
  induction zs generalizing i with
  | nil => simpa using hp
  | cons a zs ih =>
    obtain ⟨ha⟩ := hzs a (by simp)
    have h := prop_homology_of_cone P (tensorScalarHomotopy a zs ha) i hp
    have h' := ih (fun b hb => hzs b (by simp [hb])) (i + 1) h
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc,
      add_comm (1 : ℤ)] using h'

end Lech.Koszul
end

end OAI
