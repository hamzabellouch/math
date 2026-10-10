import Mathlib
import OAI.RingTheory.Multiplicity.TensorTotalHomologyProperty

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

private lemma extended_square {C : Type*} [Category C]
    {X X' Y Y' Z W : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X' ⟶ Y') (a : X' ⟶ Z) (b : Y' ⟶ W) (g : Z ⟶ W)
    (h : f ≫ b = a ≫ g) :
    (eX.hom ≫ f ≫ eY.inv) ≫ (eY.hom ≫ b) = (eX.hom ≫ a) ≫ g := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (eX.hom ≫ ·) h

private lemma inverse_square_comp {C : Type*} [Category C]
    {X X' Y Y' Z W : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ Z) (b : Y ⟶ W) (k : Z ⟶ W)
    (h : f ≫ eY.hom = eX.hom ≫ g) (h' : f ≫ b = a ≫ k) :
    g ≫ (eY.inv ≫ b) = (eX.inv ≫ a) ≫ k := by
  apply (cancel_epi eX.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc eX.hom g, ← h]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h'

private lemma map_square_comp {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {X X' Y Y' : C}
    {V V' : D} (eX : X ≅ X') (eY : Y ≅ Y')
    (qX : T.obj X' ≅ V) (qY : T.obj Y' ≅ V')
    (f : X ⟶ Y) (g : X' ⟶ Y') (k : V ⟶ V')
    (h : f ≫ eY.hom = eX.hom ≫ g) (h' : T.map g ≫ qY.hom = qX.hom ≫ k) :
    T.map f ≫ (T.map eY.hom ≫ qY.hom) = (T.map eX.hom ≫ qX.hom) ≫ k := by
  rw [← Category.assoc, ← T.map_comp, h, T.map_comp, Category.assoc, h', Category.assoc]

namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

 
noncomputable def augmentationRingIso :
    (complex I z hz 0).X 0 ≅ ModuleCat.of R R := by
  refine augmentationIso I z hz 0 ≪≫ ?_
  exact (show ↥(I^0) ≃ₗ[R] R from
    { toFun := Subtype.val
      invFun := fun r => ⟨r,by simp⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toModuleIso

lemma augmentationRingIso_naturality (M : ℕ) :
    (inclusion I z hz (Nat.zero_le M)).f 0 ≫ (augmentationRingIso I z hz).hom =
      (augmentationIso I z hz M).hom ≫ ModuleCat.ofHom (I^M).subtype := by
  dsimp only [augmentationRingIso,Iso.trans_hom]
  rw [←Category.assoc,augmentationIso_naturality,Category.assoc]
  rfl
end Lech.FilteredCech


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

 

noncomputable def finiteThickeningZeroIso (M : ℕ) :
    (finiteThickening I z hz 0 M).X 0 ≅ ModuleCat.of R (R ⧸ I^M) := by
  unfold finiteThickening
  refine PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) 0) _ ≪≫ ?_
  refine cokernel.mapIso _ (ModuleCat.ofHom (I^(0+M)).subtype)
    (FilteredCech.augmentationIso I z (coordinate_mem I z hz) (0+M))
    (FilteredCech.augmentationRingIso I z (coordinate_mem I z hz))
    (FilteredCech.augmentationRingIso_naturality I z (coordinate_mem I z hz) (0+M)) ≪≫ ?_
  exact idealCokernelIso (I^(0+M)) ≪≫
    (Submodule.quotEquivOfEq (I^(0+M)) (I^M) (by rw [Nat.zero_add])).toModuleIso

@[reassoc]
lemma finiteThickeningZeroIso_π (M : ℕ) :
    (cokernel.π (FilteredCech.inclusion I z (coordinate_mem I z hz)
      (Nat.le_add_right 0 M))).f 0 ≫ (finiteThickeningZeroIso I z hz M).hom =
      (FilteredCech.augmentationRingIso I z (coordinate_mem I z hz)).hom ≫
        ModuleCat.ofHom (I^M).mkQ := by
  let G := HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) 0
  let f := FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M)
  let e := cokernel.mapIso (G.map f) (ModuleCat.ofHom (I^(0+M)).subtype)
    (FilteredCech.augmentationIso I z (coordinate_mem I z hz) (0+M))
    (FilteredCech.augmentationRingIso I z (coordinate_mem I z hz))
    (FilteredCech.augmentationRingIso_naturality I z (coordinate_mem I z hz) (0+M))
  let e' := idealCokernelIso (I^(0+M)) ≪≫
    (Submodule.quotEquivOfEq (I^(0+M)) (I^M) (by rw [Nat.zero_add])).toModuleIso
  have hp : G.map (cokernel.π f) ≫ (PreservesCokernel.iso G f).hom ≫ e.hom ≫ e'.hom =
      (FilteredCech.augmentationRingIso I z (coordinate_mem I z hz)).hom ≫
        ModuleCat.ofHom (I^M).mkQ := by
    rw [PreservesCokernel.π_iso_hom_assoc]
    dsimp only [e,e',Iso.trans_hom]
    simp only [cokernel.mapIso_hom,cokernel.map,cokernel.π_desc_assoc,Category.assoc,idealCokernelIso_π_assoc]
    ext
    rfl
  exact hp

 

lemma finiteThickeningZeroIso_transition {M N : ℕ} (hMN : M ≤ N) :
    (finiteThickeningTransition I z hz 0 hMN).f 0 ≫ (finiteThickeningZeroIso I z hz M).hom =
      (finiteThickeningZeroIso I z hz N).hom ≫
        ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right hMN)) := by
  let f := FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 N)
  have he : cokernel.π f ≫ finiteThickeningTransition I z hz 0 hMN =
      cokernel.π (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right 0 M)) := by
    exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)
  have he' := congrArg (fun k => k.f 0) he
  have hM := finiteThickeningZeroIso_π I z hz M
  have hN := finiteThickeningZeroIso_π I z hz N
  apply (cancel_epi ((cokernel.π f).f 0)).mp
  calc
    _ = ((cokernel.π f).f 0 ≫ (finiteThickeningTransition I z hz 0 hMN).f 0) ≫
        (finiteThickeningZeroIso I z hz M).hom := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k => k ≫ (finiteThickeningZeroIso I z hz M).hom) he'
    _ = _ := hM
    _ = ((cokernel.π f).f 0 ≫ (finiteThickeningZeroIso I z hz N).hom) ≫
        ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right hMN)) := by
      rw [hN,Category.assoc]
      congr 1
    _ = _ := Category.assoc _ _ _

end Lech.SourceGraded


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (ell : AllModuleLength R)

 

lemma finiteThickening_totalTensor_homology_zero
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (t M : ℕ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ j, Module.Free R (F.X j)) (hfinite : ∀ j, Module.Finite R (F.X j))
    (m : ℤ) (N : ℕ) (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j)) (i : ℤ) :
    ell.value (((TensorTotal.functor
      ((finiteThickening I z hz t M).extend ComplexShape.embeddingUpNat)).obj F).homology i)=0 := by
  let P := (ell.torsionLength ⊥).zeroClass
  have hK : ∀ i, P (((finiteThickening I z hz t M).extend ComplexShape.embeddingUpNat).homology i) :=
    homology_property_extendUpNat P _ (fun n => ell.mem_zeroClass _
      (finiteThickening_homology_zero I z hz ell hh hmu ha t M n))
  exact (TensorTotal.homology_property_of_bounded_free _ P hK F hfree hfinite m N hb i).2
end Lech.SourceGraded


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

noncomputable def augmentedThickening (M : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (finiteThickening I z hz 0 M).extend ComplexShape.embeddingUpNat

lemma augmentedThickening_boundedBelow (M : ℕ) :
    ∀ i, i < (0 : ℤ) → IsZero ((augmentedThickening I z hz M).X i) := by
  intro i hi
  apply (finiteThickening I z hz 0 M).isZero_extend_X
  intro n hn
  change (n : ℤ)=i at hn
  omega

noncomputable def augmentedThickeningZeroIso (M : ℕ) :
    (augmentedThickening I z hz M).X 0 ≅ ModuleCat.of R (R ⧸ I^M) :=
  (finiteThickening I z hz 0 M).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl ≪≫
    finiteThickeningZeroIso I z hz M

 

noncomputable def thickeningCech (M : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  FiniteComplex.dropBottom (augmentedThickening I z hz M) 0
    (augmentedThickening_boundedBelow I z hz M)

noncomputable def augmentedThickeningTransition {M N : ℕ} (hMN : M ≤ N) :
    augmentedThickening I z hz N ⟶ augmentedThickening I z hz M :=
  extendMap (finiteThickeningTransition I z hz 0 hMN) ComplexShape.embeddingUpNat

noncomputable def thickeningCechTransition {M N : ℕ} (hMN : M ≤ N) :
    thickeningCech I z hz N ⟶ thickeningCech I z hz M :=
  FiniteComplex.dropBottomMap (augmentedThickening I z hz N) 0
    (augmentedThickening_boundedBelow I z hz N)
    (augmentedThickening_boundedBelow I z hz M) (augmentedThickeningTransition I z hz hMN)

lemma augmentedThickeningZeroIso_transition {M N : ℕ} (hMN : M ≤ N) :
    (augmentedThickeningTransition I z hz hMN).f 0 ≫ (augmentedThickeningZeroIso I z hz M).hom =
      (augmentedThickeningZeroIso I z hz N).hom ≫
        ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right hMN)) := by
  simp only [augmentedThickeningTransition]
  refine (congrArg (· ≫ (augmentedThickeningZeroIso I z hz M).hom)
    (extendMap_f (finiteThickeningTransition I z hz 0 hMN)
      ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl))).trans ?_
  exact extended_square _ _ _ _ _ _ (finiteThickeningZeroIso_transition I z hz hMN)

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

noncomputable def thickeningTensorBottomIso (M : ℕ) :
    (TensorTotal.Right.functor F).obj ((single (ModuleCat.{u} R) (.up ℤ) 0).obj
      ((augmentedThickening I z hz M).X 0)) ≅ (complexQuotient (I^M) (.up ℤ)).obj F :=
  (TensorTotal.Right.functor F).mapIso
    ((single (ModuleCat.{u} R) (.up ℤ) 0).mapIso (augmentedThickeningZeroIso I z hz M)) ≪≫
    TensorTotal.tensorSingleQuotientIso (I^M) F

 

noncomputable def thickeningComparison (M : ℕ) (i : ℤ) :
    ((complexQuotient (I^M) (.up ℤ)).obj F).homology i ⟶
      ((TensorTotal.Right.functor F).obj (thickeningCech I z hz M)).homology (i+1) :=
  ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso (thickeningTensorBottomIso I z hz F M)).inv ≫
    TensorTotal.bottomComparison F (augmentedThickening I z hz M)
      (augmentedThickening_boundedBelow I z hz M) i

variable [Nontrivial R] (ell : AllModuleLength R)
lemma thickeningComparison_isoModSerre
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I)))
    (hfree : ∀ j, Module.Free R (F.X j)) (hfinite : ∀ j, Module.Finite R (F.X j))
    (m : ℤ) (N : ℕ) (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j)) (M : ℕ) (i : ℤ) :
    (ell.torsionLength ⊥).zeroClass.isoModSerre (thickeningComparison I z hz F M i) := by
  let P := (ell.torsionLength ⊥).zeroClass
  apply P.isoModSerre.comp_mem
  · exact P.isoModSerre_of_isIso
      ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
        (thickeningTensorBottomIso I z hz F M)).inv
  · apply TensorTotal.bottomComparison_isoModSerre
    intro j
    exact ell.mem_zeroClass _
      (finiteThickening_totalTensor_homology_zero I z hz ell hh hmu ha 0 M F hfree hfinite m N hb j)
end Lech.SourceGraded


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [CommRing R]

 
noncomputable def moduleQuotientMap {I J : Ideal R} (h : I ≤ J) :
    (moduleQuotient I : ModuleCat.{v} R ⥤ _) ⟶ moduleQuotient J where
  app M := ModuleCat.ofHom (Submodule.factor (Submodule.smul_mono h le_rfl))
  naturality {M N} f := by
    ext x
    obtain ⟨x,rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
    rfl

@[reassoc (attr := simp)]
lemma moduleQuotientπ_map {I J : Ideal R} (h : I ≤ J) (M : ModuleCat.{v} R) :
    (moduleQuotientπ I).app M ≫ (moduleQuotientMap h).app M =
      (moduleQuotientπ J).app M := by ext x; rfl

@[reassoc]
lemma moduleQuotientMap_comp {I J K : Ideal R} (h : I ≤ J) (h' : J ≤ K)
    (M : ModuleCat.{v} R) :
    (moduleQuotientMap h).app M ≫ (moduleQuotientMap h').app M =
      (moduleQuotientMap (h.trans h')).app M := by
  apply (cancel_epi ((moduleQuotientπ I).app M)).mp
  simp

noncomputable def complexQuotientMap {I J : Ideal R} (h : I ≤ J)
    {ι : Type*} (c : ComplexShape ι) :
    (complexQuotient I c : HomologicalComplex (ModuleCat.{v} R) c ⥤ _) ⟶
      complexQuotient J c := (moduleQuotientMap h).mapHomologicalComplex c

@[reassoc (attr := simp)]
lemma complexQuotientπ_map {I J : Ideal R} (h : I ≤ J)
    {ι : Type*} {c : ComplexShape ι} (F : HomologicalComplex (ModuleCat.{v} R) c) :
    complexQuotientπ I F ≫ (complexQuotientMap h c).app F = complexQuotientπ J F := by
  ext i : 1
  exact moduleQuotientπ_map h (F.X i)

 

lemma complexQuotient_shortExact (I : Ideal R) {ι : Type*} {c : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c))
    (σ : ∀ i, (S.map (HomologicalComplex.eval (ModuleCat.{v} R) c i)).Splitting) :
    (S.map (complexQuotient I c)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact ((σ i).map (moduleQuotient I)).shortExact

end Lech


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

@[reassoc] lemma termTensorQuotientIso_naturality {I J : Ideal R} (hIJ : I ≤ J)
    (M : ModuleCat.{u} R) :
    (M ◁ ModuleCat.ofHom (Submodule.factor hIJ)) ≫ (termTensorQuotientIso J).hom.app M =
      (termTensorQuotientIso I).hom.app M ≫ (moduleQuotientMap hIJ).app M := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m q
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
  change TensorProduct.tensorQuotEquivQuotSMul M J (m ⊗ₜ[R] Ideal.Quotient.mk J r) =
    (Submodule.factor (Submodule.smul_mono hIJ le_rfl))
      (TensorProduct.tensorQuotEquivQuotSMul M I (m ⊗ₜ[R] Ideal.Quotient.mk I r))
  simp [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]

@[reassoc] lemma tensorSingleQuotientIso_naturality {I J : Ideal R} (hIJ : I ≤ J)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    mapBifunctorMap (𝟙 F) ((single (ModuleCat.{u} R) (.up ℤ) 0).map
      (ModuleCat.ofHom (Submodule.factor hIJ))) (curriedTensor (ModuleCat.{u} R)) (.up ℤ) ≫
        (tensorSingleQuotientIso J F).hom =
    (tensorSingleQuotientIso I F).hom ≫ (complexQuotientMap hIJ (.up ℤ)).app F := by
  refine inverse_square_comp (tensorSingleIso F (ModuleCat.of R (R ⧸ I)))
    (tensorSingleIso F (ModuleCat.of R (R ⧸ J))) _ _ _ _ _
      (tensorSingleIso_naturality F _ (ModuleCat.ofHom (Submodule.factor hIJ))) ?_
  apply Hom.ext
  funext i
  exact termTensorQuotientIso_naturality hIJ (F.X i)

end Lech.TensorTotal


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

@[reassoc] lemma thickeningTensorBottomIso_transition {M N : ℕ} (hMN : M ≤ N) :
    (TensorTotal.Right.functor F).map ((single (ModuleCat.{u} R) (.up ℤ) 0).map
      ((augmentedThickeningTransition I z hz hMN).f 0)) ≫ (thickeningTensorBottomIso I z hz F M).hom =
    (thickeningTensorBottomIso I z hz F N).hom ≫
      (complexQuotientMap (Ideal.pow_le_pow_right hMN) (.up ℤ)).app F := by
  exact map_square_comp ((single (ModuleCat.{u} R) (.up ℤ) 0) ⋙ TensorTotal.Right.functor F)
    (augmentedThickeningZeroIso I z hz N) (augmentedThickeningZeroIso I z hz M)
    (TensorTotal.tensorSingleQuotientIso (I^N) F) (TensorTotal.tensorSingleQuotientIso (I^M) F)
    _ _ _ (augmentedThickeningZeroIso_transition I z hz hMN)
    (TensorTotal.tensorSingleQuotientIso_naturality (Ideal.pow_le_pow_right hMN) F)

 

@[reassoc] lemma thickeningComparison_transition {M N : ℕ} (hMN : M ≤ N) (i : ℤ) :
    homologyMap ((complexQuotientMap (Ideal.pow_le_pow_right hMN) (.up ℤ)).app F) i ≫
      thickeningComparison I z hz F M i =
    thickeningComparison I z hz F N i ≫
      homologyMap ((TensorTotal.Right.functor F).map (thickeningCechTransition I z hz hMN)) (i+1) := by
  let H := homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
  let eN := H.mapIso (thickeningTensorBottomIso I z hz F N)
  let eM := H.mapIso (thickeningTensorBottomIso I z hz F M)
  let f := (TensorTotal.Right.functor F).map ((single (ModuleCat.{u} R) (.up ℤ) 0).map
    ((augmentedThickeningTransition I z hz hMN).f 0))
  have hh : H.map f ≫ eM.hom = eN.hom ≫
      homologyMap ((complexQuotientMap (Ideal.pow_le_pow_right hMN) (.up ℤ)).app F) i := by
    dsimp only [H,eM,eN,f,Functor.mapIso,homologyFunctor]
    simpa only [homologyMap_comp] using
      (congrArg (fun g => homologyMap g i) (thickeningTensorBottomIso_transition I z hz F hMN))
  exact inverse_square_comp eN eM _ _ _ _ _ hh
    (TensorTotal.bottomComparison_naturality F (augmentedThickening I z hz N)
    (augmentedThickening_boundedBelow I z hz N) (augmentedThickening I z hz M)
    (augmentedThickening_boundedBelow I z hz M) (augmentedThickeningTransition I z hz hMN) i).symm
end Lech.SourceGraded

namespace Lech.FilteredFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w z c : R} {d k : ℕ}
  (hw : w ∈ I^d) (hc : c ∈ I^k) (hwc : z*c=w) (hdk : k+1=d)

 
def inverseFactor (m : ℕ) : Localization.Away w :=
  Localization.mk (c^m) (⟨w^m,m,rfl⟩ : Submonoid.powers w)

include hwc in
lemma inverseFactor_mul (m : ℕ) :
    algebraMap R (Localization.Away w) (z^m) * inverseFactor (w := w) (c := c) m=1 := by
  rw [←Localization.mk_one_eq_algebraMap]
  dsimp only [inverseFactor]
  rw [Localization.mk_mul,one_mul,←mul_pow,hwc]
  exact Localization.mk_self (⟨w^m,m,rfl⟩ : Submonoid.powers w)

include hc hdk in
lemma inverseFactor_fraction (t m n : ℕ) (a : ↥(I^(n*d+(t+m)))) :
    ∃ b : ↥(I^((n+m)*d+t)),
      inverseFactor (w := w) (c := c) m * fraction I w d (t+m) n a = fraction I w d t (n+m) b := by
  have hc' : c^m ∈ I^(m*k) := by
    simpa only [pow_mul,mul_comm m k] using Ideal.pow_mem_pow hc m
  have heq : m*k+(n*d+(t+m))=(n+m)*d+t := by rw [←hdk]; ring
  have hb : c^m*(a:R) ∈ I^((n+m)*d+t) := by
    rw [←heq,pow_add]
    exact Ideal.mul_mem_mul hc' a.property
  refine ⟨⟨c^m*(a:R),hb⟩,?_⟩
  change Localization.mk (c^m) (⟨w^m,m,rfl⟩ : Submonoid.powers w) * Localization.mk (a:R) (⟨w^n,n,rfl⟩ : Submonoid.powers w) = Localization.mk (c^m*(a:R)) (⟨w^(n+m),n+m,rfl⟩ : Submonoid.powers w)
  rw [Localization.mk_mul,Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,Submonoid.coe_mul,pow_add]
  ring

include hw hc hdk in
lemma inverseFactor_mem (t m : ℕ) (x : piece I w d (t+m)) :
    inverseFactor (w := w) (c := c) m * x.val ∈ piece I w d t := by
  obtain ⟨n,a,ha⟩ := exists_fraction I w d hw (t+m) x
  rw [←ha]
  obtain ⟨b,hb⟩ := inverseFactor_fraction I hc hdk t m n a
  rw [hb]
  exact fraction_mem I w d t (n+m) b

 

def divide (t m : ℕ) : piece I w d (t+m) →ₗ[R] piece I w d t where
  toFun x := ⟨inverseFactor (w := w) (c := c) m * x.val,inverseFactor_mem I hw hc hdk t m x⟩
  map_add' _x _y := Subtype.ext (mul_add _ _ _)
  map_smul' _r _x := Subtype.ext (mul_smul_comm _ _ _)

include hwc in
lemma smul_divide (t m : ℕ) (x : piece I w d (t+m)) :
    z^m • divide I hw hc hdk t m x = Submodule.inclusion (antitone I w d (Nat.le_add_right t m)) x := by
  apply Subtype.ext
  change z^m • (inverseFactor (w := w) (c := c) m * x.val)=x.val
  rw [Algebra.smul_def,←mul_assoc,inverseFactor_mul hwc,one_mul]
end Lech.FilteredFraction


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

 
def divide {s : Finset (Fin h)} (i : Fin h) (hi : i∈s) (t m : ℕ) :
    term I z (t+m) s →ₗ[R] term I z t s := by
  classical
  exact FilteredFraction.divide I (denominator_mem I z hz s)
    (denominator_mem I z hz (s.erase i)) (Finset.card_erase_add_one hi) t m

lemma smul_divide {s : Finset (Fin h)} (i : Fin h) (hi : i∈s) (t m : ℕ)
    (x : term I z (t+m) s) :
    z i ^ m • divide I z hz i hi t m x =
      Submodule.inclusion (FilteredFraction.antitone I _ _ (Nat.le_add_right t m)) x := by
  classical
  apply FilteredFraction.smul_divide
  exact Finset.mul_prod_erase s z hi
end Lech.FilteredCech
end

end OAI
