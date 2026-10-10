import Mathlib
import OAI.RingTheory.Multiplicity.LechCokernelComp
import OAI.RingTheory.Multiplicity.ProductSourceCoverCechNat

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

 

lemma homology_property_of_bounded_free
    (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hK : ∀ i, P (K.homology i))
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ j, Module.Free R (F.X j)) (hfinite : ∀ j, Module.Finite R (F.X j))
    (m : ℤ) (N : ℕ) (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j)) (i : ℤ) :
    P (((functor K).obj F).homology i) := by
  apply FiniteComplex.homology_devissage P (functor K) (splitting K) m N F i hb
  intro j
  let T := single (ModuleCat.{u} R) (.up ℤ) j ⋙ functor K ⋙
    homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
  let := hfree j
  let := hfinite j
  exact prop_additive_free P T
    (P.prop_of_iso (singleRingHomologyIso K j i).symm (hK (i-j))) (F.X j)

end Lech.TensorTotal


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {C : Type u} [Category C] [Abelian C]

 

lemma homology_property_extendUpNat
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (K : CochainComplex C ℕ) (hK : ∀ n, P (K.homology n)) (i : ℤ) :
    P ((K.extend ComplexShape.embeddingUpNat).homology i) := by
  by_cases hi : 0 ≤ i
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact P.prop_of_iso (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).symm (hK n)
  · apply P.prop_of_isZero
    apply (exactAt_iff_isZero_homology _ _).mp
    apply K.extend_exactAt
    intro n hn
    change (n : ℤ)=i at hn
    omega
end Lech


namespace Lech.TensorTotal.Right
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

 
def functor (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
  {F G H : CochainComplex (ModuleCat.{u} R) ℤ}

 

def degreeMap (a : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    ((functor K).obj F).X i ⟶ ((functor K).obj G).X i :=
  mapBifunctorDesc (fun p q hpq =>
    ((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).map (a q) ≫
      ιMapBifunctor K G (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq)

@[reassoc (attr := simp)] lemma ι_degreeMap (a : ∀ j, F.X j ⟶ G.X j)
    (p q i : ℤ) (hpq : p+q=i) :
    ιMapBifunctor K F (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫ degreeMap K a i =
      ((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).map (a q) ≫
        ιMapBifunctor K G (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq := by
  apply ι_mapBifunctorDesc

lemma degreeMap_id (i : ℤ) : degreeMap K (fun j => 𝟙 (F.X j)) i = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  change _ = ιMapBifunctor K F (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫
    𝟙 ((mapBifunctor K F (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).X i)
  simp

lemma degreeMap_comp (a : ∀ j, F.X j ⟶ G.X j) (b : ∀ j, G.X j ⟶ H.X j) (i : ℤ) :
    degreeMap K (fun j => a j ≫ b j) i=degreeMap K a i ≫ degreeMap K b i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  refine (ι_degreeMap K (fun j => a j ≫ b j) p q i hpq).trans ?_
  simp only [Functor.map_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).map (a q) ≫ ·)
      (ι_degreeMap K b p q i hpq).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ degreeMap K b i) (ι_degreeMap K a p q i hpq).symm).trans
            (Category.assoc _ _ _))))

lemma degreeMap_add (a b : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    degreeMap K (fun j => a j+b j) i=degreeMap K a i+degreeMap K b i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  refine (ι_degreeMap K (fun j => a j + b j) p q i hpq).trans ?_
  simp only [Functor.map_add]
  exact (Preadditive.add_comp _ _ _ _ _ _).trans
    ((congrArg₂ (· + ·) (ι_degreeMap K a p q i hpq).symm
      (ι_degreeMap K b p q i hpq).symm).trans (Preadditive.comp_add _ _ _ _ _ _).symm)

lemma map_f (f : F ⟶ G) (i : ℤ) :
    ((functor K).map f).f i=degreeMap K f.f i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp [functor]
  refine (ι_mapBifunctorMap (𝟙 K) f (curriedTensor (ModuleCat.{u} R)) (.up ℤ)
    p q i hpq).trans ?_
  exact (congrArg (fun t => t ≫
    ((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).map (f.f q) ≫
      ιMapBifunctor K G (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq)
        (congrArg (fun t => t.app (F.X q)) ((curriedTensor (ModuleCat.{u} R)).map_id (K.X p)))).trans
    ((Category.id_comp _).trans (ι_degreeMap K f.f p q i hpq).symm)

instance : (functor K).Additive where
  map_add {F G} f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    change ((functor K).map (f+g)).f i=((functor K).map f).f i+((functor K).map g).f i
    simp only [map_f]
    exact degreeMap_add K f.f g.f i

 

def splitting (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (s : ∀ j, (S.map (eval (ModuleCat.{u} R) (.up ℤ) j)).Splitting) (i : ℤ) :
    ((S.map (functor K)).map (eval (ModuleCat.{u} R) (.up ℤ) i)).Splitting where
  r := degreeMap K (fun j => (s j).r) i
  s := degreeMap K (fun j => (s j).s) i
  f_r := by
    change ((functor K).map S.f).f i ≫ degreeMap K (fun j => (s j).r) i = 𝟙 (((functor K).obj S.X₁).X i)
    rw [map_f,←degreeMap_comp]
    simp only [show (fun j => S.f.f j ≫ (s j).r)=(fun j => 𝟙 (S.X₁.X j)) from
      funext (fun j => (s j).f_r),degreeMap_id]
  s_g := by
    change degreeMap K (fun j => (s j).s) i ≫ ((functor K).map S.g).f i = 𝟙 (((functor K).obj S.X₃).X i)
    rw [map_f,←degreeMap_comp]
    simp only [show (fun j => (s j).s ≫ S.g.f j)=(fun j => 𝟙 (S.X₃.X j)) from
      funext (fun j => (s j).s_g),degreeMap_id]
  id := by
    change degreeMap K (fun j => (s j).r) i ≫ ((functor K).map S.f).f i + ((functor K).map S.g).f i ≫ degreeMap K (fun j => (s j).s) i = 𝟙 (((functor K).obj S.X₂).X i)
    rw [map_f,map_f,←degreeMap_comp,←degreeMap_comp,←degreeMap_add]
    simp only [show (fun j => (show S.X₂.X j ⟶ S.X₁.X j from (s j).r) ≫ S.f.f j + S.g.f j ≫ (show S.X₃.X j ⟶ S.X₂.X j from (s j).s))=
      (fun j => 𝟙 (S.X₂.X j)) from funext (fun j => (s j).id),degreeMap_id]

end Lech.TensorTotal.Right


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]
  (F K : CochainComplex (ModuleCat.{u} R) ℤ)
  (hK : ∀ j, j < 0 → IsZero (K.X j))

noncomputable def bottomSequence : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (FiniteComplex.bottomShortComplex K 0 hK).map (Right.functor F)

lemma bottomSequence_shortExact : (bottomSequence F K hK).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact (Right.splitting F _ (FiniteComplex.bottomSplitting K 0 hK) i).shortExact

noncomputable def bottomComparison (i : ℤ) :
    ((Right.functor F).obj ((single (ModuleCat.{u} R) (.up ℤ) 0).obj (K.X 0))).homology i ⟶
      ((Right.functor F).obj (FiniteComplex.dropBottom K 0 hK)).homology (i+1) :=
  (bottomSequence_shortExact F K hK).δ i (i+1) rfl

lemma bottomComparison_isoModSerre (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (h : ∀ i, P (((Right.functor F).obj K).homology i)) (i : ℤ) :
    P.isoModSerre (bottomComparison F K hK i) :=
  connecting_isoModSerre P (bottomSequence_shortExact F K hK) i (i+1) rfl (h i) (h (i+1))

@[reassoc]
lemma bottomComparison_naturality (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hL : ∀ j, j < 0 → IsZero (L.X j)) (f : K ⟶ L) (i : ℤ) :
    bottomComparison F K hK i ≫ homologyMap ((Right.functor F).map
      (FiniteComplex.dropBottomMap K 0 hK hL f)) (i+1) =
    homologyMap ((Right.functor F).map ((single (ModuleCat.{u} R) (.up ℤ) 0).map (f.f 0))) i ≫
      bottomComparison F L hL i := by
  exact HomologySequence.δ_naturality
    ((Right.functor F).mapShortComplex.map (FiniteComplex.bottomShortComplexMap K 0 hK hL f))
    (bottomSequence_shortExact F K hK) (bottomSequence_shortExact F L hL) i (i+1) rfl
end Lech.TensorTotal


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (Q : ModuleCat.{u} R)

abbrev singleZero := (single (ModuleCat.{u} R) (.up ℤ) 0).obj Q
abbrev tensorSingle := mapBifunctor F (singleZero Q) (curriedTensor (ModuleCat.{u} R)) (.up ℤ)
abbrev termTensor := ((curriedTensor (ModuleCat.{u} R)).flip.obj Q).mapHomologicalComplex (.up ℤ)

def intoTensorSingle (i : ℤ) : ((termTensor Q).obj F).X i ⟶ (tensorSingle F Q).X i :=
  (F.X i ◁ (singleObjXSelf (.up ℤ) 0 Q).inv) ≫
    ιMapBifunctor F (singleZero Q) (curriedTensor (ModuleCat.{u} R)) (.up ℤ) i 0 i (by simp)

def outOfTensorSingle (i : ℤ) : (tensorSingle F Q).X i ⟶ ((termTensor Q).obj F).X i :=
  mapBifunctorDesc (fun p q hpq => if hq : q=0 then
    have hp : p=i := by change p+q=i at hpq; omega
    (F.X p ◁ (singleObjXIsoOfEq (.up ℤ) 0 Q q hq).hom) ≫ (F.XIsoOfEq hp).hom ▷ Q
    else 0)

lemma into_out (i : ℤ) : intoTensorSingle F Q i ≫ outOfTensorSingle F Q i = 𝟙 _ := by
  simp only [intoTensorSingle,outOfTensorSingle,Category.assoc,ι_mapBifunctorDesc,
    dite_true,XIsoOfEq_rfl,Iso.refl_hom,id_whiskerRight,Category.comp_id]
  rw [←whiskerLeft_comp]
  simp only [singleObjXSelf,Iso.inv_hom_id,whiskerLeft_id]
  rfl

lemma out_into (i : ℤ) : outOfTensorSingle F Q i ≫ intoTensorSingle F Q i = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  by_cases hq : q=0
  · subst q
    have hp : p=i := by change p+0=i at hpq; omega
    subst p
    simp only [outOfTensorSingle,ι_mapBifunctorDesc_assoc,
      dite_true,XIsoOfEq_rfl,Iso.refl_hom,id_whiskerRight,Category.comp_id]
    dsimp only [intoTensorSingle]
    rw [←whiskerLeft_comp_assoc]
    simp only [singleObjXSelf,Iso.hom_inv_id,whiskerLeft_id,Category.id_comp]
  · have hzero := (curriedTensor (ModuleCat.{u} R)).obj (F.X p) |>.map_isZero
        (isZero_single_obj_X (.up ℤ) 0 Q q hq)
    exact hzero.eq_of_src _ _

def tensorSingleXIso (i : ℤ) : ((termTensor Q).obj F).X i ≅ (tensorSingle F Q).X i where
  hom := intoTensorSingle F Q i
  inv := outOfTensorSingle F Q i
  hom_inv_id := into_out F Q i
  inv_hom_id := out_into F Q i

lemma tensorSingle_d₂ (p q j : ℤ) :
    mapBifunctor.d₂ F (singleZero Q) (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q j = 0 := by
  by_cases h : p+(q+1)=j
  · rw [mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel q (q+1) from rfl) _ h]
    simp
  · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ (show (ComplexShape.up ℤ).Rel q (q+1) from rfl) _ h]

lemma intoTensorSingle_comm (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    intoTensorSingle F Q i ≫ (tensorSingle F Q).d i j =
      ((termTensor Q).obj F).d i j ≫ intoTensorSingle F Q j := by
  simp only [intoTensorSingle,Category.assoc,mapBifunctor.d_eq,Preadditive.comp_add,
    mapBifunctor.ι_D₁,mapBifunctor.ι_D₂,tensorSingle_d₂,comp_zero,add_zero]
  rw [mapBifunctor.d₁_eq _ _ _ _ hij _ _ (by simp)]
  dsimp
  simp [←whisker_exchange_assoc]

 

def tensorSingleIso : (termTensor Q).obj F ≅ tensorSingle F Q :=
  Hom.isoOfComponents (tensorSingleXIso F Q) (fun _ _ hij => intoTensorSingle_comm F Q _ _ hij)

def termTensorMap {Q' : ModuleCat.{u} R} (f : Q ⟶ Q') :
    (termTensor Q).obj F ⟶ (termTensor Q').obj F :=
  ((curriedTensor (ModuleCat.{u} R)).flip.map f).mapHomologicalComplex (.up ℤ) |>.app F

@[reassoc] lemma tensorSingleIso_naturality {Q' : ModuleCat.{u} R} (f : Q ⟶ Q') :
    termTensorMap F Q f ≫ (tensorSingleIso F Q').hom =
      (tensorSingleIso F Q).hom ≫ mapBifunctorMap (𝟙 F)
        ((single (ModuleCat.{u} R) (.up ℤ) 0).map f) (curriedTensor (ModuleCat.{u} R)) (.up ℤ) := by
  apply Hom.ext
  funext i
  change (F.X i ◁ f) ≫ intoTensorSingle F Q' i = intoTensorSingle F Q i ≫ _
  simp only [intoTensorSingle,Category.assoc,ι_mapBifunctorMap,HomologicalComplex.id_f,
    single_map_f_self]
  dsimp
  simp only [id_whiskerRight, Category.id_comp, ←whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc]

end Lech.TensorTotal


namespace Lech
universe u v
variable {R : Type u} [CommRing R]

 
noncomputable def moduleQuotient (I : Ideal R) : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M)))
  map {M N} f := ModuleCat.ofHom ((I • (⊤ : Submodule R M)).mapQ
    (I • (⊤ : Submodule R N)) f.hom (Submodule.smul_top_le_comap_smul_top I f.hom))
  map_id M := by
    apply ModuleCat.hom_ext
    exact Submodule.mapQ_id _
  map_comp {M N P} f g := by
    ext x
    rfl

instance moduleQuotient_additive (I : Ideal R) : (moduleQuotient I : ModuleCat.{v} R ⥤ _).Additive where
  map_add {M N} f g := by
    ext x
    obtain ⟨x,rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
    rfl

 
noncomputable def moduleQuotientπ (I : Ideal R) : 𝟭 (ModuleCat.{v} R) ⟶ moduleQuotient I where
  app M := ModuleCat.ofHom (I • (⊤ : Submodule R M)).mkQ
  naturality {M N} f := by
    ext x
    rfl

instance moduleQuotientπ_epi (I : Ideal R) (M : ModuleCat.{v} R) :
    Epi ((moduleQuotientπ I).app M) :=
  (ModuleCat.epi_iff_surjective _).mpr (I • (⊤ : Submodule R M)).mkQ_surjective

lemma moduleQuotient_annihilated (I : Ideal R) (r : R) (hr : r ∈ I)
    (M : ModuleCat.{v} R) : r • 𝟙 ((moduleQuotient I).obj M) = 0 := by
  ext x
  obtain ⟨x,rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
  change (I • (⊤ : Submodule R M)).mkQ (r • x) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hr trivial)

 
noncomputable def complexQuotient (I : Ideal R) {ι : Type*} (c : ComplexShape ι) :
    HomologicalComplex (ModuleCat.{v} R) c ⥤ HomologicalComplex (ModuleCat.{v} R) c :=
  (moduleQuotient I).mapHomologicalComplex c

instance complexQuotient_additive (I : Ideal R) {ι : Type*} (c : ComplexShape ι) :
    (complexQuotient I c : HomologicalComplex (ModuleCat.{v} R) c ⥤ _).Additive :=
  inferInstanceAs ((moduleQuotient I).mapHomologicalComplex c).Additive

noncomputable def complexQuotientπ (I : Ideal R) {ι : Type*} {c : ComplexShape ι}
    (F : HomologicalComplex (ModuleCat.{v} R) c) : F ⟶ (complexQuotient I c).obj F where
  f i := (moduleQuotientπ I).app (F.X i)
  comm' i j _hij := (moduleQuotientπ I).naturality (F.d i j)

lemma complexQuotient_annihilated (I : Ideal R) (r : R) (hr : r ∈ I)
    {ι : Type*} {c : ComplexShape ι} (F : HomologicalComplex (ModuleCat.{v} R) c) :
    r • 𝟙 ((complexQuotient I c).obj F) = 0 := by
  ext i : 1
  exact moduleQuotient_annihilated I r hr (F.X i)

end Lech


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

 
def termTensorQuotientIso (I : Ideal R) :
    (curriedTensor (ModuleCat.{u} R)).flip.obj (ModuleCat.of R (R ⧸ I)) ≅ moduleQuotient I :=
  NatIso.ofComponents (fun M => (TensorProduct.tensorQuotEquivQuotSMul M I).toModuleIso)
    (fun {M N} f => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro m q
      obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
      change TensorProduct.tensorQuotEquivQuotSMul N I (f.hom m ⊗ₜ[R] Ideal.Quotient.mk I r) =
        ((moduleQuotient I).map f).hom (TensorProduct.tensorQuotEquivQuotSMul M I
          (m ⊗ₜ[R] Ideal.Quotient.mk I r))
      simp only [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
      change _ = Submodule.Quotient.mk (f.hom (r • m))
      rw [map_smul])

 

def tensorSingleQuotientIso (I : Ideal R) (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSingle F (ModuleCat.of R (R ⧸ I)) ≅ (complexQuotient I (.up ℤ)).obj F :=
  (tensorSingleIso F (ModuleCat.of R (R ⧸ I))).symm ≪≫
    (NatIso.mapHomologicalComplex (termTensorQuotientIso I) (.up ℤ)).app F
end Lech.TensorTotal


namespace Lech.LocalizationCech
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {h : ℕ} (y : Fin h → R)
  (F : ∀ s : Finset (Fin h), Submodule R (ambient y s))

 
noncomputable def augmentationIso : ModuleCat.of R (cochains y F 0) ≅ ModuleCat.of R (F ∅) := by
  have e := (LinearEquiv.piUnique R (fun a : Fin 0 → Fin h => ↥(F (ActualCech.intersection a)))).toModuleIso
  refine e ≪≫ eqToIso ?_
  have he : ActualCech.intersection (default : Fin 0 → Fin h) = ∅ := by
    simp [ActualCech.intersection]
  rw [he]
end Lech.LocalizationCech


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

 
noncomputable def augmentationIso (t : ℕ) :
    (complex I z hz t).X 0 ≅ ModuleCat.of R ↥(I^t) := by
  refine (LocalizationCech.augmentationIso z (term I z t)) ≪≫ ?_
  have e := (FilteredFraction.augmentationEquiv I t).symm.toModuleIso
  convert e using 1
  simp only [term,GradedChart.denominator,Finset.prod_empty,Finset.card_empty]
  rfl

 
lemma augmentationIso_naturality {s t : ℕ} (hst : s ≤ t) :
    (inclusion I z hz hst).f 0 ≫ (augmentationIso I z hz s).hom =
      (augmentationIso I z hz t).hom ≫ ModuleCat.ofHom
        (Submodule.inclusion (show I^t ≤ I^s from Ideal.pow_le_pow_right hst)) := by
  apply (cancel_mono (augmentationIso I z hz s).inv).1
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
  apply (cancel_epi (augmentationIso I z hz t).inv).1
  simp only [Iso.inv_hom_id_assoc]
  ext a
  funext b
  apply Subtype.ext
  rfl
end Lech.FilteredCech


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R]

 
noncomputable def idealCokernelIso (J : Ideal R) :
    cokernel (ModuleCat.ofHom J.subtype) ≅ ModuleCat.of R (R ⧸ J) := by
  refine ModuleCat.cokernelIsoRangeQuotient _ ≪≫ ?_
  change ModuleCat.of R (R ⧸ LinearMap.range J.subtype) ≅ _
  exact (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _)).toModuleIso

@[reassoc (attr := simp)]
lemma idealCokernelIso_π (J : Ideal R) :
    cokernel.π (ModuleCat.ofHom J.subtype) ≫ (idealCokernelIso J).hom = ModuleCat.ofHom J.mkQ := by
  unfold idealCokernelIso
  simp only [Iso.trans_hom]
  rw [← Category.assoc,ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  ext
  rfl
end Lech
end

end OAI
