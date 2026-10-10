import Mathlib
import OAI.RingTheory.Multiplicity.FilteredFractionReesDenominatorTheory

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

 

lemma cokernel_comp_shortExact {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    (kernelCokernelCompSequence.snakeInput f g).L₃.ShortExact where
  exact := (kernelCokernelCompSequence.snakeInput f g).L₃_exact
  mono_f := (kernelCokernelCompSequence.snakeInput f g).L₂'_exact.mono_g
    ((isZero_kernel_of_mono g).eq_of_src _ _)
  epi_g := by
    change Epi (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))
    infer_instance

 

noncomputable def cokernelIsoOfShortExact {S : ShortComplex C} (hS : S.ShortExact) :
    cokernel S.f ≅ S.X₃ :=
  (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel

lemma cokernel_homology_property_of_shortExact {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i : ι)
    (h : P (S.X₃.homology i)) : P ((cokernel S.f).homology i) :=
  P.prop_of_iso ((homologyFunctor C c i).mapIso (cokernelIsoOfShortExact hS)).symm h

 

lemma homology_middle_property {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact) (i : ι)
    (h₁ : P (S.X₁.homology i)) (h₃ : P (S.X₃.homology i)) : P (S.X₂.homology i) :=
  P.prop_X₂_of_exact (hS.homology_exact₂ i) h₁ h₃

 

lemma cokernel_comp_homology_property {ι : Type*} {c : ComplexShape ι}
    (P : ObjectProperty C) [P.IsSerreClass]
    {K L M : HomologicalComplex C c} (f : K ⟶ L) (g : L ⟶ M) [Mono g]
    (i : ι) (hf : P ((cokernel f).homology i)) (hg : P ((cokernel g).homology i)) :
    P ((cokernel (f ≫ g)).homology i) :=
  homology_middle_property P (cokernel_comp_shortExact f g) i hf hg
end Lech


namespace Lech.FilteredFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma fraction_one_zero (t n : ℕ) (a : ↥(I^(n*0+t))) :
    fraction I (1:R) 0 t n a=algebraMap R (Localization.Away (1:R)) a := by
  change Localization.mk (a:R) (⟨(1:R)^n,n,rfl⟩ : Submonoid.powers (1:R))=_
  have he : (⟨(1:R)^n,n,rfl⟩ : Submonoid.powers (1:R))=1 := Subtype.ext (one_pow n)
  rw [he,Localization.mk_eq_mk',IsLocalization.mk'_one]

 

noncomputable def augmentationEquiv (t : ℕ) : ↥(I^t) ≃ₗ[R] piece I (1:R) 0 t :=
  LinearEquiv.ofBijective
    (show ↥(I^t) →ₗ[R] piece I (1:R) 0 t from
    { toFun := fun a => ⟨algebraMap R _ a,by
        simpa only [fraction_one_zero] using fraction_mem I (1:R) 0 t 0 ⟨a.val,by simp⟩⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext ((Algebra.linearMap R (Localization.Away (1:R))).map_smul _ _) })
    ⟨by
      intro a b hab
      apply Subtype.ext
      exact (IsLocalization.atOne R (Localization.Away (1:R))).injective (congrArg Subtype.val hab),by
      intro x
      obtain ⟨n,a,ha⟩ := exists_fraction I (1:R) 0 (by simp) t x
      exact ⟨⟨a.val,by simpa using a.property⟩,Subtype.ext ((fraction_one_zero I t n a).symm.trans ha)⟩⟩

@[simp] lemma augmentationEquiv_val (t : ℕ) (a : ↥(I^t)) :
    (augmentationEquiv I t a).val=algebraMap R (Localization.Away (1:R)) a := rfl

lemma augmentationEquiv_mem {s t : ℕ} (a : ↥(I^s)) :
    (augmentationEquiv I s a).val ∈ piece I (1:R) 0 t ↔ (a:R) ∈ I^t := by
  constructor
  · intro ha
    obtain ⟨b,hb⟩ := (augmentationEquiv I t).surjective ⟨(augmentationEquiv I s a).val,ha⟩
    have he : (b:R)=(a:R) := (IsLocalization.atOne R (Localization.Away (1:R))).injective
      (congrArg Subtype.val hb)
    exact he ▸ b.property
  · intro ha
    simpa only [augmentationEquiv_val] using (augmentationEquiv I t ⟨a.val,ha⟩).property
end Lech.FilteredFraction


namespace Lech
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]
lemma linearMap_sum_smul {A B ι : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] [Fintype ι]
    (f : A →ₗ[R] B) (r : ι → R) (x : ι → A) (y : ι → B)
    (hy : ∀ i, f (x i)=y i) : f (∑ i, r i • x i)=∑ i, r i • y i := by
  simp only [map_sum,map_smul,hy]

 

def cochainOfMap {X Y : ℕ → ModuleCat.{u} R}
    {dX : ∀ n, X n ⟶ X (n+1)} {dY : ∀ n, Y n ⟶ Y (n+1)}
    {hX : ∀ n, dX n ≫ dX (n+1)=0} {hY : ∀ n, dY n ≫ dY (n+1)=0}
    (f : ∀ n, X n ⟶ Y n)
    (hf : ∀ n (x : X n), (dY n).hom ((f n).hom x)=(f (n+1)).hom ((dX n).hom x)) :
    CochainComplex.of X dX hX ⟶ CochainComplex.of Y dY hY :=
  CochainComplex.ofHom f (fun n => by
    change f n ≫ CochainComplex.of.d Y dY n (n+1)=CochainComplex.of.d X dX n (n+1) ≫ f (n+1)
    rw [CochainComplex.of_d,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (hf n))
end Lech


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] TwistedLocalization.piece FilteredFraction.piece IdealGraded.polynomialMap

 
def filteredReductionCochains (n t : ℕ) :
    LocalizationCech.cochains z (FilteredCech.term I z t) n →ₗ[R]
      RestrictedPolynomialImageCech.cochains (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I) (h := h)
        (targetGrade I) (mapR I z hz) n t :=
  LinearMap.pi (fun a => (filteredReduction I z hz (ActualCech.intersection a) t).comp
    (LinearMap.proj a))

lemma filteredReductionCochains_d (n t : ℕ)
    (x : LocalizationCech.cochains z (FilteredCech.term I z t) n) :
    filteredReductionCochains I z hz (n+1) t
      (LocalizationCech.d z (FilteredCech.term I z t)
        (FilteredCech.restriction_mem I z (coordinate_mem I z hz) t) n x) =
    RestrictedPolynomialImageCech.d (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I) (h := h)
      (targetGrade I) (mapR I z hz) n t (filteredReductionCochains I z hz n t x) := by
  funext a
  change filteredReduction I z hz (ActualCech.intersection a) t
    (∑ i : Fin (n+1), (-1:R)^i.val •
      LocalizationCech.restrict z (FilteredCech.term I z t)
        (FilteredCech.restriction_mem I z (coordinate_mem I z hz) t)
        (ActualCech.intersection_delete a i) (x (a ∘ i.succAbove))) = _
  apply linearMap_sum_smul
  intro i
  exact filteredReduction_naturality I z hz (ActualCech.intersection_delete a i) t (x (a ∘ i.succAbove))

 
def filteredReductionCech (t : ℕ) :
    FilteredCech.complex I z (coordinate_mem I z hz) t ⟶ exceptionalCech I z hz t :=
  cochainOfMap
    (hX := fun n => ModuleCat.hom_ext (LinearMap.ext (LocalizationCech.d_square z
      (FilteredCech.term I z t) (FilteredCech.restriction_mem I z (coordinate_mem I z hz) t) n)))
    (hY := fun n => ModuleCat.hom_ext (LinearMap.ext (RestrictedPolynomialImageCech.d_square
      (R := R) (S := R ⧸ I) (B := IdealGraded.Ring I) (h := h) (targetGrade I)
      (mapR I z hz) (mapR_smul I z hz) (mapR_surjective I z hz) n t)))
    (fun n => ModuleCat.ofHom (filteredReductionCochains I z hz n t))
    (fun n x => (filteredReductionCochains_d I z hz n t x).symm)

lemma filteredReductionCochains_surjective (n t : ℕ) :
    Function.Surjective (filteredReductionCochains I z hz n t) := by
  intro x
  choose y hy using fun a => filteredReduction_surjective I z hz
    (ActualCech.intersection a) t (x a)
  exact ⟨y,funext hy⟩

lemma filteredReductionCochains_kernel (n t : ℕ) :
    (filteredReductionCochains I z hz n t).ker =
      (LocalizationCech.inclusionLinear z (FilteredCech.term I z (t+1))
        (FilteredCech.term I z t) (fun _ => FilteredFraction.antitone I _ _ (Nat.le_succ t)) n).range := by
  ext x
  constructor
  · intro hx
    have hx' : ∀ a, (x a).val ∈ FilteredCech.term I z (t+1) (ActualCech.intersection a) := by
      intro a
      have ha : x a ∈ (filteredReduction I z hz (ActualCech.intersection a) t).ker :=
        congrFun hx a
      rw [filteredReduction_kernel] at ha
      exact ha
    exact ⟨fun a => ⟨(x a).val,hx' a⟩,rfl⟩
  · rintro ⟨y,rfl⟩
    change filteredReductionCochains I z hz n t
      (LocalizationCech.inclusionLinear z (FilteredCech.term I z (t+1))
        (FilteredCech.term I z t) (fun _ => FilteredFraction.antitone I _ _ (Nat.le_succ t)) n y)=0
    funext a
    apply (show _ ∈ (filteredReduction I z hz (ActualCech.intersection a) t).ker from ?_)
    rw [filteredReduction_kernel]
    exact (y a).property

lemma filteredReductionCech_comp_zero (t : ℕ) :
    FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_succ t) ≫
      filteredReductionCech I z hz t=0 := by
  ext n x
  have hx : LocalizationCech.inclusionLinear z (FilteredCech.term I z (t+1))
      (FilteredCech.term I z t) (fun _ => FilteredFraction.antitone I _ _ (Nat.le_succ t)) n x ∈
      (filteredReductionCochains I z hz n t).ker := by
    rw [filteredReductionCochains_kernel]
    exact ⟨x,rfl⟩
  exact hx

 

def filteredLayerSequence (t : ℕ) : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_succ t))
    (filteredReductionCech I z hz t) (filteredReductionCech_comp_zero I z hz t)

lemma filteredLayerSequence_shortExact (t : ℕ) : (filteredLayerSequence I z hz t).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · apply LinearMap.exact_iff.mpr
    exact filteredReductionCochains_kernel I z hz n t
  · exact LocalizationCech.inclusionLinear_injective z (FilteredCech.term I z (t+1))
      (FilteredCech.term I z t) (fun _ => FilteredFraction.antitone I _ _ (Nat.le_succ t)) n
  · exact filteredReductionCochains_surjective I z hz n t
end Lech.SourceGraded


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (ell : AllModuleLength R)

 

noncomputable def finiteThickening (t M : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  cokernel (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t M))

 

lemma finiteThickening_homology_zero
    (hh : 0 < h) (hmu : ell.value (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ell.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ell.value (ModuleCat.of R (R ⧸ I))) (t M n : ℕ) :
    ell.value ((finiteThickening I z hz t M).homology n)=0 := by
  let P := (ell.torsionLength ⊥).zeroClass
  have hp : P ((finiteThickening I z hz t M).homology n) := by
    induction M with
    | zero =>
      have hi : Epi (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t 0)) := by
        simpa only [FilteredCech.inclusion_refl] using (inferInstance : Epi (𝟙 (FilteredCech.complex I z (coordinate_mem I z hz) t)))
      unfold finiteThickening
      exact P.prop_of_isZero ((homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map_isZero
        (isZero_cokernel_of_epi (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t 0))))
    | succ M ih =>
      have hl : P ((cokernel
          (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_succ (t+M)))).homology n) :=
        cokernel_homology_property_of_shortExact P (filteredLayerSequence_shortExact I z hz (t+M)) n
          (ell.mem_zeroClass _ (exceptionalCech_homology_zero I z hz ell hh hmu ha (t+M) n))
      have hc := cokernel_comp_homology_property P
        (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_succ (t+M)))
        (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.le_add_right t M)) n hl ih
      rw [FilteredCech.inclusion_comp] at hc
      exact hc
  exact hp.2

 
noncomputable def finiteThickeningTransition (t : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    finiteThickening I z hz t N ⟶ finiteThickening I z hz t M :=
  cokernel.map _ _
    (FilteredCech.inclusion I z (coordinate_mem I z hz) (Nat.add_le_add_left hMN t)) (𝟙 _)
    (by simp only [Category.comp_id,FilteredCech.inclusion_comp])

lemma finiteThickeningTransition_refl (t M : ℕ) :
    finiteThickeningTransition I z hz t (le_refl M)=𝟙 (finiteThickening I z hz t M) := by
  unfold finiteThickeningTransition finiteThickening
  apply (cancel_epi (cokernel.π _)).mp
  simp only [cokernel.map,cokernel.π_desc,Category.id_comp,Category.comp_id]

lemma finiteThickeningTransition_comp (t : ℕ) {L M N : ℕ} (hLM : L ≤ M) (hMN : M ≤ N) :
    finiteThickeningTransition I z hz t hMN ≫ finiteThickeningTransition I z hz t hLM =
      finiteThickeningTransition I z hz t (hLM.trans hMN) := by
  unfold finiteThickeningTransition finiteThickening
  apply (cancel_epi (cokernel.π _)).mp
  simp only [cokernel.map,cokernel.π_desc_assoc,cokernel.π_desc,Category.id_comp]
end Lech.SourceGraded


namespace Lech
universe u v
variable {R : Type u} [CommRing R] {C : Type v} [Category C] [Abelian C]

 

lemma prop_additive_free (P : ObjectProperty C) [P.IsSerreClass]
    (T : ModuleCat.{u} R ⥤ C) [T.Additive]
    (hR : P (T.obj (ModuleCat.of R R))) (M : ModuleCat.{u} R)
    [Module.Free R M] [Module.Finite R M] [Nontrivial R] : P (T.obj M) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts T
  have hfin : ∀ n : ℕ, P (T.obj (ModuleCat.of R (Fin n → R))) := by
    intro n
    induction n with
    | zero =>
      apply P.prop_of_isZero
      apply T.map_isZero
      rw [ModuleCat.isZero_iff_subsingleton]
      infer_instance
    | succ n ih =>
      let X := ModuleCat.of R R
      let Y := ModuleCat.of R (Fin n → R)
      let e : X ⊞ Y ≅ ModuleCat.of R (Fin (n + 1) → R) :=
        ModuleCat.biprodIsoProd X Y ≪≫
          LinearEquiv.toModuleIso (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R))
      apply P.prop_of_iso (T.mapIso e)
      apply P.prop_of_iso (T.mapBiprod X Y).symm
      exact P.prop_biprod hR ih
  exact P.prop_of_iso (T.mapIso (LinearEquiv.toModuleIso
    (Module.finBasis R M).equivFun).symm) (hfin _)

end Lech


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

 
def functor (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.flip.obj K

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
  {F G H : CochainComplex (ModuleCat.{u} R) ℤ}

 

def degreeMap (a : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    ((functor K).obj F).X i ⟶ ((functor K).obj G).X i :=
  mapBifunctorDesc (fun p q hpq =>
    ((curriedTensor (ModuleCat.{u} R)).map (a p)).app (K.X q) ≫
      ιMapBifunctor G K (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq)

@[reassoc (attr := simp)] lemma ι_degreeMap (a : ∀ j, F.X j ⟶ G.X j)
    (p q i : ℤ) (hpq : p+q=i) :
    ιMapBifunctor F K (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫ degreeMap K a i =
      ((curriedTensor (ModuleCat.{u} R)).map (a p)).app (K.X q) ≫
        ιMapBifunctor G K (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq := by
  apply ι_mapBifunctorDesc

lemma degreeMap_id (i : ℤ) : degreeMap K (fun j => 𝟙 (F.X j)) i = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  change _ = ιMapBifunctor F K (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫
    𝟙 ((mapBifunctor F K (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).X i)
  simp

lemma degreeMap_comp (a : ∀ j, F.X j ⟶ G.X j) (b : ∀ j, G.X j ⟶ H.X j) (i : ℤ) :
    degreeMap K (fun j => a j ≫ b j) i=degreeMap K a i ≫ degreeMap K b i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  refine (ι_degreeMap K (fun j => a j ≫ b j) p q i hpq).trans ?_
  simp only [Functor.map_comp, NatTrans.comp_app]
  exact (Category.assoc _ _ _).trans
    ((congrArg (((curriedTensor (ModuleCat.{u} R)).map (a p)).app (K.X q) ≫ ·)
      (ι_degreeMap K b p q i hpq).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ degreeMap K b i) (ι_degreeMap K a p q i hpq).symm).trans
            (Category.assoc _ _ _))))

lemma degreeMap_add (a b : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    degreeMap K (fun j => a j+b j) i=degreeMap K a i+degreeMap K b i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  refine (ι_degreeMap K (fun j => a j + b j) p q i hpq).trans ?_
  simp only [Functor.map_add, NatTrans.app_add]
  exact (Preadditive.add_comp _ _ _ _ _ _).trans
    ((congrArg₂ (· + ·) (ι_degreeMap K a p q i hpq).symm
      (ι_degreeMap K b p q i hpq).symm).trans (Preadditive.comp_add _ _ _ _ _ _).symm)

lemma map_f (f : F ⟶ G) (i : ℤ) :
    ((functor K).map f).f i=degreeMap K f.f i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp [functor]
  refine (ι_mapBifunctorMap f (𝟙 K) (curriedTensor (ModuleCat.{u} R)) (.up ℤ)
    p q i hpq).trans ?_
  exact (congrArg (fun t => ((curriedTensor (ModuleCat.{u} R)).map (f.f p)).app (K.X q) ≫
    t ≫ ιMapBifunctor G K (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq)
      (((curriedTensor (ModuleCat.{u} R)).obj (G.X p)).map_id (K.X q))).trans
    ((congrArg (((curriedTensor (ModuleCat.{u} R)).map (f.f p)).app (K.X q) ≫ ·)
      (Category.id_comp _)).trans (ι_degreeMap K f.f p q i hpq).symm)

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

 

def singleRingHomologyIso (j i : ℤ) :
    ((functor K).obj ((single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R))).homology i ≅
      K.homology (i-j) := by
  let U := (single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R R)
  let e : U⟦-j⟧ ≅ (single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R) :=
    ((CochainComplex.singleFunctors (ModuleCat.{u} R)).shiftIso (-j) j 0 (by omega)).app _
  let e' : (functor K).obj ((single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R)) ≅ K⟦-j⟧ :=
    (functor K).mapIso e.symm ≪≫
      CochainComplex.mapBifunctorShift₁Iso U K (curriedTensor (ModuleCat.{u} R)) (-j) ≪≫
      (shiftFunctor _ (-j)).mapIso (HomologicalComplex.leftUnitor K)
  exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso e' ≪≫
    ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftIso (-j) i (i-j) (by omega)).app K
end Lech.TensorTotal
end

end OAI
