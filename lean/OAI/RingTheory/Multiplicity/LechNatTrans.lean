import Mathlib
import OAI.RingTheory.Multiplicity.KoszulHomologyMap

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
namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open scoped ZeroObject
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

lemma natTrans_homology_isoMod_of_iso (P : ObjectProperty D) [P.IsSerreClass]
    {A B : CochainComplex C ℤ ⥤ CochainComplex D ℤ} (α : A ⟶ B)
    {F G : CochainComplex C ℤ} (e : F ≅ G)
    (hF : ∀ i, P.isoModSerre (homologyMap (α.app F) i)) (i : ℤ) :
    P.isoModSerre (homologyMap (α.app G) i) := by
  have he : α.app G = A.map e.inv ≫ α.app F ≫ B.map e.hom := by
    rw [← α.naturality e.hom, ← Category.assoc, ← Functor.map_comp,
      e.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [he, homologyMap_comp, homologyMap_comp]
  exact P.isoModSerre.comp_mem _ _ (P.isoModSerre_of_isIso _)
    (P.isoModSerre.comp_mem _ _ (hF i) (P.isoModSerre_of_isIso _))

 

lemma bounded_natTrans_homology_isoMod (P : ObjectProperty D) [P.IsSerreClass]
    (A B : CochainComplex C ℤ ⥤ CochainComplex D ℤ) [A.Additive] [B.Additive]
    (α : A ⟶ B)
    (hA : ∀ (S : ShortComplex (CochainComplex C ℤ)),
      (∀ j, (S.map (eval C (.up ℤ) j)).Splitting) → (S.map A).ShortExact)
    (hB : ∀ (S : ShortComplex (CochainComplex C ℤ)),
      (∀ j, (S.map (eval C (.up ℤ) j)).Splitting) → (S.map B).ShortExact)
    (F : CochainComplex C ℤ) (n : ℤ) (h : ℕ)
    (hsupp : ∀ i, i < n ∨ n + h ≤ i → IsZero (F.X i))
    (hterms : ∀ j i, P.isoModSerre (homologyMap
      (α.app ((single C (.up ℤ) j).obj (F.X j))) i)) (i : ℤ) :
    P.isoModSerre (homologyMap (α.app F) i) := by
  let Q : ObjectProperty (CochainComplex C ℤ) := fun F =>
    ∀ i, P.isoModSerre (homologyMap (α.app F) i)
  have : Q.ContainsZero := ⟨0, isZero_zero _, by
    intro i
    have hAz := (homologyFunctor D (.up ℤ) i).map_isZero
      (A.map_isZero (isZero_zero _))
    have hBz := (homologyFunctor D (.up ℤ) i).map_isZero
      (B.map_isZero (isZero_zero _))
    have : IsIso (homologyMap (α.app 0) i) := hAz.isIso hBz _
    exact P.isoModSerre_of_isIso _⟩
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e hF =>
    natTrans_homology_isoMod_of_iso P α e hF⟩
  apply FiniteComplex.devissage Q ?_ n h F hsupp hterms i
  intro S σ h₁ h₃ j
  let φ : S.map A ⟶ S.map B :=
    { τ₁ := α.app S.X₁, τ₂ := α.app S.X₂, τ₃ := α.app S.X₃
      comm₁₂ := (α.naturality S.f).symm
      comm₂₃ := (α.naturality S.g).symm }
  exact homology_middle_isoModSerre P φ (hA S σ) (hB S σ) h₁ h₃ j

end Lech


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex HomologicalComplex
universe u v
variable {R : Type u} [CommRing R]

@[reassoc]
lemma augmentation_naturality_source
    {F F' G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ F') (g : F' ⟶ G) (zs : List R) (H : ∀ r ∈ zs, r • 𝟙 G = 0) :
    (tensorFunctor zs).map f ≫ augmentation g zs H = augmentation (f ≫ g) zs H := by
  induction zs with
  | nil => rfl
  | cons r zs ih =>
    change mappingCone.map _ _ _ _ (by simp [Linear.smul_comp, Linear.comp_smul]) ≫ mappingCone.desc _ 0 _ _ =
      mappingCone.desc _ 0 _ _
    ext i : 1
    apply (mappingCone.ext_from_iff _ (i+1) i rfl _ _).mpr
    constructor
    · simp [mappingCone.map, HomologicalComplex.comp_f, Category.assoc]
    · simpa [mappingCone.map, HomologicalComplex.comp_f, Category.assoc, tensorFunctor, tensorMap] using
        congrArg (fun f => f.f i) (ih _)

@[reassoc]
lemma complexQuotientπ_naturality (I : Ideal R)
    {F G : CochainComplex (ModuleCat.{v} R) ℤ} (f : F ⟶ G) :
    f ≫ complexQuotientπ I G = complexQuotientπ I F ≫ (complexQuotient I (.up ℤ)).map f := by
  ext i : 1
  exact (moduleQuotientπ I).naturality (f.f i)

noncomputable def quotientAugmentationNat (zs : List R) :
    (tensorFunctor zs : CochainComplex (ModuleCat.{v} R) ℤ ⥤ _) ⟶
      complexQuotient (entryIdeal zs) (.up ℤ) where
  app F := quotientAugmentation F zs
  naturality {F G} f := by
    change (tensorFunctor zs).map f ≫ augmentation _ zs _ =
      augmentation _ zs _ ≫ _
    let HF := fun r hr => complexQuotient_annihilated (entryIdeal zs) r
      (Ideal.subset_span hr) F
    let HG := fun r hr => complexQuotient_annihilated (entryIdeal zs) r
      (Ideal.subset_span hr) G
    exact (augmentation_naturality_source f (complexQuotientπ (entryIdeal zs) G)
      zs HG).trans ((congrArg (fun k => augmentation k zs HG)
        (complexQuotientπ_naturality (entryIdeal zs) f)).trans
        (augmentation_naturality_target (complexQuotientπ (entryIdeal zs) F)
          ((complexQuotient (entryIdeal zs) (.up ℤ)).map f) zs HF HG).symm)

 

lemma quotientAugmentation_bounded
    (P : ObjectProperty (ModuleCat.{v} R)) [P.IsSerreClass]
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R) (n : ℤ) (h : ℕ)
    (hsupp : ∀ i, i < n ∨ n+h ≤ i → IsZero (F.X i))
    (hterms : ∀ j i, P.isoModSerre (homologyMap (quotientAugmentation
      ((single (ModuleCat.{v} R) (.up ℤ) j).obj (F.X j)) zs) i)) (i : ℤ) :
    P.isoModSerre (homologyMap (quotientAugmentation F zs) i) := by
  apply bounded_natTrans_homology_isoMod P (tensorFunctor zs)
    (complexQuotient (entryIdeal zs) (.up ℤ)) (quotientAugmentationNat zs)
    _ _ F n h hsupp hterms i
  · intro S σ
    exact HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun j => (tensorSplitting zs S σ j).shortExact)
  · exact complexQuotient_shortExact (entryIdeal zs)




lemma tensor_isZero_above (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (zs : List R) (n : ℤ) (hF : ∀ j, n < j → IsZero (F.X j)) :
    ∀ j, n < j → IsZero ((tensor zs F).X j) := by
  induction zs with
  | nil => exact hF
  | cons r zs ih =>
    intro j hj
    have hS := coneShortComplex_shortExact (r • 𝟙 (tensor zs F))
    have := hS.mono_f
    have := hS.epi_g
    exact (hS.map (eval _ _ j)).exact.isZero_of_both_isZero
      (ih j hj) (ih (j+1) (by omega))

lemma coneInr_isIso_at_top (F G : CochainComplex (ModuleCat.{v} R) ℤ)
    (f : F ⟶ G) (n : ℤ) (hF : IsZero (F.X (n+1))) :
    IsIso ((mappingCone.inr f).f n) := by
  have hS := coneShortComplex_shortExact f
  have := hS.mono_f
  have := hS.epi_g
  exact (hS.map (eval _ _ n)).isIso_f_iff.mpr hF

lemma inclusion_isIso_at_top (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (zs : List R) (n : ℤ) (hF : ∀ j, n < j → IsZero (F.X j)) :
    IsIso ((inclusion F zs).f n) := by
  induction zs with
  | nil => change IsIso (𝟙 (F.X n)); infer_instance
  | cons r zs ih =>
    have := coneInr_isIso_at_top _ _ (r • 𝟙 (tensor zs F)) n
      (tensor_isZero_above F zs n hF (n+1) (by omega))
    change IsIso ((inclusion F zs).f n ≫ (mappingCone.inr (r • 𝟙 (tensor zs F))).f n)
    infer_instance

 

lemma scalarCone_boundary_range (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (r : R) (n : ℤ) :
    LinearMap.range (((mappingCone.snd (r • 𝟙 F)).v n n (by omega)).hom.comp
      ((mappingCone (r • 𝟙 F)).d (n-1) n).hom) =
      LinearMap.range (r • (LinearMap.id : F.X n →ₗ[R] F.X n)) ⊔
        LinearMap.range (F.d (n-1) n).hom := by
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    have he := mappingCone.d_snd_v (r • 𝟙 F) (n-1) n (by omega)
    have hx := congrArg (fun f => f.hom x) he
    simp only [ModuleCat.hom_comp, ModuleCat.hom_add, LinearMap.add_apply,
      LinearMap.comp_apply] at hx
    change ((mappingCone.snd (r • 𝟙 F)).v n n (by omega)).hom
      (((mappingCone (r • 𝟙 F)).d (n-1) n).hom x) ∈ _
    rw [hx]
    exact Submodule.add_mem_sup
      ⟨_,rfl⟩ ⟨_,rfl⟩
  · apply sup_le
    · rintro y ⟨x,rfl⟩
      refine ⟨((mappingCone.inl (r • 𝟙 F)).v n (n-1) (by omega)).hom x, ?_⟩
      have he := mappingCone.inl_v_d (r • 𝟙 F) n (n-1) (n+1) (by omega) (by omega)
      have he' := congrArg (fun f => (f ≫ (mappingCone.snd (r • 𝟙 F)).v n n (by omega)).hom x) he
      simpa only [Preadditive.sub_comp, Category.assoc,
        mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v, comp_zero,
        sub_zero, Category.comp_id, ModuleCat.hom_comp, LinearMap.comp_apply,
        HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, ModuleCat.hom_smul,
        ModuleCat.hom_id, LinearMap.smul_apply] using he'
    · rintro y ⟨x,rfl⟩
      refine ⟨((mappingCone.inr (r • 𝟙 F)).f (n-1)).hom x, ?_⟩
      have he := mappingCone.inr_f_d (r • 𝟙 F) (n-1) n
      have he' := congrArg (fun f => (f ≫ (mappingCone.snd (r • 𝟙 F)).v n n (by omega)).hom x) he
      simpa only [Category.assoc, mappingCone.inr_f_snd_v, Category.comp_id,
        ModuleCat.hom_comp, LinearMap.comp_apply] using he'

 

noncomputable def projectionTerm (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) : (zs : List R) → ((tensor zs F).X n ⟶ F.X n)
  | [] => 𝟙 _
  | r :: zs => (mappingCone.snd (r • 𝟙 (tensor zs F))).v n n (by omega) ≫
      projectionTerm F n zs

@[reassoc (attr := simp)]
lemma inclusion_projectionTerm (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) (zs : List R) :
    (inclusion F zs).f n ≫ projectionTerm F n zs = 𝟙 _ := by
  induction zs with
  | nil => simp [inclusion, projectionTerm]
  | cons r zs ih =>
    change ((inclusion F zs).f n ≫ (mappingCone.inr (r • 𝟙 (tensor zs F))).f n) ≫
      ((mappingCone.snd (r • 𝟙 (tensor zs F))).v n n (by omega) ≫ projectionTerm F n zs) = _
    simpa only [Category.assoc, mappingCone.inr_f_snd_v_assoc] using ih

lemma projectionTerm_surjective (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) (zs : List R) : Function.Surjective (projectionTerm F n zs).hom := by
  intro x
  refine ⟨((inclusion F zs).f n).hom x, ?_⟩
  exact congrArg (fun f => f.hom x) (inclusion_projectionTerm F n zs)

lemma scalar_range_eq_ideal_smul (M : ModuleCat.{v} R) (r : R) :
    LinearMap.range (r • (LinearMap.id : M →ₗ[R] M)) =
      (Ideal.span {r}) • (⊤ : Submodule R M) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def,
    Submodule.map_top]
  rfl

lemma entryIdeal_cons_for_top (r : R) (zs : List R) :
    entryIdeal (r::zs) = Ideal.span {r} ⊔ entryIdeal zs := by
  simp only [entryIdeal, List.mem_cons, Set.ofPred_or, Set.ofPred_eq_eq_singleton,
    Ideal.span_union]

 

lemma projectionTerm_boundary_range
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (zs : List R) :
    LinearMap.range (((tensor zs F).d (n-1) n ≫ projectionTerm F n zs).hom) =
      entryIdeal zs • (⊤ : Submodule R (F.X n)) ⊔
        LinearMap.range (F.d (n-1) n).hom := by
  induction zs with
  | nil => simp [projectionTerm, entryIdeal]; rfl
  | cons r zs ih =>
    change LinearMap.range (((mappingCone (r • 𝟙 (tensor zs F))).d (n-1) n ≫
      (mappingCone.snd _).v n n _ ≫ projectionTerm F n zs).hom) = _
    rw [← Category.assoc, ModuleCat.hom_comp, LinearMap.range_comp,
      ModuleCat.hom_comp, scalarCone_boundary_range, Submodule.map_sup,
      scalar_range_eq_ideal_smul, Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (projectionTerm_surjective F n zs)]
    rw [← LinearMap.range_comp, ← ModuleCat.hom_comp, ih, entryIdeal_cons_for_top,
      Submodule.sup_smul, sup_assoc]

lemma projectionTerm_isIso_at_top
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (zs : List R)
    (hF : ∀ j, n < j → IsZero (F.X j)) : IsIso (projectionTerm F n zs) := by
  have := inclusion_isIso_at_top F zs n hF
  have : IsIso ((inclusion F zs).f n ≫ projectionTerm F n zs) := by
    rw [inclusion_projectionTerm]
    infer_instance
  exact IsIso.of_isIso_comp_left ((inclusion F zs).f n) _

lemma augmentation_f_at_top
    {F G : CochainComplex (ModuleCat.{v} R) ℤ} (f : F ⟶ G) (zs : List R)
    (H : ∀ r ∈ zs, r • 𝟙 G = 0) (n : ℤ)
    (hF : ∀ j, n < j → IsZero (F.X j)) :
    (augmentation f zs H).f n = projectionTerm F n zs ≫ f.f n := by
  have := inclusion_isIso_at_top F zs n hF
  apply (cancel_epi ((inclusion F zs).f n)).mp
  rw [← Category.assoc, inclusion_projectionTerm, Category.id_comp]
  exact congrArg (fun f => f.f n) (inclusion_augmentation f zs H)

 

lemma shortComplex_homologyMap_iso_of_augmentation
    {C : Type*} [Category C] [Abelian C] {S T : ShortComplex C} (φ : S ⟶ T)
    (hSg : S.g = 0) (hTf : T.f = 0) (hTg : T.g = 0)
    (he : (ShortComplex.mk S.f φ.τ₂ (by rw [← φ.comm₁₂, hTf, comp_zero])).Exact)
    [Epi φ.τ₂] : IsIso (ShortComplex.homologyMap φ) := by
  let hS := ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork S hSg
    (CokernelCofork.ofπ φ.τ₂ (by rw [← φ.comm₁₂, hTf, comp_zero])) he.gIsCokernel
  let hT := ShortComplex.LeftHomologyData.ofZeros T hTf hTg
  let γ : ShortComplex.LeftHomologyMapData φ hS hT :=
    { φK := φ.τ₂
      φH := 𝟙 _
      commi := by change φ.τ₂ ≫ 𝟙 _ = 𝟙 _ ≫ φ.τ₂; simp
      commf' := by
        exact φ.comm₁₂.symm.trans (congrArg (φ.τ₁ ≫ ·)
          (hTf.trans (ShortComplex.LeftHomologyData.ofZeros_f' T hTf hTg).symm))
      commπ := by rfl }
  apply (ShortComplex.quasiIso_iff φ).mp
  exact γ.quasiIso_iff.mpr (by change IsIso (𝟙 T.X₂); infer_instance)

 

lemma quotientAugmentation_homology_top
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ) (zs : List R)
    (hF : ∀ j, n < j → IsZero (F.X j)) (hd : F.d (n-1) n = 0) :
    IsIso (homologyMap (quotientAugmentation F zs) n) := by
  let K := tensor zs F
  let G := (complexQuotient (entryIdeal zs) (.up ℤ)).obj F
  let f := quotientAugmentation F zs
  let p := projectionTerm F n zs
  have hp : IsIso p := projectionTerm_isIso_at_top F n zs hF
  have hpf : f.f n = p ≫ (moduleQuotientπ (entryIdeal zs)).app (F.X n) :=
    augmentation_f_at_top _ zs _ n hF
  have hepi : Epi (f.f n) := by
    rw [hpf]
    exact epi_comp' (inferInstanceAs (Epi p))
      (inferInstanceAs (Epi ((moduleQuotientπ (entryIdeal zs)).app (F.X n))))
  have hGf : G.d (n-1) n = 0 := by
    change (moduleQuotient (entryIdeal zs)).map (F.d (n-1) n) = 0
    rw [hd, Functor.map_zero]
  have hGg : G.d n (n+1) = 0 := by
    change (moduleQuotient (entryIdeal zs)).map (F.d n (n+1)) = 0
    rw [(hF (n+1) (by omega)).eq_zero_of_tgt (F.d n (n+1)), Functor.map_zero]
  have hKg : K.d n (n+1) = 0 :=
    (tensor_isZero_above F zs n hF (n+1) (by omega)).eq_zero_of_tgt _
  have : Epi ((shortComplexFunctor _ (.up ℤ) n).map f).τ₂ := hepi
  have hprev : (ComplexShape.up ℤ).prev n = n-1 :=
    (ComplexShape.up ℤ).prev_eq' (by change n-1+1=n; omega)
  have hnext : (ComplexShape.up ℤ).next n = n+1 :=
    (ComplexShape.up ℤ).next_eq' (by rfl)
  refine shortComplex_homologyMap_iso_of_augmentation
    ((shortComplexFunctor _ (.up ℤ) n).map f)
    (by change K.d n ((ComplexShape.up ℤ).next n) = 0; rw [hnext]; exact hKg)
    (by change G.d ((ComplexShape.up ℤ).prev n) n = 0; rw [hprev]; exact hGf)
    (by change G.d n ((ComplexShape.up ℤ).next n) = 0; rw [hnext]; exact hGg) ?_
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx' : p.hom x ∈ entryIdeal zs • (⊤ : Submodule R (F.X n)) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change ((moduleQuotientπ (entryIdeal zs)).app (F.X n)).hom (p.hom x) = 0
    change (f.f n).hom x = 0 at hx
    rw [hpf] at hx
    exact hx
  have hr := projectionTerm_boundary_range F n zs
  rw [hd, ModuleCat.hom_zero, LinearMap.range_zero, sup_bot_eq] at hr
  rw [← hr] at hx'
  obtain ⟨y,hy⟩ := hx'
  refine ⟨(K.XIsoOfEq hprev).inv.hom y, ?_⟩
  have hy' := (ModuleCat.mono_iff_injective p).mp inferInstance hy
  change (K.d ((ComplexShape.up ℤ).prev n) n).hom ((K.XIsoOfEq hprev).inv.hom y) = x
  have hc : (K.XIsoOfEq hprev).inv ≫ K.d ((ComplexShape.up ℤ).prev n) n = K.d (n-1) n := by simp
  change (((K.XIsoOfEq hprev).inv ≫ K.d ((ComplexShape.up ℤ).prev n) n).hom) y = x
  rw [hc]
  exact hy' 

end Lech.Koszul


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v w

 

lemma isIso_app_of_finite_retract
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (A B : C ⥤ D) [A.Additive] [B.Additive] (α : A ⟶ B)
    (X Y : C) {ι : Type*} [Fintype ι] (s : ι → (X ⟶ Y)) (r : ι → (Y ⟶ X))
    (hs : ∑ i, s i ≫ r i = 𝟙 X) [IsIso (α.app Y)] : IsIso (α.app X) := by
  classical
  let β : B.obj X ⟶ A.obj X := ∑ i, B.map (s i) ≫ inv (α.app Y) ≫ A.map (r i)
  refine ⟨⟨β, ?_, ?_⟩⟩
  · dsimp [β]
    rw [Preadditive.comp_sum]
    have h : ∀ i, α.app X ≫ (B.map (s i) ≫ inv (α.app Y) ≫ A.map (r i)) =
        A.map (s i ≫ r i) := by
      intro i
      rw [← Category.assoc, ← α.naturality, Category.assoc,
        IsIso.hom_inv_id_assoc, ← Functor.map_comp]
    simp_rw [h]
    rw [← A.map_sum, hs, A.map_id]
  · dsimp [β]
    rw [Preadditive.sum_comp]
    have h : ∀ i, (B.map (s i) ≫ inv (α.app Y) ≫ A.map (r i)) ≫ α.app X =
        B.map (s i ≫ r i) := by
      intro i
      rw [Category.assoc, Category.assoc, α.naturality, IsIso.inv_hom_id_assoc,
        ← Functor.map_comp]
    simp_rw [h]
    rw [← B.map_sum, hs, B.map_id]

 
lemma basis_finite_retract {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] {ι : Type w} [Fintype ι] (b : Module.Basis ι R M) :
    ∑ i, (ModuleCat.ofHom (b.coord i)) ≫
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))) =
      𝟙 (ModuleCat.of R M) := by
  classical
  ext x
  simp

 

lemma isIso_app_of_finite_free
    {R : Type u} [CommRing R] {D : Type*} [Category D] [Preadditive D]
    (A B : ModuleCat.{u} R ⥤ D) [A.Additive] [B.Additive] (α : A ⟶ B)
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M]
    [IsIso (α.app (ModuleCat.of R R))] : IsIso (α.app M) := by
  let b := Module.Free.chooseBasis R M
  let := Module.Free.ChooseBasisIndex.fintype R M
  exact isIso_app_of_finite_retract A B α M (ModuleCat.of R R)
    (fun i => ModuleCat.ofHom (b.coord i))
    (fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i)))
    (basis_finite_retract b)

end Lech
end

end OAI
