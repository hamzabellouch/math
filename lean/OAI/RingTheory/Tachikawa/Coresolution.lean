import OAI.RingTheory.Tachikawa.Twisting

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {R : Type*} [Ring R]

def coresolutionOfExact (M : ModuleCat R) (P : ℕ → ModuleCat R)
    (d : ∀ n, P n ⟶ P (n+1)) (ε : M ⟶ P 0)
    (hd : ∀ n, Function.Exact (d n) (d (n+1)))
    (hε : Function.Exact ε (d 0)) (inj : Function.Injective ε)
    (injs : ∀ n, Injective (P n)) : InjectiveResolution M := by
  let sq : ∀ n, d n ≫ d (n+1) = 0 := fun n => ModuleCat.hom_ext <| LinearMap.ext <|
    (hd n).apply_apply_eq_zero
  let K := CochainComplex.of P d sq
  let ι : (CochainComplex.single₀ (ModuleCat R)).obj M ⟶ K :=
    (CochainComplex.fromSingle₀Equiv _ _).symm ⟨ε, by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact hε.apply_apply_eq_zero⟩
  refine {cocomplex := K, ι := ι, injective := injs, quasiIso := ⟨fun n => ?_⟩}
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros _ (by rfl) (by rfl) (by simp; rfl)]
    · constructor
      · apply (ShortComplex.moduleCat_exact_iff _).2
        change ∀ x : P 0, K.d 0 1 x = 0 → ∃ y : M, ε y = x
        rw [show K.d 0 1 = d 0 from CochainComplex.of_d P d 0]
        exact fun x => (hε x).mp
      · change Mono ε
        exact (ModuleCat.mono_iff_injective ε).2 inj
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
    rw [HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)]
    apply (ShortComplex.moduleCat_exact_iff _).2
    change ∀ x : P (n+1), K.d (n+1) (n+2) x = 0 → ∃ y, K.d n (n+1) y = x
    rw [show K.d n (n+1) = d n from CochainComplex.of_d P d n,
      show K.d (n+1) (n+2) = d (n+1) from CochainComplex.of_d P d (n+1)]
    exact fun x => (hd n x).mp

theorem ext_subsingleton_of_coboundaries {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (I : InjectiveResolution Y) (n : ℕ)
    (h : ∀ f : X ⟶ I.cocomplex.X (n+1),
      f ≫ I.cocomplex.d (n+1) (n+2) = 0 →
      ∃ g : X ⟶ I.cocomplex.X n, g ≫ I.cocomplex.d n (n+1) = f) :
    Subsingleton (Abelian.Ext X Y (n+1)) := by
  have hzero (α : Abelian.Ext X Y (n+1)) : α = 0 := by
    obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α (n+2) rfl
    exact (I.extMk_eq_zero_iff f (n+2) rfl hf n rfl).mpr (h f hf)
  exact ⟨fun α β => (hzero α).trans (hzero β).symm⟩
end Tachikawa



namespace Tachikawa.FiniteModule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))

lemma embed_exact : Function.Exact (M.embed t) (M.negDifferential t 0) := by
  intro x
  constructor
  · intro hx
    have hz : (LinearMap.range (M.embed t)).mkQ x = 0 :=
      (M.negative t 1).embed_injective t (hx.trans ((M.negative t 1).embed t).map_zero.symm)
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  · rintro ⟨y,rfl⟩
    change (M.negative t 1).embed t ((LinearMap.range (M.embed t)).mkQ (M.embed t y)) = 0
    have hz : (LinearMap.range (M.embed t)).mkQ (M.embed t y) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨y,rfl⟩
    exact (congrArg ((M.negative t 1).embed t) hz).trans
      ((M.negative t 1).embed t).map_zero

def coresolution : InjectiveResolution M.obj :=
  coresolutionOfExact M.obj (fun n => ModuleCat.of R (M.negTerm t n))
    (fun n => ModuleCat.ofHom (M.negDifferential t n)) (ModuleCat.ofHom (M.embed t))
    (M.neg_exact t) (M.embed_exact t) (M.embed_injective t) (by
      intro n
      let : Module.Injective R R := t.injective
      exact Module.injective_object_of_injective_module R (M.negTerm t n))

@[simp] lemma coresolution_d (n : ℕ) :
    (M.coresolution t).cocomplex.d n (n+1) = ModuleCat.ofHom (M.negDifferential t n) := by
  dsimp only [coresolution,coresolutionOfExact]
  exact CochainComplex.of_d _ _ n

@[simp] lemma coresolution_ι :
    (M.coresolution t).ι.f 0 = ModuleCat.ofHom (M.embed t) := rfl
end Tachikawa.FiniteModule



namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

def inverseTwistHom {X Y : ModuleCat R} (f : X ⟶ (twistFunctor σ).obj Y) :
    (twistFunctor σ.symm).obj X ⟶ Y := ModuleCat.ofHom
  (X := (twistFunctor σ.symm).obj X) (Y := Y)
  { toFun := f
    map_add' := f.hom.map_add
    map_smul' a x := by
      change f (σ a • (show X from x)) = a • (show Y from f x)
      have h := f.hom.map_smul (σ a) (show X from x)
      change f (σ a • (show X from x)) = σ.symm (σ a) • (show Y from f x) at h
      simpa only [AlgEquiv.symm_apply_apply] using h }

@[simp] lemma inverseTwistHom_apply {X Y : ModuleCat R} (f : X ⟶ (twistFunctor σ).obj Y)
    (x : (twistFunctor σ.symm).obj X) : inverseTwistHom σ f x = f x := rfl

variable {J : Type} {c : ComplexShape J}

def inverseTwistComplex {P Q : HomologicalComplex (ModuleCat R) c}
    (f : P ⟶ ((twistFunctor σ).mapHomologicalComplex c).obj Q) :
    ((twistFunctor σ.symm).mapHomologicalComplex c).obj P ⟶ Q where
  f j := inverseTwistHom σ (f.f j)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun h => h x) (f.comm i j)

end Tachikawa.SymmetrizingForm



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
  {Y : C} (P : InjectiveResolution Y)

def mappedCoresolution : InjectiveResolution (F.obj Y) where
  cocomplex := (F.mapHomologicalComplex _).obj P.cocomplex
  injective n := Functor.PreservesInjectiveObjects.injective_obj (P.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex _ _ _).inv.app _ ≫
    (F.mapHomologicalComplex _).map P.ι
  quasiIso := inferInstance

def mappedCoresolutionCochainXIso (j : ℤ) :
    (mappedCoresolution F P).cochainComplex.X j ≅ F.obj (P.cochainComplex.X j) := by
  by_cases h : 0 ≤ j
  · let n := j.toNat
    have hn : (n : ℤ) = j := by dsimp [n]; omega
    exact (mappedCoresolution F P).cochainComplexXIso j n hn ≪≫
      (F.mapIso (P.cochainComplexXIso j n hn)).symm
  · exact (CochainComplex.isZero_of_isStrictlyGE (mappedCoresolution F P).cochainComplex 0 j).isoZero ≪≫
      (F.map_isZero (CochainComplex.isZero_of_isStrictlyGE P.cochainComplex 0 j)).isoZero.symm

lemma mappedCoresolutionCochainXIso_nonneg (j : ℤ) (n : ℕ) (hn : (n : ℤ) = j) :
    mappedCoresolutionCochainXIso F P j =
      (mappedCoresolution F P).cochainComplexXIso j n hn ≪≫
      (F.mapIso (P.cochainComplexXIso j n hn)).symm := by
  have hj : 0 ≤ j := by omega
  simp only [mappedCoresolutionCochainXIso,dite_eq_left hj]
  have : j.toNat = n := by omega
  subst n
  rfl

lemma mappedCoresolutionCochainXIso_comm (i j : ℤ) :
    (mappedCoresolution F P).cochainComplex.d i j ≫ (mappedCoresolutionCochainXIso F P j).hom =
      (mappedCoresolutionCochainXIso F P i).hom ≫ F.map (P.cochainComplex.d i j) := by
  by_cases hi : 0 ≤ i
  · by_cases hj : 0 ≤ j
    · obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le hi
      obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hj
      rw [mappedCoresolutionCochainXIso_nonneg F P _ a rfl,
        mappedCoresolutionCochainXIso_nonneg F P _ b rfl,
        InjectiveResolution.cochainComplex_d _ _ _ a b rfl rfl,
        InjectiveResolution.cochainComplex_d _ _ _ a b rfl rfl]
      dsimp only [mappedCoresolution]
      simp only [Iso.trans_hom,Iso.symm_hom,Functor.mapIso_inv,Functor.map_comp,
        Category.assoc,Iso.inv_hom_id_assoc]
      rw [← F.map_comp_assoc,Iso.inv_hom_id,F.map_id,Category.id_comp]
      rfl
    · exact (F.map_isZero (CochainComplex.isZero_of_isStrictlyGE P.cochainComplex 0 j)).eq_of_tgt _ _
  · exact (CochainComplex.isZero_of_isStrictlyGE (mappedCoresolution F P).cochainComplex 0 i).eq_of_src _ _

def mappedCoresolutionCochainIso : (mappedCoresolution F P).cochainComplex ≅
    (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (mappedCoresolutionCochainXIso F P)
    (fun i j _ => (mappedCoresolutionCochainXIso_comm F P i j).symm)

lemma mappedCoresolutionCochainIso_ι :
    (mappedCoresolution F P).ι' ≫ (mappedCoresolutionCochainIso F P).hom =
      (F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
        (F.mapHomologicalComplex (.up ℤ)).map P.ι' := by
  apply HomologicalComplex.hom_ext
  intro j
  by_cases hj : j = 0
  · subst j
    dsimp only [mappedCoresolution]
    simp only [HomologicalComplex.comp_f,Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.Hom.isoOfComponents_hom_f, mappedCoresolutionCochainIso,
      mappedCoresolutionCochainXIso_nonneg F P 0 0 rfl,
      InjectiveResolution.ι'_f_zero, Functor.map_comp]
    simp [mappedCoresolution,Functor.mapCochainComplexSingleFunctor,
      singleMapHomologicalComplex]
    simp only [singleObjXSelf,singleObjXIsoOfEq,eqToIso.hom]
    erw [eqToHom_refl, Category.id_comp, eqToHom_refl, Category.id_comp,
      F.map_id, Category.id_comp, F.map_comp]
  · exact (isZero_single_obj_X (.up ℤ) 0 (F.obj Y) j hj).eq_of_src _ _

open CochainComplex CochainComplex.HomComplex
omit [F.PreservesInjectiveObjects] [F.PreservesHomology] in
lemma map_fromSingle_shifted {K : CochainComplex C ℤ} {X : C}
    {p n : ℤ} (f : X ⟶ K.X p) (h : 0+n=p) (p' : ℤ) (hp' : p+1=p')
    (hf : f ≫ K.d p p' = 0) :
    (F.mapCochainComplexSingleFunctor 0).inv.app X ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f h p' hp' hf))
        (F.mapHomologicalComplex (.up ℤ)) =
      Cocycle.equivHomShift.symm (Cocycle.fromSingleMk (F.map f) h p' hp'
        (by simp only [Functor.mapHomologicalComplex_obj_d,← F.map_comp,hf,F.map_zero])) := by
  ext j
  simp [ShiftedHom.map,Cocycle.equivHomShift_symm_apply,
    Cocycle.fromSingleMk,Cocycle.homOf,Cocycle.rightShift,
    Cochain.rightShift_v, Cochain.fromSingleMk,
    Functor.mapCochainComplexSingleFunctor,singleMapHomologicalComplex]
  by_cases hj : j = 0
  · subst j
    simp [Cochain.single,h,HomologicalComplex.XIsoOfEq,
      singleObjXSelf,singleObjXIsoOfEq,eqToHom_map]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hj]
end Tachikawa



namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

instance twist_isEquivalence : (twistFunctor σ).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv σ.symm.toRingEquiv

instance twist_preserves_injective : (twistFunctor σ).PreservesInjectiveObjects := inferInstance
instance twist_preserves_projective : (twistFunctor σ).PreservesProjectiveObjects := inferInstance

end Tachikawa.SymmetrizingForm
namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
  {Y : C} (P : InjectiveResolution Y)

@[simp] lemma mappedCoresolution_ι_zero : (mappedCoresolution F P).ι.f 0 = F.map (P.ι.f 0) := by
  change (𝟙 (F.obj Y)) ≫ F.map (P.ι.f 0) = F.map (P.ι.f 0)
  exact Category.id_comp _

end Tachikawa
namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)
  {X : ModuleCat R} (P : InjectiveResolution X)
  (e : (twistFunctor σ).obj X ≅ X) (he : ∀ x, e.hom x = x)
  (e' : (twistFunctor σ.symm).obj X ≅ X) (he' : ∀ x, e'.hom x = x)

include he in
lemma twistIso_inv_apply (x : X) : e.inv x = x := by
  have h := congrArg (fun f => f x) e.inv_hom_id
  change e.hom (e.inv x) = x at h
  rw [he] at h
  exact h

def inverseCoresolutionHom
    (l : InjectiveResolution.Hom P (mappedCoresolution (twistFunctor σ) P) e.inv) :
    InjectiveResolution.Hom (mappedCoresolution (twistFunctor σ.symm) P) P e'.hom where
  hom := inverseTwistComplex σ l.hom
  ι_f_zero_comp_hom_f_zero := by
    rw [mappedCoresolution_ι_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change X at x
    have h := congrArg (fun f => f (show X from x)) l.ι_f_zero_comp_hom_f_zero
    rw [mappedCoresolution_ι_zero] at h
    change l.hom.f 0 (P.ι.f 0 x) = P.ι.f 0 (e.inv x) at h
    change l.hom.f 0 (P.ι.f 0 x) = P.ι.f 0 (e'.hom x)
    rw [twistIso_inv_apply σ e he] at h
    exact h.trans (congrArg (fun y : X => P.ι.f 0 y) (he' x)).symm

end Tachikawa.SymmetrizingForm



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} (P : InjectiveResolution Y)

lemma injective_extMk_hom_roof [HasDerivedCategory C] [HasExt C]
    {n : ℕ} (f : X ⟶ P.cocomplex.X n) (hf : f ≫ P.cocomplex.d n (n+1) = 0) :
    (P.extMk f (n+1) rfl hf).hom =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (f ≫ (P.cochainComplexXIso n n rfl).inv)
          (zero_add _) ((n+1 : ℕ) : ℤ) (by omega)
          (by
            rw [InjectiveResolution.cochainComplex_d _ _ _ n (n+1) rfl rfl]
            simp only [Category.assoc,Iso.inv_hom_id_assoc]
            rw [← Category.assoc,hf,zero_comp])))
        DerivedCategory.Q ≫ (inv (DerivedCategory.Q.map P.ι'))⟦(n : ℤ)⟧' := by
  rw [InjectiveResolution.extMk_hom]
  simp [DerivedCategory.singleFunctorIsoCompQ,ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀]
  erw [CategoryTheory.Functor.map_id,Category.id_comp,IsIso.inv_hom_id,Category.comp_id]

lemma mappedCoresolutionCochain_cocycle {n : ℕ} (f : X ⟶ P.cocomplex.X n)
    (hf : f ≫ P.cocomplex.d n (n+1) = 0) :
    (F.mapCochainComplexSingleFunctor 0).inv.app X ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (f ≫ (P.cochainComplexXIso n n rfl).inv)
          (zero_add _) ((n+1 : ℕ) : ℤ) (by omega)
          (by
            rw [InjectiveResolution.cochainComplex_d _ _ _ n (n+1) rfl rfl]
            simp only [Category.assoc,Iso.inv_hom_id_assoc]
            rw [← Category.assoc,hf,zero_comp])))
        (F.mapHomologicalComplex (.up ℤ)) ≫
      ((mappedCoresolutionCochainIso F P).inv)⟦(n : ℤ)⟧' =
    Cocycle.equivHomShift.symm (Cocycle.fromSingleMk
      (F.map f ≫ ((mappedCoresolution F P).cochainComplexXIso n n rfl).inv)
      (zero_add _) ((n+1 : ℕ) : ℤ) (by omega) (by
        rw [InjectiveResolution.cochainComplex_d _ _ _ n (n+1) rfl rfl]
        dsimp only [mappedCoresolution]
        simp only [Category.assoc,Iso.inv_hom_id_assoc]
        change F.map f ≫ F.map (P.cocomplex.d n (n+1)) ≫ _ = 0
        rw [← F.map_comp_assoc,hf,F.map_zero,zero_comp])) := by
  rw [← Category.assoc,map_fromSingle_shifted]
  erw [← Cocycle.equivHomShift_symm_postcomp,← Cocycle.fromSingleMk_postcomp]
  congr 2
  change F.map (f ≫ (P.cochainComplexXIso n n rfl).inv) ≫
    (mappedCoresolutionCochainXIso F P n).inv = _
  rw [mappedCoresolutionCochainXIso_nonneg F P n n rfl]
  dsimp only [mappedCoresolution]
  simp only [Iso.trans_inv,Iso.symm_inv,Functor.mapIso_hom,Functor.map_comp,
    Category.assoc,← F.map_comp_assoc,Iso.inv_hom_id,F.map_id,Category.id_comp]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CochainComplex

section Shift
variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ] {X Y Z : C} {n : ℤ}
lemma shifted_map_precomp (a : X ⟶ Y) (b : Y ⟶ Z⟦n⟧) :
    ShiftedHom.map (a ≫ b) F = F.map a ≫ ShiftedHom.map b F := by
  simp only [ShiftedHom.map,Functor.map_comp,Category.assoc]
lemma shifted_map_postcomp (a : X ⟶ Y⟦n⟧) (b : Y ⟶ Z) :
    ShiftedHom.map (a ≫ b⟦n⟧') F = ShiftedHom.map a F ≫ (F.map b)⟦n⟧' := by
  simp only [ShiftedHom.map,Functor.map_comp,Category.assoc,
    Functor.commShiftIso_hom_naturality]
end Shift

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} {K : CochainComplex C ℤ}

lemma derived_roof_map {n : ℤ} (p : K ⟶ (singleFunctor C 0).obj X) [QuasiIso p]
    (f : K ⟶ ((singleFunctor C 0).obj Y)⟦n⟧) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      ShiftedHom.map (inv (DerivedCategory.Q.map p) ≫ ShiftedHom.map f DerivedCategory.Q)
        F.mapDerivedCategory ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧' =
    inv (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map p ≫
        (F.mapCochainComplexSingleFunctor 0).hom.app X)) ≫
      ShiftedHom.map (ShiftedHom.map f (F.mapHomologicalComplex (.up ℤ)) ≫
        ((F.mapCochainComplexSingleFunctor 0).hom.app Y)⟦n⟧') DerivedCategory.Q := by
  let A := F.mapDerivedCategoryFactors
  have hf : ShiftedHom.map (ShiftedHom.map f DerivedCategory.Q) F.mapDerivedCategory =
      A.hom.app K ≫ ShiftedHom.map
        (ShiftedHom.map f (F.mapHomologicalComplex (.up ℤ))) DerivedCategory.Q ≫
          (A.inv.app ((singleFunctor C 0).obj Y))⟦n⟧' := by
    have h := ShiftedHom.map_naturality_2 f A
    simpa only [ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀,ShiftedHom.comp_map] using h.symm
  have hp : F.mapDerivedCategory.map (inv (DerivedCategory.Q.map p)) ≫ A.hom.app K =
      A.hom.app ((singleFunctor C 0).obj X) ≫
        inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map p)) := by
    apply (cancel_mono (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map p))).mp
    simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]
    rw [← F.mapDerivedCategoryFactors_hom_naturality p,← Category.assoc,
      ← F.mapDerivedCategory.map_comp,IsIso.inv_hom_id,F.mapDerivedCategory.map_id,
      Category.id_comp]
  rw [shifted_map_precomp,hf]
  simp only [Category.assoc]
  rw [← Category.assoc _ (A.hom.app K),hp]
  simp only [Category.assoc]
  dsimp only [A]
  have hy : F.mapDerivedCategoryFactors.inv.app ((singleFunctor C 0).obj Y) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app Y =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app Y) :=
    F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app Y
  have hx : (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      F.mapDerivedCategoryFactors.hom.app ((singleFunctor C 0).obj X) =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) :=
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X
  rw [← Functor.map_comp]
  erw [hy]
  rw [← Category.assoc ((F.mapDerivedCategorySingleFunctor 0).inv.app X)
    (F.mapDerivedCategoryFactors.hom.app ((singleFunctor C 0).obj X))]
  erw [hx]
  have hc : DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) =
      inv (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X)) := by
    apply IsIso.eq_inv_of_hom_inv_id
    rw [← DerivedCategory.Q.map_comp,Iso.hom_inv_id_app,DerivedCategory.Q.map_id]
  simp only [Functor.map_comp,IsIso.inv_comp,shifted_map_postcomp,Category.assoc]
  rw [hc]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CochainComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} {K : CochainComplex C ℤ}

lemma derived_roof_map_dual {n : ℤ} (p : (singleFunctor C 0).obj Y ⟶ K) [QuasiIso p]
    (f : (singleFunctor C 0).obj X ⟶ K⟦n⟧) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      ShiftedHom.map (ShiftedHom.map f DerivedCategory.Q ≫ (inv (DerivedCategory.Q.map p))⟦n⟧')
        F.mapDerivedCategory ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦n⟧' =
    ShiftedHom.map ((F.mapCochainComplexSingleFunctor 0).inv.app X ≫
      ShiftedHom.map f (F.mapHomologicalComplex (.up ℤ))) DerivedCategory.Q ≫
      (inv (DerivedCategory.Q.map
        ((F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
          (F.mapHomologicalComplex (.up ℤ)).map p)))⟦n⟧' := by
  let A := F.mapDerivedCategoryFactors
  have hf : ShiftedHom.map (ShiftedHom.map f DerivedCategory.Q) F.mapDerivedCategory =
      A.hom.app ((singleFunctor C 0).obj X) ≫ ShiftedHom.map
        (ShiftedHom.map f (F.mapHomologicalComplex (.up ℤ))) DerivedCategory.Q ≫
          (A.inv.app K)⟦n⟧' := by
    have h := ShiftedHom.map_naturality_2 f A
    simpa only [ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀,ShiftedHom.comp_map] using h.symm
  have hp : A.inv.app K ≫ F.mapDerivedCategory.map (inv (DerivedCategory.Q.map p)) =
      inv (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map p)) ≫
        A.inv.app ((singleFunctor C 0).obj Y) := by
    apply (cancel_epi (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map p))).1
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Category.assoc]
    erw [A.inv.naturality p]
    simp only [Functor.comp_map,Category.assoc,← F.mapDerivedCategory.map_comp,IsIso.hom_inv_id,
      F.mapDerivedCategory.map_id]
    erw [Category.comp_id]
  rw [shifted_map_postcomp,hf]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc,hp]
  simp only [Functor.map_comp,Category.assoc]
  have hy : F.mapDerivedCategoryFactors.inv.app ((singleFunctor C 0).obj Y) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app Y =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app Y) :=
    F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app Y
  have hx : (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      F.mapDerivedCategoryFactors.hom.app ((singleFunctor C 0).obj X) =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) :=
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X
  rw [← Functor.map_comp]
  erw [hy]
  rw [← Category.assoc ((F.mapDerivedCategorySingleFunctor 0).inv.app X)
    (A.hom.app ((singleFunctor C 0).obj X))]
  erw [hx]
  have hc : DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app Y) =
      inv (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app Y)) := by
    apply IsIso.eq_inv_of_hom_inv_id
    rw [← DerivedCategory.Q.map_comp,Iso.inv_hom_id_app,DerivedCategory.Q.map_id]
  simp only [Functor.map_comp,IsIso.inv_comp,shifted_map_precomp,Category.assoc]
  rw [hc]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasExt C] [HasExt D]
  {X Y : C} (P : InjectiveResolution Y)

lemma mapExactFunctor_injective_extMk {n : ℕ} (f : X ⟶ P.cocomplex.X n)
    (hf : f ≫ P.cocomplex.d n (n+1) = 0) :
    (P.extMk f (n+1) rfl hf).mapExactFunctor F =
      (mappedCoresolution F P).extMk (F.map f) (n+1) rfl
        (by change F.map _ ≫ F.map _ = 0; rw [← F.map_comp,hf,F.map_zero]) := by
  apply Ext.ext
  rw [Ext.mapExactFunctor_hom,injective_extMk_hom_roof,derived_roof_map_dual]
  conv_rhs => erw [injective_extMk_hom_roof (mappedCoresolution F P)]
  have hι := mappedCoresolutionCochainIso_ι F P
  have hc := mappedCoresolutionCochain_cocycle F P f hf
  have hq := congrArg (fun z => DerivedCategory.Q.map z) hι
  simp only [Functor.map_comp] at hq
  have hr : DerivedCategory.Q.map (mappedCoresolutionCochainIso F P).inv ≫
      inv (DerivedCategory.Q.map (mappedCoresolution F P).ι') =
      inv (DerivedCategory.Q.map
        ((F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
          (F.mapHomologicalComplex (.up ℤ)).map P.ι')) := by
    apply (cancel_epi (DerivedCategory.Q.map
      ((F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
        (F.mapHomologicalComplex (.up ℤ)).map P.ι'))).1
    rw [IsIso.hom_inv_id]
    simp only [Functor.map_comp]
    rw [← hq]
    simp only [Category.assoc,← DerivedCategory.Q.map_comp_assoc,Iso.hom_inv_id,
      DerivedCategory.Q.map_id,Category.id_comp,IsIso.hom_inv_id]
  rw [← Category.assoc] at hc
  dsimp only [mappedCoresolution] at hc ⊢
  rw [← hc]
  erw [shifted_map_postcomp]
  simp only [Category.assoc]
  rw [← Functor.map_comp]
  erw [hr]
end Tachikawa



namespace Tachikawa.VectorSplit
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}
variable (K : HomologicalComplex (ModuleCat k) c)

abbrev homologyComplex : HomologicalComplex (ModuleCat k) c where
  X i := ModuleCat.of k (H K i)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def inclusion : homologyComplex K ⟶ K where
  f i := ModuleCat.ofHom ((inc K i).comp (representatives K i))
  comm' i j _ := by
    rw [show (homologyComplex K).d i j = 0 from rfl, Limits.zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change H K i at x
    change K.d i j (representatives K i x) = 0
    exact cycle_d K i j _

def projection : K ⟶ homologyComplex K where
  f i := ModuleCat.ofHom ((quotient K i).comp (retract K i))
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change 0 = quotient K j (retract K j (K.d i j x))
    have hi : c.prev j = i := c.prev_eq' hij
    subst i
    change 0 = quotient K j (retract K j (boundary K j x))
    rw [retract_cycle, quotient_boundary]

lemma inclusion_projection : inclusion K ≫ projection K = 𝟙 (homologyComplex K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change H K i at x
  change quotient K i (retract K i (representatives K i x)) = x
  rw [retract_cycle, quotient_representatives_apply]

def hom (i j : I) : K.X i ⟶ K.X j := by
  classical
  exact if h : c.Rel j i then
    ModuleCat.ofHom (homotopyComponent K i) ≫ (K.XIsoOfEq (c.prev_eq' h)).hom
    else 0

lemma hom_eq (i j : I) (h : c.Rel j i) :
    hom K i j = ModuleCat.ofHom (homotopyComponent K i) ≫
      (K.XIsoOfEq (c.prev_eq' h)).hom := dite_eq_left h

lemma hom_eq_zero (i j : I) (h : ¬ c.Rel j i) : hom K i j = 0 := dite_eq_right h

lemma d_hom_of_rel (i j : I) (h : c.Rel i j) :
    K.d i j ≫ hom K j i = ModuleCat.ofHom (complement K i) := by
  obtain rfl := c.prev_eq' h
  rw [hom_eq K j (c.prev j) h]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact homotopy_boundary K j h x

lemma d_hom (i : I) :
    K.d i (c.next i) ≫ hom K (c.next i) i = ModuleCat.ofHom (complement K i) := by
  by_cases h : c.Rel i (c.next i)
  · exact d_hom_of_rel K i (c.next i) h
  · rw [K.shape _ _ h, CategoryTheory.Limits.zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : x ∈ Z K i := by
      change K.d i (c.next i) x = 0
      rw [K.shape _ _ h]
      rfl
    exact (complement_cycle K i ⟨x,hx⟩).symm

lemma hom_d (i : I) (x : K.X i) :
    (hom K i (c.prev i) ≫ K.d (c.prev i) i) x =
      inc K i (retract K i x) - inc K i (representatives K i (quotient K i (retract K i x))) := by
  by_cases h : c.Rel (c.prev i) i
  · rw [hom_eq K i (c.prev i) h]
    exact homotopy_d K i x
  · rw [hom_eq_zero K _ _ h, CategoryTheory.Limits.zero_comp]
    have hh := homotopy_d K i x
    rw [K.shape _ _ h] at hh
    exact hh

def idHomotopy : Homotopy (𝟙 K) (projection K ≫ inclusion K) where
  hom := hom K
  zero := hom_eq_zero K
  comm i := by
    change 𝟙 (K.X i) = K.d i (c.next i) ≫ hom K (c.next i) i +
      hom K i (c.prev i) ≫ K.d (c.prev i) i + (projection K ≫ inclusion K).f i
    rw [d_hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = complement K i x + (hom K i (c.prev i) ≫ K.d (c.prev i) i) x +
      inc K i (representatives K i (quotient K i (retract K i x)))
    rw [hom_d]
    change x = (x - inc K i (retract K i x)) +
      (inc K i (retract K i x) - inc K i (representatives K i (quotient K i (retract K i x)))) +
      inc K i (representatives K i (quotient K i (retract K i x)))
    abel

def homologyHomotopyEquiv : HomotopyEquiv K (homologyComplex K) where
  hom := projection K
  inv := inclusion K
  homotopyHomInvId := (idHomotopy K).symm
  homotopyInvHomId := Homotopy.ofEq (inclusion_projection K)

end Tachikawa.VectorSplit



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  {K₁ L₁ M₁ : HomologicalComplex C₁ c₁} {K₂ L₂ M₂ : HomologicalComplex C₂ c₂}
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [HasMapBifunctor M₁ M₂ F c]

lemma bifunctorMap_comp (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    mapBifunctorMap f₁ f₂ F c ≫ mapBifunctorMap g₁ g₂ F c =
      mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂) F c := by
  ext j i₁ i₂ h
  simp only [HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc, ι_mapBifunctorMap,
    Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [NatTrans.naturality_assoc]

lemma bifunctorMap_id : mapBifunctorMap (𝟙 K₁) (𝟙 K₂) F c = 𝟙 _ := by
  ext j i₁ i₂ h
  rw [ι_mapBifunctorMap]
  change (F.map (𝟙 (K₁.X i₁))).app (K₂.X i₂) ≫
    (F.obj (K₁.X i₁)).map (𝟙 (K₂.X i₂)) ≫ _ = _
  rw [F.map_id, (F.obj (K₁.X i₁)).map_id]
  simp only [NatTrans.id_app, Category.id_comp, HomologicalComplex.id_f, Category.comp_id]

def bifunctorHomotopyEquiv (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (mapBifunctor K₁ K₂ F c) (mapBifunctor L₁ L₂ F c) where
  hom := mapBifunctorMap e₁.hom e₂.hom F c
  inv := mapBifunctorMap e₁.inv e₂.inv F c
  homotopyHomInvId := (Homotopy.ofEq (bifunctorMap_comp F c _ _ _ _)).trans
    ((mapBifunctorMapHomotopy₁ e₁.homotopyHomInvId (e₂.hom ≫ e₂.inv) F c).trans
      ((mapBifunctorMapHomotopy₂ (𝟙 K₁) e₂.homotopyHomInvId F c).trans
        (Homotopy.ofEq (bifunctorMap_id F c))))
  homotopyInvHomId := (Homotopy.ofEq (bifunctorMap_comp F c _ _ _ _)).trans
    ((mapBifunctorMapHomotopy₁ e₁.homotopyInvHomId (e₂.inv ≫ e₂.hom) F c).trans
      ((mapBifunctorMapHomotopy₂ (𝟙 L₁) e₂.homotopyInvHomId F c).trans
        (Homotopy.ofEq (bifunctorMap_id F c))))

end Tachikawa



namespace Tachikawa.VectorSplit
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k] {I₁ I₂ J : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K₁ : HomologicalComplex (ModuleCat k) c₁) (K₂ : HomologicalComplex (ModuleCat k) c₂)
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]

abbrev tensorFunctor := CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)
variable [HasMapBifunctor K₁ K₂ (tensorFunctor (k := k)) c]
  [HasMapBifunctor (homologyComplex K₁) (homologyComplex K₂) (tensorFunctor (k := k)) c]

def tensorHomologyHomotopyEquiv :
    HomotopyEquiv (mapBifunctor K₁ K₂ (tensorFunctor (k := k)) c)
      (mapBifunctor (homologyComplex K₁) (homologyComplex K₂) (tensorFunctor (k := k)) c) :=
  bifunctorHomotopyEquiv _ c (homologyHomotopyEquiv K₁) (homologyHomotopyEquiv K₂)

omit [HasMapBifunctor K₁ K₂ (tensorFunctor (k := k)) c] in
lemma tensorHomology_d (j j' : J) :
    (mapBifunctor (homologyComplex K₁) (homologyComplex K₂) (tensorFunctor (k := k)) c).d j j' = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro i₁ i₂ h
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, Limits.comp_zero]
  simp only [HomologicalComplex₂.d₁, HomologicalComplex₂.d₂,
    Functor.mapBifunctorHomologicalComplex_obj_obj_d_f,
    Functor.mapBifunctorHomologicalComplex_obj_obj_X_d]
  change (ComplexShape.ε₁ c₁ c₂ c (i₁,i₂) •
    ((tensorFunctor (k := k)).map 0).app _ ≫ _) +
    (ComplexShape.ε₂ c₁ c₂ c (i₁,i₂) •
    ((tensorFunctor (k := k)).obj _).map 0 ≫ _) = 0
  dsimp only [homologyComplex,Functor.mapBifunctorHomologicalComplex]
  simp only [Functor.map_zero, Limits.zero_app]
  erw [Limits.zero_comp, Limits.zero_comp]
  have zero_sum (domain codomain : ModuleCat k) (sign₁ sign₂ : ℤˣ) :
      sign₁ • (0 : domain ⟶ codomain) + sign₂ • (0 : domain ⟶ codomain) = 0 := by
    simp only [smul_zero, add_zero]
  exact zero_sum _ _ _ _

def zeroDifferentialHomologyIso {C : Type*} [Category* C] [Preadditive C]
    {I : Type*} {d : ComplexShape I} (L : HomologicalComplex C d)
    (hd : ∀ i j, L.d i j = 0) (i : I) [L.HasHomology i] :
    L.homology i ≅ L.X i :=
  (ShortComplex.HomologyData.ofZeros (L.sc i) (hd _ _) (hd _ _)).left.homologyIso

def tensorHomologyIso (j : J) :
    (mapBifunctor K₁ K₂ (tensorFunctor (k := k)) c).homology j ≅
      (mapBifunctor (homologyComplex K₁) (homologyComplex K₂) (tensorFunctor (k := k)) c).X j :=
  (tensorHomologyHomotopyEquiv K₁ K₂ c).toHomologyIso j ≪≫
    zeroDifferentialHomologyIso _ (tensorHomology_d K₁ K₂ c) j

end Tachikawa.VectorSplit



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable (k R : Type) [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat R) ℕ) (N : ModuleCat R)

def resolutionHom : CochainComplex (ModuleCat k) ℕ :=
  (((linearYoneda k (ModuleCat R)).obj N).mapHomologicalComplex (.up ℕ)).obj P.op

@[simp] lemma resolutionHom_X (n : ℕ) :
    (resolutionHom k R P N).X n = ModuleCat.of k (P.X n ⟶ N) := rfl

@[simp] lemma resolutionHom_d (i j : ℕ) (f : P.X i ⟶ N) :
    (resolutionHom k R P N).d i j f = P.d j i ≫ f := rfl

lemma resolutionHom_memZ (n : ℕ) (f : P.X n ⟶ N) :
    f ∈ VectorSplit.Z (resolutionHom k R P N) n ↔ P.d (n+1) n ≫ f = 0 := by
  change (resolutionHom k R P N).d n ((ComplexShape.up ℕ).next n) f = 0 ↔ _
  rw [show (ComplexShape.up ℕ).next n = n+1 from
    (ComplexShape.up ℕ).next_eq' rfl]
  rfl

variable {k R} {M : ModuleCat R} (Q : ProjectiveResolution M)

lemma extMk_smul {n : ℕ} (f : Q.complex.X n ⟶ N)
    (hf : Q.complex.d (n+1) n ≫ f = 0) (r : k)
    (hrf : Q.complex.d (n+1) n ≫ (r • f) = 0) :
    Q.extMk (r • f) (n+1) rfl hrf = r • Q.extMk f (n+1) rfl hf := by
  have h := Q.extMk_comp_mk₀ f (n+1) rfl hf (r • 𝟙 N)
  simpa only [CategoryTheory.Linear.comp_smul, Category.comp_id, Ext.mk₀_smul,
    Ext.comp_smul, Ext.comp_mk₀_id] using h.symm

def resolutionCyclesToExt (n : ℕ) :
    VectorSplit.Z (resolutionHom k R Q.complex N) n →ₗ[k] Ext M N n where
  toFun z := Q.extMk z.val (n+1) rfl ((resolutionHom_memZ k R Q.complex N n z.val).mp z.property)
  map_add' x y := (Q.add_extMk x.val y.val (n+1) rfl _ _).symm
  map_smul' r z := extMk_smul N Q z.val ((resolutionHom_memZ k R Q.complex N n z.val).mp z.property) r _

lemma resolutionCyclesToExt_surjective (n : ℕ) :
    Function.Surjective (resolutionCyclesToExt N Q n (k := k)) := by
  intro x
  obtain ⟨f,hf,rfl⟩ := Q.extMk_surjective x (n+1) rfl
  exact ⟨⟨f,(resolutionHom_memZ k R Q.complex N n f).mpr hf⟩,rfl⟩

lemma resolutionCyclesToExt_ker (n : ℕ) :
    LinearMap.ker (resolutionCyclesToExt N Q (n+1) (k := k)) =
      LinearMap.range (VectorSplit.boundary (resolutionHom k R Q.complex N) (n+1)) := by
  ext z
  change Q.extMk z.val (n+2) rfl
    ((resolutionHom_memZ k R Q.complex N (n+1) z.val).mp z.property) = 0 ↔ _
  erw [Q.extMk_eq_zero_iff _ _ _ _ n rfl]
  have hp : (ComplexShape.up ℕ).prev (n+1) = n :=
    (ComplexShape.up ℕ).prev_eq' rfl
  change (∃ g : Q.complex.X n ⟶ N, Q.complex.d (n+1) n ≫ g = z.val) ↔
    ∃ g : (resolutionHom k R Q.complex N).X ((ComplexShape.up ℕ).prev (n+1)),
      VectorSplit.boundary _ (n+1) g = z
  simp only [← Subtype.val_inj]
  change (∃ g : Q.complex.X n ⟶ N, Q.complex.d (n+1) n ≫ g = z.val) ↔
    ∃ g : Q.complex.X ((ComplexShape.up ℕ).prev (n+1)) ⟶ N,
      Q.complex.d (n+1) ((ComplexShape.up ℕ).prev (n+1)) ≫ g = z.val
  rw [hp]

def resolutionHomologyExt (n : ℕ) :
    VectorSplit.H (resolutionHom k R Q.complex N) (n+1) ≃ₗ[k] Ext M N (n+1) := by
  change (VectorSplit.Z (resolutionHom k R Q.complex N) (n+1) ⧸
    LinearMap.range (VectorSplit.boundary (resolutionHom k R Q.complex N) (n+1))) ≃ₗ[k] _
  rw [← resolutionCyclesToExt_ker N Q n]
  exact (resolutionCyclesToExt N Q (n+1)).quotKerEquivOfSurjective
    (resolutionCyclesToExt_surjective N Q (n+1))

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CochainComplex.HomComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {M N : ModuleCat R} (Q : ProjectiveResolution M)

lemma extMk_zeroDegree_eq_zero (f : Q.complex.X 0 ⟶ N)
    (hf : Q.complex.d 1 0 ≫ f = 0) :
    Q.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  simp only [← Q.extEquivCohomologyClass.apply_eq_iff_eq,
    ProjectiveResolution.extEquivCohomologyClass_extMk,
    ProjectiveResolution.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by norm_num)]
  have hz := CochainComplex.isZero_of_isStrictlyLE Q.cochainComplex 0 1
  constructor
  · rintro ⟨g,hg⟩
    have hg0 : g = 0 := hz.eq_of_src _ _
    rw [hg0, Limits.comp_zero] at hg
    have h := congrArg (fun h => (Q.cochainComplexXIso (-(0 : ℕ)) 0 rfl).inv ≫ h) hg.symm
    simpa using h
  · intro h
    subst f
    exact ⟨0,by simp⟩

lemma resolutionBoundary_zero :
    VectorSplit.boundary (resolutionHom k R Q.complex N) 0 = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Q.complex.X ((ComplexShape.up ℕ).prev 0) ⟶ N at x
  change Q.complex.d 0 ((ComplexShape.up ℕ).prev 0) ≫ x = 0
  rw [Q.complex.shape _ _ (by change ¬ _+1=0; omega), Limits.zero_comp]

lemma resolutionCyclesToExt_ker_all (n : ℕ) :
    LinearMap.ker (resolutionCyclesToExt N Q n (k := k)) =
      LinearMap.range (VectorSplit.boundary (resolutionHom k R Q.complex N) n) := by
  cases n with
  | succ n => exact resolutionCyclesToExt_ker N Q n
  | zero =>
    rw [resolutionBoundary_zero, LinearMap.range_zero]
    ext z
    change Q.extMk z.val 1 rfl ((resolutionHom_memZ k R Q.complex N 0 z.val).mp z.property) = 0 ↔ z = 0
    refine (extMk_zeroDegree_eq_zero Q z.val _).trans ?_
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      subst z
      rfl

def resolutionHomologyExtAll (n : ℕ) :
    VectorSplit.H (resolutionHom k R Q.complex N) n ≃ₗ[k] Ext M N n := by
  change (VectorSplit.Z (resolutionHom k R Q.complex N) n ⧸
    LinearMap.range (VectorSplit.boundary (resolutionHom k R Q.complex N) n)) ≃ₗ[k] _
  rw [← resolutionCyclesToExt_ker_all Q n]
  exact (resolutionCyclesToExt N Q n).quotKerEquivOfSurjective
    (resolutionCyclesToExt_surjective N Q n)

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CochainComplex.HomComplex
open scoped ModuleCat.Algebra
variable (k R : Type) [Field k] [Ring R] [Algebra k R]
  (P : CochainComplex (ModuleCat R) ℕ) (N : ModuleCat R)

def coresolutionHom : CochainComplex (ModuleCat k) ℕ :=
  (((linearCoyoneda k (ModuleCat R)).obj (Opposite.op N)).mapHomologicalComplex (.up ℕ)).obj P

@[simp] lemma coresolutionHom_X (n : ℕ) :
    (coresolutionHom k R P N).X n = ModuleCat.of k (N ⟶ P.X n) := rfl
@[simp] lemma coresolutionHom_d (i j : ℕ) (f : N ⟶ P.X i) :
    (coresolutionHom k R P N).d i j f = f ≫ P.d i j := rfl
lemma coresolutionHom_memZ (n : ℕ) (f : N ⟶ P.X n) :
    f ∈ VectorSplit.Z (coresolutionHom k R P N) n ↔ f ≫ P.d n (n+1) = 0 := by
  change (coresolutionHom k R P N).d n ((ComplexShape.up ℕ).next n) f = 0 ↔ _
  rw [show (ComplexShape.up ℕ).next n = n+1 from (ComplexShape.up ℕ).next_eq' rfl]
  rfl

variable {k R} {M : ModuleCat R} (Q : InjectiveResolution M)
lemma injective_extMk_smul {n : ℕ} (f : N ⟶ Q.cocomplex.X n)
    (hf : f ≫ Q.cocomplex.d n (n+1) = 0) (r : k)
    (hrf : (r • f) ≫ Q.cocomplex.d n (n+1) = 0) :
    Q.extMk (r • f) (n+1) rfl hrf = r • Q.extMk f (n+1) rfl hf := by
  have h := Q.mk₀_comp_extMk f (n+1) rfl hf (r • 𝟙 N)
  simpa only [CategoryTheory.Linear.smul_comp, Category.id_comp, Ext.mk₀_smul,
    Ext.smul_comp, Ext.mk₀_id_comp] using h.symm

def coresolutionCyclesToExt (n : ℕ) :
    VectorSplit.Z (coresolutionHom k R Q.cocomplex N) n →ₗ[k] Ext N M n where
  toFun z := Q.extMk z.val (n+1) rfl ((coresolutionHom_memZ k R Q.cocomplex N n z.val).mp z.property)
  map_add' x y := (Q.add_extMk x.val y.val (n+1) rfl _ _).symm
  map_smul' r z := injective_extMk_smul N Q z.val
    ((coresolutionHom_memZ k R Q.cocomplex N n z.val).mp z.property) r _
lemma coresolutionCyclesToExt_surjective (n : ℕ) :
    Function.Surjective (coresolutionCyclesToExt N Q n (k := k)) := by
  intro x
  obtain ⟨f,hf,rfl⟩ := Q.extMk_surjective x (n+1) rfl
  exact ⟨⟨f,(coresolutionHom_memZ k R Q.cocomplex N n f).mpr hf⟩,rfl⟩
lemma coresolutionCyclesToExt_ker (n : ℕ) :
    LinearMap.ker (coresolutionCyclesToExt N Q (n+1) (k := k)) =
      LinearMap.range (VectorSplit.boundary (coresolutionHom k R Q.cocomplex N) (n+1)) := by
  ext z
  change Q.extMk z.val (n+2) rfl
    ((coresolutionHom_memZ k R Q.cocomplex N (n+1) z.val).mp z.property) = 0 ↔ _
  erw [Q.extMk_eq_zero_iff _ _ _ _ n rfl]
  have hp : (ComplexShape.up ℕ).prev (n+1) = n := (ComplexShape.up ℕ).prev_eq' rfl
  change (∃ g : N ⟶ Q.cocomplex.X n, g ≫ Q.cocomplex.d n (n+1) = z.val) ↔
    ∃ g : (coresolutionHom k R Q.cocomplex N).X ((ComplexShape.up ℕ).prev (n+1)),
      VectorSplit.boundary _ (n+1) g = z
  simp only [← Subtype.val_inj]
  change (∃ g : N ⟶ Q.cocomplex.X n, g ≫ Q.cocomplex.d n (n+1) = z.val) ↔
    ∃ g : N ⟶ Q.cocomplex.X ((ComplexShape.up ℕ).prev (n+1)),
      g ≫ Q.cocomplex.d ((ComplexShape.up ℕ).prev (n+1)) (n+1) = z.val
  rw [hp]
lemma injective_extMk_zeroDegree_eq_zero (f : N ⟶ Q.cocomplex.X 0)
    (hf : f ≫ Q.cocomplex.d 0 1 = 0) :
    Q.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  simp only [← Q.extEquivCohomologyClass.apply_eq_iff_eq,
    InjectiveResolution.extEquivCohomologyClass_extMk,
    InjectiveResolution.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1) (by norm_num)]
  have hz := CochainComplex.isZero_of_isStrictlyGE Q.cochainComplex 0 (-1)
  constructor
  · rintro ⟨g,hg⟩
    have hg0 : g = 0 := hz.eq_of_tgt _ _
    rw [hg0, Limits.zero_comp] at hg
    have h := congrArg (fun h => h ≫ (Q.cochainComplexXIso (0 : ℕ) 0 rfl).hom) hg.symm
    simpa using h
  · intro h
    subst f
    exact ⟨0,by simp⟩
lemma coresolutionBoundary_zero :
    VectorSplit.boundary (coresolutionHom k R Q.cocomplex N) 0 = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change N ⟶ Q.cocomplex.X ((ComplexShape.up ℕ).prev 0) at x
  change x ≫ Q.cocomplex.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  rw [Q.cocomplex.shape _ _ (by change ¬ _+1=0; omega), Limits.comp_zero]
lemma coresolutionCyclesToExt_ker_all (n : ℕ) :
    LinearMap.ker (coresolutionCyclesToExt N Q n (k := k)) =
      LinearMap.range (VectorSplit.boundary (coresolutionHom k R Q.cocomplex N) n) := by
  cases n with
  | succ n => exact coresolutionCyclesToExt_ker N Q n
  | zero =>
    rw [coresolutionBoundary_zero, LinearMap.range_zero]
    ext z
    change Q.extMk z.val 1 rfl ((coresolutionHom_memZ k R Q.cocomplex N 0 z.val).mp z.property) = 0 ↔ z = 0
    refine (injective_extMk_zeroDegree_eq_zero N Q z.val _).trans ?_
    exact ⟨fun h => Subtype.ext h, fun h => by subst z; rfl⟩
def coresolutionHomologyExtAll (n : ℕ) :
    VectorSplit.H (coresolutionHom k R Q.cocomplex N) n ≃ₗ[k] Ext N M n := by
  change (VectorSplit.Z (coresolutionHom k R Q.cocomplex N) n ⧸
    LinearMap.range (VectorSplit.boundary (coresolutionHom k R Q.cocomplex N) n)) ≃ₗ[k] _
  rw [← coresolutionCyclesToExt_ker_all N Q n]
  exact (coresolutionCyclesToExt N Q n).quotKerEquivOfSurjective
    (coresolutionCyclesToExt_surjective N Q n)
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
universe u v w
variable {k : Type*} [Field k] {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [Linear k C]
variable {X X' Y Y' : C}

def extIso (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) : Ext X Y n ≃ₗ[k] Ext X' Y' n where
  toFun x := (Ext.mk₀ e.inv).comp (x.comp (Ext.mk₀ f.hom) (add_zero n)) (zero_add n)
  invFun x := (Ext.mk₀ e.hom).comp (x.comp (Ext.mk₀ f.inv) (add_zero n)) (zero_add n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp only [Ext.add_comp,Ext.comp_add]
  map_smul' c x := by simp only [Ext.smul_comp,Ext.comp_smul,RingHom.id_apply]

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesInjectiveObjects] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : ModuleCat R} (P : InjectiveResolution X) (e : F.obj X ≅ X)

def coresolutionTwistHom (l : (mappedCoresolution F P).cocomplex ⟶ P.cocomplex) :
    coresolutionHom k R P.cocomplex X ⟶ coresolutionHom k R P.cocomplex X := by
  change (F.mapHomologicalComplex (.up ℕ)).obj P.cocomplex ⟶ P.cocomplex at l
  exact {
  f n := ModuleCat.ofHom
    (show (X ⟶ P.cocomplex.X n) →ₗ[k] (X ⟶ P.cocomplex.X n) from
    { toFun f := e.inv ≫ F.map f ≫ l.f n
      map_add' f g := by rw [F.map_add,Preadditive.add_comp,Preadditive.comp_add]
      map_smul' r f := by rw [F.map_smul,Linear.smul_comp,Linear.comp_smul]; rfl })
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change X ⟶ P.cocomplex.X i at f
    symm
    change e.inv ≫ F.map (f ≫ P.cocomplex.d i j) ≫ l.f j =
      e.inv ≫ F.map f ≫ l.f i ≫ P.cocomplex.d i j
    have hl := l.comm i j
    change l.f i ≫ P.cocomplex.d i j = F.map (P.cocomplex.d i j) ≫ l.f j at hl
    simp only [F.map_comp,Category.assoc]
    rw [hl] }

lemma coresolutionTwistHom_extMk
    (l : InjectiveResolution.Hom (mappedCoresolution F P) P e.hom)
    {n : ℕ} (f : X ⟶ P.cocomplex.X n) (hf : f ≫ P.cocomplex.d n (n+1) = 0) :
    extIso (k := k) e e n ((P.extMk f (n+1) rfl hf).mapExactFunctor F) =
      P.extMk ((coresolutionTwistHom (k := k) F P e l.hom).f n f) (n+1) rfl
        (by change (e.inv ≫ F.map f ≫ l.hom.f n) ≫ P.cocomplex.d n (n+1) = 0
            dsimp only [mappedCoresolution] at l ⊢
            rw [Category.assoc,Category.assoc,l.hom.comm]
            change e.inv ≫ F.map f ≫ F.map (P.cocomplex.d n (n+1)) ≫ l.hom.f (n+1) = 0
            rw [← F.map_comp_assoc,hf,F.map_zero,zero_comp,comp_zero]) := by
  let := HasDerivedCategory.standard (ModuleCat R)
  change (Ext.mk₀ e.inv).comp
    (((P.extMk f (n+1) rfl hf).mapExactFunctor F).comp (Ext.mk₀ e.hom) (add_zero n))
      (zero_add n) = _
  rw [mapExactFunctor_injective_extMk]
  have hcomp := InjectiveResolution.extMk_comp_mk₀ (R := mappedCoresolution F P)
    (show F.obj X ⟶ (mappedCoresolution F P).cocomplex.X n from F.map f)
    (n+1) rfl (by change F.map f ≫ F.map _ = 0; rw [← F.map_comp,hf,F.map_zero]) l
  erw [hcomp, P.mk₀_comp_extMk]
  rfl



lemma coresolutionTwist_diff_boundary
    (l : InjectiveResolution.Hom (mappedCoresolution F P) P e.hom) (n : ℕ) (r : k)
    (h : ∀ x : Ext X X (n+1), extIso (k := k) e e (n+1) (x.mapExactFunctor F) = r • x)
    (g : X ⟶ P.cocomplex.X (n+1)) (hg : g ≫ P.cocomplex.d (n+1) (n+2) = 0) :
    ∃ a : X ⟶ P.cocomplex.X n, a ≫ P.cocomplex.d n (n+1) =
      (show X ⟶ P.cocomplex.X (n+1) from
        (coresolutionTwistHom (k := k) F P e l.hom).f (n+1) g) - r • g := by
  let K := coresolutionHom k R P.cocomplex X
  let S := coresolutionTwistHom (k := k) F P e l.hom
  have hgS : S.f (n+1) g ≫ P.cocomplex.d (n+1) (n+2) = 0 := by
    have he := congrArg (fun f => f g) (S.comm (n+1) (n+2))
    change S.f (n+1) g ≫ P.cocomplex.d (n+1) (n+2) =
      S.f (n+2) (g ≫ P.cocomplex.d (n+1) (n+2)) at he
    rw [he,hg]
    exact (S.f (n+2)).hom.map_zero
  let z : VectorSplit.Z K (n+1) := ⟨g,(coresolutionHom_memZ _ _ _ _ _ _).mpr hg⟩
  let zS : VectorSplit.Z K (n+1) := ⟨S.f (n+1) g,(coresolutionHom_memZ _ _ _ _ _ _).mpr hgS⟩
  have he : coresolutionCyclesToExt X P (n+1) (zS-r•z) = 0 := by
    rw [map_sub,map_smul]
    have ha := coresolutionTwistHom_extMk (k := k) F P e l g hg
    change extIso (k := k) e e (n+1)
      ((coresolutionCyclesToExt X P (n+1) z).mapExactFunctor F) =
      coresolutionCyclesToExt X P (n+1) zS at ha
    rw [← ha,h,sub_self]
  have hz : ((show X ⟶ P.cocomplex.X (n+1) from S.f (n+1) g) - r • g) ≫
      P.cocomplex.d (n+1) (n+2) = 0 := by
    rw [Preadditive.sub_comp, Linear.smul_comp, hgS, hg, smul_zero, sub_self]
  exact (P.extMk_eq_zero_iff _ (n+2) rfl hz n rfl).mp he
end Tachikawa



namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (t : SymmetrizingForm (k := k) (R := R)) (σ : R ≃ₐ[k] R)
  (ι : Type) [Fintype ι] [DecidableEq ι] (N : ModuleCat R)

lemma freeHomDual_semilinear_adjoint
    (c : k) (hc : ∀ r, t.linear (σ r) = c * t.linear r)
    (l : ModuleCat.of R (ι → R) ⟶ (twistFunctor σ).obj (ModuleCat.of R (ι → R)))
    (e : (twistFunctor σ).obj N ⟶ N) (he : ∀ x, e x = x)
    (g g' : N →ₗ[R] (ι → R)) (hg : ∀ x, g' x = l (g x))
    (f : (ι → R) →ₗ[R] N) :
    t.freeHomDual ι g ((l ≫ (twistFunctor σ).map (ModuleCat.ofHom f) ≫ e).hom) =
      c * t.freeHomDual ι g' f := by
  let L := (l ≫ (freeTwistIso σ ι).hom).hom
  have h0 : (l ≫ (twistFunctor σ).map (ModuleCat.ofHom f) ≫ e).hom =
      e.hom.comp ((twistFromFree σ ι N f).comp L) := by
    apply LinearMap.ext
    intro x
    change e (f (l x)) = e (f (fun i => σ.symm (σ (l x i))))
    simp only [AlgEquiv.symm_apply_apply]
  rw [h0,← t.freeHomDual_natural]
  rw [t.freeHomDual_cyclic]
  have h1 : L.comp (g.comp e.hom) = twistToFree σ ι N g' := by
    ext x i
    change σ (l (g (e x)) i) = σ (g' x i)
    rw [he]
    exact congrArg σ (congrFun (hg (show N from x)) i).symm
  rw [h1,t.freeHomDual_twist σ ι N c hc]
end Tachikawa.SymmetrizingForm



namespace Tachikawa.SymmetrizingForm
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (t : SymmetrizingForm (k := k) (R := R))
  {ι κ τ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype τ] [DecidableEq τ]
  {N : Type} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

lemma free_boundary_iff_pair_cycles (d : (ι → R) →ₗ[R] (κ → R)) (f : (ι → R) →ₗ[R] N) :
    (∃ h : (κ → R) →ₗ[R] N, h.comp d = f) ↔
      ∀ g : N →ₗ[R] (ι → R), d.comp g = 0 → t.freeHomDual ι g f = 0 := by
  constructor
  · rintro ⟨h,rfl⟩ g hg
    rw [t.freeHomDual_cyclic_rect, hg, map_zero,LinearMap.zero_apply]
  · intro h
    change f ∈ LinearMap.range (homPrecompose (k := k) (N := N) d)
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ f).mp
    intro φ hφ
    obtain ⟨g,rfl⟩ := (t.freeHomDual ι (N := N)).surjective φ
    apply h
    apply (t.freeHomDual κ).injective
    ext a
    rw [map_zero,LinearMap.zero_apply,← t.freeHomDual_cyclic_rect]
    exact (Submodule.mem_dualAnnihilator _).mp hφ _ ⟨a,rfl⟩

lemma free_boundary_of_adjoint_scalar
    (d : (ι → R) →ₗ[R] (κ → R)) (b : (τ → R) →ₗ[R] (ι → R))
    (f f' : (ι → R) →ₗ[R] N) (hf : f.comp b = 0) (c r : k)
    (T : (N →ₗ[R] (ι → R)) → (N →ₗ[R] (ι → R)))
    (hpair : ∀ g, t.freeHomDual ι g f' = c * t.freeHomDual ι (T g) f)
    (hT : ∀ g, d.comp g = 0 →
      ∃ a : N →ₗ[R] (τ → R), b.comp a = T g - r • g) :
    ∃ a : (κ → R) →ₗ[R] N, a.comp d = f' - (c*r) • f := by
  apply (t.free_boundary_iff_pair_cycles d _).mpr
  intro g hg
  obtain ⟨a,ha⟩ := hT g hg
  have hb : t.freeHomDual ι (b.comp a) f = 0 := by
    rw [← t.freeHomDual_cyclic_rect,hf,map_zero]
  rw [ha,map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply] at hb
  have he : t.freeHomDual ι (T g) f = r * t.freeHomDual ι g f := sub_eq_zero.mp hb
  rw [map_sub,map_smul,hpair,he]
  change c * (r * _) - (c*r) * _ = 0
  ring
end Tachikawa.SymmetrizingForm



namespace Tachikawa.FiniteModule
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R)) (σ : R ≃ₐ[k] R)
  (e : (twistFunctor σ).obj M.obj ≅ M.obj) (he : ∀ x, e.hom x = x)
  (e' : (twistFunctor σ.symm).obj M.obj ≅ M.obj) (he' : ∀ x, e'.hom x = x)

include he he' in

lemma negativeTwist_diff_boundary
    (l : InjectiveResolution.Hom (M.coresolution t)
      (mappedCoresolution (twistFunctor σ) (M.coresolution t)) e.inv)
    (n : ℕ) (c r : k) (hc : ∀ a, t.linear (σ a) = c * t.linear a)
    (hr : ∀ x : Ext M.obj M.obj (n+1),
      extIso (k := k) e' e' (n+1) (x.mapExactFunctor (twistFunctor σ.symm)) = r • x)
    (f : M.negTerm t (n+1) →ₗ[R] M)
    (hf : f.comp (M.negDifferential t n) = 0) :
    ∃ a : M.negTerm t (n+2) →ₗ[R] M,
      a.comp (M.negDifferential t (n+1)) =
        (show M.negTerm t (n+1) →ₗ[R] M from
          (l.hom.f (n+1) ≫ (twistFunctor σ).map (ModuleCat.ofHom f) ≫ e.hom).hom) -
          (c*r) • f := by
  let li := inverseCoresolutionHom σ (M.coresolution t) e he e' he' l
  let S := coresolutionTwistHom (k := k) (twistFunctor σ.symm) (M.coresolution t) e' li.hom
  let T : (M →ₗ[R] M.negTerm t (n+1)) → (M →ₗ[R] M.negTerm t (n+1)) := fun g =>
    (show M.obj ⟶ ModuleCat.of R (M.negTerm t (n+1)) from S.f (n+1) (ModuleCat.ofHom g)).hom
  apply t.free_boundary_of_adjoint_scalar (M.negDifferential t (n+1))
    (M.negDifferential t n) f _ hf c r T
  · intro g
    apply t.freeHomDual_semilinear_adjoint σ _ M.obj c hc (l.hom.f (n+1)) e.hom he g (T g) _ f
    intro x
    change l.hom.f (n+1) (g (e'.inv x)) = l.hom.f (n+1) (g x)
    rw [twistIso_inv_apply σ.symm e' he']
  · intro g hg
    obtain ⟨a,ha⟩ := coresolutionTwist_diff_boundary (k := k) (twistFunctor σ.symm)
      (M.coresolution t) e' li n r hr (ModuleCat.ofHom g) (by
        rw [M.coresolution_d]
        exact ModuleCat.hom_ext hg)
    refine ⟨a.hom,?_⟩
    rw [M.coresolution_d] at ha
    apply LinearMap.ext
    intro x
    have h := congrArg (fun u => u x) ha
    change M.negDifferential t n (a x) = T g x -
      (algebraMap k R r) • g x at h
    rw [IsScalarTower.algebraMap_smul R r (g x)] at h
    exact h

end Tachikawa.FiniteModule

end

end OAI
