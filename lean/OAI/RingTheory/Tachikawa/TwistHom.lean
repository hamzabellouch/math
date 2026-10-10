import OAI.RingTheory.Tachikawa.Coresolution

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects] [F.PreservesHomology]
  {X : C} (P : ProjectiveResolution X)

abbrev mappedResolution := F.mapProjectiveResolution P

def mappedResolutionCochainXIso (j : ℤ) :
    (mappedResolution F P).cochainComplex.X j ≅ F.obj (P.cochainComplex.X j) := by
  by_cases h : j ≤ 0
  · let n := (-j).toNat
    have hn : -(n : ℤ) = j := by dsimp [n]; omega
    exact (mappedResolution F P).cochainComplexXIso j n hn ≪≫
      (F.mapIso (P.cochainComplexXIso j n hn)).symm
  · exact (CochainComplex.isZero_of_isStrictlyLE (mappedResolution F P).cochainComplex 0 j).isoZero ≪≫
      (F.map_isZero (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 j)).isoZero.symm

lemma mappedResolutionCochainXIso_nonpos (j : ℤ) (n : ℕ) (hn : -(n : ℤ) = j) :
    mappedResolutionCochainXIso F P j =
      (mappedResolution F P).cochainComplexXIso j n hn ≪≫
      (F.mapIso (P.cochainComplexXIso j n hn)).symm := by
  have hj : j ≤ 0 := by omega
  simp only [mappedResolutionCochainXIso,dite_eq_left hj]
  have : (-j).toNat = n := by omega
  subst n
  rfl

lemma mappedResolutionCochainXIso_comm (i j : ℤ) :
    (mappedResolution F P).cochainComplex.d i j ≫ (mappedResolutionCochainXIso F P j).hom =
      (mappedResolutionCochainXIso F P i).hom ≫ F.map (P.cochainComplex.d i j) := by
  by_cases hi : i ≤ 0
  · by_cases hj : j ≤ 0
    · obtain ⟨a,rfl⟩ := Int.exists_eq_neg_ofNat hi
      obtain ⟨b,rfl⟩ := Int.exists_eq_neg_ofNat hj
      rw [mappedResolutionCochainXIso_nonpos F P _ a rfl,
        mappedResolutionCochainXIso_nonpos F P _ b rfl,
        ProjectiveResolution.cochainComplex_d _ _ _ a b rfl rfl,
        ProjectiveResolution.cochainComplex_d _ _ _ a b rfl rfl]
      dsimp only [mappedResolution, Functor.mapProjectiveResolution,
        Functor.mapHomologicalComplex]
      simp only [Iso.trans_hom,Iso.symm_hom,Functor.mapIso_inv,Functor.map_comp,
        Category.assoc,Iso.inv_hom_id_assoc]
      rw [← F.map_comp_assoc,Iso.inv_hom_id,F.map_id,Category.id_comp]
    · exact (F.map_isZero (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 j)).eq_of_tgt _ _
  · exact (CochainComplex.isZero_of_isStrictlyLE (mappedResolution F P).cochainComplex 0 i).eq_of_src _ _

def mappedResolutionCochainIso : (mappedResolution F P).cochainComplex ≅
    (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (mappedResolutionCochainXIso F P)
    (fun i j _ => (mappedResolutionCochainXIso_comm F P i j).symm)

end Tachikawa

namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects] [F.PreservesHomology]
  {X : C} (P : ProjectiveResolution X)

lemma mappedResolutionCochainIso_π :
    (mappedResolutionCochainIso F P).hom ≫
      (F.mapHomologicalComplex (.up ℤ)).map P.π' ≫
        (F.mapCochainComplexSingleFunctor 0).hom.app X =
      (mappedResolution F P).π' := by
  ext j
  by_cases hj : j = 0
  · subst j
    dsimp only [mappedResolution, Functor.mapProjectiveResolution,
      Functor.mapHomologicalComplex]
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.Hom.isoOfComponents_hom_f, mappedResolutionCochainIso,
      mappedResolutionCochainXIso_nonpos F P 0 0 rfl,
      ProjectiveResolution.π'_f_zero, Functor.map_comp]
    simp [mappedResolution,
      Functor.mapCochainComplexSingleFunctor,
      singleMapHomologicalComplex]
    simp only [singleObjXSelf,singleObjXIsoOfEq,eqToIso.inv]
    erw [eqToHom_refl, Category.comp_id, eqToHom_refl, Category.comp_id]
    change (((mappedResolution F P).cochainComplexXIso 0 0 rfl).hom ≫
        F.map (P.cochainComplexXIso 0 0 rfl).inv) ≫
          F.map (P.cochainComplexXIso 0 0 rfl).hom ≫ F.map (P.π.f 0) =
      ((mappedResolution F P).cochainComplexXIso 0 0 rfl).hom ≫
        F.map (P.π.f 0) ≫ 𝟙 _ ≫ 𝟙 _
    erw [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id,
      Category.id_comp, Category.comp_id, Category.comp_id]
  · exact (isZero_single_obj_X (.up ℤ) 0 (F.obj X) j hj).eq_of_tgt _ _

omit [F.PreservesProjectiveObjects] [F.PreservesHomology] in
lemma map_toSingle_shifted {K : CochainComplex C ℤ} {Y : C}
    {p n : ℤ} (f : K.X p ⟶ Y) (h : p+n=0) (p' : ℤ) (hp' : p'+1=p)
    (hf : K.d p' p ≫ f = 0) :
    ShiftedHom.map (Cocycle.equivHomShift.symm (Cocycle.toSingleMk f h p' hp' hf))
      (F.mapHomologicalComplex (.up ℤ)) ≫
        ((F.mapCochainComplexSingleFunctor 0).hom.app Y)⟦n⟧' =
      Cocycle.equivHomShift.symm (Cocycle.toSingleMk (F.map f) h p' hp'
        (by simp only [Functor.mapHomologicalComplex_obj_d,← F.map_comp,hf,F.map_zero])) := by
  ext j
  simp [ShiftedHom.map,Cocycle.equivHomShift_symm_apply,
    Cocycle.toSingleMk,Cocycle.homOf,Cocycle.rightShift,
    Cochain.rightShift_v, Cochain.toSingleMk,
    Functor.mapCochainComplexSingleFunctor,singleMapHomologicalComplex]
  by_cases hj : j = p
  · subst j
    simp [Cochain.single,h,HomologicalComplex.XIsoOfEq,
      singleObjXSelf,singleObjXIsoOfEq,eqToHom_map]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hj]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} (P : ProjectiveResolution X)

lemma extMk_hom_roof [HasDerivedCategory C] [HasExt C]
    {n : ℕ} (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n+1) n ≫ f = 0) :
    (P.extMk f (n+1) rfl hf).hom = inv (DerivedCategory.Q.map P.π') ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.toSingleMk ((P.cochainComplexXIso (-n) n rfl).hom ≫ f)
          (by simp) (-((n+1 : ℕ) : ℤ)) (by omega)
          (by
            rw [ProjectiveResolution.cochainComplex_d _ _ _ (n+1) n rfl rfl]
            simp only [Category.assoc,Iso.inv_hom_id_assoc,hf,comp_zero])))
        DerivedCategory.Q := by
  rw [ProjectiveResolution.extMk_hom]
  simp [DerivedCategory.singleFunctorIsoCompQ,ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀]
  change _ ≫ (CategoryTheory.shiftFunctor (DerivedCategory C) (n : ℤ)).map
    (𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj Y))) = _
  rw [CategoryTheory.Functor.map_id,Category.comp_id]

lemma mappedResolutionCochain_cocycle {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f = 0) :
    (mappedResolutionCochainIso F P).hom ≫
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.toSingleMk ((P.cochainComplexXIso (-n) n rfl).hom ≫ f)
          (by simp) (-((n+1 : ℕ) : ℤ)) (by omega)
          (by
            rw [ProjectiveResolution.cochainComplex_d _ _ _ (n+1) n rfl rfl]
            simp only [Category.assoc,Iso.inv_hom_id_assoc,hf,comp_zero])))
        (F.mapHomologicalComplex (.up ℤ)) ≫
      ((F.mapCochainComplexSingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' =
    Cocycle.equivHomShift.symm (Cocycle.toSingleMk
      (((mappedResolution F P).cochainComplexXIso (-n) n rfl).hom ≫ F.map f)
      (by simp) (-((n+1 : ℕ) : ℤ)) (by omega) (by
        rw [ProjectiveResolution.cochainComplex_d _ _ _ (n+1) n rfl rfl]
        dsimp only [mappedResolution, Functor.mapProjectiveResolution,
          Functor.mapHomologicalComplex]
        simp only [Category.assoc,Iso.inv_hom_id_assoc]
        change _ ≫ F.map (P.complex.d (n+1) n) ≫ F.map f = 0
        rw [← F.map_comp,hf,F.map_zero,comp_zero])) := by
  rw [map_toSingle_shifted]
  rw [← Cocycle.equivHomShift_symm_precomp,← Cocycle.toSingleMk_precomp]
  congr 2
  change (mappedResolutionCochainXIso F P (-n)).hom ≫
    F.map ((P.cochainComplexXIso (-n) n rfl).hom ≫ f) = _
  rw [mappedResolutionCochainXIso_nonpos F P (-n) n rfl]
  dsimp only [mappedResolution, Functor.mapProjectiveResolution,
    Functor.mapHomologicalComplex]
  simp [← F.map_comp_assoc]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasExt C] [HasExt D]
  {X Y : C} (P : ProjectiveResolution X)

lemma mapExactFunctor_extMk {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f = 0) :
    (P.extMk f (n+1) rfl hf).mapExactFunctor F =
      (mappedResolution F P).extMk (F.map f) (n+1) rfl
        (by change F.map _ ≫ F.map _ = 0; rw [← F.map_comp,hf,F.map_zero]) := by
  apply Ext.ext
  rw [Ext.mapExactFunctor_hom,extMk_hom_roof,derived_roof_map]
  conv_rhs => erw [extMk_hom_roof (mappedResolution F P)]
  have hπ := mappedResolutionCochainIso_π F P
  have hc := mappedResolutionCochain_cocycle F P f hf
  have hq := congrArg (fun z => DerivedCategory.Q.map z) hπ
  simp only [Functor.map_comp] at hq
  have hr : inv (DerivedCategory.Q.map (mappedResolution F P).π') ≫
      DerivedCategory.Q.map (mappedResolutionCochainIso F P).hom =
      inv (DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map P.π' ≫
          (F.mapCochainComplexSingleFunctor 0).hom.app X)) := by
    apply (cancel_mono (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map P.π' ≫
        (F.mapCochainComplexSingleFunctor 0).hom.app X))).1
    simp only [Functor.map_comp,Category.assoc,IsIso.inv_hom_id]
    rw [hq,IsIso.inv_hom_id]
  dsimp only [mappedResolution] at hc ⊢
  rw [← hc]
  simp only [shifted_map_precomp]
  rw [← Category.assoc (inv (DerivedCategory.Q.map (mappedResolution F P).π')),hr]
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesProjectiveObjects] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : ModuleCat R} (P : ProjectiveResolution X) (e : F.obj X ≅ X)

def resolutionTwistHom (l : P.complex ⟶ (mappedResolution F P).complex) :
    resolutionHom k R P.complex X ⟶ resolutionHom k R P.complex X := by
  change P.complex ⟶ (F.mapHomologicalComplex (.down ℕ)).obj P.complex at l
  exact {
  f n := ModuleCat.ofHom
    (show (P.complex.X n ⟶ X) →ₗ[k] (P.complex.X n ⟶ X) from
    { toFun f := l.f n ≫ F.map f ≫ e.hom
      map_add' f g := by rw [F.map_add,Preadditive.add_comp,Preadditive.comp_add]
      map_smul' r f := by rw [F.map_smul,Linear.smul_comp,Linear.comp_smul]; rfl })
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change P.complex.X i ⟶ X at f
    symm
    change l.f j ≫ F.map (P.complex.d j i ≫ f) ≫ e.hom =
      P.complex.d j i ≫ l.f i ≫ F.map f ≫ e.hom
    have hl := l.comm j i
    change l.f j ≫ F.map (P.complex.d j i) = P.complex.d j i ≫ l.f i at hl
    simp only [F.map_comp,← Category.assoc]
    rw [hl] }

lemma resolutionTwistHom_extMk
    (l : ProjectiveResolution.Hom P (mappedResolution F P) e.inv)
    {n : ℕ} (f : P.complex.X n ⟶ X) (hf : P.complex.d (n+1) n ≫ f = 0) :
    extIso (k := k) e e n ((P.extMk f (n+1) rfl hf).mapExactFunctor F) =
      P.extMk ((resolutionTwistHom (k := k) F P e l.hom).f n f) (n+1) rfl
        (by change P.complex.d (n+1) n ≫ l.hom.f n ≫ F.map f ≫ e.hom = 0
            erw [← l.hom.comm_assoc]
            change l.hom.f (n+1) ≫ F.map (P.complex.d (n+1) n) ≫ F.map f ≫ e.hom = 0
            erw [← F.map_comp_assoc,hf,F.map_zero,zero_comp,comp_zero]) := by
  let := HasDerivedCategory.standard (ModuleCat R)
  change (Ext.mk₀ e.inv).comp
    (((P.extMk f (n+1) rfl hf).mapExactFunctor F).comp (Ext.mk₀ e.hom) (add_zero n))
      (zero_add n) = _
  erw [mapExactFunctor_extMk,(mappedResolution F P).extMk_comp_mk₀,
    ProjectiveResolution.mk₀_comp_extMk _ _ _ _ l]
  rfl

end Tachikawa



namespace Tachikawa.FiniteModule
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))

@[simp] lemma projectiveResolution_d (n : ℕ) :
    M.projectiveResolution.complex.d (n+1) n = ModuleCat.ofHom (M.posDifferential n) := by
  dsimp only [projectiveResolution,resolutionOfExact]
  exact ChainComplex.of_d _ _ n
@[simp] lemma projectiveResolution_π : M.projectiveResolution.π.f 0 = ModuleCat.ofHom M.cover.map := rfl

variable (σ : R ≃ₐ[k] R) (e : (twistFunctor σ).obj M.obj ≅ M.obj)

def positiveTwistLift : ProjectiveResolution.Hom M.projectiveResolution
    (mappedResolution (twistFunctor σ) M.projectiveResolution) e.inv where
  hom := ProjectiveResolution.lift e.inv _ _
  hom_f_zero_comp_π_f_zero := ProjectiveResolution.lift_commutes_zero _ _ _

def negativeTwistLift : InjectiveResolution.Hom (M.coresolution t)
    (mappedCoresolution (twistFunctor σ) (M.coresolution t)) e.inv where
  hom := InjectiveResolution.desc e.inv _ _
  ι_f_zero_comp_hom_f_zero := InjectiveResolution.desc_commutes_zero _ _ _

def completeTwistComponent : ∀ j : ℤ, (M.complete t).X j ⟶
    (twistFunctor σ).obj ((M.complete t).X j)
  | .ofNat n => (M.positiveTwistLift σ e).hom.f n
  | .negSucc n => (M.negativeTwistLift t σ e).hom.f n

lemma completeTwistComponent_comm (j : ℤ) :
    M.completeTwistComponent t σ e (j+1) ≫ (twistFunctor σ).map (M.differential t j) =
      M.differential t j ≫ M.completeTwistComponent t σ e j := by
  cases j with
  | ofNat n =>
    have h := (M.positiveTwistLift σ e).hom.comm (n+1) n
    rw [M.projectiveResolution_d] at h
    change _ ≫ (twistFunctor σ).map (M.projectiveResolution.complex.d (n+1) n) = _ at h
    rw [M.projectiveResolution_d] at h
    exact h
  | negSucc n =>
    cases n with
    | zero =>
      have hp := (M.positiveTwistLift σ e).hom_f_zero_comp_π_f_zero
      have hi := (M.negativeTwistLift t σ e).ι_f_zero_comp_hom_f_zero
      change (M.positiveTwistLift σ e).hom.f 0 ≫ (twistFunctor σ).map (M.projectiveResolution.π.f 0) =
        M.projectiveResolution.π.f 0 ≫ e.inv at hp
      rw [M.projectiveResolution_π] at hp
      rw [mappedCoresolution_ι_zero,M.coresolution_ι] at hi
      change ModuleCat.ofHom (M.embed t) ≫ (M.negativeTwistLift t σ e).hom.f 0 =
        e.inv ≫ (twistFunctor σ).map (ModuleCat.ofHom (M.embed t)) at hi
      change (M.positiveTwistLift σ e).hom.f 0 ≫
        (twistFunctor σ).map (ModuleCat.ofHom M.cover.map ≫ ModuleCat.ofHom (M.embed t)) =
        (ModuleCat.ofHom M.cover.map ≫ ModuleCat.ofHom (M.embed t)) ≫
          (M.negativeTwistLift t σ e).hom.f 0
      erw [Functor.map_comp,← Category.assoc,hp,Category.assoc,← hi,Category.assoc]
      rfl
    | succ n =>
      have h := (M.negativeTwistLift t σ e).hom.comm n (n+1)
      rw [M.coresolution_d] at h
      change _ ≫ (twistFunctor σ).map ((M.coresolution t).cocomplex.d n (n+1)) = _ at h
      rw [M.coresolution_d] at h
      exact h

def completeTwistLift : M.complete t ⟶
    ((twistFunctor σ).mapHomologicalComplex (.down ℤ)).obj (M.complete t) where
  f := M.completeTwistComponent t σ e
  comm' i j hij := by
    have hi : i=j+1 := by change j+1=i at hij; omega
    subst i
    change _ ≫ (twistFunctor σ).map ((M.complete t).d (j+1) j) = _
    rw [M.complete_d]
    exact M.completeTwistComponent_comm t σ e j

end Tachikawa.FiniteModule



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesProjectiveObjects] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  {X : ModuleCat R} (P : ProjectiveResolution X) (e : F.obj X ≅ X)

lemma resolutionTwist_diff_boundary
    (l : ProjectiveResolution.Hom P (mappedResolution F P) e.inv) (n : ℕ) (r : k)
    (h : ∀ x : Ext X X (n+1), extIso (k := k) e e (n+1) (x.mapExactFunctor F) = r • x)
    (g : P.complex.X (n+1) ⟶ X) (hg : P.complex.d (n+2) (n+1) ≫ g = 0) :
    ∃ a : P.complex.X n ⟶ X, P.complex.d (n+1) n ≫ a =
      (show P.complex.X (n+1) ⟶ X from
        (resolutionTwistHom (k := k) F P e l.hom).f (n+1) g) - r • g := by
  let K := resolutionHom k R P.complex X
  let S := resolutionTwistHom (k := k) F P e l.hom
  have hgS : P.complex.d (n+2) (n+1) ≫ (S.f (n+1) g) = 0 := by
    have he := congrArg (fun f => f g) (S.comm (n+1) (n+2))
    change P.complex.d (n+2) (n+1) ≫ S.f (n+1) g =
      S.f (n+2) (P.complex.d (n+2) (n+1) ≫ g) at he
    exact he.trans ((congrArg (fun morphism : P.complex.X (n+2) ⟶ X =>
      S.f (n+2) morphism) hg).trans (map_zero (S.f (n+2)).hom))
  let z : VectorSplit.Z K (n+1) := ⟨g,(resolutionHom_memZ _ _ _ _ _ _).mpr hg⟩
  let zS : VectorSplit.Z K (n+1) := ⟨S.f (n+1) g,(resolutionHom_memZ _ _ _ _ _ _).mpr hgS⟩
  have he : resolutionCyclesToExt X P (n+1) (zS-r•z) = 0 := by
    rw [map_sub,map_smul]
    have ha := resolutionTwistHom_extMk (k := k) F P e l g hg
    change extIso (k := k) e e (n+1)
      ((resolutionCyclesToExt X P (n+1) z).mapExactFunctor F) =
      resolutionCyclesToExt X P (n+1) zS at ha
    rw [← ha,h,sub_self]
  have hz : P.complex.d (n+2) (n+1) ≫
      ((show P.complex.X (n+1) ⟶ X from S.f (n+1) g) - r • g) = 0 := by
    rw [Preadditive.comp_sub,Linear.comp_smul,hgS,hg,smul_zero,sub_self]
  exact (P.extMk_eq_zero_iff _ (n+2) rfl hz n rfl).mp he
end Tachikawa



namespace Tachikawa.FiniteModule
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R)) (σ : R ≃ₐ[k] R)
  (e : (twistFunctor σ).obj M.obj ≅ M.obj)

def completeTwistHom : completeHom (k := k) (M.complete t) M.obj ⟶
    completeHom (k := k) (M.complete t) M.obj :=
  completeFunctorHom (k := k) (twistFunctor σ) (M.complete t) (M.complete t) M.obj
    (M.completeTwistLift t σ e) ≫ completeHomMap (M.complete t) e.hom

lemma completeTwistHom_positive (n : ℕ) (r : k)
    (hr : ∀ x : Ext M.obj M.obj (n+1),
      extIso (k := k) e e (n+1) (x.mapExactFunctor (twistFunctor σ)) = r • x)
    (x : VectorSplit.H (completeHom (k := k) (M.complete t) M.obj) ((n+1:ℕ):ℤ)) :
    VectorSplit.Hmap (M.completeTwistHom t σ e) _ x = r • x := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective _ x
  rw [VectorSplit.Hmap_quotient,← map_smul]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (VectorSplit.quotient_zero_iff_predecessor _ _).mpr
  have hz := (completeHom_memZ (M.complete t) M.obj ((n+1:ℕ):ℤ) z.val).mp z.property
  have hz' : M.projectiveResolution.complex.d (n+2) (n+1) ≫ z.val = 0 := by
    rw [M.projectiveResolution_d]
    rw [M.complete_d] at hz
    exact hz
  obtain ⟨a,ha⟩ := resolutionTwist_diff_boundary (k := k) (twistFunctor σ)
    M.projectiveResolution e (M.positiveTwistLift σ e) n r hr z.val hz'
  rw [M.projectiveResolution_d] at ha
  rw [show ((n+1:ℕ):ℤ)-1 = (n:ℤ) by omega]
  refine ⟨a,?_⟩
  change (M.complete t).d ((n:ℤ)+1) (n:ℤ) ≫ a = _
  rw [M.complete_d]
  exact ha

lemma completeTwistHom_negative (he : ∀ x, e.hom x = x)
    (e' : (twistFunctor σ.symm).obj M.obj ≅ M.obj) (he' : ∀ x, e'.hom x = x)
    (n : ℕ) (c r : k) (hc : ∀ a, t.linear (σ a) = c * t.linear a)
    (hr : ∀ x : Ext M.obj M.obj (n+1),
      extIso (k := k) e' e' (n+1) (x.mapExactFunctor (twistFunctor σ.symm)) = r • x)
    (x : VectorSplit.H (completeHom (k := k) (M.complete t) M.obj) (Int.negSucc (n+1))) :
    VectorSplit.Hmap (M.completeTwistHom t σ e) _ x = (c*r) • x := by
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective _ x
  rw [VectorSplit.Hmap_quotient,← map_smul]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (VectorSplit.quotient_zero_iff_predecessor _ _).mpr
  have hz := (completeHom_memZ (M.complete t) M.obj (Int.negSucc (n+1)) z.val).mp z.property
  have hz' : z.val.hom.comp (M.negDifferential t n) = 0 := by
    rw [M.complete_d] at hz
    exact ModuleCat.hom_ext_iff.mp hz
  obtain ⟨a,ha⟩ := M.negativeTwist_diff_boundary t σ e he e' he'
    (M.negativeTwistLift t σ e) n c r hc hr z.val.hom hz'
  rw [show Int.negSucc (n+1)-1 = Int.negSucc (n+2) by omega]
  refine ⟨ModuleCat.ofHom a,?_⟩
  change (M.complete t).d (Int.negSucc (n+2)+1) (Int.negSucc (n+2)) ≫ ModuleCat.ofHom a = _
  rw [M.complete_d]
  apply ModuleCat.hom_ext
  exact ha

end Tachikawa.FiniteModule



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (N : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))
  (σ : R ≃ₐ[k] R) (e : (twistFunctor σ).obj N.obj ≅ N.obj)

def tensorTwistLift : N.complete t ⟶ tensorComplex (twistedRegular σ) (N.complete t) :=
  N.completeTwistLift t σ e ≫
    ((twistedTensorNatIso σ).inv.mapHomologicalComplex (.down ℤ)).app (N.complete t)

lemma tensorTwistLift_aug : (tensorTwistLift N t σ e).f 0 ≫
    (tensorFunctor (twistedRegular σ)).map (ModuleCat.ofHom N.cover.map) =
      ModuleCat.ofHom N.cover.map ≫ e.inv ≫ (twistedTensorIso σ N.obj).inv := by
  have hc := (N.positiveTwistLift σ e).hom_f_zero_comp_π_f_zero
  change (N.positiveTwistLift σ e).hom.f 0 ≫ (twistFunctor σ).map
    (ModuleCat.ofHom N.cover.map) = ModuleCat.ofHom N.cover.map ≫ e.inv at hc
  change ((N.positiveTwistLift σ e).hom.f 0 ≫ (twistedTensorNatIso σ).inv.app _) ≫ _ = _
  have hn := (twistedTensorNatIso σ).inv.naturality
    (show N.projectiveResolution.complex.X 0 ⟶ N.obj from ModuleCat.ofHom N.cover.map)
  change (twistFunctor σ).map (ModuleCat.ofHom N.cover.map) ≫ (twistedTensorIso σ N.obj).inv =
    (twistedTensorNatIso σ).inv.app (N.projectiveResolution.complex.X 0) ≫
      (tensorFunctor (twistedRegular σ)).map (ModuleCat.ofHom N.cover.map) at hn
  erw [Category.assoc,← hn,← Category.assoc,hc,Category.assoc]

lemma tensorTwistLift_action :
    completeFunctorHom (k := k) (tensorFunctor (twistedRegular σ))
        (N.complete t) (N.complete t) N.obj (tensorTwistLift N t σ e) ≫
      completeHomMap (N.complete t) ((twistedTensorIso σ N.obj).hom ≫ e.hom) =
      N.completeTwistHom t σ e := by
  have hn := completeFunctorHom_natural (k := k) (twistFunctor σ)
    (tensorFunctor (twistedRegular σ)) (N.complete t) (N.complete t) N.obj
    (N.completeTwistLift t σ e) (twistedTensorNatIso σ).inv
  change completeFunctorHom (k := k) (twistFunctor σ) (N.complete t) (N.complete t) N.obj
    (N.completeTwistLift t σ e) ≫ completeHomMap _ (twistedTensorIso σ N.obj).inv =
    completeFunctorHom (tensorFunctor (twistedRegular σ)) (N.complete t) (N.complete t) N.obj
      (tensorTwistLift N t σ e) at hn
  rw [← hn,Category.assoc,← completeHomMap_comp,(twistedTensorIso σ N.obj).inv_hom_id_assoc]
  rfl

variable {M : ModuleCat (Alg k R R)} (v : N.obj ⟶ (tensorFunctor M).obj N.obj)
  (l : N.complete t ⟶ tensorComplex M (N.complete t))
  (hl : l.f 0 ≫ (tensorFunctor M).map (ModuleCat.ofHom N.cover.map) = ModuleCat.ofHom N.cover.map ≫ v)
  (p : M ⟶ twistedRegular σ)
  (hv : v ≫ evalMap N.obj p = e.inv ≫ (twistedTensorIso σ N.obj).inv)

include hl hv in
lemma tensor_projected_action (a : ℤ) :
    VectorSplit.Hmap
      (completeFunctorHom (k := k) (tensorFunctor M) (N.complete t) (N.complete t) N.obj l ≫
        completeHomMap (N.complete t) (evalMap N.obj p ≫ (twistedTensorIso σ N.obj).hom ≫ e.hom)) a =
      VectorSplit.Hmap (N.completeTwistHom t σ e) a := by
  let lp := l ≫ ((tensorNatTrans p).mapHomologicalComplex (.down ℤ)).app (N.complete t)
  have hpaug : lp.f 0 ≫ (tensorFunctor (twistedRegular σ)).map (ModuleCat.ofHom N.cover.map) =
      (tensorTwistLift N t σ e).f 0 ≫ (tensorFunctor (twistedRegular σ)).map (ModuleCat.ofHom N.cover.map) := by
    change (l.f 0 ≫ (tensorNatTrans p).app _) ≫ _ = _
    erw [Category.assoc,← (tensorNatTrans p).naturality,← Category.assoc,hl, Category.assoc]
    change ModuleCat.ofHom N.cover.map ≫ (v ≫ evalMap N.obj p) = _
    rw [hv,tensorTwistLift_aug]
    rfl
  obtain ⟨h⟩ := complete_homotopy_of_augmentation (k := k) (N.complete_totallyAcyclic t)
    (tensorComplex_exact (twistedRegular σ) _ (N.complete_exact t)) (N.complete_projective t)
    (tensorComplex_finite (twistedRegular σ) _ (N.complete_finite t))
    (tensorComplex_projective (twistedRegular σ) _ (N.complete_finite t) (N.complete_projective t))
    ((tensorFunctor (twistedRegular σ)).map (ModuleCat.ofHom N.cover.map)).hom
    (tensor_augmentation_exact (twistedRegular σ) N t)
    (tensor_map_surjective (twistedRegular σ) (X := (N.complete t).X 0) (Y := N.obj)
      (ModuleCat.ofHom N.cover.map) N.cover.surjective) lp (tensorTwistLift N t σ e)
    (ModuleCat.hom_ext_iff.mp hpaug)
  have hn := completeFunctorHom_natural (k := k) (tensorFunctor M)
    (tensorFunctor (twistedRegular σ)) (N.complete t) (N.complete t) N.obj l (tensorNatTrans p)
  change completeFunctorHom (k := k) (tensorFunctor M) (N.complete t) (N.complete t) N.obj l ≫
    completeHomMap _ (evalMap N.obj p) =
    completeFunctorHom (tensorFunctor (twistedRegular σ)) (N.complete t) (N.complete t) N.obj lp at hn
  erw [completeHomMap_comp,← Category.assoc,hn]
  have he := congrArg (fun morphism =>
    (VectorSplit.Hmap (completeHomMap (N.complete t)
      ((twistedTensorIso σ N.obj).hom ≫ e.hom)) a).comp morphism)
    (completeFunctorHom_homotopic (k := k) _ _ _ _ _ h a)
  exact (VectorSplit.Hmap_comp _ _ a).trans (he.trans
    ((VectorSplit.Hmap_comp _ _ a).symm.trans
      (congrArg (fun morphism => VectorSplit.Hmap morphism a)
        (tensorTwistLift_action N t σ e))))

end Tachikawa.Enveloping

end

end OAI
