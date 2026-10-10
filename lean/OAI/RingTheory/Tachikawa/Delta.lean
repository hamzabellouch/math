import OAI.RingTheory.Tachikawa.HomProfile

namespace OAI


noncomputable section
namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R)

instance : (evaluation (S := S) (k := k) X).Linear k where
  map_smul {M N} f c := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (k := k) (R := R) (S := S) (N := X)
      (leftMap (c • f) m) x = c • BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := X) (leftMap f m) x
    change BalancedTensor.mk (k := k) (R := R) (S := S) (N := X)
      (c • leftMap f m) x = _
    exact congrArg (fun h : X →ₗ[k] evalType X N => h x)
      ((BalancedTensor.mk (k := k) (R := R) (S := S) (M := Obj N) (N := X)).map_smul_of_tower c
        (leftMap f m))

@[simp] lemma evalMap_smul {M N : ModuleCat (Alg k S R)} (c : k) (f : M ⟶ N) :
    evalMap X (c • f) = c • evalMap X f :=
  (evaluation X).map_smul c f

end Tachikawa.Enveloping



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def WZeroEquiv : MissingYProfile.W q 0 ≃ₗ[k] k :=
  Classical.choice ((y_profile q hq hp 0).1 (Or.inr rfl))

def wZero : MissingYProfile.W q 0 := (WZeroEquiv q hq hp).symm 1

lemma wZero_ne_zero : wZero q hq hp ≠ 0 := by
  intro h
  have := congrArg (WZeroEquiv q hq hp) h
  simp [wZero] at this

variable (H : k) (hH : H ≠ 0)

def evaluatedStableMap : ((finiteU q H hH).obj ⟶ (Y q).obj) →ₗ[k]
    MissingYProfile.W q 0 where
  toFun g := stableClass (k := k) (((uXIso q H hH).inv ≫
    Enveloping.evalMap (xObj q) g).hom)
  map_add' g h := by
    change stableClass (k := k) _ = _
    rw [show Enveloping.evalMap (xObj q) (g+h) =
      Enveloping.evalMap (xObj q) g + Enveloping.evalMap (xObj q) h from
      (Enveloping.evaluation (xObj q)).map_add,Preadditive.comp_add]
    exact map_add _ _ _
  map_smul' c g := by
    rw [Enveloping.evalMap_smul,Linear.comp_smul]
    exact map_smul _ _ _

lemma exists_normalized_map : ∃ g : (finiteU q H hH).obj ⟶ (Y q).obj,
    evaluatedStableMap q H hH g = wZero q hq hp := by
  obtain ⟨g,hg⟩ := exists_nonzero_X_YX q H hH hq
  have hn : evaluatedStableMap q H hH g ≠ 0 := by
    exact fun h => hg ((stableClass_eq_zero_iff _).mp h)
  have hc : WZeroEquiv q hq hp (evaluatedStableMap q H hH g) ≠ 0 := by
    intro h
    exact hn ((WZeroEquiv q hq hp).injective (h.trans (map_zero _).symm))
  refine ⟨(WZeroEquiv q hq hp (evaluatedStableMap q H hH g))⁻¹ • g,?_⟩
  apply (WZeroEquiv q hq hp).injective
  rw [map_smul,map_smul]
  simp [wZero,smul_eq_mul,inv_mul_cancel₀ hc]

def normalizedMap : (finiteU q H hH).obj ⟶ (Y q).obj :=
  Classical.choose (exists_normalized_map q hq hp H hH)

lemma normalizedMap_class : evaluatedStableMap q H hH (normalizedMap q hq hp H hH) =
    wZero q hq hp := Classical.choose_spec (exists_normalized_map q hq hp H hH)

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra

lemma projective_kernel_of_surjective {R M P N : Type} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module.Projective R P] [Module.Projective R N]
    (i : M →ₗ[R] P) (q : P →ₗ[R] N)
    (hi : Function.Injective i) (hq : Function.Surjective q) (he : Function.Exact i q) :
    Module.Projective R M := by
  let h := linearShortExact i q he hi hq
  have : CategoryTheory.Projective (linearShortComplex i q he).X₃ :=
    show CategoryTheory.Projective (ModuleCat.of R N) from inferInstance
  have : Module.Projective R (linearShortComplex i q he).X₂ :=
    show Module.Projective R P from inferInstance
  let s := h.splittingOfProjective
  exact Module.Projective.of_split i s.r.hom (ModuleCat.hom_ext_iff.mp s.f_r)

namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

def leftProdEquiv (M N : ModuleCat (Alg k R S)) :
    Obj (ModuleCat.of (Alg k R S) (M × N)) ≃ₗ[R] (Obj M × Obj N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rightProdEquiv (M N : ModuleCat (Alg k R S)) :
    Obj (ModuleCat.of (Alg k R S) (M × N)) ≃ₗ[Sᵐᵒᵖ] (Obj M × Obj N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (U V Y : FiniteModule k (Alg k R S)) (g : U.obj ⟶ Y.obj) (h : V.obj ⟶ Y.obj)

def fiberCover : ModuleCat (Alg k R S) := ModuleCat.of (Alg k R S) (Fin Y.cover.rank → Alg k R S)
def fiberMiddle : ModuleCat (Alg k R S) :=
  ModuleCat.of (Alg k R S) (U.obj × (V.obj × fiberCover Y))

def fiberProjection : fiberMiddle U V Y ⟶ Y.obj :=
  ModuleCat.ofHom (g.hom.coprod (h.hom.coprod Y.cover.map))

omit [FiniteDimensional k R] [FiniteDimensional k S] in
lemma fiberProjection_surjective : Function.Surjective (fiberProjection U V Y g h) := by
  intro y
  obtain ⟨z,hz⟩ := Y.cover.surjective y
  refine ⟨(0,(0,z)),?_⟩
  change g 0 + (h 0 + Y.cover.map z) = y
  rw [map_zero,map_zero,zero_add,zero_add,hz]

def fiber : FiniteModule k (Alg k R S) where
  obj := ModuleCat.of (Alg k R S) (LinearMap.ker (fiberProjection U V Y g h).hom)
  finite := by
    let : IsNoetherianRing (Alg k R S) := IsNoetherianRing.of_finite k (Alg k R S)
    let : Module.Finite (Alg k R S) (fiberMiddle U V Y) := by
      change Module.Finite (Alg k R S) (U.obj × (V.obj × (Fin Y.cover.rank → Alg k R S)))
      infer_instance
    exact Module.Finite.of_injective (LinearMap.ker (fiberProjection U V Y g h).hom).subtype
      Subtype.val_injective

def fiberInclusion : (fiber U V Y g h).obj ⟶ fiberMiddle U V Y :=
  ModuleCat.ofHom (LinearMap.ker (fiberProjection U V Y g h).hom).subtype

lemma fiberInclusion_injective : Function.Injective (fiberInclusion U V Y g h) :=
  Subtype.val_injective

lemma fiber_exact : Function.Exact (fiberInclusion U V Y g h) (fiberProjection U V Y g h) := by
  intro x
  exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩

lemma fiber_left_projective [Module.Projective R (Obj U.obj)]
    [Module.Projective R (Obj V.obj)] [Module.Projective R (Obj Y.obj)] :
    Module.Projective R (Obj (fiber U V Y g h).obj) := by
  let : Module.Projective R (Obj (fiberCover Y)) := freeLeftProjective _
  let : Module.Projective R (Obj (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))) :=
    Module.Projective.of_equiv (leftProdEquiv V.obj (fiberCover Y)).symm
  let : Module.Projective R (Obj (fiberMiddle U V Y)) :=
    Module.Projective.of_equiv (leftProdEquiv U.obj
      (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))).symm
  exact projective_kernel_of_surjective (leftMap (fiberInclusion U V Y g h))
    (leftMap (fiberProjection U V Y g h)) (fiberInclusion_injective U V Y g h)
    (fiberProjection_surjective U V Y g h) (fiber_exact U V Y g h)

lemma fiber_right_projective [Module.Projective Sᵐᵒᵖ (Obj U.obj)]
    [Module.Projective Sᵐᵒᵖ (Obj V.obj)] [Module.Projective Sᵐᵒᵖ (Obj Y.obj)] :
    Module.Projective Sᵐᵒᵖ (Obj (fiber U V Y g h).obj) := by
  let : Module.Projective Sᵐᵒᵖ (Obj (fiberCover Y)) := freeRightProjective _
  let : Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))) :=
    Module.Projective.of_equiv (rightProdEquiv V.obj (fiberCover Y)).symm
  let : Module.Projective Sᵐᵒᵖ (Obj (fiberMiddle U V Y)) :=
    Module.Projective.of_equiv (rightProdEquiv U.obj
      (ModuleCat.of (Alg k R S) (V.obj × fiberCover Y))).symm
  exact projective_kernel_of_surjective (rightMap (fiberInclusion U V Y g h))
    (rightMap (fiberProjection U V Y g h)) (fiberInclusion_injective U V Y g h)
    (fiberProjection_surjective U V Y g h) (fiber_exact U V Y g h)

end Enveloping
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

def concreteF : FiniteModule k (Enveloping.Alg k (E q) (E q)) :=
  Enveloping.fiber (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)
    (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)

lemma concreteF_side_projective :
    Module.Projective (E q) (Enveloping.Obj (concreteF q hq hp H₁ H₂ h₁ h₂).obj) ∧
    Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (concreteF q hq hp H₁ H₂ h₁ h₂).obj) := by
  let : Module.Projective (E q) (Enveloping.Obj (finiteU q H₁ h₁).obj) := by
    exact inferInstanceAs (Module.Projective (E q)
      (Enveloping.Obj (Enveloping.twistedRegular (sigma q H₁ h₁))))
  let : Module.Projective (E q) (Enveloping.Obj (finiteU q H₂ h₂).obj) := by
    exact inferInstanceAs (Module.Projective (E q)
      (Enveloping.Obj (Enveloping.twistedRegular (sigma q H₂ h₂))))
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (finiteU q H₁ h₁).obj) := by
    exact inferInstanceAs (Module.Projective (E q)ᵐᵒᵖ
      (Enveloping.Obj (Enveloping.twistedRegular (sigma q H₁ h₁))))
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (finiteU q H₂ h₂).obj) := by
    exact inferInstanceAs (Module.Projective (E q)ᵐᵒᵖ
      (Enveloping.Obj (Enveloping.twistedRegular (sigma q H₂ h₂))))
  let := (Y_side_projective q hq).1
  let := (Y_side_projective q hq).2
  constructor
  · exact Enveloping.fiber_left_projective _ _ _ _ _
  · exact Enveloping.fiber_right_projective _ _ _ _ _

abbrev concreteMiddle := Enveloping.fiberMiddle (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)
abbrev concreteProjection := Enveloping.fiberProjection (finiteU q H₁ h₁) (finiteU q H₂ h₂)
  (Y q) (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)
abbrev concreteInclusion := Enveloping.fiberInclusion (finiteU q H₁ h₁) (finiteU q H₂ h₂)
  (Y q) (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)

lemma concrete_evaluated_injective : Function.Injective
    (Enveloping.evalMap (xObj q) (concreteInclusion q hq hp H₁ H₂ h₁ h₂)) := by
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj
      (Enveloping.fiber (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)
        (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)).obj) :=
    (concreteF_side_projective q hq hp H₁ H₂ h₁ h₂).2
  exact Enveloping.evalMap_injective (xObj q) (formE q) _
    (Enveloping.fiberInclusion_injective _ _ _ _ _)

lemma concrete_evaluated_exact : Function.Exact
    (Enveloping.evalMap (xObj q) (concreteInclusion q hq hp H₁ H₂ h₁ h₂))
    (Enveloping.evalMap (xObj q) (concreteProjection q hq hp H₁ H₂ h₁ h₂)) := by
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj
      (Enveloping.fiber (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)
        (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)).obj) :=
    (concreteF_side_projective q hq hp H₁ H₂ h₁ h₂).2
  exact Enveloping.evalMap_exact (xObj q) (formE q) _ _
    (Enveloping.fiberInclusion_injective _ _ _ _ _)
    (Enveloping.fiber_exact _ _ _ _ _) (Enveloping.fiberProjection_surjective _ _ _ _ _)

lemma concrete_evaluated_surjective : Function.Surjective
    (Enveloping.evalMap (xObj q) (concreteProjection q hq hp H₁ H₂ h₁ h₂)) :=
  Enveloping.evalMap_surjective (xObj q) _ (Enveloping.fiberProjection_surjective _ _ _ _ _)

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (U V Y : FiniteModule k (Alg k R S))

def fiberInl : U.obj ⟶ fiberMiddle U V Y := ModuleCat.ofHom (LinearMap.inl _ _ _)
def fiberInm : V.obj ⟶ fiberMiddle U V Y :=
  ModuleCat.ofHom ((LinearMap.inr _ _ _).comp (LinearMap.inl _ _ _))
def fiberInr : fiberCover Y ⟶ fiberMiddle U V Y :=
  ModuleCat.ofHom ((LinearMap.inr _ _ _).comp (LinearMap.inr _ _ _))
def fiberFst : fiberMiddle U V Y ⟶ U.obj := ModuleCat.ofHom (LinearMap.fst _ _ _)
def fiberSnd : fiberMiddle U V Y ⟶ V.obj :=
  ModuleCat.ofHom ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))

@[simp] lemma fiberInl_fst : fiberInl U V Y ≫ fiberFst U V Y = 𝟙 _ := rfl
@[simp] lemma fiberInl_snd : fiberInl U V Y ≫ fiberSnd U V Y = 0 := rfl
@[simp] lemma fiberInm_fst : fiberInm U V Y ≫ fiberFst U V Y = 0 := rfl
@[simp] lemma fiberInm_snd : fiberInm U V Y ≫ fiberSnd U V Y = 𝟙 _ := rfl
@[simp] lemma fiberInr_fst : fiberInr U V Y ≫ fiberFst U V Y = 0 := rfl
@[simp] lemma fiberInr_snd : fiberInr U V Y ≫ fiberSnd U V Y = 0 := rfl

variable (g : U.obj ⟶ Y.obj) (h : V.obj ⟶ Y.obj)
@[simp] lemma fiberInl_projection : fiberInl U V Y ≫ fiberProjection U V Y g h = g := by
  ext x
  change g x + (h 0 + Y.cover.map 0) = g x
  simp only [map_zero,add_zero]
@[simp] lemma fiberInm_projection : fiberInm U V Y ≫ fiberProjection U V Y g h = h := by
  ext x
  change g 0 + (h x + Y.cover.map 0) = h x
  simp only [map_zero,add_zero,zero_add]
@[simp] lemma fiberInr_projection : fiberInr U V Y ≫ fiberProjection U V Y g h =
    ModuleCat.ofHom Y.cover.map := by
  ext x
  change g 0 + (h 0 + Y.cover.map x) = Y.cover.map x
  simp only [map_zero,zero_add]
end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {X M F Y Q : ModuleCat R}

lemma exists_stable_kernel_lift (i : F ⟶ M) (p : M ⟶ Y) (j : Q ⟶ M)
    (hi : Function.Injective i) (he : Function.Exact i p)
    (hq : Function.Surjective (j ≫ p)) (a : X ⟶ M)
    (ha : stableClass (k := k) (a ≫ p).hom = 0) :
    ∃ (v : X ⟶ F) (b : X ⟶ Q), v ≫ i = a - b ≫ j := by
  obtain ⟨P,hfin,hproj,u,w,hw⟩ := (stableClass_eq_zero_iff _).mp ha
  let := hproj
  obtain ⟨l,hl⟩ := Module.projective_lifting_property (j ≫ p).hom w hq
  let b : X ⟶ Q := ModuleCat.ofHom (l.comp u)
  have hzero : (a - b ≫ j) ≫ p = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change p (a x - j (l (u x))) = 0
    rw [map_sub]
    have h := LinearMap.congr_fun hw x
    change w (u x) = p (a x) at h
    have h' := LinearMap.congr_fun hl (u x)
    change p (j (l (u x))) = w (u x) at h'
    rw [h',h,sub_self]
  let e := LinearEquiv.ofInjective i.hom hi
  have hr (x : X) : (a - b ≫ j) x ∈ LinearMap.range i.hom := by
    exact (he _).mp (congrArg (fun f => f x) hzero)
  let c : X →ₗ[R] LinearMap.range i.hom := (a - b ≫ j).hom.codRestrict _ hr
  refine ⟨ModuleCat.ofHom (e.symm.toLinearMap.comp c), b, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (e.apply_symm_apply (c x))

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

abbrev concreteFst := concreteInclusion q hq hp H₁ H₂ h₁ h₂ ≫
  Enveloping.fiberFst (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)
abbrev concreteSnd := concreteInclusion q hq hp H₁ H₂ h₁ h₂ ≫
  Enveloping.fiberSnd (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)

lemma exists_concrete_vZero : ∃ v : xObj q ⟶ Enveloping.evalObj (xObj q)
    (concreteF q hq hp H₁ H₂ h₁ h₂).obj,
    v ≫ Enveloping.evalMap (xObj q) (concreteFst q hq hp H₁ H₂ h₁ h₂) = (uXIso q H₁ h₁).inv ∧
    v ≫ Enveloping.evalMap (xObj q) (concreteSnd q hq hp H₁ H₂ h₁ h₂) = (uXIso q H₂ h₂).inv := by
  let L := Enveloping.evaluation (k := k) (S := E q) (xObj q)
  let U := finiteU q H₁ h₁
  let V := finiteU q H₂ h₂
  let g := normalizedMap q hq hp H₁ h₁
  let h := normalizedMap q hq hp H₂ h₂
  let i := L.map (concreteInclusion q hq hp H₁ H₂ h₁ h₂)
  let p := L.map (concreteProjection q hq hp H₁ H₂ h₁ h₂)
  let j := L.map (Enveloping.fiberInr U V (Y q))
  let a := (uXIso q H₁ h₁).inv ≫ L.map (Enveloping.fiberInl U V (Y q)) +
    (uXIso q H₂ h₂).inv ≫ L.map (Enveloping.fiberInm U V (Y q))
  have hap : a ≫ p = (uXIso q H₁ h₁).inv ≫ L.map g +
      (uXIso q H₂ h₂).inv ≫ L.map h := by
    change (_ + _) ≫ L.map (Enveloping.fiberProjection U V (Y q) g h) = _
    refine (Preadditive.add_comp _ _ _ _ _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact (Category.assoc _ _ _).trans (congrArg (fun morphism =>
        (uXIso q H₁ h₁).inv ≫ morphism) ((L.map_comp _ _).symm.trans
          (congrArg L.map (Enveloping.fiberInl_projection U V (Y q) g h))))
    · exact (Category.assoc _ _ _).trans (congrArg (fun morphism =>
        (uXIso q H₂ h₂).inv ≫ morphism) ((L.map_comp _ _).symm.trans
          (congrArg L.map (Enveloping.fiberInm_projection U V (Y q) g h))))
  have haz : stableClass (k := k) (a ≫ p).hom = 0 := by
    rw [hap]
    change evaluatedStableMap q H₁ h₁ g + evaluatedStableMap q H₂ h₂ h = 0
    rw [normalizedMap_class,normalizedMap_class,← two_smul k]
    have hz : (2:k) = 0 := CharP.cast_eq_zero k 2
    rw [hz,zero_smul]
  have hjp : j ≫ p = L.map (ModuleCat.ofHom (Y q).cover.map) := by
    rw [← L.map_comp]
    exact congrArg L.map (Enveloping.fiberInr_projection U V (Y q) g h)
  have hj : Function.Surjective (j ≫ p) := by
    rw [hjp]
    exact Enveloping.evalMap_surjective (xObj q) _ (Y q).cover.surjective
  obtain ⟨v,b,hv⟩ := exists_stable_kernel_lift i p j
    (concrete_evaluated_injective q hq hp H₁ H₂ h₁ h₂)
    (concrete_evaluated_exact q hq hp H₁ H₂ h₁ h₂) hj a haz
  refine ⟨v,?_,?_⟩
  · change v ≫ L.map (_ ≫ Enveloping.fiberFst U V (Y q)) = _
    rw [L.map_comp,← Category.assoc]
    change (v ≫ i) ≫ L.map (Enveloping.fiberFst U V (Y q)) = _
    rw [hv]
    have hl : L.map (Enveloping.fiberInl U V (Y q)) ≫
        L.map (Enveloping.fiberFst U V (Y q)) = 𝟙 _ :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInl_fst U V (Y q)))).trans (L.map_id _)
    have hm : L.map (Enveloping.fiberInm U V (Y q)) ≫
        L.map (Enveloping.fiberFst U V (Y q)) = 0 :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInm_fst U V (Y q)))).trans (L.map_zero _ _)
    have hr : j ≫ L.map (Enveloping.fiberFst U V (Y q)) = 0 :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInr_fst U V (Y q)))).trans (L.map_zero _ _)
    have ha : a ≫ L.map (Enveloping.fiberFst U V (Y q)) = (uXIso q H₁ h₁).inv :=
      (Preadditive.add_comp _ _ _ _ _ _).trans ((congrArg₂ (· + ·)
        ((Category.assoc _ _ _).trans ((congrArg (fun morphism =>
          (uXIso q H₁ h₁).inv ≫ morphism) hl).trans (Category.comp_id _)))
        ((Category.assoc _ _ _).trans ((congrArg (fun morphism =>
          (uXIso q H₂ h₂).inv ≫ morphism) hm).trans comp_zero))).trans (add_zero _))
    have hb : (b ≫ j) ≫ L.map (Enveloping.fiberFst U V (Y q)) = 0 :=
      (Category.assoc _ _ _).trans ((congrArg (fun morphism => b ≫ morphism) hr).trans
        comp_zero)
    exact (Preadditive.sub_comp _ _ _).trans
      ((congrArg₂ (· - ·) ha hb).trans (sub_zero _))
  · change v ≫ L.map (_ ≫ Enveloping.fiberSnd U V (Y q)) = _
    rw [L.map_comp,← Category.assoc]
    change (v ≫ i) ≫ L.map (Enveloping.fiberSnd U V (Y q)) = _
    rw [hv]
    have hl : L.map (Enveloping.fiberInl U V (Y q)) ≫
        L.map (Enveloping.fiberSnd U V (Y q)) = 0 :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInl_snd U V (Y q)))).trans (L.map_zero _ _)
    have hm : L.map (Enveloping.fiberInm U V (Y q)) ≫
        L.map (Enveloping.fiberSnd U V (Y q)) = 𝟙 _ :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInm_snd U V (Y q)))).trans (L.map_id _)
    have hr : j ≫ L.map (Enveloping.fiberSnd U V (Y q)) = 0 :=
      ((L.map_comp _ _).symm.trans (congrArg L.map
        (Enveloping.fiberInr_snd U V (Y q)))).trans (L.map_zero _ _)
    have ha : a ≫ L.map (Enveloping.fiberSnd U V (Y q)) = (uXIso q H₂ h₂).inv :=
      (Preadditive.add_comp _ _ _ _ _ _).trans ((congrArg₂ (· + ·)
        ((Category.assoc _ _ _).trans ((congrArg (fun morphism =>
          (uXIso q H₁ h₁).inv ≫ morphism) hl).trans comp_zero))
        ((Category.assoc _ _ _).trans ((congrArg (fun morphism =>
          (uXIso q H₂ h₂).inv ≫ morphism) hm).trans (Category.comp_id _)))).trans
            (zero_add _))
    have hb : (b ≫ j) ≫ L.map (Enveloping.fiberSnd U V (Y q)) = 0 :=
      (Category.assoc _ _ _).trans ((congrArg (fun morphism => b ≫ morphism) hr).trans
        comp_zero)
    exact (Preadditive.sub_comp _ _ _).trans
      ((congrArg₂ (· - ·) ha hb).trans (sub_zero _))

def concreteVZero := (exists_concrete_vZero q hq hp H₁ H₂ h₁ h₂).choose
lemma concreteVZero_fst : concreteVZero q hq hp H₁ H₂ h₁ h₂ ≫
    Enveloping.evalMap (xObj q) (concreteFst q hq hp H₁ H₂ h₁ h₂) = (uXIso q H₁ h₁).inv :=
  (exists_concrete_vZero q hq hp H₁ H₂ h₁ h₂).choose_spec.1
lemma concreteVZero_snd : concreteVZero q hq hp H₁ H₂ h₁ h₂ ≫
    Enveloping.evalMap (xObj q) (concreteSnd q hq hp H₁ H₂ h₁ h₂) = (uXIso q H₂ h₂).inv :=
  (exists_concrete_vZero q hq hp H₁ H₂ h₁ h₂).choose_spec.2

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : TotallyAcyclic P)
  {L M N Q : ModuleCat.{0} R} [Module.Finite R Q] [Module.Projective R Q]
  (i₁ : M ⟶ L) (i₂ : N ⟶ L) (i₃ : Q ⟶ L)
  (p₁ : L ⟶ M) (p₂ : L ⟶ N) (p₃ : L ⟶ Q)
  (h11 : i₁ ≫ p₁ = 𝟙 _) (h12 : i₁ ≫ p₂ = 0)
  (h21 : i₂ ≫ p₁ = 0) (h22 : i₂ ≫ p₂ = 𝟙 _)
  (hs : p₁ ≫ i₁ + p₂ ≫ i₂ + p₃ ≫ i₃ = 𝟙 _)

include hP h11 h12 h21 h22 hs in
lemma completeHpair_bijective (a : ℤ) : Function.Bijective
    ((completeHmap (k := k) P p₁ a).prod (completeHmap P p₂ a)) := by
  have pair_id : ((completeHmap (k := k) P i₁ a).comp (completeHmap P p₁ a) +
      (completeHmap P i₂ a).comp (completeHmap P p₂ a)) = LinearMap.id := by
    have hh := congrArg (fun f => completeHmap (k := k) P f a) hs
    simp only [completeHmap_add,completeHmap_comp,completeHmap_id] at hh
    have hz : (completeHmap (k := k) P i₃ a).comp (completeHmap P p₃ a) = 0 := by
      apply LinearMap.ext
      intro x
      let := completeHom_projective_zero (k := k) P hP Q a
      change completeHmap P i₃ a (completeHmap P p₃ a x) = 0
      rw [Subsingleton.elim (completeHmap P p₃ a x) 0,map_zero]
    rwa [hz,add_zero] at hh
  constructor
  · intro x y h
    have hf := congrArg (fun z => completeHmap P i₁ a z.1 + completeHmap P i₂ a z.2) h
    change (completeHmap P i₁ a).comp (completeHmap P p₁ a) x +
        (completeHmap P i₂ a).comp (completeHmap P p₂ a) x =
      (completeHmap P i₁ a).comp (completeHmap P p₁ a) y +
        (completeHmap P i₂ a).comp (completeHmap P p₂ a) y at hf
    simp only [← LinearMap.add_apply,pair_id,LinearMap.id_apply] at hf
    exact hf
  · rintro ⟨x,y⟩
    refine ⟨completeHmap P i₁ a x + completeHmap P i₂ a y,?_⟩
    apply Prod.ext
    · change completeHmap P p₁ a (_+_) = x
      rw [map_add,← LinearMap.comp_apply,← LinearMap.comp_apply,
        ← completeHmap_comp,← completeHmap_comp,h11,h21,completeHmap_id,completeHmap_zero]
      exact add_zero _
    · change completeHmap P p₂ a (_+_) = y
      rw [map_add,← LinearMap.comp_apply,← LinearMap.comp_apply,
        ← completeHmap_comp,← completeHmap_comp,h12,h22,completeHmap_id,completeHmap_zero]
      exact zero_add _
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (U V Y : FiniteModule k (Alg k R S))

def fiberThird : fiberMiddle U V Y ⟶ fiberCover Y :=
  ModuleCat.ofHom ((LinearMap.snd (Alg k R S) V.obj (fiberCover Y)).comp
    (LinearMap.snd (Alg k R S) U.obj (V.obj × fiberCover Y)))

lemma fiber_sum_id : fiberFst U V Y ≫ fiberInl U V Y +
    fiberSnd U V Y ≫ fiberInm U V Y + fiberThird U V Y ≫ fiberInr U V Y = 𝟙 _ := by
  ext x
  change (x.1,(0,0)) + (0,(x.2.1,0)) + (0,(0,x.2.2)) = x
  rcases x with ⟨x,y,z⟩
  apply Prod.ext
  · change (x+0)+0=x
    simp
  · apply Prod.ext
    · change (0+y)+0=y
      simp
    · change (0+0)+z=z
      simp
end Tachikawa.Enveloping



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

abbrev XHom := completeHom (k := k) (xComplete q) (xObj q)
abbrev FHom := completeHom (k := k) (xComplete q)
  (Enveloping.evalObj (xObj q) (concreteF q hq hp H₁ H₂ h₁ h₂).obj)
abbrev middleHom := completeHom (k := k) (xComplete q)
  (Enveloping.evalObj (xObj q) (concreteMiddle q H₁ H₂ h₁ h₂))
abbrev FHomInclusion := completeHomMap (k := k) (xComplete q)
  (Enveloping.evalMap (xObj q) (concreteInclusion q hq hp H₁ H₂ h₁ h₂))
abbrev FHomProjection := completeHomMap (k := k) (xComplete q)
  (Enveloping.evalMap (xObj q) (concreteProjection q hq hp H₁ H₂ h₁ h₂))

lemma FHom_shortExact :
    (∀ a, Function.Injective ((FHomInclusion q hq hp H₁ H₂ h₁ h₂).f a)) ∧
    (∀ a, Function.Exact ((FHomInclusion q hq hp H₁ H₂ h₁ h₂).f a)
      ((FHomProjection q hq hp H₁ H₂ h₁ h₂).f a)) ∧
    (∀ a, Function.Surjective ((FHomProjection q hq hp H₁ H₂ h₁ h₂).f a)) :=
  ⟨completeHomMap_injective _ _ (concrete_evaluated_injective q hq hp H₁ H₂ h₁ h₂),
    completeHomMap_exact _ _ _ (concrete_evaluated_injective q hq hp H₁ H₂ h₁ h₂)
      (concrete_evaluated_exact q hq hp H₁ H₂ h₁ h₂),
    completeHomMap_surjective _ _ (concrete_evaluated_surjective q hq hp H₁ H₂ h₁ h₂)
      ((finiteX q).complete_projective (formE q))⟩

def middleHpair (a : ℤ) :=
  (completeHmap (k := k) (xComplete q) (Enveloping.evalMap (xObj q)
      (Enveloping.fiberFst (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q))) a).prod
  (completeHmap (k := k) (xComplete q) (Enveloping.evalMap (xObj q)
      (Enveloping.fiberSnd (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q))) a)

omit [CharP k 2] in
lemma middleHpair_bijective (a : ℤ) : Function.Bijective (middleHpair q H₁ H₂ h₁ h₂ a) := by
  let L := Enveloping.evaluation (k := k) (S := E q) (xObj q)
  let U := finiteU q H₁ h₁
  let V := finiteU q H₂ h₂
  let : Module.Finite (Enveloping.Alg k (E q) (E q)) (Enveloping.fiberCover (Y q)) := by
    exact inferInstanceAs (Module.Finite (Enveloping.Alg k (E q) (E q))
      (Fin (Y q).cover.rank → Enveloping.Alg k (E q) (E q)))
  let : Module.Projective (Enveloping.Alg k (E q) (E q)) (Enveloping.fiberCover (Y q)) := by
    exact inferInstanceAs (Module.Projective (Enveloping.Alg k (E q) (E q))
      (Fin (Y q).cover.rank → Enveloping.Alg k (E q) (E q)))
  let : IsScalarTower k (Enveloping.Alg k (E q) (E q)) (Enveloping.fiberCover (Y q)) :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := Enveloping.Alg k (E q) (E q))
      (M := Enveloping.fiberCover (Y q)) (fun _ _ => rfl)
  let : FiniteDimensional k (Enveloping.fiberCover (Y q)) :=
    Module.Finite.trans (R := k) (A := Enveloping.Alg k (E q) (E q)) _
  let : Module.Finite (E q) (L.obj (Enveloping.fiberCover (Y q))) :=
    Enveloping.eval_finite (xObj q)
  let : CategoryTheory.Projective (Enveloping.fiberCover (Y q)) :=
    ModuleCat.projective_of_categoryTheory_projective _
  let : CategoryTheory.Projective (L.obj (Enveloping.fiberCover (Y q))) :=
    Enveloping.evaluation_projective (xObj q) _
  let : Module.Projective (E q) (L.obj (Enveloping.fiberCover (Y q))) :=
    ModuleCat.projective_of_module_projective _
  change Function.Bijective
    ((completeHmap (k := k) (xComplete q) (L.map (Enveloping.fiberFst U V (Y q))) a).prod
      (completeHmap (xComplete q) (L.map (Enveloping.fiberSnd U V (Y q))) a))
  apply completeHpair_bijective (xComplete q) ((finiteX q).complete_totallyAcyclic (formE q))
    (L.map (Enveloping.fiberInl U V (Y q))) (L.map (Enveloping.fiberInm U V (Y q)))
    (L.map (Enveloping.fiberInr U V (Y q))) _ _ (L.map (Enveloping.fiberThird U V (Y q)))
  · rw [← L.map_comp,Enveloping.fiberInl_fst,L.map_id]
  · rw [← L.map_comp,Enveloping.fiberInl_snd,L.map_zero]
  · rw [← L.map_comp,Enveloping.fiberInm_fst,L.map_zero]
  · rw [← L.map_comp,Enveloping.fiberInm_snd,L.map_id]
  · rw [← L.map_comp,← L.map_comp,← L.map_comp,← L.map_add,← L.map_add,
      Enveloping.fiber_sum_id,L.map_id]

include hq hp in
lemma FHomInclusion_bijective (a : ℤ) (h3 : a ≠ -3) (h2 : a ≠ -2)
    (h0 : a ≠ 0) (h1 : a ≠ 1) :
    Function.Bijective (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a) := by
  have hs := FHom_shortExact q hq hp H₁ H₂ h₁ h₂
  exact VectorSplit.Hmap_bijective_of_zeros _ _ hs.1 hs.2.1 hs.2.2 a
    (completeYHomology_zero q hq hp (a-1) (by omega) (by omega))
    (completeYHomology_zero q hq hp a h3 h0)
end Tachikawa.Construction



namespace Tachikawa.VectorSplit
open CategoryTheory
variable {k : Type*} [Field k] {K L M : CochainComplex (ModuleCat k) ℤ}
  (i : K ⟶ L) (p : L ⟶ M)
  (hi : ∀ a, Function.Injective (i.f a))
  (he : ∀ a, Function.Exact (i.f a) (p.f a))
  (hp : ∀ a, Function.Surjective (p.f a))

include hi he hp in
lemma Hmap_exact (a : ℤ) : Function.Exact (Hmap i a) (Hmap p a) := by
  intro x
  constructor
  · intro hx
    obtain ⟨z,rfl⟩ := quotient_surjective a x
    obtain ⟨y,hy⟩ := (quotient_zero_iff_predecessor a _).mp hx
    obtain ⟨v,hv⟩ := hp (a-1) y
    have hz' : p.f a (z.val - L.d (a-1) a v) = 0 := by
      rw [map_sub,← comm_apply p,hv,hy]
      exact sub_self _
    obtain ⟨u,hu⟩ := (he a _).mp hz'
    have huz : u ∈ Z K a := by
      rw [memZ_iff]
      apply hi (a+1)
      rw [map_zero,← comm_apply i,hu,map_sub]
      rw [(memZ_iff a z.val).mp z.property]
      have hd := congrArg (fun f => f v) (L.d_comp_d (a-1) a (a+1))
      change L.d a (a+1) (L.d (a-1) a v) = 0 at hd
      rw [hd,sub_self]
    refine ⟨quotient K a ⟨u,huz⟩,?_⟩
    rw [Hmap_quotient]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (quotient_zero_iff_predecessor a _).mpr
    use -v
    change L.d (a-1) a (-v) = i.f a u - z.val
    rw [map_neg,hu]
    abel
  · rintro ⟨y,rfl⟩
    obtain ⟨z,rfl⟩ := quotient_surjective a y
    rw [Hmap_quotient,Hmap_quotient]
    have hz : cycleMap p a (cycleMap i a z) = 0 := by
      apply Subtype.ext
      exact (he a _).mpr ⟨z.val,rfl⟩
    rw [hz,map_zero]
end Tachikawa.VectorSplit



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

abbrev zeroHomEquiv (N : ModuleCat (E q)) :=
  CompleteHom.zeroEquiv (k := k) (xComplete q) ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q))
    ((finiteX q).cokerEquiv (formE q)) N

lemma FHomProjection_zero_surjective : Function.Surjective
    (VectorSplit.Hmap (FHomProjection q hq hp H₁ H₂ h₁ h₂) 0) := by
  let L := Enveloping.evaluation (k := k) (S := E q) (xObj q)
  let U := finiteU q H₁ h₁
  let V := finiteU q H₂ h₂
  let a := (uXIso q H₁ h₁).inv ≫ L.map (Enveloping.fiberInl U V (Y q))
  let x := (zeroHomEquiv q _).symm (stableClass (k := k) a.hom)
  let ep := zeroHomEquiv q (Enveloping.evalObj (xObj q) (Y q).obj)
  let ew := ep.trans (WZeroEquiv q hq hp)
  apply linear_surjective_to_line _ ew x
  intro hz
  have hn := CompleteHom.zeroEquiv_natural (xComplete q)
    ((finiteX q).complete_totallyAcyclic (formE q))
    ((finiteX q).complete_finite (formE q)) ((finiteX q).complete_projective (formE q))
    ((finiteX q).cokerEquiv (formE q)) (L.map (concreteProjection q hq hp H₁ H₂ h₁ h₂)) x
  change ep (VectorSplit.Hmap (FHomProjection q hq hp H₁ H₂ h₁ h₂) 0 x) = _ at hn
  have hez : ep (VectorSplit.Hmap (FHomProjection q hq hp H₁ H₂ h₁ h₂) 0 x) = 0 :=
    (congrArg ep hz).trans (map_zero ep.toLinearMap)
  have hx : zeroHomEquiv q _ x = stableClass (k := k) a.hom := LinearEquiv.apply_symm_apply _ _
  rw [hx] at hn
  have ha : a ≫ L.map (concreteProjection q hq hp H₁ H₂ h₁ h₂) =
      (uXIso q H₁ h₁).inv ≫ L.map (normalizedMap q hq hp H₁ h₁) := by
    change ((uXIso q H₁ h₁).inv ≫ L.map (Enveloping.fiberInl U V (Y q))) ≫
      L.map (Enveloping.fiberProjection U V (Y q) _ _) = _
    exact (Category.assoc _ _ _).trans (congrArg (fun morphism =>
      (uXIso q H₁ h₁).inv ≫ morphism) ((L.map_comp _ _).symm.trans
        (congrArg L.map (Enveloping.fiberInl_projection U V (Y q)
          (normalizedMap q hq hp H₁ h₁) (normalizedMap q hq hp H₂ h₂)))))
  have hn' : stableClass (k := k) (a ≫ L.map (concreteProjection q hq hp H₁ H₂ h₁ h₂)).hom = 0 := hn.symm.trans hez
  rw [ha] at hn'
  change evaluatedStableMap q H₁ h₁ (normalizedMap q hq hp H₁ h₁) = 0 at hn'
  rw [normalizedMap_class] at hn'
  exact wZero_ne_zero q hq hp hn'

lemma FHomInclusion_one_bijective : Function.Bijective
    (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) 1) := by
  have hs := FHom_shortExact q hq hp H₁ H₂ h₁ h₂
  exact ⟨VectorSplit.Hmap_injective_of_prev_surjective _ _ hs.1 hs.2.1 hs.2.2 1
    (FHomProjection_zero_surjective q hq hp H₁ H₂ h₁ h₂),
    VectorSplit.Hmap_surjective_of_right_zero _ _ hs.1 hs.2.1 hs.2.2 1
      (completeYHomology_zero q hq hp 1 (by decide) (by decide))⟩

def middleHpairX (a : ℤ) :=
  ((completeHomIso (k := k) (xComplete q) (uXIso q H₁ h₁) a).prodCongr
    (completeHomIso (k := k) (xComplete q) (uXIso q H₂ h₂) a)).toLinearMap.comp
      (middleHpair q H₁ H₂ h₁ h₂ a)

omit [CharP k 2] in
lemma middleHpairX_bijective (a : ℤ) : Function.Bijective (middleHpairX q H₁ H₂ h₁ h₂ a) := by
  dsimp only [middleHpairX, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact Function.Bijective.comp (LinearEquiv.bijective _) (middleHpair_bijective q H₁ H₂ h₁ h₂ a)

def FHomPair (a : ℤ) := (middleHpairX q H₁ H₂ h₁ h₂ a).comp
    (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a)

omit [CharP k 2] in
lemma middleHom_zero (a : ℤ) (hz : Subsingleton (VectorSplit.H (selfHom q) a)) :
    Subsingleton (VectorSplit.H (middleHom q H₁ H₂ h₁ h₂) a) := by
  let := hz
  exact (middleHpairX_bijective q H₁ H₂ h₁ h₂ a).1.subsingleton

lemma FHomInclusion_injective (a : ℤ) (h2 : a ≠ -2) (h1 : a ≠ 1) :
    Function.Injective (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a) := by
  have hs := FHom_shortExact q hq hp H₁ H₂ h₁ h₂
  exact VectorSplit.Hmap_injective_of_prev_zero _ _ hs.1 hs.2.1 hs.2.2 a
    (completeYHomology_zero q hq hp (a-1) (by omega) (by omega))

lemma FHom_minusThree_zero : Subsingleton
    (VectorSplit.H (FHom q hq hp H₁ H₂ h₁ h₂) (-3)) := by
  have hi := FHomInclusion_injective q hq hp H₁ H₂ h₁ h₂ (-3) (by decide) (by decide)
  let := middleHom_zero q H₁ H₂ h₁ h₂ (-3) (selfHom_zero_near q hq hp).2.2.2
  exact hi.subsingleton

lemma FHomPair_bijective (a : ℤ) (ha : 0 < a ∨ a ≤ -3) :
    Function.Bijective (FHomPair q hq hp H₁ H₂ h₁ h₂ a) := by
  by_cases h3 : a = -3
  · subst a
    have hF := FHom_minusThree_zero q hq hp H₁ H₂ h₁ h₂
    have hX := (selfHom_zero_near q hq hp).2.2.2
    exact ⟨fun _ _ _ => hF.elim _ _,fun x => ⟨0,Prod.ext (hX.elim _ _) (hX.elim _ _)⟩⟩
  · apply (middleHpairX_bijective q H₁ H₂ h₁ h₂ a).comp
    by_cases h1 : a = 1
    · subst a
      exact FHomInclusion_one_bijective q hq hp H₁ H₂ h₁ h₂
    · exact FHomInclusion_bijective q hq hp H₁ H₂ h₁ h₂ a h3 (by omega) (by omega) h1

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
lemma evalMap_comp (X : ModuleCat R) {U V W : ModuleCat (Alg k R R)} (f : U ⟶ V) (g : V ⟶ W) :
    evalMap X (f ≫ g) = evalMap X f ≫ evalMap X g := (evaluation X).map_comp f g

lemma completeHmap_eval_comp (P : ChainComplex (ModuleCat R) ℤ) (X N : ModuleCat R)
    {U V W : ModuleCat (Alg k R R)} (f : U ⟶ V) (g : V ⟶ W)
    (h : evalObj X W ⟶ N) (a : ℤ) :
    completeHmap (k := k) P (evalMap X (f ≫ g) ≫ h) a =
      (completeHmap P h a).comp
        ((completeHmap P (evalMap X g) a).comp (completeHmap P (evalMap X f) a)) := by
  rw [evalMap_comp,completeHmap_comp,completeHmap_comp]
end Tachikawa.Enveloping

namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

omit [CharP k 2] in
lemma uXIso_hom_twist (H : k) (hH : H ≠ 0) :
    (uXIso q H hH).hom = (Enveloping.twistedTensorIso (sigma q H hH) (xObj q)).hom ≫
      (XTwistIso q H hH).hom := by
  rw [XTwistIso_hom]
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  change (show E q from m) • x = (sigma q H hH).symm (show E q from m) • x
  have h := sigma_fixed_x q H hH ((sigma q H hH).symm (show E q from m)) x
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

omit [CharP k 2] in
lemma uXIso_inv_twist (H : k) (hH : H ≠ 0) :
    (uXIso q H hH).inv = (XTwistIso q H hH).inv ≫
      (Enveloping.twistedTensorIso (sigma q H hH) (xObj q)).inv := by
  apply (cancel_mono (uXIso q H hH).hom).1
  rw [(uXIso q H hH).inv_hom_id,uXIso_hom_twist]
  erw [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id]

local instance concreteF_left_projective : Module.Projective (E q)
    (Enveloping.Obj (concreteF q hq hp H₁ H₂ h₁ h₂).obj) :=
  (concreteF_side_projective q hq hp H₁ H₂ h₁ h₂).1
local instance concreteF_right_projective : Module.Projective (E q)ᵐᵒᵖ
    (Enveloping.Obj (concreteF q hq hp H₁ H₂ h₁ h₂).obj) :=
  (concreteF_side_projective q hq hp H₁ H₂ h₁ h₂).2
local instance concreteF_finite : FiniteDimensional k
    (Enveloping.Obj (concreteF q hq hp H₁ H₂ h₁ h₂).obj) :=
by
  change Module.Finite k (concreteF q hq hp H₁ H₂ h₁ h₂)
  infer_instance

abbrev concreteLift := Enveloping.tensorCompleteLift (concreteF q hq hp H₁ H₂ h₁ h₂).obj
  (finiteX q) (formE q) (concreteVZero q hq hp H₁ H₂ h₁ h₂)
abbrev FAction : selfHom q ⟶ FHom q hq hp H₁ H₂ h₁ h₂ :=
  completeFunctorHom (k := k) (Enveloping.tensorFunctor (concreteF q hq hp H₁ H₂ h₁ h₂).obj)
    (xComplete q) (xComplete q) (xObj q) (concreteLift q hq hp H₁ H₂ h₁ h₂)
abbrev VAction : selfHom q ⟶ FHom q hq hp H₁ H₂ h₁ h₂ :=
  completeHomMap (k := k) (xComplete q) (concreteVZero q hq hp H₁ H₂ h₁ h₂)
abbrev FFirst : FHom q hq hp H₁ H₂ h₁ h₂ ⟶ selfHom q :=
  completeHomMap (k := k) (xComplete q)
    (Enveloping.evalMap (xObj q) (concreteFst q hq hp H₁ H₂ h₁ h₂) ≫ (uXIso q H₁ h₁).hom)
abbrev FSecond : FHom q hq hp H₁ H₂ h₁ h₂ ⟶ selfHom q :=
  completeHomMap (k := k) (xComplete q)
    (Enveloping.evalMap (xObj q) (concreteSnd q hq hp H₁ H₂ h₁ h₂) ≫ (uXIso q H₂ h₂).hom)

lemma FHomPair_eq (a : ℤ) : FHomPair q hq hp H₁ H₂ h₁ h₂ a =
    (VectorSplit.Hmap (FFirst q hq hp H₁ H₂ h₁ h₂) a).prod
      (VectorSplit.Hmap (FSecond q hq hp H₁ H₂ h₁ h₂) a) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change completeHmap _ (uXIso q H₁ h₁).hom a
      (completeHmap _ (Enveloping.evalMap _ (Enveloping.fiberFst _ _ _)) a
      (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a x)) =
      completeHmap _ (Enveloping.evalMap (xObj q)
        (concreteInclusion q hq hp H₁ H₂ h₁ h₂ ≫
          Enveloping.fiberFst (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)) ≫
        (uXIso q H₁ h₁).hom) a x
    exact (LinearMap.congr_fun (Enveloping.completeHmap_eval_comp
      (xComplete q) (xObj q) (xObj q) _ _ (uXIso q H₁ h₁).hom a) x).symm
  · change completeHmap _ (uXIso q H₂ h₂).hom a
      (completeHmap _ (Enveloping.evalMap _ (Enveloping.fiberSnd _ _ _)) a
      (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) a x)) =
      completeHmap _ (Enveloping.evalMap (xObj q)
        (concreteInclusion q hq hp H₁ H₂ h₁ h₂ ≫
          Enveloping.fiberSnd (finiteU q H₁ h₁) (finiteU q H₂ h₂) (Y q)) ≫
        (uXIso q H₂ h₂).hom) a x
    exact (LinearMap.congr_fun (Enveloping.completeHmap_eval_comp
      (xComplete q) (xObj q) (xObj q) _ _ (uXIso q H₂ h₂).hom a) x).symm

lemma FAction_first (a : ℤ) : VectorSplit.Hmap
    (FAction q hq hp H₁ H₂ h₁ h₂ ≫ FFirst q hq hp H₁ H₂ h₁ h₂) a =
    VectorSplit.Hmap (xTwistHom q H₁ h₁) a := by
  dsimp only [FFirst]
  rw [uXIso_hom_twist]
  exact Enveloping.tensor_projected_action (finiteX q) (formE q) (sigma q H₁ h₁)
    (XTwistIso q H₁ h₁) (concreteVZero q hq hp H₁ H₂ h₁ h₂)
    (concreteLift q hq hp H₁ H₂ h₁ h₂)
    (Enveloping.tensorCompleteLift_aug _ _ _ _)
    (concreteFst q hq hp H₁ H₂ h₁ h₂)
    ((concreteVZero_fst q hq hp H₁ H₂ h₁ h₂).trans (uXIso_inv_twist q H₁ h₁)) a

lemma FAction_second (a : ℤ) : VectorSplit.Hmap
    (FAction q hq hp H₁ H₂ h₁ h₂ ≫ FSecond q hq hp H₁ H₂ h₁ h₂) a =
    VectorSplit.Hmap (xTwistHom q H₂ h₂) a := by
  dsimp only [FSecond]
  rw [uXIso_hom_twist]
  exact Enveloping.tensor_projected_action (finiteX q) (formE q) (sigma q H₂ h₂)
    (XTwistIso q H₂ h₂) (concreteVZero q hq hp H₁ H₂ h₁ h₂)
    (concreteLift q hq hp H₁ H₂ h₁ h₂)
    (Enveloping.tensorCompleteLift_aug _ _ _ _)
    (concreteSnd q hq hp H₁ H₂ h₁ h₂)
    ((concreteVZero_snd q hq hp H₁ H₂ h₁ h₂).trans (uXIso_inv_twist q H₂ h₂)) a

lemma VAction_first : VAction q hq hp H₁ H₂ h₁ h₂ ≫ FFirst q hq hp H₁ H₂ h₁ h₂ = 𝟙 _ := by
  rw [← completeHomMap_comp,← Category.assoc,concreteVZero_fst,Iso.inv_hom_id,completeHomMap_id]
lemma VAction_second : VAction q hq hp H₁ H₂ h₁ h₂ ≫ FSecond q hq hp H₁ H₂ h₁ h₂ = 𝟙 _ := by
  rw [← completeHomMap_comp,← Category.assoc,concreteVZero_snd,Iso.inv_hom_id,completeHomMap_id]

end Tachikawa.Construction



namespace Tachikawa
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def scalarPair (r s : k) : (V × V) →ₗ[k] (V × V) :=
  ((r • LinearMap.fst k V V) + LinearMap.snd k V V).prod
    ((s • LinearMap.fst k V V) + LinearMap.snd k V V)

lemma scalarPair_bijective (r s : k) (hrs : r ≠ s) :
    Function.Bijective (scalarPair (V := V) r s) := by
  have hn : r-s ≠ 0 := sub_ne_zero.mpr hrs
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨g,h⟩ hz
    have h1 : r • g + h = 0 := congrArg Prod.fst hz
    have h2 : s • g + h = 0 := congrArg Prod.snd hz
    have hg : (r-s) • g = 0 := by rw [sub_smul]; exact (add_left_inj h).mp (h1.trans h2.symm) |> sub_eq_zero.mpr
    have hg0 : g = 0 := (smul_eq_zero.mp hg).resolve_left hn
    simp only [hg0,smul_zero,zero_add] at h1
    exact Prod.ext hg0 h1
  · rintro ⟨x,y⟩
    let g := (r-s)⁻¹ • (x-y)
    refine ⟨(g,x-r•g),?_⟩
    apply Prod.ext
    · change r•g+(x-r•g)=x
      abel
    · change s•g+(x-r•g)=y
      have he : (r-s) • g = x-y := by
        dsimp [g]
        rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
      rw [sub_smul] at he
      calc
        s•g+(x-r•g) = x-(r•g-s•g) := by abel
        _ = y := by rw [he]; abel

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

def delta (a : ℤ) : (VectorSplit.H (selfHom q) a × VectorSplit.H (selfHom q) a) →ₗ[k]
    VectorSplit.H (FHom q hq hp H₁ H₂ h₁ h₂) a :=
  (VectorSplit.Hmap (FAction q hq hp H₁ H₂ h₁ h₂) a).coprod
    (VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) a)

lemma delta_pair (a : ℤ) (x y : VectorSplit.H (selfHom q) a) :
    FHomPair q hq hp H₁ H₂ h₁ h₂ a (delta q hq hp H₁ H₂ h₁ h₂ a (x,y)) =
      (VectorSplit.Hmap (xTwistHom q H₁ h₁) a x + y,
        VectorSplit.Hmap (xTwistHom q H₂ h₂) a x + y) := by
  rw [FHomPair_eq]
  change (VectorSplit.Hmap (FFirst q hq hp H₁ H₂ h₁ h₂) a
      (VectorSplit.Hmap (FAction q hq hp H₁ H₂ h₁ h₂) a x +
        VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) a y),
    VectorSplit.Hmap (FSecond q hq hp H₁ H₂ h₁ h₂) a
      (VectorSplit.Hmap (FAction q hq hp H₁ H₂ h₁ h₂) a x +
        VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) a y)) = _
  simp only [map_add, ← LinearMap.comp_apply,← VectorSplit.Hmap_comp,
    FAction_first,FAction_second,VAction_first,VAction_second,VectorSplit.Hmap_id,
    LinearMap.id_apply]

lemma delta_bijective_weights (a : ℤ) (ha : 0 < a ∨ a ≤ -3) (r s : k) (hrs : r ≠ s)
    (hr : ∀ x, VectorSplit.Hmap (xTwistHom q H₁ h₁) a x = r • x)
    (hs : ∀ x, VectorSplit.Hmap (xTwistHom q H₂ h₂) a x = s • x) :
    Function.Bijective (delta q hq hp H₁ H₂ h₁ h₂ a) := by
  have he : (FHomPair q hq hp H₁ H₂ h₁ h₂ a).comp (delta q hq hp H₁ H₂ h₁ h₂ a) =
      scalarPair r s := by
    apply LinearMap.ext
    rintro ⟨x,y⟩
    exact (delta_pair q hq hp H₁ H₂ h₁ h₂ a x y).trans (by rw [hr,hs]; rfl)
  have hb := scalarPair_bijective (V := VectorSplit.H (selfHom q) a) r s hrs
  rw [← he] at hb
  exact ⟨fun _ _ h => hb.1 (congrArg (FHomPair q hq hp H₁ H₂ h₁ h₂ a) h),fun z => by
    obtain ⟨x,hx⟩ := hb.2 (FHomPair q hq hp H₁ H₂ h₁ h₂ a z)
    exact ⟨x,(FHomPair_bijective q hq hp H₁ H₂ h₁ h₂ a ha).1 hx⟩⟩

lemma delta_bijective_of_zero (a : ℤ) (ha : 0 < a ∨ a ≤ -3)
    (hz : Subsingleton (VectorSplit.H (selfHom q) a)) :
    Function.Bijective (delta q hq hp H₁ H₂ h₁ h₂ a) := by
  let := hz
  let : Subsingleton (VectorSplit.H (FHom q hq hp H₁ H₂ h₁ h₂) a) :=
    (FHomPair_bijective q hq hp H₁ H₂ h₁ h₂ a ha).1.subsingleton
  exact ⟨fun _ _ _ => Subsingleton.elim _ _,fun x => ⟨0,Subsingleton.elim _ _⟩⟩

lemma delta_minusTwo_injective : Function.Injective (delta q hq hp H₁ H₂ h₁ h₂ (-2)) := by
  let := (selfHom_zero_near q hq hp).2.2.1
  exact fun _ _ _ => Subsingleton.elim _ _

end Construction

namespace SourceField
open Construction
abbrev sourceDelta (a : ℤ) := delta q (parameter_ne_zero 0) one_add_q_pow_ne_zero
  H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2) a

lemma sourceDelta_positive (n : ℕ) : Function.Bijective (sourceDelta ((n+1:ℕ):ℤ)) := by
  by_cases hlow : n+1 < 3
  · apply delta_bijective_of_zero _ _ _ _ _ _ _ _ (Or.inl (by omega))
    exact positiveSelfHom_zero q (parameter_ne_zero 0) one_add_q_pow_ne_zero n (by omega)
  · apply delta_bijective_weights _ _ _ _ _ _ _ _ (Or.inl (by omega))
      ((H₁⁻¹)^((n+1)/3)) ((H₂⁻¹)^((n+1)/3))
    · simpa only [inv_pow] using H_inverse_powers_distinct ((n+1)/3) (by omega)
    · exact xTwistHom_positive q _ _ (parameter_ne_zero 0) one_add_q_pow_ne_zero n
    · exact xTwistHom_positive q _ _ (parameter_ne_zero 0) one_add_q_pow_ne_zero n

lemma sourceDelta_negative (n : ℕ) : Function.Bijective (sourceDelta (Int.negSucc (n+2))) := by
  apply delta_bijective_weights _ _ _ _ _ _ _ _ (Or.inr (by omega))
    (H₁^2*H₁^((n+2)/3)) (H₂^2*H₂^((n+2)/3))
  · simpa only [← pow_add] using H_powers_distinct (2+(n+2)/3) (by omega)
  · exact xTwistHom_negative q _ _ (parameter_ne_zero 0) one_add_q_pow_ne_zero (n+1)
  · exact xTwistHom_negative q _ _ (parameter_ne_zero 0) one_add_q_pow_ne_zero (n+1)

lemma sourceDelta_bijective (a : ℤ) (ha : 0 < a ∨ a ≤ -3) :
    Function.Bijective (sourceDelta a) := by
  rcases ha with ha | ha
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, a = ((n+1:ℕ):ℤ) := ⟨(a-1).toNat,by omega⟩
    exact sourceDelta_positive n
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, a = Int.negSucc (n+2) := ⟨(-a-3).toNat,by omega⟩
    exact sourceDelta_negative n

end SourceField
end Tachikawa



namespace Tachikawa
variable {k A B C V : Type*} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup V] [Module k V]

lemma exact_line_surjective (i : A →ₗ[k] B) (p : B →ₗ[k] C)
    (hi : Function.Injective i) (hp : Function.Surjective p) (he : Function.Exact i p)
    (eB : B ≃ₗ[k] k × k) (eC : C ≃ₗ[k] k) (eV : V ≃ₗ[k] k)
    (v : V →ₗ[k] A) (hv : Function.Injective v) : Function.Surjective v := by
  let : FiniteDimensional k B := eB.symm.finiteDimensional
  let : FiniteDimensional k C := eC.symm.finiteDimensional
  let : FiniteDimensional k V := eV.symm.finiteDimensional
  let : FiniteDimensional k A := Module.Finite.of_injective i hi
  have hB : Module.finrank k B = 2 := by simpa using eB.finrank_eq
  have hC : Module.finrank k C = 1 := by simpa using eC.finrank_eq
  have hV : Module.finrank k V = 1 := by simpa using eV.finrank_eq
  have hr : Module.finrank k p.range = 1 := by rw [LinearMap.range_eq_top.mpr hp]; simpa using hC
  have ha : Module.finrank k A = 1 := by
    have h := p.finrank_range_add_finrank_ker
    rw [he.linearMap_ker_eq,LinearMap.finrank_range_of_inj hi,hr,hB] at h
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hV.trans ha.symm)).mp hv

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
  (H₁ H₂ : k) (h₁ : H₁ ≠ 0) (h₂ : H₂ ≠ 0)

lemma VAction_injective (a : ℤ) : Function.Injective
    (VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) a) := by
  have he := VAction_first q hq hp H₁ H₂ h₁ h₂
  have hh := congrArg (fun f => VectorSplit.Hmap f a) he
  rw [VectorSplit.Hmap_comp,VectorSplit.Hmap_id] at hh
  intro x y hxy
  have hx := LinearMap.congr_fun hh x
  have hy := LinearMap.congr_fun hh y
  rw [LinearMap.comp_apply,LinearMap.id_apply] at hx hy
  exact hx.symm.trans ((congrArg (VectorSplit.Hmap (FFirst q hq hp H₁ H₂ h₁ h₂) a) hxy).trans hy)

lemma VAction_zero_surjective : Function.Surjective
    (VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) 0) := by
  let em := (LinearEquiv.ofBijective (middleHpairX q H₁ H₂ h₁ h₂ 0)
    (middleHpairX_bijective q H₁ H₂ h₁ h₂ 0)).trans
      ((selfHomZeroEquiv q hq hp).prodCongr (selfHomZeroEquiv q hq hp))
  let ey := (zeroHomEquiv q (Enveloping.evalObj (xObj q) (Y q).obj)).trans (WZeroEquiv q hq hp)
  have hs := FHom_shortExact q hq hp H₁ H₂ h₁ h₂
  exact exact_line_surjective
    (VectorSplit.Hmap (FHomInclusion q hq hp H₁ H₂ h₁ h₂) 0)
    (VectorSplit.Hmap (FHomProjection q hq hp H₁ H₂ h₁ h₂) 0)
    (FHomInclusion_injective q hq hp H₁ H₂ h₁ h₂ 0 (by decide) (by decide))
    (FHomProjection_zero_surjective q hq hp H₁ H₂ h₁ h₂)
    (VectorSplit.Hmap_exact _ _ hs.1 hs.2.1 hs.2.2 0)
    em ey (selfHomZeroEquiv q hq hp) _ (VAction_injective q hq hp H₁ H₂ h₁ h₂ 0)

lemma delta_zero_surjective : Function.Surjective (delta q hq hp H₁ H₂ h₁ h₂ 0) := by
  intro x
  obtain ⟨y,hy⟩ := VAction_zero_surjective q hq hp H₁ H₂ h₁ h₂ x
  refine ⟨(0,y),?_⟩
  change VectorSplit.Hmap (FAction q hq hp H₁ H₂ h₁ h₂) 0 0 +
    VectorSplit.Hmap (VAction q hq hp H₁ H₂ h₁ h₂) 0 y = x
  rw [map_zero,zero_add,hy]

end Construction
namespace SourceField
open Construction

theorem sourceDelta_vanishing_ranges (a : ℤ) (ha : 0 < a ∨ a ≤ -2) :
    Function.Injective (sourceDelta a) ∧ Function.Surjective (sourceDelta (a-1)) := by
  constructor
  · by_cases h2 : a = -2
    · subst a
      exact delta_minusTwo_injective _ _ _ _ _ _ _
    · exact (sourceDelta_bijective a (by omega)).1
  · by_cases h1 : a = 1
    · subst a
      exact delta_zero_surjective _ _ _ _ _ _ _
    · exact (sourceDelta_bijective (a-1) (by omega)).2
end SourceField
end Tachikawa

end

end OAI
