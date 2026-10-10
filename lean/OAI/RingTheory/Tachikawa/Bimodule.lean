import OAI.RingTheory.Tachikawa.ReverseResolution

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace ModuleFiber
variable {K L : ChainComplex (ModuleCat R) ℤ} (f : K ⟶ L)

def obj (_f : K ⟶ L) (j : ℤ) : ModuleCat R := ModuleCat.of R (L.X (j+1) × K.X j)

def differential (j : ℤ) : obj f (j+1) ⟶ obj f j :=
  ModuleCat.ofHom <|
    (((L.d (j+1+1) (j+1)).hom.comp (LinearMap.fst R _ _) +
        (f.f (j+1)).hom.comp (LinearMap.snd R _ _)).prod
      (-((K.d (j+1) j).hom.comp (LinearMap.snd R _ _))))

lemma differential_apply (j : ℤ) (x : obj f (j+1)) :
    differential f j x = (L.d (j+1+1) (j+1) x.1 + f.f (j+1) x.2,
      -K.d (j+1) j x.2) := rfl

lemma differential_comp (j : ℤ) : differential f (j+1) ≫ differential f j = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change L.d (j+1+1) (j+1) (L.d (j+1+1+1) (j+1+1) x.1 +
        f.f (j+1+1) x.2) + f.f (j+1) (-K.d (j+1+1) (j+1) x.2) = 0
    rw [map_add, map_neg]
    have hz := congrArg (fun a : L.X (j+1+1+1) ⟶ L.X (j+1) => a x.1)
      (L.d_comp_d (j+1+1+1) (j+1+1) (j+1))
    have hc := congrArg (fun a : K.X (j+1+1) ⟶ L.X (j+1) => a x.2)
      (f.comm (j+1+1) (j+1))
    change L.d (j+1+1) (j+1) (L.d (j+1+1+1) (j+1+1) x.1) = 0 at hz
    change L.d (j+1+1) (j+1) (f.f (j+1+1) x.2) =
      f.f (j+1) (K.d (j+1+1) (j+1) x.2) at hc
    rw [hz, zero_add, hc, add_neg_cancel]
  · change -K.d (j+1) j (-K.d (j+1+1) (j+1) x.2) = 0
    rw [map_neg, neg_neg]
    exact congrArg (fun a : K.X (j+1+1) ⟶ K.X j => a x.2)
      (K.d_comp_d (j+1+1) (j+1) j)

def complex : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (obj f) (differential f) (differential_comp f)

@[simp] lemma complex_d (j : ℤ) : (complex f).d (j+1) j = differential f j :=
  ChainComplex.of_d _ _ j

lemma differential_exact [QuasiIso f] (j : ℤ) :
    Function.Exact (differential f (j+1)) (differential f j) := by
  have hqi (n : ℤ) := (quasiIsoAt_iff' f (n+1) n (n-1) (by simp) (by simp)).mp
    (inferInstance : QuasiIsoAt f n)
  have hc (n : ℤ) := shortComplex_cycles_of_quasiIso _ (hqi n)
  intro x
  constructor
  · intro hx
    have hx₁ : L.d (j+1+1) (j+1) x.1 + f.f (j+1) x.2 = 0 := congrArg Prod.fst hx
    have hx₂ : K.d (j+1) j x.2 = 0 := neg_eq_zero.mp (congrArg Prod.snd hx)
    have hx₂' : K.d (j+1) (j+1-1) x.2 = 0 := by
      rw [show j+1-1 = j by omega]
      exact hx₂
    obtain ⟨s,hs⟩ := (hc (j+1)).1 x.2 hx₂' ⟨-x.1, by
      change L.d (j+1+1) (j+1) (-x.1) = f.f (j+1) x.2
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_right hx₁).symm⟩
    change K.X (j+1+1) at s
    change K.d (j+1+1) (j+1) s = x.2 at hs
    have hy : L.d (j+1+1) (j+1+1-1) (x.1 + f.f (j+1+1) s) = 0 := by
      rw [show j+1+1-1 = j+1 by omega, map_add]
      have hh := congrArg (fun a : K.X (j+1+1) ⟶ L.X (j+1) => a s)
        (f.comm (j+1+1) (j+1))
      change L.d (j+1+1) (j+1) (f.f (j+1+1) s) =
        f.f (j+1) (K.d (j+1+1) (j+1) s) at hh
      rw [hh, hs]
      exact hx₁
    obtain ⟨t,ht,u,hu⟩ := (hc (j+1+1)).2 (x.1 + f.f (j+1+1) s) hy
    change K.X (j+1+1) at t
    change L.X (j+1+1+1) at u
    change K.d (j+1+1) (j+1+1-1) t = 0 at ht
    rw [show j+1+1-1 = j+1 by omega] at ht
    change L.d (j+1+1+1) (j+1+1) u =
      f.f (j+1+1) t - (x.1 + f.f (j+1+1) s) at hu
    refine ⟨(-u,-s+t), ?_⟩
    apply Prod.ext
    · change L.d (j+1+1+1) (j+1+1) (-u) + f.f (j+1+1) (-s+t) = x.1
      rw [map_neg, map_add, map_neg, hu]
      abel
    · change -K.d (j+1+1) (j+1) (-s+t) = x.2
      rw [map_add,map_neg,hs,ht,add_zero,neg_neg]
  · rintro ⟨y,rfl⟩
    exact congrArg (fun a : obj f (j+1+1) ⟶ obj f j => a y) (differential_comp f j)

lemma exact [QuasiIso f] : ComplexExact (complex f) := by
  intro j
  obtain ⟨i,rfl⟩ : ∃ i : ℤ, j = i+1 := ⟨j-1, by omega⟩
  rw [show i+1-1 = i by omega, complex_d, complex_d]
  exact differential_exact f i

lemma totallyAcyclic [QuasiIso f] [Module.Injective R R] : TotallyAcyclic (complex f) := by
  refine ⟨exact f, ?_⟩
  intro j g hg
  obtain ⟨h,hh⟩ := Module.Injective.extension_property R R
    (CokerAt (complex f) j) ((complex f).X (j-1))
    (CokerAt.ι (complex f) j) (CokerAt.ι_injective _ _ (exact f j))
    (CokerAt.descend _ _ g hg)
  refine ⟨h, ?_⟩
  have hh' := congrArg (fun a => a.comp (CokerAt.π (complex f) j)) hh
  simpa only [LinearMap.comp_assoc, CokerAt.ι_comp_π, CokerAt.descend_comp_π] using hh'

end ModuleFiber
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma forwardJ_finite (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Finite k ((forwardJ q hp).X j) := by
  cases j with
  | ofNat n => exact C.inducedObj_finite q n
  | negSucc n =>
    change Module.Finite k ((TrivialInduction.functor (k := k)).obj (ModuleCat.of (C k q) PUnit))
    have : Subsingleton ((TrivialInduction.functor (k := k)).obj (ModuleCat.of (C k q) PUnit)) :=
      ModuleCat.subsingleton_of_isZero <| (TrivialInduction.functor (k := k)).map_isZero
        (ModuleCat.isZero_of_subsingleton _)
    infer_instance

lemma forwardJ_projective (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Projective (C.T q) ((forwardJ q hp).X j) := by
  cases j with
  | ofNat n => exact C.inducedObj_projective q n
  | negSucc n =>
    change Module.Projective (C.T q) (TrivialInduction.Obj k (C k q) (ModuleCat.of (C k q) PUnit))
    infer_instance

omit [CharP k 2] in
lemma reverseObj_finite (j : ℤ) : Module.Finite k (C.reverseObj q j) := by
  let : Module.Finite k (C.Ce q) := Module.Finite.of_injective
    ((C.Ce q).subtype.restrictScalars k) Subtype.val_injective
  let : Module.Finite k (C.Cf q) := Module.Finite.of_injective
    ((C.Cf q).subtype.restrictScalars k) Subtype.val_injective
  let : Module.Finite (C k q) (C.Ce q) := Module.Finite.of_restrictScalars_finite k _ _
  let : Module.Finite (C k q) (C.Cf q) := Module.Finite.of_restrictScalars_finite k _ _
  have hE : Module.Finite (C k q) (ModuleCat.of (C k q) (C.Ce q)) := inferInstance
  have hF : Module.Finite (C k q) (ModuleCat.of (C k q) (C.Cf q)) := inferInstance
  have hf : Module.Finite (C k q) (C.reverseObj q j) := by
    cases j with
    | ofNat n =>
      rcases n with _ | _ | _ | n
      · exact hE
      · exact hE
      · exact hF
      · exact inferInstanceAs (Module.Finite (C k q) PUnit)
    | negSucc n => exact hE
  exact Module.Finite.trans (C k q) (C.reverseObj q j)

omit [CharP k 2] in
lemma reverseObj_projective (j : ℤ) : Module.Projective (C k q) (C.reverseObj q j) := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | _ | n
    · exact inferInstanceAs (Module.Projective (C k q) (C.Ce q))
    · exact inferInstanceAs (Module.Projective (C k q) (C.Ce q))
    · exact inferInstanceAs (Module.Projective (C k q) (C.Cf q))
    · exact inferInstanceAs (Module.Projective (C k q) PUnit)
  | negSucc n => exact inferInstanceAs (Module.Projective (C k q) (C.Ce q))

lemma reverseJ_finite (hq : q ≠ 0) (j : ℤ) :
    Module.Finite k ((reverseJ q hq).X j) := by
  let := reverseObj_finite q j
  have : Module.Finite k (TrivialInduction.Obj k (C k q) (C.reverseObj q j)) := inferInstance
  let : Module.Finite (C.T q) (TrivialInduction.Obj k (C k q) (C.reverseObj q j)) :=
    Module.Finite.of_restrictScalars_finite k _ _
  have : Module.Finite (C.T q) ((reverseJ q hq).X j) := by
    change Module.Finite (C.T q) (TrivialInduction.Obj k (C k q) (C.reverseObj q j))
    infer_instance
  exact Module.Finite.trans (C.T q) ((reverseJ q hq).X j)

lemma reverseJ_projective (hq : q ≠ 0) (j : ℤ) :
    Module.Projective (C.T q) ((reverseJ q hq).X j) := by
  let := reverseObj_finite q j
  let : Module.Finite (C k q) (C.reverseObj q j) := Module.Finite.of_restrictScalars_finite k _ _
  let := reverseObj_projective q j
  change Module.Projective (C.T q) (TrivialInduction.Obj k (C k q) (C.reverseObj q j))
  infer_instance

lemma forwardJ_below (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) (hj : j < 0) :
    IsZero ((forwardJ q hp).X j) := by
  cases j with
  | ofNat n => change (n : ℤ) < 0 at hj; omega
  | negSucc n =>
    exact (TrivialInduction.functor (k := k)).map_isZero
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of (C k q) PUnit))

lemma reverseJ_above (hq : q ≠ 0) (j : ℤ) (hj : 2 < j) :
    IsZero ((reverseJ q hq).X j) := by
  cases j with
  | ofNat n =>
    change 2 < (n : ℤ) at hj
    rcases n with _ | _ | _ | n
    · norm_num at hj
    · norm_num at hj
    · norm_num at hj
    · exact (TrivialInduction.functor (k := k)).map_isZero
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of (C k q) PUnit))
  | negSucc n => change 2 < -((n : ℤ)+1) at hj; omega

lemma forwardJJ_finite (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Finite (E q) ((forwardJJ q hp).X j) :=
  OuterTensor.total_finite_below_int _ _ 0 0 (forwardJ_finite q hp) (forwardJ_finite q hp)
    (forwardJ_below q hp) (forwardJ_below q hp) j

lemma reverseJJ_finite (hq : q ≠ 0) (j : ℤ) :
    Module.Finite (E q) ((reverseJJ q hq).X j) :=
  OuterTensor.total_finite_above_int _ _ 2 2 (reverseJ_finite q hq) (reverseJ_finite q hq)
    (reverseJ_above q hq) (reverseJ_above q hq) j

lemma forwardJJ_projective (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Projective (E q) ((forwardJJ q hp).X j) := by
  have h (i : ℤ) : Module.Finite (C.T q) ((forwardJ q hp).X i) := by
    let := forwardJ_finite q hp i
    exact Module.Finite.of_restrictScalars_finite k _ _
  let := OuterTensor.total_projective_int (k := k) _ _ h h (forwardJ_projective q hp) (forwardJ_projective q hp) j
  infer_instance

lemma reverseJJ_projective (hq : q ≠ 0) (j : ℤ) :
    Module.Projective (E q) ((reverseJJ q hq).X j) := by
  have h (i : ℤ) : Module.Finite (C.T q) ((reverseJ q hq).X i) := by
    let := reverseJ_finite q hq i
    exact Module.Finite.of_restrictScalars_finite k _ _
  let := OuterTensor.total_projective_int (k := k) _ _ h h (reverseJ_projective q hq) (reverseJ_projective q hq) j
  infer_instance

def jjFiber (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ChainComplex (ModuleCat (E q)) ℤ := ModuleFiber.complex (jjReverseComparison q hq hp)

lemma jjFiber_totallyAcyclic (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    TotallyAcyclic (jjFiber q hq hp) := by
  let := jjReverseComparison_quasiIso q hq hp
  let := (formE q).injective
  exact ModuleFiber.totallyAcyclic _

lemma jjFiber_finite (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Finite (E q) ((jjFiber q hq hp).X j) := by
  let := forwardJJ_finite q hp j
  let := reverseJJ_finite q hq (j+1)
  exact inferInstanceAs (Module.Finite (E q) ((reverseJJ q hq).X (j+1) × (forwardJJ q hp).X j))

lemma jjFiber_projective (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (j : ℤ) :
    Module.Projective (E q) ((jjFiber q hq hp).X j) := by
  let := forwardJJ_projective q hp j
  let := reverseJJ_projective q hq (j+1)
  exact inferInstanceAs (Module.Projective (E q) ((reverseJJ q hq).X (j+1) × (forwardJJ q hp).X j))

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace HomBimodule
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R) (Z : ModuleCat S)

def Base : Type := X →ₗ[k] Z
instance : CoeFun (Base (k := k) X Z) (fun _ => X → Z) := ⟨fun f => (show X →ₗ[k] Z from f)⟩
instance : AddCommGroup (Base (k := k) X Z) := inferInstanceAs (AddCommGroup (X →ₗ[k] Z))
instance : Module k (Base (k := k) X Z) := inferInstanceAs (Module k (X →ₗ[k] Z))
instance : Module S (Base (k := k) X Z) := inferInstanceAs (Module S (X →ₗ[k] Z))
instance : IsScalarTower k S (Base (k := k) X Z) :=
  inferInstanceAs (IsScalarTower k S (X →ₗ[k] Z))

def rightAction : Rᵐᵒᵖ →+* Module.End S (Base (k := k) X Z) where
  toFun r :=
    { toFun := fun f => (show X →ₗ[k] Z from f).comp ((Algebra.lsmul k k X) r.unop)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    exact congrArg f (one_smul R x)
  map_mul' r s := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    exact congrArg f (mul_smul s.unop r.unop x)
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    change f ((0:R) • x) = 0
    exact (congrArg f (zero_smul R x)).trans (show X →ₗ[k] Z from f).map_zero
  map_add' r s := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    exact (congrArg f (add_smul r.unop s.unop x)).trans (f.map_add _ _)

instance : Module Rᵐᵒᵖ (Base (k := k) X Z) := Module.compHom _ (rightAction (k := k) X Z)
instance : SMulCommClass S Rᵐᵒᵖ (Base (k := k) X Z) where
  smul_comm _ _ _ := rfl
instance : IsScalarTower k Rᵐᵒᵖ (Base (k := k) X Z) :=
  IsScalarTower.of_algebraMap_smul fun c f => by
    apply LinearMap.ext
    intro x
    change f ((algebraMap k R c) • x) = c • f x
    rw [IsScalarTower.algebraMap_smul]
    exact f.map_smul c x

def obj : ModuleCat (Enveloping.Alg k S R) :=
  Enveloping.ofBimodule (k := k) (R := S) (S := R) (Base (k := k) X Z)

lemma tmul_smul_apply (s : S) (r : Rᵐᵒᵖ) (f : obj (k := k) X Z) (x : X) :
    (show X →ₗ[k] Z from ((s ⊗ₜ[k] r) • f)) x =
      s • (show X →ₗ[k] Z from f) (r.unop • x) := rfl

lemma left_smul_apply (s : S) (f : Enveloping.Obj (obj (k := k) X Z)) (x : X) :
    (show X →ₗ[k] Z from (s • f)) x = s • (show X →ₗ[k] Z from f) x := by
  change s • (show X →ₗ[k] Z from f) ((1:R) • x) = _
  rw [one_smul]

lemma right_smul_apply (r : Rᵐᵒᵖ) (f : Enveloping.Obj (obj (k := k) X Z)) (x : X) :
    (show X →ₗ[k] Z from (r • f)) x = (show X →ₗ[k] Z from f) (r.unop • x) := by
  change (1:S) • (show X →ₗ[k] Z from f) (r.unop • x) = _
  rw [one_smul]

lemma k_smul_apply (c : k) (f : obj (k := k) X Z) (x : X) :
    (show X →ₗ[k] Z from (c • f)) x = c • (show X →ₗ[k] Z from f) x := by
  change (show X →ₗ[k] Z from ((algebraMap k (Enveloping.Alg k S R) c) • f)) x = _
  change (show X →ₗ[k] Z from (((algebraMap k S c) ⊗ₜ[k] (1:Rᵐᵒᵖ)) • f)) x = _
  apply Eq.trans (tmul_smul_apply X Z (algebraMap k S c) 1 f x)
  exact (congrArg (fun y : X => (algebraMap k S c) • (show X →ₗ[k] Z from f) y)
    (one_smul R x)).trans (IsScalarTower.algebraMap_smul S c ((show X →ₗ[k] Z from f) x))

end HomBimodule



namespace BimoduleTensorHom
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {M : ModuleCat (Enveloping.Alg k S R)} {X : ModuleCat R} {Z : ModuleCat S}

def uncurryLinear (f : M ⟶ HomBimodule.obj (k := k) X Z) :
    Enveloping.Obj M →ₗ[S] (X →ₗ[k] Z) where
  toFun := fun m => f m
  map_add' a b := f.hom.map_add a b
  map_smul' s m := by
    apply LinearMap.ext
    intro x
    exact (congrArg (fun h : Enveloping.Obj (HomBimodule.obj (k := k) X Z) =>
      (show X →ₗ[k] Z from h) x) ((Enveloping.leftMap f).map_smul s m)).trans
        (HomBimodule.left_smul_apply X Z s (f m) x)

lemma uncurryLinear_balanced (f : M ⟶ HomBimodule.obj (k := k) X Z)
    (r : R) (m : Enveloping.Obj M) (x : X) :
    uncurryLinear f (MulOpposite.op r • m) x = uncurryLinear f m (r • x) :=
  (congrArg (fun h : Enveloping.Obj (HomBimodule.obj (k := k) X Z) =>
      (show X →ₗ[k] Z from h) x) ((Enveloping.rightMap f).map_smul (MulOpposite.op r) m)).trans
    (HomBimodule.right_smul_apply X Z (MulOpposite.op r) (f m) x)

def uncurry (f : M ⟶ HomBimodule.obj (k := k) X Z) : Enveloping.evalObj X M ⟶ Z :=
  ModuleCat.ofHom (BalancedTensor.lift (uncurryLinear f) (uncurryLinear_balanced f))

@[simp] lemma uncurry_mk (f : M ⟶ HomBimodule.obj (k := k) X Z)
    (m : Enveloping.Obj M) (x : X) :
    uncurry f (BalancedTensor.mk m x) = (show X →ₗ[k] Z from f m) x := rfl

def curryLinear (g : Enveloping.evalObj X M ⟶ Z) :
    Enveloping.Obj M →ₗ[S] HomBimodule.Base (k := k) X Z where
  toFun m := (g.hom.restrictScalars k).comp (BalancedTensor.mk m)
  map_add' m n := by
    apply LinearMap.ext
    intro x
    change g (BalancedTensor.mk (m+n) x) = g (BalancedTensor.mk m x) + g (BalancedTensor.mk n x)
    exact (congrArg g (congrArg (fun h : X →ₗ[k] Enveloping.evalType X M => h x)
      ((BalancedTensor.mk (k := k) (R := R) (S := S) (M := Enveloping.Obj M) (N := X)).map_add m n))).trans
      (g.hom.map_add _ _)
  map_smul' s m := by
    apply LinearMap.ext
    intro x
    change g (BalancedTensor.mk (s • m) x) = s • g (BalancedTensor.mk m x)
    exact (congrArg g (congrArg (fun h : X →ₗ[k] Enveloping.evalType X M => h x)
      ((BalancedTensor.mk (k := k) (R := R) (S := S) (M := Enveloping.Obj M) (N := X)).map_smul s m))).trans
      (g.hom.map_smul s _)

lemma curryLinear_right (g : Enveloping.evalObj X M ⟶ Z) (r : Rᵐᵒᵖ) (m : Enveloping.Obj M) :
    curryLinear g (r • m) = r • curryLinear g m := by
  apply LinearMap.ext
  intro x
  change g (BalancedTensor.mk (r • m) x) = g (BalancedTensor.mk m (r.unop • x))
  exact congrArg g (BalancedTensor.balance r.unop m x)

def curry (g : Enveloping.evalObj X M ⟶ Z) : M ⟶ HomBimodule.obj (k := k) X Z :=
  (Enveloping.reassembleIso M).inv ≫
    Enveloping.ofBimoduleHom (curryLinear g) (curryLinear_right g)

@[simp] lemma curry_apply (g : Enveloping.evalObj X M ⟶ Z) (m : M) (x : X) :
    (show X →ₗ[k] Z from curry g m) x = g (BalancedTensor.mk (show Enveloping.Obj M from m) x) := rfl

lemma uncurry_curry (g : Enveloping.evalObj X M ⟶ Z) : uncurry (curry g) = g := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  rfl

lemma curry_uncurry (f : M ⟶ HomBimodule.obj (k := k) X Z) : curry (uncurry f) = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  rfl

def equiv : (M ⟶ HomBimodule.obj (k := k) X Z) ≃ₗ[k] (Enveloping.evalObj X M ⟶ Z) where
  toFun := uncurry
  invFun := curry
  left_inv := curry_uncurry
  right_inv := uncurry_curry
  map_add' f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    exact HomBimodule.k_smul_apply X Z c (f m) x

lemma uncurry_precompose {N : ModuleCat (Enveloping.Alg k S R)}
    (a : N ⟶ M) (f : M ⟶ HomBimodule.obj (k := k) X Z) :
    uncurry (a ≫ f) = Enveloping.evalMap X a ≫ uncurry f := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  rfl

end BimoduleTensorHom
end Tachikawa



namespace Tachikawa.HomBimodule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R) {Z Z' : ModuleCat S}

def postLinear (g : Z ⟶ Z') : Base (k := k) X Z →ₗ[S] Base (k := k) X Z' where
  toFun f := (g.hom.restrictScalars k).comp (show X →ₗ[k] Z from f)
  map_add' f h := by
    apply LinearMap.ext
    intro x
    exact g.hom.map_add _ _
  map_smul' s f := by
    apply LinearMap.ext
    intro x
    exact g.hom.map_smul s _

def postMap (g : Z ⟶ Z') : obj (k := k) X Z ⟶ obj (k := k) X Z' :=
  Enveloping.ofBimoduleHom (postLinear X g) (fun _ _ => rfl)

@[simp] lemma postMap_apply (g : Z ⟶ Z') (f : obj (k := k) X Z) (x : X) :
    (show X →ₗ[k] Z' from postMap X g f) x = g ((show X →ₗ[k] Z from f) x) := rfl

lemma postMap_surjective (g : Z ⟶ Z') (hg : Function.Surjective g) :
    Function.Surjective (postMap (k := k) X g) := by
  intro f
  obtain ⟨p, hp⟩ := Module.projective_lifting_property (g.hom.restrictScalars k)
    (show X →ₗ[k] Z' from f) hg
  refine ⟨p, ?_⟩
  exact hp

instance (g : Z ⟶ Z') [Epi g] : Epi (postMap (k := k) X g) :=
  (ModuleCat.epi_iff_surjective _).mpr (postMap_surjective X g ((ModuleCat.epi_iff_surjective g).mp inferInstance))

end Tachikawa.HomBimodule



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
namespace BimoduleTensorHom
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {M : ModuleCat.{0} (Enveloping.Alg k S R)} {X : ModuleCat.{0} R} {Z Z' : ModuleCat.{0} S}

lemma uncurry_postcompose (f : M ⟶ HomBimodule.obj (k := k) X Z) (g : Z ⟶ Z') :
    uncurry (f ≫ HomBimodule.postMap X g) = uncurry f ≫ g := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  rfl

end BimoduleTensorHom
namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R) (M : ModuleCat.{0} (Alg k S R))

instance evaluation_projective [CategoryTheory.Projective M] :
    CategoryTheory.Projective (evalObj X M) where
  factors {Z Z'} f g _ := by
    obtain ⟨h, hh⟩ := CategoryTheory.Projective.factors (BimoduleTensorHom.curry f)
      (HomBimodule.postMap (k := k) X g)
    refine ⟨BimoduleTensorHom.uncurry h, ?_⟩
    rw [← BimoduleTensorHom.uncurry_postcompose, hh, BimoduleTensorHom.uncurry_curry]

end Enveloping
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R)

def homBimoduleFunctor : ModuleCat.{0} S ⥤ ModuleCat.{0} (Enveloping.Alg k S R) where
  obj Z := HomBimodule.obj (k := k) X Z
  map g := HomBimodule.postMap X g
  map_id Z := by ext f; rfl
  map_comp g h := by ext f; rfl

def evaluationAdjunction : Enveloping.evaluation (k := k) (S := S) X ⊣
    homBimoduleFunctor (k := k) (S := S) X :=
  Adjunction.mkOfHomEquiv
  { homEquiv := fun M Z => (BimoduleTensorHom.equiv (M := M) (X := X) (Z := Z)).toEquiv.symm
    homEquiv_naturality_left_symm := by
      intro M M' Z f g
      exact BimoduleTensorHom.uncurry_precompose f g
    homEquiv_naturality_right := by
      intro M Z Z' f g
      apply (BimoduleTensorHom.equiv (M := M) (X := X) (Z := Z')).injective
      change BimoduleTensorHom.uncurry (BimoduleTensorHom.curry (f ≫ g)) =
        BimoduleTensorHom.uncurry (BimoduleTensorHom.curry f ≫ HomBimodule.postMap X g)
      exact (BimoduleTensorHom.uncurry_curry (f ≫ g)).trans
        ((congrArg (fun h => h ≫ g) (BimoduleTensorHom.uncurry_curry f)).symm.trans
          (BimoduleTensorHom.uncurry_postcompose (BimoduleTensorHom.curry f) g).symm) }

end Tachikawa



namespace Tachikawa
open CategoryTheory
variable {R M P N : Type} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
  [AddCommGroup N] [Module R N]

lemma projective_cokernel_of_injective [Module.Injective R M] [Module.Projective R P]
    (i : M →ₗ[R] P) (q : P →ₗ[R] N)
    (hi : Function.Injective i) (hq : Function.Surjective q) (he : Function.Exact i q) :
    Module.Projective R N := by
  let h := linearShortExact i q he hi hq
  have : CategoryTheory.Injective (linearShortComplex i q he).X₁ :=
    show CategoryTheory.Injective (ModuleCat.of R M) from Module.injective_object_of_injective_module R M
  have : Module.Projective R (linearShortComplex i q he).X₂ :=
    show Module.Projective R P from inferInstance
  let s := h.splittingOfInjective
  exact Module.Projective.of_split s.s.hom q (ModuleCat.hom_ext_iff.mp s.s_g)

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R))
  (u : SymmetrizingForm (k := k) (R := S))
  (M : FiniteModule k (Alg k R S))

abbrev envelopingForm : SymmetrizingForm (k := k) (R := Alg k R S) := t.tensor u.op

lemma cosyzygy_left_projective [Module.Projective R (Obj M.obj)] :
    Module.Projective R (Obj (M.cosyzygy (envelopingForm t u)).obj) := by
  let : Module.Finite R (Obj M.obj) := Module.Finite.of_restrictScalars_finite k R _
  let : Module.Injective R R := t.injective
  let : Module.Injective R (Obj M.obj) := injective_of_finite_projective
  let τ := envelopingForm t u
  let J := ModuleCat.of (Alg k R S) (Fin (Module.finrank k M) → Alg k R S)
  let : Module.Projective R (Obj J) := freeLeftProjective _
  let i : M.obj ⟶ J := ModuleCat.ofHom (M.embed τ)
  let q : J ⟶ (M.cosyzygy τ).obj := ModuleCat.ofHom (LinearMap.range (M.embed τ)).mkQ
  apply projective_cokernel_of_injective (leftMap i) (leftMap q)
  · exact M.embed_injective τ
  · change Function.Surjective (Submodule.mkQ (LinearMap.range (M.embed τ)))
    exact Submodule.mkQ_surjective _
  · change Function.Exact (M.embed τ) (Submodule.mkQ (LinearMap.range (M.embed τ)))
    intro x
    exact Submodule.Quotient.mk_eq_zero _

lemma cosyzygy_right_projective [Module.Projective Sᵐᵒᵖ (Obj M.obj)] :
    Module.Projective Sᵐᵒᵖ (Obj (M.cosyzygy (envelopingForm t u)).obj) := by
  let : Module.Finite Sᵐᵒᵖ (Obj M.obj) := Module.Finite.of_restrictScalars_finite k Sᵐᵒᵖ _
  let : Module.Injective Sᵐᵒᵖ Sᵐᵒᵖ := u.op.injective
  let : Module.Injective Sᵐᵒᵖ (Obj M.obj) := injective_of_finite_projective
  let τ := envelopingForm t u
  let J := ModuleCat.of (Alg k R S) (Fin (Module.finrank k M) → Alg k R S)
  let : Module.Projective Sᵐᵒᵖ (Obj J) := freeRightProjective _
  let i : M.obj ⟶ J := ModuleCat.ofHom (M.embed τ)
  let q : J ⟶ (M.cosyzygy τ).obj := ModuleCat.ofHom (LinearMap.range (M.embed τ)).mkQ
  apply projective_cokernel_of_injective (rightMap i) (rightMap q)
  · exact M.embed_injective τ
  · change Function.Surjective (Submodule.mkQ (LinearMap.range (M.embed τ)))
    exact Submodule.mkQ_surjective _
  · change Function.Exact (M.embed τ) (Submodule.mkQ (LinearMap.range (M.embed τ)))
    intro x
    exact Submodule.Quotient.mk_eq_zero _

theorem negative_side_projective (n : ℕ)
    [Module.Projective R (Obj M.obj)] [Module.Projective Sᵐᵒᵖ (Obj M.obj)] :
    Module.Projective R (Obj (M.negative (envelopingForm t u) n).obj) ∧
      Module.Projective Sᵐᵒᵖ (Obj (M.negative (envelopingForm t u) n).obj) := by
  induction n with
  | zero => change Module.Projective R (Obj M.obj) ∧ Module.Projective Sᵐᵒᵖ (Obj M.obj)
            exact ⟨inferInstance,inferInstance⟩
  | succ n ih =>
    let := ih.1
    let := ih.2
    exact ⟨cosyzygy_left_projective t u _,cosyzygy_right_projective t u _⟩

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace NatCoker
variable (P : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
abbrev C := P.X (n+1) ⧸ LinearMap.range (P.d (n+2) (n+1)).hom

def π : P.X (n+1) →ₗ[R] C P n := (LinearMap.range (P.d (n+2) (n+1)).hom).mkQ

def ι : C P n →ₗ[R] P.X n :=
  (LinearMap.range (P.d (n+2) (n+1)).hom).liftQ (P.d (n+1) n).hom (by
    rintro x ⟨y,rfl⟩
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (P.d_comp_d (n+2) (n+1) n)) y)

lemma projective_of_contraction [Module.Projective R (P.X n)]
    (a : P.X n →ₗ[R] P.X (n+1)) (b : P.X (n+1) →ₗ[R] P.X (n+2))
    (h : a.comp (P.d (n+1) n).hom + (P.d (n+2) (n+1)).hom.comp b = LinearMap.id) :
    Module.Projective R (C P n) := by
  apply Module.Projective.of_split (ι P n) ((π P n).comp a)
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n+2) (n+1)).hom) x
  change π P n (a (P.d (n+1) n y)) = π P n y
  have he := congrArg (π P n) (LinearMap.congr_fun h y)
  change π P n (a (P.d (n+1) n y) + P.d (n+2) (n+1) (b y)) = π P n y at he
  rw [map_add] at he
  have hz : π P n (P.d (n+2) (n+1) (b y)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨b y,rfl⟩
  simpa only [hz,add_zero] using he

lemma projective_of_homotopy {Q : ChainComplex (ModuleCat R) ℕ}
    (e : HomotopyEquiv P Q) [Subsingleton (Q.X (n+1))]
    [Module.Projective R (P.X n)] : Module.Projective R (C P n) := by
  let h := e.homotopyHomInvId.symm
  have he := h.comm (n+1)
  rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n+1) n from rfl),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel (n+2) (n+1) from rfl)] at he
  have hz : (e.hom ≫ e.inv).f (n+1) = 0 := by
    apply ModuleCat.hom_ext
    ext x
    change e.inv.f (n+1) (e.hom.f (n+1) x) = 0
    rw [Subsingleton.elim (e.hom.f (n+1) x) 0, map_zero]
  rw [hz,add_zero] at he
  exact projective_of_contraction P n (h.hom n (n+1)).hom (h.hom (n+1) (n+2)).hom
    (ModuleCat.hom_ext_iff.mp he.symm)

end NatCoker
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (φ : R →ₐ[k] S)

abbrev envelopingMap : Alg k R R →ₐ[k] Alg k S S :=
  Algebra.TensorProduct.map φ φ.op

def inducedRegularComplex : ChainComplex (ModuleCat.{0} (Alg k S S)) ℕ :=
  ((AlgebraInduction.functor (envelopingMap φ)).mapHomologicalComplex (.down ℕ)).obj
    (regularResolution (k := k) (R := R)).complex

instance inducedRegularComplex_finite (n : ℕ) :
    FiniteDimensional k ((inducedRegularComplex φ).X n) := by
  change FiniteDimensional k
    ((AlgebraInduction.functor (envelopingMap φ)).obj ((regularResolution (k := k) (R := R)).complex.X n))
  let : FiniteDimensional k ((regularResolution (k := k) (R := R)).complex.X n) :=
    Module.Finite.trans (Alg k R R) _
  infer_instance

instance inducedRegularComplex_finiteAlg (n : ℕ) :
    Module.Finite (Alg k S S) ((inducedRegularComplex φ).X n) :=
  Module.Finite.of_restrictScalars_finite k _ _

instance inducedRegularComplex_projective (n : ℕ) :
    Module.Projective (Alg k S S) ((inducedRegularComplex φ).X n) := by
  change Module.Projective (Alg k S S)
    ((AlgebraInduction.functor (envelopingMap φ)).obj ((regularResolution (k := k) (R := R)).complex.X n))
  infer_instance

instance inducedRegularComplex_leftProjective (n : ℕ) :
    Module.Projective S (Obj ((inducedRegularComplex φ).X n)) := projective_left _

instance inducedRegularComplex_rightProjective (n : ℕ) :
    Module.Projective Sᵐᵒᵖ (Obj ((inducedRegularComplex φ).X n)) := projective_right _

def inducedCokerFive : FiniteModule k (Alg k S S) where
  obj := ModuleCat.of (Alg k S S) (NatCoker.C (inducedRegularComplex φ) 4)
  finite := inferInstance

def inducedY (t : SymmetrizingForm (k := k) (R := S)) : FiniteModule k (Alg k S S) :=
  (inducedCokerFive φ).negative (envelopingForm t t) 4

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)

def restrictionUnderlyingEquiv (X : ModuleCat.{0} S) :
    (AlgebraInduction.res φ).obj X ≃ₗ[k] X where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change φ (algebraMap k R c) • (show X from x) = (algebraMap k S c) • (show X from x)
    rw [φ.commutes]

def homBimoduleRestrictionEquiv (X Z : ModuleCat.{0} S) :
    (AlgebraInduction.res (Enveloping.envelopingMap φ)).obj (HomBimodule.obj (k := k) X Z) ≃ₗ[
      Enveloping.Alg k R R]
        HomBimodule.obj (k := k) ((AlgebraInduction.res φ).obj X) ((AlgebraInduction.res φ).obj Z) where
  toFun f := (restrictionUnderlyingEquiv φ Z).symm.toLinearMap.comp
    ((show X →ₗ[k] Z from f).comp (restrictionUnderlyingEquiv φ X).toLinearMap)
  invFun f := (restrictionUnderlyingEquiv φ Z).toLinearMap.comp
    ((show (AlgebraInduction.res φ).obj X →ₗ[k] (AlgebraInduction.res φ).obj Z from f).comp
      (restrictionUnderlyingEquiv φ X).symm.toLinearMap)
  left_inv f := by apply LinearMap.ext; intro x; rfl
  right_inv f := by apply LinearMap.ext; intro x; rfl
  map_add' f g := by apply LinearMap.ext; intro x; rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro x
    induction a using TensorProduct.inductionOn with
    | tmul r s => rfl
    | add a b ha hb =>
      change (show X →ₗ[k] Z from (Enveloping.envelopingMap φ (a+b)) •
        (show HomBimodule.obj (k := k) X Z from f)) x = _
      simp only [map_add]
      erw [add_smul, add_smul]
      exact congrArg₂ (fun u v => u+v) ha hb

def homBimoduleRestrictionIso (X Z : ModuleCat.{0} S) :
    (AlgebraInduction.res (Enveloping.envelopingMap φ)).obj (HomBimodule.obj (k := k) X Z) ≅
      HomBimodule.obj (k := k) ((AlgebraInduction.res φ).obj X) ((AlgebraInduction.res φ).obj Z) :=
  LinearEquiv.toModuleIso (homBimoduleRestrictionEquiv φ X Z)

def homBimoduleRestriction (X : ModuleCat.{0} S) :
    homBimoduleFunctor (k := k) X ⋙ AlgebraInduction.res (Enveloping.envelopingMap φ) ≅
      AlgebraInduction.res φ ⋙ homBimoduleFunctor (k := k) ((AlgebraInduction.res φ).obj X) :=
  NatIso.ofComponents (homBimoduleRestrictionIso φ X) (by
    intro Z Z' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro x
    rfl)

end Tachikawa



namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

def adjunction (φ : R →ₐ[k] S) : functor φ ⊣ res φ :=
  Adjunction.mkOfHomEquiv
  { homEquiv := homEquiv φ
    homEquiv_naturality_left_symm := by
      intro X X' Y f g
      apply ModuleCat.hom_ext
      apply BalancedTensor.hom_ext
      intro s x
      rfl
    homEquiv_naturality_right := by
      intro X Y Y' f g
      ext x
      rfl }

def compositionIso (φ : R →ₐ[k] S) (ψ : S →ₐ[k] U) :
    functor φ ⋙ functor ψ ≅ functor (ψ.comp φ) := by
  let a := (adjunction φ).comp (adjunction ψ)
  let b := adjunction (ψ.comp φ)
  exact Adjunction.leftAdjointUniq a b

end Tachikawa.AlgebraInduction



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

lemma leftFunctor_eq : leftFunctor (k := k) (R := R) (S := S) =
    ModuleCat.restrictScalars (Algebra.TensorProduct.includeLeft : R →ₐ[k] Alg k R S).toRingHom := rfl
lemma rightFunctor_eq : rightFunctor (k := k) (R := R) (S := S) =
    ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[k] Alg k R S).toRingHom := rfl

lemma leftFunctor_map_exact (T : ShortComplex (ModuleCat (Alg k R S))) (h : T.Exact) :
    (T.map (leftFunctor (k := k) (R := R) (S := S))).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h
lemma rightFunctor_map_exact (T : ShortComplex (ModuleCat (Alg k R S))) (h : T.Exact) :
    (T.map (rightFunctor (k := k) (R := R) (S := S))).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

instance : PreservesFiniteLimits (leftFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (leftFunctor (k := k) (R := R) (S := S))).out 2 4).mp
    (leftFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.1
instance : PreservesFiniteColimits (leftFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (leftFunctor (k := k) (R := R) (S := S))).out 2 4).mp
    (leftFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.2
instance : PreservesFiniteLimits (rightFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (rightFunctor (k := k) (R := R) (S := S))).out 2 4).mp
    (rightFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.1
instance : PreservesFiniteColimits (rightFunctor (k := k) (R := R) (S := S)) := by
  have h := ((Functor.exact_tfae (rightFunctor (k := k) (R := R) (S := S))).out 2 4).mp
    (rightFunctor_map_exact (k := k) (R := R) (S := S))
  exact h.2

end Tachikawa.Enveloping

end

end OAI
