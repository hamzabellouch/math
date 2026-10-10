import OAI.RingTheory.Tachikawa.Period

namespace OAI


noncomputable section
namespace Tachikawa
open scoped TensorProduct
namespace Construction
variable {k : Type*} [Field k] (q : k)

abbrev T := TrivialExtension k (C k q)
abbrev E := T q ⊗[k] T q

def characterT : T q →ₐ[k] k :=
  (C.character q).comp (TrivSqZeroExt.fstHom k (C k q) (DualBimodule k (C k q)))
def characterE : E q →ₐ[k] k :=
  Algebra.TensorProduct.productMap (characterT q) (characterT q)

def formE : SymmetrizingForm (k := k) (R := E q) :=
  TrivialExtension.symmetrizingForm.tensor TrivialExtension.symmetrizingForm

def X (_q : k) := k
instance : AddCommGroup (X q) := inferInstanceAs (AddCommGroup k)
instance : Module k (X q) := inferInstanceAs (Module k k)
instance : Module (E q) (X q) := Module.compHom (X q) (characterE q).toRingHom
instance : IsScalarTower k (E q) (X q) :=
  IsScalarTower.of_algebraMap_smul (R := k) (A := E q) (M := X q) fun r x => by
    change (characterE q (algebraMap k (E q) r)) • x = r • x
    rw [AlgHom.commutes]
    rfl
instance : FiniteDimensional k (X q) := inferInstanceAs (FiniteDimensional k k)
instance : Module.Injective (E q) (E q) := (formE q).injective

@[simp] lemma X_smul (a : E q) (x : X q) : a • x = (characterE q a : k) • x := rfl

def sigma (H : k) (hH : H ≠ 0) : E q ≃ₐ[k] E q :=
  Algebra.TensorProduct.congr (TrivialExtension.scaleDual H hH)
    (TrivialExtension.scaleDual H hH)

@[simp] lemma characterT_scaleDual (H : k) (hH : H ≠ 0) (a : T q) :
    characterT q (TrivialExtension.scaleDual H hH a) = characterT q a := rfl

@[simp] lemma characterE_sigma (H : k) (hH : H ≠ 0) (a : E q) :
    characterE q (sigma q H hH a) = characterE q a := by
  induction a using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

lemma formE_sigma (H : k) (hH : H ≠ 0) (a : E q) :
    (formE q).linear (sigma q H hH a) = H^2 * (formE q).linear a := by
  induction a using TensorProduct.inductionOn with
  | tmul a b =>
    change (H * a.snd 1) * (H * b.snd 1) = H^2 * (a.snd 1 * b.snd 1)
    ring
  | add a b ha hb => simp only [map_add, ha, hb, mul_add]

end Construction
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev sFinite : FiniteModule k (T q) :=
  ⟨C.simpleObj q, Module.Finite.of_restrictScalars_finite k (T q) _⟩
abbrev sResolution := (sFinite q).projectiveResolution
abbrev XTensorObj : ModuleCat (E q) :=
  ((OuterTensor.bifunctor k (T q) (T q)).obj (C.simpleObj q)).obj (C.simpleObj q)

def XExtKunneth (n : ℕ) :
    Ext (XTensorObj q) (XTensorObj q) n ≃ₗ[k]
      (∀ t : TotalDualPairing.Diag n,
        Ext (C.simpleObj q) (C.simpleObj q) t.val.1 ⊗[k]
        Ext (C.simpleObj q) (C.simpleObj q) t.val.2) :=
  OuterTensor.extKunneth (sResolution q) (sResolution q) n

lemma XExt_zero_off_multiples (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) (hn : n % 3 ≠ 0) :
    Subsingleton (Ext (XTensorObj q) (XTensorObj q) n) := by
  have hcomp (t : TotalDualPairing.Diag n) :
      Subsingleton (Ext (C.simpleObj q) (C.simpleObj q) t.val.1 ⊗[k]
        Ext (C.simpleObj q) (C.simpleObj q) t.val.2) := by
    by_cases h : t.val.1 % 3 = 0
    · have h' : t.val.2 % 3 ≠ 0 := by
        have ht := t.property
        omega
      let := C.simpleExt_zero_off_multiples q hq hp t.val.2 h'
      infer_instance
    · let := C.simpleExt_zero_off_multiples q hq hp t.val.1 h
      infer_instance
  let := hcomp
  exact (XExtKunneth q n).injective.subsingleton

lemma XExtThree_nontrivial (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    Nontrivial (Ext (XTensorObj q) (XTensorObj q) 3) := by
  let t : TotalDualPairing.Diag 3 := ⟨(3,0),rfl⟩
  let e := (TensorProduct.congr (C.simpleExtMultiple q hq hp 1)
    (C.simpleExtZeroEquiv q)).trans (TensorProduct.lid k k)
  have ht : Nontrivial (Ext (C.simpleObj q) (C.simpleObj q) t.val.1 ⊗[k]
      Ext (C.simpleObj q) (C.simpleObj q) t.val.2) := e.symm.injective.nontrivial
  let := ht
  have hpi : Nontrivial (∀ t : TotalDualPairing.Diag 3,
      Ext (C.simpleObj q) (C.simpleObj q) t.val.1 ⊗[k]
      Ext (C.simpleObj q) (C.simpleObj q) t.val.2) :=
    Function.Surjective.nontrivial (Function.surjective_eval t)
  let := hpi
  exact (XExtKunneth q 3).symm.injective.nontrivial

lemma XTensor_nonprojective (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ¬ Module.Projective (E q) (XTensorObj q) := by
  intro h
  let := h
  let := XExtThree_nontrivial q hq hp
  have := Ext.subsingleton_of_projective (XTensorObj q) (XTensorObj q) 2
  exact not_subsingleton (Ext (XTensorObj q) (XTensorObj q) 3) ⟨Subsingleton.elim⟩

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

instance simpleTwist_preserves_projective : (C.tTwist q H hH).PreservesProjectiveObjects := by
  have : (C.tTwist q H hH).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      (TrivialExtension.scaleDual (R := C k q) H hH).symm.toRingEquiv
  infer_instance

def simpleResolutionTwistLift : ProjectiveResolution.Hom (sResolution q)
    (mappedResolution (C.tTwist q H hH) (sResolution q)) (C.simpleTwistIso q H hH).inv where
  hom := ProjectiveResolution.lift _ _ _
  hom_f_zero_comp_π_f_zero := ProjectiveResolution.lift_commutes_zero _ _ _

abbrev simpleResolutionTwist := resolutionTwistHom (k := k) (C.tTwist q H hH) (sResolution q)
  (C.simpleTwistIso q H hH) (simpleResolutionTwistLift q H hH).hom

include hq hp in
lemma simpleResolutionTwist_scalar (n : ℕ) :
    (VectorSplit.inclusion (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) ≫
      simpleResolutionTwist q H hH ≫
      VectorSplit.projection (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q))).f n =
        (H⁻¹)^(n/3) • 𝟙 _ := by
  apply resolutionTwistHom_scalar
  intro x
  by_cases hn : n % 3 = 0
  · obtain ⟨m,rfl⟩ := Nat.dvd_of_mod_eq_zero hn
    change C.simpleTwistExt q H hH (3*m) x = _
    rw [C.simpleTwist_weight q H hH hq hp, Nat.mul_div_cancel_left m (by omega : 0<3)]
  · let := C.simpleExt_zero_off_multiples q hq hp n hn
    exact Subsingleton.elim _ _

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev eTwist := OuterTensor.algebraTwist (sigma q H hH)
abbrev XTensorTwistIso := OuterTensor.tensorTwistObjIso
  (TrivialExtension.scaleDual (R := C k q) H hH) (TrivialExtension.scaleDual (R := C k q) H hH)
  (C.simpleTwistIso q H hH) (C.simpleTwistIso q H hH)
abbrev xTensorTwistLift := OuterTensor.tensorTwistLift
  (TrivialExtension.scaleDual (R := C k q) H hH) (TrivialExtension.scaleDual (R := C k q) H hH)
  (sResolution q) (sResolution q) (C.simpleTwistIso q H hH) (C.simpleTwistIso q H hH)
  (simpleResolutionTwistLift q H hH) (simpleResolutionTwistLift q H hH)
abbrev xTensorResolution := OuterTensor.tensorResolution (k := k) (sResolution q) (sResolution q)
abbrev xTensorTwist := resolutionTwistHom (k := k) (eTwist q H hH) (xTensorResolution q)
  (XTensorTwistIso q H hH) (xTensorTwistLift q H hH).hom

include hq hp in
lemma tensorHom_twist_scalar (n : ℕ) :
    homologyMap (mapBifunctorMap (simpleResolutionTwist q H hH) (simpleResolutionTwist q H hH)
      (OuterTensor.tensorF k) (.up ℕ)) n = (H⁻¹)^(n/3) • 𝟙 _ := by
  apply VectorSplit.tensor_homology_scalar _ _ n (fun i => (H⁻¹)^(i/3)) (fun i => (H⁻¹)^(i/3))
    ((H⁻¹)^(n/3)) (simpleResolutionTwist_scalar q H hH hq hp)
    (simpleResolutionTwist_scalar q H hH hq hp)
  intro i j hij
  by_cases hi : i % 3 = 0
  · by_cases hj : j % 3 = 0
    · left
      rw [← pow_add]
      congr 1
      omega
    · right
      let := C.simpleExt_zero_off_multiples q hq hp j hj
      let : Subsingleton (VectorSplit.H
          (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) j) :=
        (resolutionHomologyExtAll (N := C.simpleObj q) (sResolution q) j (k := k)).injective.subsingleton
      change IsZero (ModuleCat.of k (VectorSplit.H
        (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) i ⊗[k]
        VectorSplit.H (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) j))
      exact ModuleCat.isZero_of_subsingleton _
  · right
    let := C.simpleExt_zero_off_multiples q hq hp i hi
    let : Subsingleton (VectorSplit.H
        (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) i) :=
      (resolutionHomologyExtAll (N := C.simpleObj q) (sResolution q) i (k := k)).injective.subsingleton
    change IsZero (ModuleCat.of k (VectorSplit.H
      (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) i ⊗[k]
      VectorSplit.H (resolutionHom k (T q) (sResolution q).complex (C.simpleObj q)) j))
    exact ModuleCat.isZero_of_subsingleton _

include hq hp in
lemma xTensorTwist_homology_scalar (n : ℕ) :
    homologyMap (xTensorTwist q H hH) n = (H⁻¹)^(n/3) • 𝟙 _ := by
  exact homologyMap_scalar_of_intertwine
    (OuterTensor.homTotalIso (k := k) (sResolution q).complex (sResolution q).complex
      (sFinite q).obj (sFinite q).obj) _ _
    (OuterTensor.homTotal_twist (sResolution q) (sResolution q)
      (TrivialExtension.scaleDual (R := C k q) H hH) (TrivialExtension.scaleDual (R := C k q) H hH)
      (C.simpleTwistIso q H hH) (C.simpleTwistIso q H hH)
      (simpleResolutionTwistLift q H hH) (simpleResolutionTwistLift q H hH))
    n _ (tensorHom_twist_scalar q H hH hq hp n)

include hq hp in

lemma XTensorTwist_weight (n : ℕ) (x : Ext (XTensorObj q) (XTensorObj q) n) :
    extIso (k := k) (XTensorTwistIso q H hH) (XTensorTwistIso q H hH) n
      (x.mapExactFunctor (eTwist q H hH)) = (H⁻¹)^(n/3) • x :=
  extTwist_scalar_of_homologyMap (eTwist q H hH) (xTensorResolution q)
    (XTensorTwistIso q H hH) (xTensorTwistLift q H hH) n _
      (xTensorTwist_homology_scalar q H hH hq hp n) x

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q : k)

def sCanon : ModuleCat (T q) := C.simpleObj q

omit [CharP k 2] in
def simpleUnderlying : sCanon q ≃ₗ[k] k where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change characterT q (algebraMap k (T q) c) * (show k from x) = c * (show k from x)
    rw [AlgHom.commutes]
    simp

omit [CharP k 2] in
lemma simpleUnderlying_smul (a : T q) (x : sCanon q) :
    simpleUnderlying q (a • x) = characterT q a * simpleUnderlying q x := rfl

omit [CharP k 2] in
def XTensorUnderlying : OuterTensor.Obj k (T q) (T q) (sCanon q) (sCanon q) ≃ₗ[k] k :=
  (TensorProduct.congr (simpleUnderlying q) (simpleUnderlying q)).trans (TensorProduct.lid k k)

omit [CharP k 2] in
lemma XTensorUnderlying_smul (a : E q)
    (x : OuterTensor.Obj k (T q) (T q) (sCanon q) (sCanon q)) :
    XTensorUnderlying q (a • x) = characterE q a * XTensorUnderlying q x := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [add_smul,map_add,ha,hb,add_mul]
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      erw [smul_add, map_add, hx, hy, map_add, mul_add]
    | tmul x y =>
      change (characterT q a * simpleUnderlying q x) *
        (characterT q b * simpleUnderlying q y) =
        (characterT q a * characterT q b) * (simpleUnderlying q x * simpleUnderlying q y)
      ring

omit [CharP k 2] in

def XTensorEquiv : XTensorObj q ≃ₗ[E q] X q where
  toFun := XTensorUnderlying q
  invFun := (XTensorUnderlying q).symm
  left_inv := (XTensorUnderlying q).left_inv
  right_inv := (XTensorUnderlying q).right_inv
  map_add' := (XTensorUnderlying q).map_add
  map_smul' a x := XTensorUnderlying_smul q a x

omit [CharP k 2] in
def XTensorIso : XTensorObj q ≅ ModuleCat.of (E q) (X q) := (XTensorEquiv q).toModuleIso

def XExt (n : ℕ) : Ext (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) n ≃ₗ[k]
    (∀ t : TotalDualPairing.Diag n,
      Ext (C.simpleObj q) (C.simpleObj q) t.val.1 ⊗[k]
      Ext (C.simpleObj q) (C.simpleObj q) t.val.2) :=
  (extIso (k := k) (XTensorIso q).symm (XTensorIso q).symm n).trans (XExtKunneth q n)

lemma X_nonprojective (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ¬ Module.Projective (E q) (X q) := by
  intro h
  let := h
  have := Module.Projective.of_equiv (XTensorEquiv q).symm
  exact XTensor_nonprojective q hq hp this

lemma XExt_zero (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (hn : n % 3 ≠ 0) :
    Subsingleton (Ext (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) n) := by
  let := XExt_zero_off_multiples q hq hp n hn
  exact (extIso (k := k) (XTensorIso q).symm (XTensorIso q).symm n).injective.subsingleton

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
open scoped ModuleCat.Algebra

lemma extIso_trans {X Y Z X' Y' Z' : ModuleCat R}
    (e : X ≅ Y) (f : Y ≅ Z) (e' : X' ≅ Y') (f' : Y' ≅ Z') (n : ℕ)
    (x : Ext X X' n) :
    extIso (k := k) f f' n (extIso (k := k) e e' n x) = extIso (k := k) (e ≪≫ f) (e' ≪≫ f') n x := by
  simp [extIso]

variable (F : ModuleCat R ⥤ ModuleCat R) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

lemma extIso_map {X Y X' Y' : ModuleCat R} (e : X ≅ Y) (f : X' ≅ Y') (n : ℕ)
    (x : Ext X X' n) :
    (extIso (k := k) e f n x).mapExactFunctor F =
      extIso (k := k) (F.mapIso e) (F.mapIso f) n (x.mapExactFunctor F) := by
  simp only [extIso,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,
    Ext.mapExactFunctor_comp,Ext.mapExactFunctor_mk₀]
  rfl

lemma extTwist_weight_transport {X Y : ModuleCat R} (e : F.obj X ≅ X)
    (u : X ≅ Y) (n : ℕ) (r : k)
    (h : ∀ x : Ext X X n, extIso (k := k) e e n (x.mapExactFunctor F) = r • x)
    (y : Ext Y Y n) :
    extIso (k := k) (F.mapIso u.symm ≪≫ e ≪≫ u) (F.mapIso u.symm ≪≫ e ≪≫ u) n
      (y.mapExactFunctor F) = r • y := by
  obtain ⟨x,rfl⟩ := (extIso (k := k) u u n).surjective y
  rw [extIso_map]
  have hi : F.mapIso u ≪≫ (F.mapIso u.symm ≪≫ e ≪≫ u) = e ≪≫ u := by
    apply Iso.ext
    simp
  rw [extIso_trans,hi,← extIso_trans,h]
  exact (extIso (k := k) u u n).map_smul r x

end Tachikawa



namespace Tachikawa.Construction
open scoped TensorProduct
variable {k : Type} [Field k] (q : k)

def zT : T q := TrivSqZeroExt.inr ((C.character q).toLinearMap : DualBimodule k (C k q))
def pT : T q := TrivSqZeroExt.inl (C.f q)
def zeta : E q := zT q ⊗ₜ[k] zT q
def pE : E q := pT q ⊗ₜ[k] pT q

lemma zT_left (a : T q) : a * zT q = characterT q a • zT q := by
  apply TrivSqZeroExt.ext
  · change a.fst * 0 = characterT q a • (0 : C k q)
    simp
  · apply LinearMap.ext; intro c
    change (C.character q) (c*a.fst) + a.snd ((0:C k q)*c) =
      characterT q a * C.character q c
    simp only [map_mul,zero_mul,map_zero,add_zero]
    exact mul_comm _ _

lemma zT_right (a : T q) : zT q * a = characterT q a • zT q := by
  apply TrivSqZeroExt.ext
  · change 0 * a.fst = characterT q a • (0 : C k q)
    simp
  · apply LinearMap.ext; intro c
    change a.snd (c*(0:C k q)) + (C.character q) (a.fst*c) =
      characterT q a * C.character q c
    simp only [mul_zero,map_zero,zero_add,map_mul]
    rfl

lemma zeta_left (a : E q) : a * zeta q = characterE q a • zeta q := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [add_mul,map_add,add_smul,ha,hb]
  | tmul a b =>
    rw [zeta,Algebra.TensorProduct.tmul_mul_tmul]
    change (a*zT q) ⊗ₜ[k] (b*zT q) = (characterT q a * characterT q b) • (zT q ⊗ₜ[k] zT q)
    rw [zT_left,zT_left,TensorProduct.smul_tmul_smul]

lemma zeta_right (a : E q) : zeta q * a = characterE q a • zeta q := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [mul_add,map_add,add_smul,ha,hb]
  | tmul a b =>
    rw [zeta,Algebra.TensorProduct.tmul_mul_tmul]
    change (zT q*a) ⊗ₜ[k] (zT q*b) = (characterT q a * characterT q b) • (zT q ⊗ₜ[k] zT q)
    rw [zT_right,zT_right,TensorProduct.smul_tmul_smul]

lemma formE_zeta : (formE q).linear (zeta q) = 1 := by
  change C.character q 1 * C.character q 1 = 1
  simp

lemma zeta_ne_zero : zeta q ≠ 0 := by
  intro h
  have h' := formE_zeta q
  rw [h,map_zero] at h'
  exact zero_ne_one h'

lemma characterE_zeta : characterE q (zeta q) = 0 := by
  change (0:k)*0=0
  exact mul_zero _

lemma characterE_pE : characterE q (pE q) = 1 := by
  change C.character q (C.f q) * C.character q (C.f q) = 1
  simp

lemma pE_idempotent : pE q * pE q = pE q := by
  have hp : pT q * pT q = pT q := by
    change TrivSqZeroExt.inl (C.f q) * TrivSqZeroExt.inl (C.f q) = TrivSqZeroExt.inl (C.f q)
    rw [TrivSqZeroExt.inl_mul_inl,C.f_idempotent]
  rw [pE,Algebra.TensorProduct.tmul_mul_tmul]
  change (pT q*pT q) ⊗ₜ[k] (pT q*pT q) = pT q ⊗ₜ[k] pT q
  rw [hp]

def socleEmbedding : X q →ₗ[E q] E q where
  toFun x := (show k from x) • zeta q
  map_add' x y := add_smul _ _ _
  map_smul' a x := by
    change k at x
    change (characterE q a * (show k from x)) • zeta q = a * ((show k from x) • zeta q)
    rw [show a * (x • zeta q) = x • (a * zeta q) from mul_smul_comm x a (zeta q),zeta_left,smul_smul,mul_comm]

lemma socleEmbedding_injective : Function.Injective (socleEmbedding q) := by
  intro x y h
  change k at x y
  have h' := congrArg (formE q).linear h
  change (formE q).linear ((show k from x) • zeta q) =
    (formE q).linear ((show k from y) • zeta q) at h'
  erw [(formE q).linear.map_smul, (formE q).linear.map_smul, formE_zeta] at h'
  change (x : k) = y
  simpa only [smul_eq_mul, mul_one] using h'

def presentation : LeftCorner (pE q) →ₗ[E q] X q where
  toFun a := characterE q a.val
  map_add' a b := map_add _ _ _
  map_smul' a b := by
    change characterE q (a*b.val) = characterE q a * characterE q b.val
    exact map_mul _ _ _

def OmegaX := LinearMap.ker (presentation q)
instance : AddCommGroup (OmegaX q) := inferInstanceAs (AddCommGroup ↥(LinearMap.ker (presentation q)))
instance : Module (E q) (OmegaX q) := inferInstanceAs (Module (E q) ↥(LinearMap.ker (presentation q)))
instance : Module k (OmegaX q) := inferInstanceAs (Module k ↥(LinearMap.ker (presentation q)))
instance : IsScalarTower k (E q) (OmegaX q) := inferInstanceAs (IsScalarTower k (E q) ↥(LinearMap.ker (presentation q)))

lemma socleEmbedding_corner (x : X q) : socleEmbedding q x ∈ LeftCorner (pE q) := by
  change k at x
  change ((show k from x) • zeta q)*pE q = (show k from x) • zeta q
  rw [show (x • zeta q)*pE q = x • (zeta q * pE q) from smul_mul_assoc x (zeta q) (pE q),zeta_right,characterE_pE,one_smul]

def socleInOmega : X q →ₗ[E q] OmegaX q :=
  ((socleEmbedding q).codRestrict (LeftCorner (pE q)) (socleEmbedding_corner q)).codRestrict
    (LinearMap.ker (presentation q)) (fun x => by
      change characterE q ((show k from x) • zeta q) = 0
      rw [map_smul,characterE_zeta,smul_zero])

lemma socleInOmega_ne_zero : socleInOmega q ≠ 0 := by
  intro h
  have h' := LinearMap.congr_fun h (show X q from (1:k))
  have h'' := congrArg (fun x : OmegaX q => x.val.val) h'
  change (1:k) • zeta q = 0 at h''
  rw [one_smul] at h''
  exact zeta_ne_zero q h''

lemma socleInOmega_not_factors : socleInOmega q ∉ projectiveFactors (k := k) := by
  intro h
  obtain ⟨g,hg⟩ := (factors_iff_extends (socleEmbedding q) (socleEmbedding_injective q)
    (socleInOmega q)).mp h
  apply socleInOmega_ne_zero q
  rw [← hg]
  apply LinearMap.ext; intro x
  apply Subtype.ext; apply Subtype.ext
  change (g ((show k from x) • zeta q)).val.val = 0
  have hr : characterE q ((g 1).val.val) = 0 := (g 1).property
  have hgz : (g (zeta q)).val.val = 0 := by
    have hsm := g.map_smul (zeta q) (1:E q)
    have he := congrArg (fun y : OmegaX q => y.val.val) hsm
    change (g (zeta q*1)).val.val = zeta q * (g 1).val.val at he
    rw [mul_one,zeta_right,hr,zero_smul] at he
    exact he
  rw [g.map_smul_of_tower]
  change (show k from x) • (g (zeta q)).val.val = 0
  rw [hgz,smul_zero]

lemma socleInOmega_stable_ne_zero : stableClass (k := k) (socleInOmega q) ≠ 0 := by
  rw [ne_eq,stableClass_eq_zero_iff]
  exact socleInOmega_not_factors q

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

lemma scaleDual_zT : TrivialExtension.scaleDual H hH (zT q) = H • zT q := by
  apply TrivSqZeroExt.ext
  · change (0 : C k q) = H • (0 : C k q)
    rw [smul_zero]
  · rfl

lemma sigma_zeta : sigma q H hH (zeta q) = H^2 • zeta q := by
  change TrivialExtension.scaleDual H hH (zT q) ⊗ₜ[k]
    TrivialExtension.scaleDual H hH (zT q) = H^2 • (zT q ⊗ₜ[k] zT q)
  rw [scaleDual_zT,TensorProduct.smul_tmul_smul,pow_two]

lemma sigma_pE : sigma q H hH (pE q) = pE q := by
  change TrivialExtension.scaleDual H hH (TrivSqZeroExt.inl (C.f q)) ⊗ₜ[k]
    TrivialExtension.scaleDual H hH (TrivSqZeroExt.inl (C.f q)) = _
  rw [TrivialExtension.scaleDual_inl]
  rfl

abbrev twistE : ModuleCat (E q) ⥤ ModuleCat (E q) :=
  AlgebraInduction.res (sigma q H hH).symm.toAlgHom

def presentationTwistComparison : (twistE q H hH).obj (ModuleCat.of (E q) (LeftCorner (pE q))) ⟶
    ModuleCat.of (E q) (LeftCorner (pE q)) := ModuleCat.ofHom
  (X := (twistE q H hH).obj (ModuleCat.of (E q) (LeftCorner (pE q))))
  (Y := ModuleCat.of (E q) (LeftCorner (pE q))) {
  toFun x := ⟨sigma q H hH x.val, by
    change sigma q H hH x.val * pE q = sigma q H hH x.val
    calc
      _ = sigma q H hH x.val * sigma q H hH (pE q) :=
        congrArg (sigma q H hH x.val * ·) (sigma_pE q H hH).symm
      _ = sigma q H hH (x.val * pE q) := (map_mul _ _ _).symm
      _ = sigma q H hH x.val := congrArg (sigma q H hH) x.property⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := by
    apply Subtype.ext
    change sigma q H hH ((sigma q H hH).symm a * x.val) =
      a * sigma q H hH x.val
    rw [map_mul,AlgEquiv.apply_symm_apply] }

def XTwistComparison : (twistE q H hH).obj (ModuleCat.of (E q) (X q)) ⟶
    ModuleCat.of (E q) (X q) := ModuleCat.ofHom
  (X := (twistE q H hH).obj (ModuleCat.of (E q) (X q)))
  (Y := ModuleCat.of (E q) (X q)) {
  toFun := id
  map_add' _ _ := rfl
  map_smul' a x := by
    change characterE q ((sigma q H hH).symm a) * (show k from x) =
      characterE q a * (show k from x)
    have hc := characterE_sigma q H hH ((sigma q H hH).symm a)
    rw [AlgEquiv.apply_symm_apply] at hc
    rw [hc] }

lemma presentationTwist_commutes :
    presentationTwistComparison q H hH ≫ ModuleCat.ofHom (presentation q) =
      (twistE q H hH).map (ModuleCat.ofHom (presentation q)) ≫ XTwistComparison q H hH := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact characterE_sigma q H hH x.val

def OmegaTwistComparison : (twistE q H hH).obj (ModuleCat.of (E q) (OmegaX q)) ⟶
    ModuleCat.of (E q) (OmegaX q) := ModuleCat.ofHom
  (X := (twistE q H hH).obj (ModuleCat.of (E q) (OmegaX q)))
  (Y := ModuleCat.of (E q) (OmegaX q)) {
  toFun x := ⟨presentationTwistComparison q H hH x.val, by
    change characterE q (sigma q H hH x.val.val) = 0
    rw [characterE_sigma]
    exact x.property⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    exact (presentationTwistComparison q H hH).hom.map_smul a x.val }

lemma socle_twist_weight :
    (twistE q H hH).map (ModuleCat.ofHom (socleInOmega q)) ≫ OmegaTwistComparison q H hH =
      XTwistComparison q H hH ≫ ModuleCat.ofHom ((H^2) • socleInOmega q) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change sigma q H hH ((show k from x) • zeta q) =
    H^2 • ((show k from x) • zeta q)
  rw [map_smul,sigma_zeta,smul_smul,smul_smul,mul_comm]

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

def XTwistIso : (twistE q H hH).obj (ModuleCat.of (E q) (X q)) ≅ ModuleCat.of (E q) (X q) :=
  (eTwist q H hH).mapIso (XTensorIso q).symm ≪≫ XTensorTwistIso q H hH ≪≫ XTensorIso q

omit [CharP k 2] in
lemma XTwistIso_hom : (XTwistIso q H hH).hom = XTwistComparison q H hH := by
  apply (cancel_epi ((eTwist q H hH).map (XTensorIso q).hom)).1
  simp only [XTwistIso,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,
    ← Functor.map_comp_assoc,Iso.hom_inv_id]
  rw [(eTwist q H hH).map_id,Category.id_comp]
  apply (cancel_epi (OuterTensor.twistObjIso
    (TrivialExtension.scaleDual (R := C k q) H hH)
    (TrivialExtension.scaleDual (R := C k q) H hH)
    (C.simpleObj q) (C.simpleObj q)).hom).1
  change _ ≫ ((_ ≫ _) ≫ _) = _
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
      (map_add _ x y).symm)

lemma XTwist_weight (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (x : Ext (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) n) :
    extIso (k := k) (XTwistIso q H hH) (XTwistIso q H hH) n
      (x.mapExactFunctor (twistE q H hH)) = (H⁻¹)^(n/3) • x :=
  extTwist_weight_transport (eTwist q H hH) (XTensorTwistIso q H hH) (XTensorIso q) n _
    (XTensorTwist_weight q H hH hq hp n) x

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

lemma sigma_symm : (sigma q H hH).symm = sigma q H⁻¹ (inv_ne_zero hH) := by
  apply AlgEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

variable [CharP k 2]

def XInverseTwistIso : (SymmetrizingForm.twistFunctor (sigma q H hH).symm).obj
    (ModuleCat.of (E q) (X q)) ≅ ModuleCat.of (E q) (X q) where
  hom := ModuleCat.ofHom
    (X := (SymmetrizingForm.twistFunctor (sigma q H hH).symm).obj (ModuleCat.of (E q) (X q)))
    (Y := ModuleCat.of (E q) (X q))
    { toFun := id
      map_add' _ _ := rfl
      map_smul' a x := by
        change characterE q (sigma q H hH a) * (show k from x) = characterE q a * (show k from x)
        rw [characterE_sigma] }
  inv := ModuleCat.ofHom
    (X := ModuleCat.of (E q) (X q))
    (Y := (SymmetrizingForm.twistFunctor (sigma q H hH).symm).obj (ModuleCat.of (E q) (X q)))
    { toFun := id
      map_add' _ _ := rfl
      map_smul' a x := by
        change characterE q a * (show k from x) = characterE q (sigma q H hH a) * (show k from x)
        rw [characterE_sigma] }

omit [CharP k 2] in
lemma XInverseTwistIso_hom_apply (x) : (XInverseTwistIso q H hH).hom x = x := rfl

lemma XTwist_weight_of_eq (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (σ : E q ≃ₐ[k] E q) (hσ : σ = sigma q H hH)
    (e : (SymmetrizingForm.twistFunctor σ).obj (ModuleCat.of (E q) (X q)) ≅
      ModuleCat.of (E q) (X q)) (he : ∀ x, e.hom x = x)
    (n : ℕ) (x : Ext (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) n) :
    extIso (k := k) e e n (x.mapExactFunctor (SymmetrizingForm.twistFunctor σ)) =
      H⁻¹^(n/3) • x := by
  subst σ
  have hee : e = XTwistIso q H hH := by
    apply Iso.ext
    rw [XTwistIso_hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact he
  subst e
  exact XTwist_weight q H hH hq hp n x

lemma XInverseTwist_weight (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (n : ℕ) (x : Ext (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) n) :
    extIso (k := k) (XInverseTwistIso q H hH) (XInverseTwistIso q H hH) n
      (x.mapExactFunctor (SymmetrizingForm.twistFunctor (sigma q H hH).symm)) =
        H^(n/3) • x := by
  simpa only [inv_inv] using XTwist_weight_of_eq q H⁻¹ (inv_ne_zero hH) hq hp
    (sigma q H hH).symm (sigma_symm q H hH) (XInverseTwistIso q H hH)
    (XInverseTwistIso_hom_apply q H hH) n x

end Tachikawa.Construction

end

end OAI
