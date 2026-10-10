import OAI.RingTheory.Tachikawa.Coinduction

namespace OAI


noncomputable section
namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

def rightRegularEndUnderlying : rightRegularObj (S := R) ≃ₗ[k] R :=
  (moduleCatUnderlyingEquiv (k := k) (R := Rᵐᵒᵖ) Rᵐᵒᵖ).trans (MulOpposite.opLinearEquiv k).symm

def ordinaryEndEquiv : ordinaryOuterObj (k := k) (R := R) ≃ₗ[k] (R →ₗ[k] R) :=
  (rightFreeUnderlying (dualLeftObj (k := k) (R := R))).trans
    ((dualOuterUnderlying (rightRegularObj (S := R))).trans (rightRegularEndUnderlying (k := k) (R := R)).congrRight)

lemma ordinaryEndEquiv_tmul (φ : dualLeftObj (k := k) (R := R))
    (s : rightRegularObj (S := R)) (a : R) :
    ordinaryEndEquiv (k := k) (R := R) (φ ⊗ₜ[k] s) a =
      (show Module.Dual k R from φ) a • (show Rᵐᵒᵖ from s).unop := by
  change rightRegularEndUnderlying (k := k) (R := R) (dualOuterUnderlying (rightRegularObj (S := R)) (φ ⊗ₜ[k] s) a) = _
  rw [dualOuterUnderlying_tmul, map_smul]
  rfl

lemma ordinaryEndEquiv_left (a : R) (z : ordinaryOuterObj (k := k) (R := R)) :
    ordinaryEndEquiv (((a ⊗ₜ[k] (1:Rᵐᵒᵖ)) : Alg k R R) • z) =
      (ordinaryEndEquiv z).comp (LinearMap.mulRight k a) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    erw [smul_add,map_add,map_add,hx,hy,LinearMap.add_comp]
  | tmul φ s =>
    apply LinearMap.ext; intro c
    change ordinaryEndEquiv ((a • φ) ⊗ₜ[k] ((1:Rᵐᵒᵖ) • s)) c = ordinaryEndEquiv (φ ⊗ₜ[k] s) (c*a)
    rw [one_smul,ordinaryEndEquiv_tmul,ordinaryEndEquiv_tmul]
    rfl

lemma ordinaryEndEquiv_right (a : R) (z : ordinaryOuterObj (k := k) (R := R)) :
    ordinaryEndEquiv (((1:R) ⊗ₜ[k] MulOpposite.op a : Alg k R R) • z) =
      (LinearMap.mulRight k a).comp (ordinaryEndEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    erw [smul_add,map_add,map_add,hx,hy,LinearMap.comp_add]
  | tmul φ s =>
    apply LinearMap.ext; intro c
    change ordinaryEndEquiv (((1:R) • φ) ⊗ₜ[k] (MulOpposite.op a • s)) c = (ordinaryEndEquiv (φ ⊗ₜ[k] s) c)*a
    rw [one_smul,ordinaryEndEquiv_tmul,ordinaryEndEquiv_tmul]
    change (show Module.Dual k R from φ) c • ((show Rᵐᵒᵖ from s).unop * a) =
      ((show Module.Dual k R from φ) c • (show Rᵐᵒᵖ from s).unop)*a
    exact Algebra.smul_mul_assoc _ _ _ |>.symm

def dualRegularUnderlying : dualRegularObj (k := k) (R := R) ≃ₗ[k] Module.Dual k R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (action (k := k) (R := R) (S := R) (DualBimodule k R)
      (algebraMap k (Alg k R R) c)) (show DualBimodule k R from x) = c • (show DualBimodule k R from x)
    rw [AlgHom.commutes]
    rfl

omit [FiniteDimensional k R] in
lemma dualRegularUnderlying_left (a : R) (φ : dualRegularObj (k := k) (R := R)) :
    dualRegularUnderlying (((a ⊗ₜ[k] (1:Rᵐᵒᵖ)) : Alg k R R) • φ) =
      (dualRegularUnderlying φ).comp (LinearMap.mulRight k a) := by
  apply LinearMap.ext; intro c
  change (show Module.Dual k R from φ) ((1:R)* (c*a)) = _
  rw [one_mul]
  rfl

omit [FiniteDimensional k R] in
lemma dualRegularUnderlying_right (a : R) (φ : dualRegularObj (k := k) (R := R)) :
    dualRegularUnderlying (((1:R) ⊗ₜ[k] MulOpposite.op a : Alg k R R) • φ) =
      (dualRegularUnderlying φ).comp (LinearMap.mulLeft k a) := by
  apply LinearMap.ext; intro c
  change (show Module.Dual k R from φ) (a * (c*1)) = _
  rw [mul_one]
  rfl




def ordinaryAlpha (f : regular (k := k) (R := R) ⟶ ordinaryOuterObj (k := k) (R := R)) :
    R →ₗ[k] (R →ₗ[k] R) :=
  ordinaryEndEquiv.toLinearMap.comp ((f.hom.restrictScalars k).comp regularUnderlyingEquiv.symm.toLinearMap)

lemma ordinaryAlpha_left (f : regular (k := k) (R := R) ⟶ ordinaryOuterObj (k := k) (R := R))
    (a b : R) : ordinaryAlpha f (a*b) = (ordinaryAlpha f b).comp (LinearMap.mulRight k a) := by
  have h := f.hom.map_smul (a ⊗ₜ[k] (1:Rᵐᵒᵖ)) (regularUnderlyingEquiv.symm b)
  have hpre : (a ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (regularUnderlyingEquiv (k := k) (R := R)).symm b =
      regularUnderlyingEquiv.symm (a*b) := by change a*(b*1)=a*b; rw [mul_one]
  rw [hpre] at h
  exact (congrArg ordinaryEndEquiv h).trans (ordinaryEndEquiv_left _ _)

lemma ordinaryAlpha_right (f : regular (k := k) (R := R) ⟶ ordinaryOuterObj (k := k) (R := R))
    (a b : R) : ordinaryAlpha f (a*b) = (LinearMap.mulRight k b).comp (ordinaryAlpha f a) := by
  have h := f.hom.map_smul ((1:R) ⊗ₜ[k] MulOpposite.op b) (regularUnderlyingEquiv.symm a)
  have hpre : ((1:R) ⊗ₜ[k] MulOpposite.op b) • (regularUnderlyingEquiv (k := k) (R := R)).symm a =
      regularUnderlyingEquiv.symm (a*b) := by change 1*(a*b)=a*b; rw [one_mul]
  rw [hpre] at h
  exact (congrArg ordinaryEndEquiv h).trans (ordinaryEndEquiv_right _ _)

def ordinaryBeta (f : ordinaryOuterObj (k := k) (R := R) ⟶ dualRegularObj (k := k) (R := R)) :
    (R →ₗ[k] R) →ₗ[k] Module.Dual k R :=
  dualRegularUnderlying.toLinearMap.comp ((f.hom.restrictScalars k).comp ordinaryEndEquiv.symm.toLinearMap)

lemma ordinaryBeta_end (f : ordinaryOuterObj (k := k) (R := R) ⟶ dualRegularObj (k := k) (R := R))
    (z : ordinaryOuterObj (k := k) (R := R)) :
    ordinaryBeta f (ordinaryEndEquiv z) = dualRegularUnderlying (f z) := by
  simp only [ordinaryBeta,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  rfl

lemma ordinaryBeta_left (f : ordinaryOuterObj (k := k) (R := R) ⟶ dualRegularObj (k := k) (R := R))
    (a : R) (F : R →ₗ[k] R) :
    ordinaryBeta f (F.comp (LinearMap.mulRight k a)) =
      (ordinaryBeta f F).comp (LinearMap.mulRight k a) := by
  obtain ⟨z,rfl⟩ := ordinaryEndEquiv (k := k) (R := R) |>.surjective F
  rw [← ordinaryEndEquiv_left,ordinaryBeta_end,ordinaryBeta_end]
  rw [f.hom.map_smul,dualRegularUnderlying_left]

lemma ordinaryBeta_right (f : ordinaryOuterObj (k := k) (R := R) ⟶ dualRegularObj (k := k) (R := R))
    (a : R) (F : R →ₗ[k] R) :
    ordinaryBeta f ((LinearMap.mulRight k a).comp F) =
      (ordinaryBeta f F).comp (LinearMap.mulLeft k a) := by
  obtain ⟨z,rfl⟩ := ordinaryEndEquiv (k := k) (R := R) |>.surjective F
  rw [← ordinaryEndEquiv_right,ordinaryBeta_end,ordinaryBeta_end]
  rw [f.hom.map_smul,dualRegularUnderlying_right]

lemma ordinaryBeta_alpha
    (a : regular (k := k) (R := R) ⟶ ordinaryOuterObj (k := k) (R := R))
    (b : ordinaryOuterObj (k := k) (R := R) ⟶ dualRegularObj (k := k) (R := R)) (x : R) :
    ordinaryBeta b (ordinaryAlpha a x) =
      dualRegularUnderlying ((a ≫ b) (regularUnderlyingEquiv.symm x)) :=
  ordinaryBeta_end b _

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

def characterBimoduleMap : Enveloping.regular (k := k) (R := B q) ⟶
    Enveloping.dualRegularObj (k := k) (R := B q) :=
  Enveloping.ofBimoduleHom
    { toFun := characterMapB q
      map_add' := (characterMapB q).map_add
      map_smul' a x := characterMapB_left q a x }
    (fun a x => characterMapB_right q x a.unop)

lemma characterBimoduleMap_apply (x : B q) :
    Enveloping.dualRegularUnderlying (characterBimoduleMap q
      (Enveloping.regularUnderlyingEquiv.symm x)) = characterMapB q x := rfl

variable [CharP k 2]

lemma ordinary_morphism_factorization_pf_zero
    (a : Enveloping.regular (k := k) (R := B q) ⟶ Enveloping.ordinaryOuterObj (k := k) (R := B q))
    (b : Enveloping.ordinaryOuterObj (k := k) (R := B q) ⟶ Enveloping.dualRegularObj (k := k) (R := B q)) :
    Enveloping.dualRegularUnderlying ((a ≫ b) (Enveloping.regularUnderlyingEquiv.symm 1)) (pf q) = 0 := by
  rw [← Enveloping.ordinaryBeta_alpha]
  exact ordinary_factorization_pf_zero q (Enveloping.ordinaryAlpha a)
    (Enveloping.ordinaryAlpha_left a) (Enveloping.ordinaryAlpha_right a)
    (Enveloping.ordinaryBeta b) (Enveloping.ordinaryBeta_left b) (Enveloping.ordinaryBeta_right b)

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

def rho : E q →ₗ[k] DualBimodule k (B q) :=
  (TensorProduct.dualDistrib k (C k q) (C k q)).comp
    (TensorProduct.map ((TrivSqZeroExt.sndHom (C k q) (DualBimodule k (C k q))).restrictScalars k)
      ((TrivSqZeroExt.sndHom (C k q) (DualBimodule k (C k q))).restrictScalars k))

lemma rho_tmul (a b : T q) (x y : C k q) :
    rho q (a ⊗ₜ[k] b) (x ⊗ₜ[k] y) = a.snd x * b.snd y := rfl

lemma rho_left (a : B q) (z : E q) :
    rho q (inclusionB q a * z) = a • rho q z := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,add_mul,ha,hb,add_smul]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [mul_add,map_add,hx,hy,smul_add]
    | tmul x y =>
      apply TensorProduct.ext'
      intro c d
      change rho q ((inclusionC q a ⊗ₜ[k] inclusionC q b) * (x ⊗ₜ[k] y))
        (c ⊗ₜ[k] d) = rho q (x ⊗ₜ[k] y) ((c ⊗ₜ[k] d) * (a ⊗ₜ[k] b))
      rw [Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,
        rho_tmul,rho_tmul]
      change (a • x.snd + MulOpposite.op x.fst • (0:DualBimodule k (C k q))) c *
        (b • y.snd + MulOpposite.op y.fst • (0:DualBimodule k (C k q))) d = _
      simp only [smul_zero,add_zero]
      rfl

lemma rho_right (a : B q) (z : E q) :
    rho q (z * inclusionB q a) = MulOpposite.op a • rho q z := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,mul_add,ha,hb,MulOpposite.op_add,add_smul]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [add_mul,map_add,hx,hy,smul_add]
    | tmul x y =>
      apply TensorProduct.ext'
      intro c d
      change rho q ((x ⊗ₜ[k] y) * (inclusionC q a ⊗ₜ[k] inclusionC q b))
        (c ⊗ₜ[k] d) = rho q (x ⊗ₜ[k] y) ((a ⊗ₜ[k] b) * (c ⊗ₜ[k] d))
      rw [Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,
        rho_tmul,rho_tmul]
      change (x.fst • (0:DualBimodule k (C k q)) + MulOpposite.op a • x.snd) c *
        (y.fst • (0:DualBimodule k (C k q)) + MulOpposite.op b • y.snd) d = _
      simp only [smul_zero,zero_add]
      rfl

lemma sigma_inclusionB (H : k) (hH : H ≠ 0) (a : B q) :
    sigma q H hH (inclusionB q a) = inclusionB q a := by
  induction a using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    change TrivialExtension.scaleDual H hH (inclusionC q x) ⊗ₜ[k]
      TrivialExtension.scaleDual H hH (inclusionC q y) = _
    have h (x : C k q) : TrivialExtension.scaleDual H hH (inclusionC q x) = inclusionC q x := by
      apply TrivSqZeroExt.ext
      · rfl
      · exact smul_zero _
    rw [h,h]
    rfl

lemma rho_zeta : rho q (zeta q) = (characterB q).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  rfl

lemma character_inclusion (a : B q) : characterE q (inclusionB q a) = characterB q a := by
  induction a using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => rfl

lemma rho_representation_socle (H : k) (hH : H ≠ 0) (a : B q) :
    rho q (Enveloping.twistedUnderlying (sigma q H hH)
      ((HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)) ≫
        socleBimoduleMap q H hH) (Enveloping.regularUnderlyingEquiv.symm (inclusionB q a)))) =
      characterMapB q a := by
  rw [representation_socle,map_smul,rho_zeta,character_inclusion]
  rfl

end Tachikawa.Construction



namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def regularHom (φ : R →ₐ[k] S) : (functor φ).obj (ModuleCat.of R R) ⟶ ModuleCat.of S S :=
  extend φ (ModuleCat.ofHom (Y := (res φ).obj (ModuleCat.of S S))
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := φ.map_mul })

def regularInv (φ : R →ₐ[k] S) : ModuleCat.of S S ⟶ (functor φ).obj (ModuleCat.of R R) :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton S _)
    (unit φ (ModuleCat.of R R) (1:R)))

lemma regularHom_unit (φ : R →ₐ[k] S) (r : R) :
    regularHom φ (unit φ (ModuleCat.of R R) r) = φ r := by
  change (1:S) * φ r = φ r
  rw [one_mul]

lemma regularInv_apply (φ : R →ₐ[k] S) (s : S) :
    regularInv φ s = s • (show (functor φ).obj (ModuleCat.of R R) from
      unit φ (ModuleCat.of R R) 1) := rfl

def regularIso (φ : R →ₐ[k] S) : (functor φ).obj (ModuleCat.of R R) ≅ ModuleCat.of S S where
  hom := regularHom φ
  inv := regularInv φ
  hom_inv_id := by
    apply (homEquiv φ (ModuleCat.of R R) _).injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change regularInv φ (regularHom φ (unit φ (ModuleCat.of R R) r)) = unit φ (ModuleCat.of R R) r
    rw [regularHom_unit, regularInv_apply]
    have h := (unit φ (ModuleCat.of R R)).hom.map_smul r (1:R)
    change (show (functor φ).obj (ModuleCat.of R R) from unit φ (ModuleCat.of R R) (r*1)) = φ r • (show (functor φ).obj (ModuleCat.of R R) from
      unit φ (ModuleCat.of R R) 1) at h
    simpa only [mul_one] using h.symm
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change regularHom φ (regularInv φ s) = s
    rw [regularInv_apply]
    apply ((regularHom φ).hom.map_smul s (show (functor φ).obj (ModuleCat.of R R) from
      unit φ (ModuleCat.of R R) 1)).trans
    change s * regularHom φ (unit φ (ModuleCat.of R R) 1) = s
    rw [regularHom_unit, map_one, mul_one]

end Tachikawa.AlgebraInduction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def LeftRestrictedRegular (_φ : R →ₐ[k] S) := S
instance (φ : R →ₐ[k] S) : AddCommGroup (LeftRestrictedRegular φ) := inferInstanceAs (AddCommGroup S)
instance (φ : R →ₐ[k] S) : Module k (LeftRestrictedRegular φ) := inferInstanceAs (Module k S)
instance (φ : R →ₐ[k] S) : Module R (LeftRestrictedRegular φ) := Module.compHom S φ.toRingHom
instance (φ : R →ₐ[k] S) : Module Sᵐᵒᵖ (LeftRestrictedRegular φ) := inferInstanceAs (Module Sᵐᵒᵖ S)
instance (φ : R →ₐ[k] S) : IsScalarTower k R (LeftRestrictedRegular φ) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change φ (algebraMap k R c) * (show S from x) = c • (show S from x)
    rw [φ.commutes, Algebra.smul_def]
instance (φ : R →ₐ[k] S) : IsScalarTower k Sᵐᵒᵖ (LeftRestrictedRegular φ) :=
  inferInstanceAs (IsScalarTower k Sᵐᵒᵖ S)
instance (φ : R →ₐ[k] S) : SMulCommClass R Sᵐᵒᵖ (LeftRestrictedRegular φ) where
  smul_comm r s x := (mul_assoc (φ r) (show S from x) s.unop).symm

abbrev leftRestrictedRegular (φ : R →ₐ[k] S) : ModuleCat (Alg k R S) :=
  ofBimodule (k := k) (R := R) (S := S) (LeftRestrictedRegular φ)

def regularRightUnitTarget (φ : R →ₐ[k] S) : regular (k := k) (R := R) ⟶
    (AlgebraInduction.res (rightEnvelopingMap (U := R) φ)).obj (leftRestrictedRegular φ) :=
  ModuleCat.ofHom (X := regular (k := k) (R := R))
    (Y := (AlgebraInduction.res (rightEnvelopingMap (U := R) φ)).obj (leftRestrictedRegular φ))
  { toFun := fun r => φ r
    map_add' := φ.map_add
    map_smul' a x := by
      change φ ((action (k := k) (R := R) (S := R) R a) x) =
        (action (k := k) (R := R) (S := S) (LeftRestrictedRegular φ) (rightEnvelopingMap φ a)) (φ x)
      induction a using TensorProduct.inductionOn with
      | tmul r s =>
        change φ (r * ((show R from x) * s.unop)) = φ r * (φ x * φ s.unop)
        rw [map_mul, map_mul]
      | add a b ha hb =>
        rw [map_add, map_add, map_add]
        change φ ((action (k := k) (R := R) (S := R) R a) x +
          (action (k := k) (R := R) (S := R) R b) x) = _
        exact (φ.map_add _ _).trans (congrArg₂ (fun x y : LeftRestrictedRegular φ => x+y) ha hb) }

def rightIndRegularHom (φ : R →ₐ[k] S) :
    rightIndObj φ (regular (k := k) (R := R)) ⟶ leftRestrictedRegular φ :=
  rightIndExtend φ (regularRightUnitTarget φ)

lemma rightIndRegularHom_mk (φ : R →ₐ[k] S) (s : AlgebraInduction.Bimod φ.op)
    (r : RightObj (regular (k := k) (R := R))) :
    (show S from rightIndRegularHom φ (BalancedTensor.mk s r)) = φ r * (show Sᵐᵒᵖ from s).unop := by
  change φ (1:R) * (φ r * (show Sᵐᵒᵖ from s).unop) = _
  rw [map_one, one_mul]

def rightIndRegularInvLinear (φ : R →ₐ[k] S) : S →ₗ[Sᵐᵒᵖ]
    RightIndType φ (regular (k := k) (R := R)) :=
  ((LinearMap.toSpanSingleton Sᵐᵒᵖ _)
    (show RightIndType φ (regular (k := k) (R := R)) from
      rightIndUnit φ (regular (k := k) (R := R)) (1:R))).comp
    (MulOpposite.opLinearEquiv Sᵐᵒᵖ).toLinearMap

lemma rightIndRegularInvLinear_apply (φ : R →ₐ[k] S) (s : S) :
    rightIndRegularInvLinear φ s = BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (N := RightObj (regular (k := k) (R := R)))
      (show AlgebraInduction.Bimod φ.op from MulOpposite.op s) (1:R) := by
  exact (AlgebraInduction.mk_one_smul φ.op
    (ModuleCat.of Rᵐᵒᵖ (RightObj (regular (k := k) (R := R)))) (MulOpposite.op s) (1:R)).symm

lemma rightIndRegularInvLinear_left (φ : R →ₐ[k] S) (r : R) (s : S) :
    rightIndRegularInvLinear φ (φ r * s) = r • rightIndRegularInvLinear φ s := by
  rw [rightIndRegularInvLinear_apply, rightIndRegularInvLinear_apply]
  trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj (regular (k := k) (R := R)))
    (MulOpposite.op (MulOpposite.op r) • (show AlgebraInduction.Bimod φ.op from MulOpposite.op s)) (1:R)
  · rfl
  trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s)
    (MulOpposite.op r • (show RightObj (regular (k := k) (R := R)) from (1:R)))
  · exact BalancedTensor.balance _ _ _
  change BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s) (1 * (1 * r)) =
    BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s) (r * (1 * 1))
  exact congrArg (fun z : R => BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (N := RightObj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ.op from MulOpposite.op s)
    (show RightObj (regular (k := k) (R := R)) from z)) (show (1:R) * (1*r) = r * (1*1) by simp only [one_mul, mul_one])

def rightIndRegularInv (φ : R →ₐ[k] S) :
    leftRestrictedRegular φ ⟶ rightIndObj φ (regular (k := k) (R := R)) :=
  ofBimoduleHom
    (show LeftRestrictedRegular φ →ₗ[R] RightIndType φ (regular (k := k) (R := R)) from
      { toFun := rightIndRegularInvLinear φ
        map_add' := (rightIndRegularInvLinear φ).map_add
        map_smul' := rightIndRegularInvLinear_left φ })
    (fun s x => (rightIndRegularInvLinear φ).map_smul s x)

def rightIndRegularIso (φ : R →ₐ[k] S) :
    rightIndObj φ (regular (k := k) (R := R)) ≅ leftRestrictedRegular φ where
  hom := rightIndRegularHom φ
  inv := rightIndRegularInv φ
  hom_inv_id := by
    apply rightInd_hom_ext φ
    intro s r
    change rightIndRegularInvLinear φ (show S from rightIndRegularHom φ
      (show rightIndObj φ (regular (k := k) (R := R)) from BalancedTensor.mk s r)) =
      (show RightIndType φ (regular (k := k) (R := R)) from BalancedTensor.mk s r)
    trans rightIndRegularInvLinear φ (φ r * (show Sᵐᵒᵖ from s).unop)
    · exact congrArg (rightIndRegularInvLinear φ) (rightIndRegularHom_mk φ s r)
    rw [rightIndRegularInvLinear_apply]
    trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj (regular (k := k) (R := R)))
      (MulOpposite.op (MulOpposite.op (show R from r)) • s) (1:R)
    · rfl
    trans BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (N := RightObj (regular (k := k) (R := R))) s
      (MulOpposite.op (show R from r) • (show RightObj (regular (k := k) (R := R)) from (1:R)))
    · exact BalancedTensor.balance _ _ _
    change BalancedTensor.mk s (show RightObj (regular (k := k) (R := R)) from (1 * (1 * (show R from r)) : R)) = BalancedTensor.mk s r
    exact congrArg (fun z : R => BalancedTensor.mk s
      (show RightObj (regular (k := k) (R := R)) from z)) (by exact (congrArg (fun z : R => (1:R)*z) (one_mul (show R from r))).trans (one_mul (show R from r)))
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change (show S from rightIndRegularHom φ (rightIndRegularInvLinear φ (show S from s))) =
      (show S from s)
    trans (show S from rightIndRegularHom φ (BalancedTensor.mk
      (show AlgebraInduction.Bimod φ.op from MulOpposite.op (show S from s))
      (show RightObj (regular (k := k) (R := R)) from (1:R))))
    · exact congrArg (fun x : RightIndType φ (regular (k := k) (R := R)) =>
        (show S from rightIndRegularHom φ x)) (rightIndRegularInvLinear_apply φ s)
    exact (rightIndRegularHom_mk φ _ _).trans
      (show φ (1:R) * (show S from s) = (show S from s) by rw [map_one, one_mul])

def leftRestrictedRegularIso (φ : R →ₐ[k] S) :
    (leftFunctor (k := k) (R := R) (S := S)).obj (leftRestrictedRegular φ) ≅
      (AlgebraInduction.res φ).obj (ModuleCat.of S S) :=
by
  let X := (leftFunctor (k := k) (R := R) (S := S)).obj (leftRestrictedRegular φ)
  let Z := (AlgebraInduction.res φ).obj (ModuleCat.of S S)
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Z)
    (m₁ := X.isModule) (m₂ := Z.isModule)
    { toFun := fun x : X =>
        (show (AlgebraInduction.res φ).obj (ModuleCat.of S S) from x)
      invFun := fun x => x
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r x := by
        change φ r * ((show S from x) * 1) = φ r * (show S from x)
        rw [mul_one] }

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

abbrev leftEnvelopingMap (φ : R →ₐ[k] S) : Alg k R U →ₐ[k] Alg k S U :=
  Algebra.TensorProduct.map φ (AlgHom.id k Uᵐᵒᵖ)

def leftIndUnit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj (leftIndObj φ M) :=
  ModuleCat.ofHom (X := M) (Y := (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj (leftIndObj φ M))
  { toFun := fun m => BalancedTensor.mk (k := k) (R := R) (S := S)
      (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from m)
    map_add' := by intro m n; exact (BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := Obj M) (show AlgebraInduction.Bimod φ from (1:S))).map_add m n
    map_smul' a m := by
      change BalancedTensor.mk (k := k) (R := R) (S := S)
        (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from a • m) =
        (action (k := k) (R := S) (S := U)
          (BalancedTensor.T (k := k) (R := R) (S := S) (M := AlgebraInduction.Bimod φ) (N := Obj M))
          (leftEnvelopingMap φ a)) _
      induction a using TensorProduct.inductionOn with
      | tmul r u =>
        change BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from (r ⊗ₜ[k] u) • m) =
          (φ r) • (u • BalancedTensor.mk (k := k) (R := R) (S := S)
            (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from m))
        trans BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (r • u • (show Obj M from m))
        · exact congrArg (BalancedTensor.mk (k := k) (R := R) (S := S)
            (show AlgebraInduction.Bimod φ from (1:S))) (tmul_smul M r u m)
        exact (AlgebraInduction.unit φ (ModuleCat.of R (Obj M))).hom.map_smul r (u • (show Obj M from m))
      | add a b ha hb =>
        rw [map_add, map_add]
        change BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from (a+b) • m) = _
        exact (congrArg (fun x : M => BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from x)) (add_smul a b m)).trans
          (((BalancedTensor.mk (k := k) (R := R) (S := S) (N := Obj M)
            (show AlgebraInduction.Bimod φ from (1:S))).map_add _ _).trans
              (congrArg₂ (fun x y => x+y) ha hb)) }

@[simp] lemma leftIndUnit_apply (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) (m : M) :
    leftIndUnit φ M m = BalancedTensor.mk (k := k) (R := R) (S := S)
      (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from m) := rfl




def leftIndResMap (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) :
    ModuleCat.of R (Obj M) ⟶ (AlgebraInduction.res φ).obj (ModuleCat.of S (Obj N)) :=
  ModuleCat.ofHom (X := ModuleCat.of R (Obj M))
    (Y := (AlgebraInduction.res φ).obj (ModuleCat.of S (Obj N)))
  { toFun := fun m => (show Obj N from f m)
    map_add' := f.hom.map_add
    map_smul' r m := by
      have h := f.hom.map_smul (r ⊗ₜ[k] (1:Uᵐᵒᵖ)) m
      change (show N from f ((r ⊗ₜ[k] (1:Uᵐᵒᵖ)) • (show M from m))) =
        (leftEnvelopingMap φ (r ⊗ₜ[k] (1:Uᵐᵒᵖ))) • (show N from f m) at h
      exact h }

lemma leftIndResMap_right (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) (u : Uᵐᵒᵖ) (m : Obj M) :
    (show Obj N from f (u • m)) = u • (show Obj N from f m) := by
  have h := f.hom.map_smul ((1:R) ⊗ₜ[k] u) m
  change (show N from f (((1:R) ⊗ₜ[k] u) • (show M from m))) =
    leftEnvelopingMap φ ((1:R) ⊗ₜ[k] u) • (show N from f m) at h
  change (show N from f (((1:R) ⊗ₜ[k] u) • (show M from m))) =
    ((1:S) ⊗ₜ[k] u) • (show N from f m)
  simpa only [leftEnvelopingMap, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using h

def leftIndExtendLinear (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) :
    BalancedTensor.T (k := k) (R := R) (S := S) (M := AlgebraInduction.Bimod φ) (N := Obj M) →ₗ[S] Obj N :=
  (AlgebraInduction.extend φ (leftIndResMap φ f)).hom

lemma leftIndExtendLinear_right (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) (u : Uᵐᵒᵖ) (x) :
    leftIndExtendLinear φ f (u • x) = u • leftIndExtendLinear φ f x := by
  induction x using BalancedTensor.induction_on with
  | h0 => simp only [smul_zero, map_zero]
  | ht s m =>
    change (show S from s) • (show Obj N from f (u • m)) =
      u • ((show S from s) • (show Obj N from f m))
    rw [leftIndResMap_right φ f, smul_comm]
  | ha x y hx hy => simp only [smul_add, map_add, hx, hy]

def leftIndExtend (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) :
    leftIndObj φ M ⟶ N :=
  ofBimoduleHom (leftIndExtendLinear φ f) (leftIndExtendLinear_right φ f) ≫ (reassembleIso N).hom

@[simp] lemma leftIndExtend_mk (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N)
    (s : AlgebraInduction.Bimod φ) (m : Obj M) :
    leftIndExtend φ f (BalancedTensor.mk s m) = (show Obj N from (show S from s) • (show Obj N from f m)) := rfl




lemma leftInd_hom_ext (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    {f g : leftIndObj φ M ⟶ N}
    (h : ∀ (s : AlgebraInduction.Bimod φ) (m : Obj M),
      f (BalancedTensor.mk s m) = g (BalancedTensor.mk s m)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on (k := k) (R := R) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := Obj M) with
  | h0 => exact f.hom.map_zero.trans g.hom.map_zero.symm
  | ht s m => exact h s m
  | ha x y hx hy =>
    exact (f.hom.map_add x y).trans
      ((congrArg₂ (fun x y => x+y) hx hy).trans (g.hom.map_add x y).symm)

def leftIndComparisonHom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M ⟶ leftIndObj φ M :=
  AlgebraInduction.extend (k := k) (R := Alg k R U) (S := Alg k S U)
    (N := M) (P := leftIndObj φ M) (leftEnvelopingMap φ) (leftIndUnit φ M)

def leftIndComparisonInv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    leftIndObj φ M ⟶ (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M :=
  leftIndExtend (k := k) (R := R) (S := S) (U := U) φ (M := M)
    (N := (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M)
    (AlgebraInduction.unit (k := k) (R := Alg k R U) (S := Alg k S U)
      (leftEnvelopingMap (U := U) φ) M)

lemma leftIndComparison_inv_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) (m : M) :
    leftIndComparisonInv φ M (leftIndUnit φ M m) =
      AlgebraInduction.unit (k := k) (R := Alg k R U) (S := Alg k S U) (leftEnvelopingMap φ) M m := by
  change (1:S) • (show Obj ((AlgebraInduction.functor (k := k) (leftEnvelopingMap (U := U) φ)).obj M) from
    AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m) = _
  exact one_smul _ _

lemma leftIndComparison_hom_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) (m : M) :
    leftIndComparisonHom φ M (AlgebraInduction.unit (k := k) (R := Alg k R U)
      (S := Alg k S U) (leftEnvelopingMap φ) M m) = leftIndUnit φ M m := by
  change (1:Alg k S U) • (show leftIndObj φ M from leftIndUnit φ M m) = _
  exact one_smul _ _

lemma leftIndComparison_hom_inv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    leftIndComparisonHom φ M ≫ leftIndComparisonInv φ M = 𝟙 _ := by
  apply (AlgebraInduction.homEquiv (k := k) (R := Alg k R U) (S := Alg k S U)
    (leftEnvelopingMap φ) M _).injective
  ext m
  change leftIndComparisonInv φ M (leftIndComparisonHom φ M
    (AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m)) =
      AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m
  rw [leftIndComparison_hom_unit, leftIndComparison_inv_unit]

lemma leftIndComparison_inv_hom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    leftIndComparisonInv φ M ≫ leftIndComparisonHom φ M = 𝟙 _ := by
  apply leftInd_hom_ext φ
  intro s m
  have h := (leftMap (leftIndComparisonHom φ M)).map_smul (show S from s)
    (show Obj ((AlgebraInduction.functor (k := k) (leftEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m)
  change leftIndComparisonHom φ M ((show S from s) •
    (show Obj ((AlgebraInduction.functor (k := k) (leftEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (leftEnvelopingMap (U := U) φ) M m)) = _
  apply h.trans
  apply Eq.trans (congrArg (fun x : Obj (leftIndObj φ M) => (show S from s) • x)
    (leftIndComparison_hom_unit φ M m))
  change (show S from s) • ((1:Uᵐᵒᵖ) •
    (BalancedTensor.mk (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj M) (show AlgebraInduction.Bimod φ from (1:S)) m)) = BalancedTensor.mk s m
  rw [one_smul]
  exact (AlgebraInduction.mk_one_smul φ (ModuleCat.of R (Obj M)) (show S from s) m).symm

def leftIndComparisonIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    (AlgebraInduction.functor (leftEnvelopingMap (U := U) φ)).obj M ≅ leftIndObj φ M where
  hom := leftIndComparisonHom φ M
  inv := leftIndComparisonInv φ M
  hom_inv_id := leftIndComparison_hom_inv φ M
  inv_hom_id := leftIndComparison_inv_hom φ M

def leftIndComparison (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (leftEnvelopingMap (U := U) φ) ≅ leftIndFunctor φ :=
  NatIso.ofComponents (leftIndComparisonIso φ) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro a m
    change (show Alg k S U from a) • (show leftIndObj φ N from leftIndUnit φ N (f m)) =
      leftIndMap φ f ((show Alg k S U from a) • (show leftIndObj φ M from leftIndUnit φ M m))
    exact ((leftIndMap φ f).hom.map_smul (show Alg k S U from a)
      (show leftIndObj φ M from leftIndUnit φ M m)).symm)

def leftIndUnderlyingComparison (φ : R →ₐ[k] S) :
    leftIndFunctor (U := U) φ ⋙ leftFunctor ≅ leftFunctor ⋙ AlgebraInduction.functor φ :=
  NatIso.ofComponents (leftIndUnderlyingIso φ) (by intro M N f; ext x; rfl)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev leftComplex (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) :=
  ((leftFunctor (k := k) (R := R) (S := S)).mapHomologicalComplex (.down ℕ)).obj P
abbrev rightComplex (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) :=
  ((rightFunctor (k := k) (R := R) (S := S)).mapHomologicalComplex (.down ℕ)).obj P

def leftCokerEquiv (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) (n : ℕ) :
    Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n)) ≃ₗ[R] NatCoker.C (leftComplex P) n where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rightCokerEquiv (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) (n : ℕ) :
    Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n)) ≃ₗ[Sᵐᵒᵖ] NatCoker.C (rightComplex P) n where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma coker_left_projective_of_homotopy (P : ChainComplex (ModuleCat (Alg k R S)) ℕ)
    (Q : ChainComplex (ModuleCat R) ℕ) (n : ℕ) (e : HomotopyEquiv (leftComplex P) Q)
    [Subsingleton (Q.X (n+1))] [Module.Projective R (Obj (P.X n))] :
    Module.Projective R (Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n))) := by
  let : Module.Projective R ((leftComplex P).X n) :=
    inferInstanceAs (Module.Projective R (Obj (P.X n)))
  let := NatCoker.projective_of_homotopy (leftComplex P) n e
  exact Module.Projective.of_equiv (leftCokerEquiv P n).symm

lemma coker_right_projective_of_homotopy (P : ChainComplex (ModuleCat (Alg k R S)) ℕ)
    (Q : ChainComplex (ModuleCat Sᵐᵒᵖ) ℕ) (n : ℕ) (e : HomotopyEquiv (rightComplex P) Q)
    [Subsingleton (Q.X (n+1))] [Module.Projective Sᵐᵒᵖ (Obj (P.X n))] :
    Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n))) := by
  let : Module.Projective Sᵐᵒᵖ ((rightComplex P).X n) :=
    inferInstanceAs (Module.Projective Sᵐᵒᵖ (Obj (P.X n)))
  let := NatCoker.projective_of_homotopy (rightComplex P) n e
  exact Module.Projective.of_equiv (rightCokerEquiv P n).symm

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C : Type*} [Category* C] [Abelian C]

def transportResolution {M N : C} (P : ProjectiveResolution M) (e : M ≅ N) :
    ProjectiveResolution N where
  complex := P.complex
  projective n := P.projective n
  π := P.π ≫ (ChainComplex.single₀ C).map e.hom
  quasiIso := inferInstance

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

lemma rightInducedResolution_finite (φ : R →ₐ[k] S) (n : ℕ) :
    Module.Finite (Alg k R S) ((rightInducedResolution φ).complex.X n) := by
  change Module.Finite (Alg k R S)
    ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
  let : FiniteDimensional k ((regularResolution (k := k) (R := R)).complex.X n) :=
    Module.Finite.trans (Alg k R R) _
  exact Module.Finite.of_restrictScalars_finite k _ _

def rightInducedLeftResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.res φ).obj (ModuleCat.of S S)) :=
  Tachikawa.transportResolution
    (leftResolutionOf (rightInducedResolution φ) (rightInducedResolution_finite φ))
    ((leftFunctor (k := k) (R := R) (S := S)).mapIso
      ((rightIndComparisonIso φ (regular (k := k) (R := R))) ≪≫ rightIndRegularIso φ) ≪≫
      leftRestrictedRegularIso φ)

def inducedFactorIso (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (rightEnvelopingMap (U := R) φ) ⋙
      AlgebraInduction.functor (leftEnvelopingMap (U := S) φ) ≅
      AlgebraInduction.functor (envelopingMap φ) :=
  AlgebraInduction.compositionIso _ _ ≪≫ eqToIso (by
    congr 1
    ext a <;> rfl)

def inducedLeftComplexIso (φ : R →ₐ[k] S) :
    leftComplex (inducedRegularComplex φ) ≅
      ((AlgebraInduction.functor φ).mapHomologicalComplex _).obj
        (rightInducedLeftResolution φ).complex := by
  let P := (regularResolution (k := k) (R := R)).complex
  let J := AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)
  let L := AlgebraInduction.functor (leftEnvelopingMap (U := S) φ)
  let U := leftFunctor (k := k) (R := S) (S := S)
  let V := leftFunctor (k := k) (R := R) (S := S)
  let I := AlgebraInduction.functor φ
  let a : L ⋙ U ≅ V ⋙ I :=
    Functor.isoWhiskerRight (leftIndComparison (U := S) φ) U ≪≫
      leftIndUnderlyingComparison (U := S) φ
  let b := Functor.isoWhiskerRight (inducedFactorIso φ) U
  exact (NatIso.mapHomologicalComplex b _).symm.app P ≪≫
    (NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft J a) _).app P

def inducedLeftHomotopy (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ).obj (ModuleCat.of S S))) :
    HomotopyEquiv (leftComplex (inducedRegularComplex φ))
      (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj Q.complex) :=
  (HomotopyEquiv.ofIso (inducedLeftComplexIso φ)).trans
    ((AlgebraInduction.functor φ).mapHomotopyEquiv
      (ProjectiveResolution.homotopyEquiv (rightInducedLeftResolution φ) Q))

lemma inducedCoker_left_projective (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ).obj (ModuleCat.of S S)))
    (n : ℕ) (hn : CategoryTheory.Limits.IsZero (Q.complex.X (n+1))) :
    Module.Projective S (Obj (ModuleCat.of (Alg k S S) (NatCoker.C (inducedRegularComplex φ) n))) := by
  let I := AlgebraInduction.functor φ
  let C := (I.mapHomologicalComplex _).obj Q.complex
  have hC : CategoryTheory.Limits.IsZero (C.X (n+1)) := I.map_isZero hn
  let : Subsingleton (C.X (n+1)) := ModuleCat.isZero_iff_subsingleton.mp hC
  exact coker_left_projective_of_homotopy (inducedRegularComplex φ) C n (inducedLeftHomotopy φ Q)




omit [FiniteDimensional k S] in
lemma left_induction_regular_quasiIso (φ : R →ₐ[k] S) :
    QuasiIso (((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
      (regularResolution (k := k) (R := R)).π) := by
  let P := regularResolution (k := k) (R := R)
  let Q := leftResolutionOf P (fun n => inferInstance)
  let : Module.Projective R (Obj (regular (k := k) (R := R))) := regular_left_projective
  let : Projective ((leftFunctor (k := k) (R := R) (S := R)).obj
      (regular (k := k) (R := R))) := by
    change Projective (ModuleCat.of R (Obj (regular (k := k) (R := R))))
    exact ModuleCat.projective_of_categoryTheory_projective _
  let I := AlgebraInduction.functor φ
  let T := leftFunctor (k := k) (R := R) (S := R)
  let T' := leftFunctor (k := k) (R := S) (S := R)
  let J := AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)
  have h : QuasiIso ((I.mapHomologicalComplex _).map Q.π) :=
    Tachikawa.map_resolution_quasiIso I Q
  change QuasiIso ((I.mapHomologicalComplex _).map
    ((T.mapHomologicalComplex _).map P.π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _)) at h
  rw [Functor.map_comp] at h
  let := h
  have hI : QuasiIso ((I.mapHomologicalComplex _).map ((T.mapHomologicalComplex _).map P.π)) :=
    quasiIso_of_comp_right _ ((I.mapHomologicalComplex _).map
      ((HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _))
  have hB : QuasiIso (((leftIndFunctor (U := R) φ ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (leftIndUnderlyingComparison (U := R) φ) P.π).mpr hI
  have hJ : QuasiIso (((J ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (Functor.isoWhiskerRight (leftIndComparison (U := R) φ) T') P.π).mpr hB
  exact (quasiIso_map_iff_of_preservesHomology
    ((J.mapHomologicalComplex _).map P.π) T').mp hJ

def leftInducedResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).obj
      (regular (k := k) (R := R))) where
  complex := ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).mapHomologicalComplex _).obj
    (regularResolution (k := k) (R := R)).complex
  projective n := by
    change Projective ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
    exact ModuleCat.projective_of_categoryTheory_projective _
  π := ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
    (regularResolution (k := k) (R := R)).π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := by
    let := left_induction_regular_quasiIso φ
    infer_instance

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev rightRestrictedRegular (φ : R →ₐ[k] S) : ModuleCat (Alg k S R) :=
  ofBimodule (k := k) (R := S) (S := R) (AlgebraInduction.Bimod φ)

def regularLeftUnitTarget (φ : R →ₐ[k] S) : regular (k := k) (R := R) ⟶
    (AlgebraInduction.res (leftEnvelopingMap (U := R) φ)).obj (rightRestrictedRegular φ) :=
  ModuleCat.ofHom (X := regular (k := k) (R := R))
    (Y := (AlgebraInduction.res (leftEnvelopingMap (U := R) φ)).obj (rightRestrictedRegular φ))
  { toFun := fun r => φ r
    map_add' := φ.map_add
    map_smul' a x := by
      change φ ((action (k := k) (R := R) (S := R) R a) x) =
        (action (k := k) (R := S) (S := R) (AlgebraInduction.Bimod φ) (leftEnvelopingMap φ a)) (φ x)
      induction a using TensorProduct.inductionOn with
      | tmul r s =>
        change φ (r * ((show R from x) * s.unop)) = φ r * (φ x * φ s.unop)
        rw [map_mul, map_mul]
      | add a b ha hb =>
        rw [map_add, map_add, map_add]
        change φ ((action (k := k) (R := R) (S := R) R a) x +
          (action (k := k) (R := R) (S := R) R b) x) = _
        exact (φ.map_add _ _).trans
          (congrArg₂ (fun x y : AlgebraInduction.Bimod φ => x+y) ha hb) }

def leftIndRegularHom (φ : R →ₐ[k] S) :
    leftIndObj φ (regular (k := k) (R := R)) ⟶ rightRestrictedRegular φ :=
  leftIndExtend φ (regularLeftUnitTarget φ)

lemma leftIndRegularHom_mk (φ : R →ₐ[k] S) (s : AlgebraInduction.Bimod φ)
    (r : Obj (regular (k := k) (R := R))) :
    (show S from leftIndRegularHom φ (BalancedTensor.mk s r)) = (show S from s) * φ r := by
  change (show S from s) * (φ r * φ (1:R)) = _
  rw [map_one, mul_one]

def leftIndRegularInvLinear (φ : R →ₐ[k] S) : S →ₗ[S]
    BalancedTensor.T (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj (regular (k := k) (R := R))) :=
  (LinearMap.toSpanSingleton S _) (BalancedTensor.mk
    (show AlgebraInduction.Bimod φ from (1:S)) (show Obj (regular (k := k) (R := R)) from (1:R)))

lemma leftIndRegularInvLinear_apply (φ : R →ₐ[k] S) (s : S) :
    leftIndRegularInvLinear φ s = BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := Obj (regular (k := k) (R := R)))
      (show AlgebraInduction.Bimod φ from s) (1:R) := by
  exact (AlgebraInduction.mk_one_smul φ
    (ModuleCat.of R (Obj (regular (k := k) (R := R)))) s (1:R)).symm

lemma leftIndRegularInvLinear_right (φ : R →ₐ[k] S) (r : Rᵐᵒᵖ) (s : S) :
    leftIndRegularInvLinear φ (s * φ r.unop) = r • leftIndRegularInvLinear φ s := by
  rw [leftIndRegularInvLinear_apply, leftIndRegularInvLinear_apply]
  trans BalancedTensor.mk (k := k) (R := R) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := Obj (regular (k := k) (R := R)))
    (r • (show AlgebraInduction.Bimod φ from s)) (1:R)
  · rfl
  trans BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ from s) (r.unop • (show Obj (regular (k := k) (R := R)) from (1:R)))
  · exact BalancedTensor.balance _ _ _
  change BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ from s) (r.unop * (1 * 1)) =
    BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R)))
    (show AlgebraInduction.Bimod φ from s) (1 * (1 * r.unop))
  exact congrArg (fun z : R => BalancedTensor.mk (k := k) (R := R) (S := S)
    (N := Obj (regular (k := k) (R := R))) (show AlgebraInduction.Bimod φ from s)
    (show Obj (regular (k := k) (R := R)) from z)) (show r.unop * ((1:R)*1) = (1:R)*(1*r.unop) by simp only [one_mul, mul_one])

def leftIndRegularInv (φ : R →ₐ[k] S) :
    rightRestrictedRegular φ ⟶ leftIndObj φ (regular (k := k) (R := R)) :=
  ofBimoduleHom
    (show AlgebraInduction.Bimod φ →ₗ[S] _ from leftIndRegularInvLinear φ)
    (leftIndRegularInvLinear_right φ)

def leftIndRegularIso (φ : R →ₐ[k] S) :
    leftIndObj φ (regular (k := k) (R := R)) ≅ rightRestrictedRegular φ where
  hom := leftIndRegularHom φ
  inv := leftIndRegularInv φ
  hom_inv_id := by
    apply leftInd_hom_ext φ
    intro s r
    change leftIndRegularInvLinear φ (show S from leftIndRegularHom φ
      (show leftIndObj φ (regular (k := k) (R := R)) from BalancedTensor.mk s r)) =
      BalancedTensor.mk s r
    trans leftIndRegularInvLinear φ ((show S from s) * φ r)
    · exact congrArg (leftIndRegularInvLinear φ) (leftIndRegularHom_mk φ s r)
    rw [leftIndRegularInvLinear_apply]
    trans BalancedTensor.mk (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj (regular (k := k) (R := R)))
      (MulOpposite.op (show R from r) • s) (1:R)
    · rfl
    trans BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := Obj (regular (k := k) (R := R))) s
      ((show R from r) • (show Obj (regular (k := k) (R := R)) from (1:R)))
    · exact BalancedTensor.balance _ _ _
    change BalancedTensor.mk s (show Obj (regular (k := k) (R := R)) from ((show R from r) * (1*1) : R)) =
      BalancedTensor.mk s r
    exact congrArg (fun z : R => BalancedTensor.mk s
      (show Obj (regular (k := k) (R := R)) from z)) (by exact (congrArg (fun z : R => (show R from r)*z) (one_mul (1:R))).trans (mul_one (show R from r)))
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change (show S from leftIndRegularHom φ (leftIndRegularInvLinear φ (show S from s))) =
      (show S from s)
    trans (show S from leftIndRegularHom φ (BalancedTensor.mk
      (show AlgebraInduction.Bimod φ from s) (show Obj (regular (k := k) (R := R)) from (1:R))))
    · exact congrArg (fun x => (show S from leftIndRegularHom φ x)) (leftIndRegularInvLinear_apply φ s)
    exact (leftIndRegularHom_mk φ _ _).trans
      (show (show S from s) * φ (1:R) = (show S from s) by rw [map_one, mul_one])

def rightRestrictedRegularIso (φ : R →ₐ[k] S) :
    (rightFunctor (k := k) (R := S) (S := R)).obj (rightRestrictedRegular φ) ≅
      (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ) :=
by
  let X := (rightFunctor (k := k) (R := S) (S := R)).obj (rightRestrictedRegular φ)
  let Z := (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Z)
    (m₁ := X.isModule) (m₂ := Z.isModule)
    { toFun := fun x : X =>
        (show (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ) from MulOpposite.op (show S from x))
      invFun := fun x => (show Sᵐᵒᵖ from x).unop
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r x := by
        change MulOpposite.op ((1:S) * ((show S from x) * φ r.unop)) =
          MulOpposite.op ((show S from x) * φ r.unop)
        rw [one_mul] }

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

lemma leftInducedResolution_finite (φ : R →ₐ[k] S) (n : ℕ) :
    Module.Finite (Alg k S R) ((leftInducedResolution φ).complex.X n) := by
  change Module.Finite (Alg k S R)
    ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
  let : FiniteDimensional k ((regularResolution (k := k) (R := R)).complex.X n) :=
    Module.Finite.trans (Alg k R R) _
  exact Module.Finite.of_restrictScalars_finite k _ _

def leftInducedRightResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)) :=
  Tachikawa.transportResolution
    (rightResolutionOf (leftInducedResolution φ) (leftInducedResolution_finite φ))
    ((rightFunctor (k := k) (R := S) (S := R)).mapIso
      ((leftIndComparisonIso φ (regular (k := k) (R := R))) ≪≫ leftIndRegularIso φ) ≪≫
      rightRestrictedRegularIso φ)

def inducedRightFactorIso (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (leftEnvelopingMap (U := R) φ) ⋙
      AlgebraInduction.functor (rightEnvelopingMap (U := S) φ) ≅
      AlgebraInduction.functor (envelopingMap φ) :=
  AlgebraInduction.compositionIso _ _ ≪≫ eqToIso (by
    congr 1
    ext a <;> rfl)

def inducedRightComplexIso (φ : R →ₐ[k] S) :
    rightComplex (inducedRegularComplex φ) ≅
      ((AlgebraInduction.functor φ.op).mapHomologicalComplex _).obj
        (leftInducedRightResolution φ).complex := by
  let P := (regularResolution (k := k) (R := R)).complex
  let J := AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)
  let L := AlgebraInduction.functor (rightEnvelopingMap (U := S) φ)
  let U := rightFunctor (k := k) (R := S) (S := S)
  let V := rightFunctor (k := k) (R := S) (S := R)
  let I := AlgebraInduction.functor φ.op
  let a : L ⋙ U ≅ V ⋙ I :=
    Functor.isoWhiskerRight (rightIndComparison (U := S) φ) U ≪≫
      rightIndUnderlyingComparison (U := S) φ
  let b := Functor.isoWhiskerRight (inducedRightFactorIso φ) U
  exact (NatIso.mapHomologicalComplex b _).symm.app P ≪≫
    (NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft J a) _).app P

def inducedRightHomotopy (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ))) :
    HomotopyEquiv (rightComplex (inducedRegularComplex φ))
      (((AlgebraInduction.functor φ.op).mapHomologicalComplex _).obj Q.complex) :=
  (HomotopyEquiv.ofIso (inducedRightComplexIso φ)).trans
    ((AlgebraInduction.functor φ.op).mapHomotopyEquiv
      (ProjectiveResolution.homotopyEquiv (leftInducedRightResolution φ) Q))

lemma inducedCoker_right_projective (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)))
    (n : ℕ) (hn : CategoryTheory.Limits.IsZero (Q.complex.X (n+1))) :
    Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k S S) (NatCoker.C (inducedRegularComplex φ) n))) := by
  let I := AlgebraInduction.functor φ.op
  let C := (I.mapHomologicalComplex _).obj Q.complex
  have hC : CategoryTheory.Limits.IsZero (C.X (n+1)) := I.map_isZero hn
  let : Subsingleton (C.X (n+1)) := ModuleCat.isZero_iff_subsingleton.mp hC
  exact coker_right_projective_of_homotopy (inducedRegularComplex φ) C n (inducedRightHomotopy φ Q)

end Tachikawa.Enveloping



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

abbrev opTensorB : ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ) ≃ₐ[k] (B q)ᵐᵒᵖ :=
  Algebra.TensorProduct.opAlgEquiv k k (C k q) (C k q)
abbrev opTensorE : ((T q)ᵐᵒᵖ ⊗[k] (T q)ᵐᵒᵖ) ≃ₐ[k] (E q)ᵐᵒᵖ :=
  Algebra.TensorProduct.opAlgEquiv k k (T q) (T q)

def tRightUnderlying : TRightObj q ≃ₗ[k] (T q)ᵐᵒᵖ where
  toFun := MulOpposite.op
  invFun := MulOpposite.unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change MulOpposite.op ((algebraMap k (C k q)ᵐᵒᵖ c) •
      (show C k q × DualBimodule k (C k q) from x)) =
      MulOpposite.op (c • (show C k q × DualBimodule k (C k q) from x))
    exact congrArg MulOpposite.op (IsScalarTower.algebraMap_smul (C k q)ᵐᵒᵖ c _)

lemma tRightUnderlying_smul (r : (C k q)ᵐᵒᵖ) (x : TRightObj q) :
    tRightUnderlying q (r • x) = (inclusionC q).op r * tRightUnderlying q x := by
  apply MulOpposite.unop_injective
  apply TrivSqZeroExt.ext
  · rfl
  · change r • (show C k q × DualBimodule k (C k q) from x).2 =
      (show C k q × DualBimodule k (C k q) from x).1 • (0 : DualBimodule k (C k q)) +
        r • (show C k q × DualBimodule k (C k q) from x).2
    rw [smul_zero, zero_add]

def eRightTensorEquiv : OuterTensor.Obj k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) ≃ₗ[k]
    ((T q)ᵐᵒᵖ ⊗[k] (T q)ᵐᵒᵖ) :=
  TensorProduct.congr (tRightUnderlying q) (tRightUnderlying q)

abbrev inclusionOppTensor : ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ) →ₐ[k] ((T q)ᵐᵒᵖ ⊗[k] (T q)ᵐᵒᵖ) :=
  Algebra.TensorProduct.map (inclusionC q).op (inclusionC q).op

lemma eRightTensorEquiv_action (r : ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ)) :
    (eRightTensorEquiv q).toLinearMap.comp
      (OuterTensor.action k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) r) =
      (LinearMap.mulLeft k (inclusionOppTensor q r)).comp (eRightTensorEquiv q).toLinearMap := by
  induction r using TensorProduct.inductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    change (tRightUnderlying q (a • x)) ⊗ₜ[k] (tRightUnderlying q (b • y)) =
      ((inclusionC q).op a ⊗ₜ[k] (inclusionC q).op b) *
        ((tRightUnderlying q x) ⊗ₜ[k] (tRightUnderlying q y))
    rw [tRightUnderlying_smul, tRightUnderlying_smul, Algebra.TensorProduct.tmul_mul_tmul]
  | add r s hr hs =>
    apply LinearMap.ext
    intro x
    change eRightTensorEquiv q ((OuterTensor.action k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) (r+s)) x) =
      inclusionOppTensor q (r+s) * eRightTensorEquiv q x
    rw [map_add, map_add]
    change eRightTensorEquiv q ((OuterTensor.action k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) r) x +
      (OuterTensor.action k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) s) x) = _
    apply ((eRightTensorEquiv q).map_add _ _).trans
    apply Eq.trans (congrArg₂ (fun a b : (T q)ᵐᵒᵖ ⊗[k] (T q)ᵐᵒᵖ => a+b) (LinearMap.congr_fun hr x) (LinearMap.congr_fun hs x))
    exact (add_mul (inclusionOppTensor q r) (inclusionOppTensor q s) (eRightTensorEquiv q x)).symm

lemma inclusionOppTensor_natural : (opTensorE q).toAlgHom.comp (inclusionOppTensor q) =
    (inclusionB q).op.comp (opTensorB q).toAlgHom := by
  ext a <;> rfl

abbrev opTensorRestriction := ModuleCat.restrictScalars (opTensorB q).symm.toRingHom

def eRightUnderlying : (opTensorRestriction q).obj (ERightObj q) ≃+ (E q)ᵐᵒᵖ :=
  (eRightTensorEquiv q).toAddEquiv.trans (opTensorE q).toAddEquiv

lemma eRightUnderlying_smul (r : (B q)ᵐᵒᵖ) (x : (opTensorRestriction q).obj (ERightObj q)) :
    eRightUnderlying q (r • x) = (inclusionB q).op r * eRightUnderlying q x := by
  change opTensorE q (eRightTensorEquiv q ((opTensorB q).symm r •
      (show OuterTensor.Obj k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) from x))) = _
  apply Eq.trans (congrArg (opTensorE q)
    (LinearMap.congr_fun (eRightTensorEquiv_action q ((opTensorB q).symm r)) x))
  apply Eq.trans ((opTensorE q).map_mul _ _)
  have h := AlgHom.congr_fun (inclusionOppTensor_natural q) ((opTensorB q).symm r)
  have h' : opTensorE q (inclusionOppTensor q ((opTensorB q).symm r)) = (inclusionB q).op r := by
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using h
  exact congrArg (fun a : (E q)ᵐᵒᵖ => a * eRightUnderlying q x) h'

def eRightRestrictionIso : (opTensorRestriction q).obj (ERightObj q) ≅
    (AlgebraInduction.res (inclusionB q).op).obj (ModuleCat.of (E q)ᵐᵒᵖ (E q)ᵐᵒᵖ) := by
  let X := (opTensorRestriction q).obj (ERightObj q)
  let Z := (AlgebraInduction.res (inclusionB q).op).obj (ModuleCat.of (E q)ᵐᵒᵖ (E q)ᵐᵒᵖ)
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Z) (m₁ := X.isModule) (m₂ := Z.isModule)
    { toFun := eRightUnderlying q
      invFun := (eRightUnderlying q).symm
      left_inv := (eRightUnderlying q).left_inv
      right_inv := (eRightUnderlying q).right_inv
      map_add' := (eRightUnderlying q).map_add
      map_smul' := eRightUnderlying_smul q }

end Tachikawa.Construction

end

end OAI
