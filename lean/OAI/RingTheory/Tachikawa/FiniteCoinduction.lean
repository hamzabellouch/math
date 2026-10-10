import OAI.RingTheory.Tachikawa.DerivedDescent

namespace OAI


noncomputable section
namespace Tachikawa
open Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

def dualTensorUnderlying :
    OuterTensor.Obj k R S (dualLeftObj (k := k) (R := R)) (dualLeftObj (k := k) (R := S)) ≃ₗ[k]
      DualBimodule k (R ⊗[k] S) :=
  (TensorProduct.congr (dualLeftUnderlying (k := k) (R := R))
    (dualLeftUnderlying (k := k) (R := S))).trans
    (TensorProduct.dualDistribEquiv k R S)

lemma dualTensorUnderlying_tmul (φ : dualLeftObj (k := k) (R := R))
    (ψ : dualLeftObj (k := k) (R := S)) (r : R) (s : S) :
    dualTensorUnderlying (φ ⊗ₜ[k] ψ) (r ⊗ₜ[k] s) =
      (show DualBimodule k R from φ) r * (show DualBimodule k S from ψ) s := by
  exact mul_comm _ _

def dualTensorLeftEquiv :
    OuterTensor.Obj k R S (dualLeftObj (k := k) (R := R)) (dualLeftObj (k := k) (R := S)) ≃ₗ[R ⊗[k] S]
      DualBimodule k (R ⊗[k] S) where
  __ := (dualTensorUnderlying (k := k) (R := R) (S := S)).toAddEquiv
  map_smul' a z := by
    change dualTensorUnderlying ((OuterTensor.action k R S _ _ a) z) = a • dualTensorUnderlying z
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => erw [map_add,LinearMap.add_apply,map_add,ha,hb,add_smul]
    | tmul r s =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => erw [map_add,map_add,hx,hy,map_add,smul_add]
      | tmul φ ψ =>
        apply TensorProduct.ext'
        intro x y
        change (show DualBimodule k S from ψ) (y*s) * (show DualBimodule k R from φ) (x*r) =
          dualTensorUnderlying (φ ⊗ₜ[k] ψ) ((x ⊗ₜ[k] y) * (r ⊗ₜ[k] s))
        rw [Algebra.TensorProduct.tmul_mul_tmul,dualTensorUnderlying_tmul,mul_comm]

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

def dualRightObj : ModuleCat Rᵐᵒᵖ := ModuleCat.of Rᵐᵒᵖ (DualBimodule k R)

def dualRightUnderlying : dualRightObj (k := k) (R := R) ≃ₗ[k] DualBimodule k R :=
  moduleCatUnderlyingEquiv (k := k) (R := Rᵐᵒᵖ) (DualBimodule k R)

def dualRightTensorUnderlying :
    OuterTensor.Obj k Rᵐᵒᵖ Sᵐᵒᵖ (dualRightObj (k := k) (R := R)) (dualRightObj (k := k) (R := S)) ≃ₗ[k]
      DualBimodule k (R ⊗[k] S) :=
  (TensorProduct.congr (dualRightUnderlying (k := k) (R := R))
    (dualRightUnderlying (k := k) (R := S))).trans
    (TensorProduct.dualDistribEquiv k R S)

lemma dualRightTensorUnderlying_tmul (φ : dualRightObj (k := k) (R := R))
    (ψ : dualRightObj (k := k) (R := S)) (r : R) (s : S) :
    dualRightTensorUnderlying (φ ⊗ₜ[k] ψ) (r ⊗ₜ[k] s) =
      (show DualBimodule k R from φ) r * (show DualBimodule k S from ψ) s := by
  exact mul_comm _ _

lemma dualRightTensor_action (a : Rᵐᵒᵖ ⊗[k] Sᵐᵒᵖ)
    (z : OuterTensor.Obj k Rᵐᵒᵖ Sᵐᵒᵖ (dualRightObj (k := k) (R := R)) (dualRightObj (k := k) (R := S))) :
    dualRightTensorUnderlying ((OuterTensor.action k Rᵐᵒᵖ Sᵐᵒᵖ _ _ a) z) =
      (Algebra.TensorProduct.opAlgEquiv k k R S a) • dualRightTensorUnderlying z := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => erw [map_add,LinearMap.add_apply,map_add,ha,hb,map_add,add_smul]
  | tmul r s =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => erw [map_add,map_add,hx,hy,map_add,smul_add]
    | tmul φ ψ =>
      apply TensorProduct.ext'
      intro x y
      change (show DualBimodule k S from ψ) (s.unop*y) * (show DualBimodule k R from φ) (r.unop*x) =
        dualRightTensorUnderlying (φ ⊗ₜ[k] ψ) ((r.unop ⊗ₜ[k] s.unop) * (x ⊗ₜ[k] y))
      rw [Algebra.TensorProduct.tmul_mul_tmul,dualRightTensorUnderlying_tmul,mul_comm]

def dualRightTensorRestriction :=
  ModuleCat.restrictScalars (Algebra.TensorProduct.opAlgEquiv k k R S).symm.toRingHom

def dualRightTensorIso :
    (dualRightTensorRestriction (k := k) (R := R) (S := S)).obj
      (((OuterTensor.bifunctor k Rᵐᵒᵖ Sᵐᵒᵖ).obj (dualRightObj (k := k) (R := R))).obj
        (dualRightObj (k := k) (R := S))) ≅ dualRightObj (k := k) (R := R ⊗[k] S) := by
  let X := (dualRightTensorRestriction (k := k) (R := R) (S := S)).obj
      (((OuterTensor.bifunctor k Rᵐᵒᵖ Sᵐᵒᵖ).obj (dualRightObj (k := k) (R := R))).obj
        (dualRightObj (k := k) (R := S)))
  let Y := dualRightObj (k := k) (R := R ⊗[k] S)
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Y) (m₁ := X.isModule) (m₂ := Y.isModule)
    { __ := (dualRightTensorUnderlying (k := k) (R := R) (S := S)).toAddEquiv
      map_smul' r x := by
        change dualRightTensorUnderlying ((OuterTensor.action k Rᵐᵒᵖ Sᵐᵒᵖ _ _
          ((Algebra.TensorProduct.opAlgEquiv k k R S).symm r)) x) = r • dualRightTensorUnderlying x
        erw [dualRightTensor_action,AlgEquiv.apply_symm_apply] }


instance dualRightTensorRestriction_additive :
    (dualRightTensorRestriction (k := k) (R := R) (S := S)).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars (Algebra.TensorProduct.opAlgEquiv k k R S).symm.toRingHom).Additive

instance dualRightTensorRestriction_isEquivalence :
    (dualRightTensorRestriction (k := k) (R := R) (S := S)).IsEquivalence :=
  inferInstanceAs (ModuleCat.restrictScalars
    (Algebra.TensorProduct.opAlgEquiv k k R S).symm.toRingEquiv.toRingHom).IsEquivalence
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma cDualLeft_finite (hq : q ≠ 0) (n : ℕ) :
    Module.Finite (C k q) ((C.leftDualProjectiveResolution q hq).complex.X n) := by
  change Module.Finite (C k q) (C.leftDualResObj q n)
  rcases n with _ | _ | _ | n
  · exact inferInstanceAs (Module.Finite (C k q) (C.Ce q × C.Ce q))
  · exact inferInstanceAs (Module.Finite (C k q) (C.Ce q))
  · exact inferInstanceAs (Module.Finite (C k q) (C.Cf q))
  · exact inferInstanceAs (Module.Finite (C k q) PUnit)

lemma cDualRight_finite (hq : q ≠ 0) (n : ℕ) :
    Module.Finite (C k q)ᵐᵒᵖ ((C.rightDualProjectiveResolution q hq).complex.X n) := by
  change Module.Finite (C k q)ᵐᵒᵖ (C.rightDualResObj q n)
  rcases n with _ | _ | _ | n
  · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.eC q × C.eC q))
  · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.eC q))
  · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.fC q))
  · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ PUnit)

lemma cDualLeft_above (hq : q ≠ 0) (n : ℕ) (hn : 2 < n) :
    IsZero ((C.leftDualProjectiveResolution q hq).complex.X n) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
  rw [Nat.add_comm 3 n]
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of (C k q) PUnit)

lemma cDualRight_above (hq : q ≠ 0) (n : ℕ) (hn : 2 < n) :
    IsZero ((C.rightDualProjectiveResolution q hq).complex.X n) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
  rw [Nat.add_comm 3 n]
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of (C k q)ᵐᵒᵖ PUnit)

def bDualLeftResolution (hq : q ≠ 0) :
    ProjectiveResolution (Enveloping.dualLeftObj (k := k) (R := B q)) :=
  Tachikawa.transportResolution
    (OuterTensor.resolution k _ _ (C.leftDualProjectiveResolution q hq)
      (C.leftDualProjectiveResolution q hq) (cDualLeft_finite q hq) (cDualLeft_finite q hq))
    (dualTensorLeftEquiv (k := k) (R := C k q) (S := C k q)).toModuleIso

def bDualRightResolution (hq : q ≠ 0) :
    ProjectiveResolution (dualRightObj (k := k) (R := B q)) :=
  Tachikawa.transportResolution
    ((dualRightTensorRestriction (k := k) (R := C k q) (S := C k q)).mapProjectiveResolution
      (OuterTensor.resolution k _ _ (C.rightDualProjectiveResolution q hq)
        (C.rightDualProjectiveResolution q hq) (cDualRight_finite q hq) (cDualRight_finite q hq)))
    (dualRightTensorIso (k := k) (R := C k q) (S := C k q))

lemma bDualLeft_above (hq : q ≠ 0) (n : ℕ) (hn : 4 < n) :
    IsZero ((bDualLeftResolution q hq).complex.X n) :=
  OuterTensor.total_isZero_above _ _ 2 2 (cDualLeft_above q hq) (cDualLeft_above q hq) n hn

lemma bDualRight_above (hq : q ≠ 0) (n : ℕ) (hn : 4 < n) :
    IsZero ((bDualRightResolution q hq).complex.X n) :=
  (dualRightTensorRestriction (k := k) (R := C k q) (S := C k q)).map_isZero
    (OuterTensor.total_isZero_above _ _ 2 2 (cDualRight_above q hq) (cDualRight_above q hq) n hn)

lemma bDualLeft_dimension (hq : q ≠ 0) :
    HasProjectiveDimensionLE (Enveloping.dualLeftObj (k := k) (R := B q)) 4 := by
  apply HasProjectiveDimensionLT.mk
  intro i hi Y α
  obtain ⟨f,hf,rfl⟩ := (bDualLeftResolution q hq).extMk_surjective α (i+1) rfl
  have h := (bDualLeft_above q hq i (by omega)).eq_of_src f 0
  subst f
  exact (bDualLeftResolution q hq).extMk_zero _ _

lemma bDualRight_dimension (hq : q ≠ 0) :
    HasProjectiveDimensionLE (dualRightObj (k := k) (R := B q)) 4 := by
  apply HasProjectiveDimensionLT.mk
  intro i hi Y α
  obtain ⟨f,hf,rfl⟩ := (bDualRightResolution q hq).extMk_surjective α (i+1) rfl
  have h := (bDualRight_above q hq i (by omega)).eq_of_src f 0
  subst f
  exact (bDualRightResolution q hq).extMk_zero _ _

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def LeftDual (M : ModuleCat Rᵐᵒᵖ) := Module.Dual k M
namespace LeftDual
variable {M N : ModuleCat Rᵐᵒᵖ}
instance : AddCommGroup (LeftDual (k := k) M) := inferInstanceAs (AddCommGroup (Module.Dual k M))
instance : Module k (LeftDual (k := k) M) := inferInstanceAs (Module k (Module.Dual k M))
instance : FunLike (LeftDual (k := k) M) M k := inferInstanceAs (FunLike (Module.Dual k M) M k)
instance : LinearMapClass (LeftDual (k := k) M) k M k := inferInstanceAs (LinearMapClass (Module.Dual k M) k M k)
@[ext] lemma ext {φ ψ : LeftDual (k := k) M} (h : ∀ x, φ x = ψ x) : φ = ψ := LinearMap.ext h
instance : Module R (LeftDual (k := k) M) where
  smul r φ := φ.comp (DistribSMul.toLinearMap k M (MulOpposite.op r))
  one_smul φ := by ext x; change φ ((1 : Rᵐᵒᵖ) • x) = φ x; simp
  mul_smul a b φ := by ext x; change φ (MulOpposite.op (a*b) • x) = φ (MulOpposite.op b • MulOpposite.op a • x); simp [mul_smul]
  smul_zero r := by ext x; rfl
  smul_add r φ ψ := by ext x; rfl
  add_smul r s φ := by ext x; change φ (MulOpposite.op (r+s) • x) = φ (MulOpposite.op r • x) + φ (MulOpposite.op s • x); simp [add_smul]
  zero_smul φ := by ext x; change φ ((0 : Rᵐᵒᵖ) • x) = 0; simp
@[simp] lemma smul_apply (r : R) (φ : LeftDual (k := k) M) (x : M) : (r • φ) x = φ (MulOpposite.op r • x) := rfl
instance : IsScalarTower k R (LeftDual (k := k) M) where
  smul_assoc c r φ := by ext x; change φ (MulOpposite.op (c • r) • x) = c • φ (MulOpposite.op r • x); simp [smul_assoc]
instance : SMulCommClass k R (LeftDual (k := k) M) where
  smul_comm c r φ := by ext x; rfl
instance [FiniteDimensional k M] : FiniteDimensional k (LeftDual (k := k) M) := inferInstanceAs (FiniteDimensional k (Module.Dual k M))

def map (f : M ⟶ N) : LeftDual (k := k) N →ₗ[R] LeftDual (k := k) M where
  toFun φ := φ.comp (f.hom.restrictScalars k)
  map_add' _ _ := rfl
  map_smul' r φ := by ext x; change φ (MulOpposite.op r • f x) = φ (f (MulOpposite.op r • x)); rw [f.hom.map_smul]
@[simp] lemma map_apply (f : M ⟶ N) (φ : LeftDual (k := k) N) (x : M) : map f φ x = φ (f x) := rfl
lemma exact {P : ModuleCat Rᵐᵒᵖ} (f : M ⟶ N) (g : N ⟶ P) (h : Function.Exact f g) : Function.Exact (map (k := k) g) (map (k := k) f) :=
  exact_dual (f.hom.restrictScalars k) (g.hom.restrictScalars k) h
lemma map_injective (f : M ⟶ N) (h : Function.Surjective f) : Function.Injective (map (k := k) f) := by
  intro φ ψ he
  ext x
  obtain ⟨y,rfl⟩ := h x
  exact congrArg (fun a : LeftDual (k := k) M => a y) he
end LeftDual

def RightDual (M : ModuleCat R) := Module.Dual k M
namespace RightDual
variable {M N : ModuleCat R}
instance : AddCommGroup (RightDual (k := k) M) := inferInstanceAs (AddCommGroup (Module.Dual k M))
instance : Module k (RightDual (k := k) M) := inferInstanceAs (Module k (Module.Dual k M))
instance : FunLike (RightDual (k := k) M) M k := inferInstanceAs (FunLike (Module.Dual k M) M k)
instance : LinearMapClass (RightDual (k := k) M) k M k := inferInstanceAs (LinearMapClass (Module.Dual k M) k M k)
@[ext] lemma ext {φ ψ : RightDual (k := k) M} (h : ∀ x, φ x = ψ x) : φ = ψ := LinearMap.ext h
instance : Module Rᵐᵒᵖ (RightDual (k := k) M) where
  smul r φ := φ.comp (DistribSMul.toLinearMap k M r.unop)
  one_smul φ := by ext x; change φ ((1 : R) • x) = φ x; simp
  mul_smul a b φ := by ext x; change φ ((b.unop*a.unop) • x) = φ (b.unop • a.unop • x); rw [mul_smul]
  smul_zero r := by ext x; rfl
  smul_add r φ ψ := by ext x; rfl
  add_smul r s φ := by ext x; change φ ((r.unop+s.unop) • x) = φ (r.unop • x) + φ (s.unop • x); simp [add_smul]
  zero_smul φ := by ext x; change φ ((0 : R) • x) = 0; simp
@[simp] lemma smul_apply (r : Rᵐᵒᵖ) (φ : RightDual (k := k) M) (x : M) : (r • φ) x = φ (r.unop • x) := rfl
instance : IsScalarTower k Rᵐᵒᵖ (RightDual (k := k) M) where
  smul_assoc c r φ := by ext x; change φ ((c • r.unop) • x) = c • φ (r.unop • x); simp [smul_assoc]
instance : SMulCommClass k Rᵐᵒᵖ (RightDual (k := k) M) where
  smul_comm c r φ := by ext x; rfl

def map (f : M ⟶ N) : RightDual (k := k) N →ₗ[Rᵐᵒᵖ] RightDual (k := k) M where
  toFun φ := φ.comp (f.hom.restrictScalars k)
  map_add' _ _ := rfl
  map_smul' r φ := by ext x; change φ (r.unop • f x) = φ (f (r.unop • x)); rw [f.hom.map_smul]
@[simp] lemma map_apply (f : M ⟶ N) (φ : RightDual (k := k) N) (x : M) : map f φ x = φ (f x) := rfl
lemma map_surjective (f : M ⟶ N) (h : Function.Injective f) : Function.Surjective (map (k := k) f) :=
  LinearMap.dualMap_surjective_of_injective h
end RightDual




def dualTranspose {M : ModuleCat R} {P : ModuleCat Rᵐᵒᵖ}
    (g : M →ₗ[R] LeftDual (k := k) P) : P →ₗ[Rᵐᵒᵖ] RightDual (k := k) M where
  toFun p :=
    { toFun := fun x => g x p
      map_add' x y := by change g (x+y) p = g x p + g y p; rw [g.map_add]; rfl
      map_smul' c x := by
        change g (c • x) p = c • g x p
        exact congrArg (fun φ : LeftDual (k := k) P => φ p)
          ((g.restrictScalars k).map_smul c x) }
  map_add' p q := by ext x; exact (g x).map_add p q
  map_smul' r p := by
    ext x
    change g x (r • p) = g (r.unop • x) p
    rw [g.map_smul]
    rfl

def dualUntranspose {M : ModuleCat R} {P : ModuleCat Rᵐᵒᵖ}
    (g : P →ₗ[Rᵐᵒᵖ] RightDual (k := k) M) : M →ₗ[R] LeftDual (k := k) P where
  toFun x :=
    { toFun := fun p => g p x
      map_add' p q := by change g (p+q) x = g p x + g q x; rw [g.map_add]; rfl
      map_smul' c p := by
        change g (c • p) x = c • g p x
        exact congrArg (fun φ : RightDual (k := k) M => φ x)
          ((g.restrictScalars k).map_smul c p) }
  map_add' x y := by ext p; exact (g p).map_add x y
  map_smul' r x := by
    ext p
    change g p (r • x) = g (MulOpposite.op r • p) x
    rw [g.map_smul]
    rfl

instance leftDual_injective (P : ModuleCat Rᵐᵒᵖ) [Module.Projective Rᵐᵒᵖ P] :
    Module.Injective R (LeftDual (k := k) P) where
  out {X Y} _ _ _ _ f hf g := by
    let : Module k X := Module.compHom X (algebraMap k R)
    let : Module k Y := Module.compHom Y (algebraMap k R)
    let : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let : IsScalarTower k R Y := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let X' : ModuleCat R := ModuleCat.of R X
    let Y' : ModuleCat R := ModuleCat.of R Y
    let f' : X' ⟶ Y' := ModuleCat.ofHom f
    let g' : X' →ₗ[R] LeftDual (k := k) P := g
    obtain ⟨h,hh⟩ := Module.projective_lifting_property (RightDual.map (k := k) f')
      (dualTranspose g') (RightDual.map_surjective f' hf)
    refine ⟨dualUntranspose (M := Y') h, ?_⟩
    intro x
    apply LeftDual.ext
    intro p
    exact congrArg (fun φ : RightDual (k := k) X' => φ x) (LinearMap.congr_fun hh p)

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def leftDualObj (M : ModuleCat Rᵐᵒᵖ) : ModuleCat R := ModuleCat.of R (LeftDual (k := k) M)

def dualResolution {M : ModuleCat Rᵐᵒᵖ} (P : ProjectiveResolution M) :
    InjectiveResolution (leftDualObj (k := k) M) := by
  let J (n : ℕ) := leftDualObj (k := k) (P.complex.X n)
  let d (n : ℕ) : J n ⟶ J (n+1) := ModuleCat.ofHom (LeftDual.map (P.complex.d (n+1) n))
  let ε : leftDualObj (k := k) M ⟶ J 0 := ModuleCat.ofHom (LeftDual.map (P.π.f 0))
  apply coresolutionOfExact _ J d ε
  · intro n
    exact LeftDual.exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (P.exact_succ n))
  · exact LeftDual.exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 P.exact₀)
  · have hπ := (ModuleCat.epi_iff_surjective (P.π.f 0)).1 inferInstance
    exact LeftDual.map_injective _ hπ
  · intro n
    let : Projective (P.complex.X n) := P.projective n
    let : Module.Projective Rᵐᵒᵖ (P.complex.X n) := inferInstance
    exact Module.injective_object_of_injective_module R (LeftDual (k := k) (P.complex.X n))

lemma leftDualObj_isZero {M : ModuleCat Rᵐᵒᵖ} (hM : IsZero M) :
    IsZero (leftDualObj (k := k) M) := by
  have hm (x : M) : x = 0 := by
    have h := hM.eq_of_src (𝟙 M) 0
    exact congrArg (fun f : M ⟶ M => f x) h
  have : Subsingleton (LeftDual (k := k) M) := by
    constructor
    intro φ ψ
    apply LeftDual.ext
    intro x
    rw [hm x]
    exact map_zero φ |>.trans (map_zero ψ).symm
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (LeftDual (k := k) M))

lemma dualResolution_above {M : ModuleCat Rᵐᵒᵖ} (P : ProjectiveResolution M)
    (d : ℕ) (h : ∀ n, d < n → IsZero (P.complex.X n)) (n : ℕ) (hn : d < n) :
    IsZero ((dualResolution (k := k) P).cocomplex.X n) :=
  leftDualObj_isZero (h n hn)

lemma dualResolution_ext_zero {M : ModuleCat Rᵐᵒᵖ} (P : ProjectiveResolution M)
    (d : ℕ) (h : ∀ n, d < n → IsZero (P.complex.X n)) (X : ModuleCat R) (n : ℕ) (hn : d < n) :
    Subsingleton (Abelian.Ext X (leftDualObj (k := k) M) n) := by
  have hz (α : Abelian.Ext X (leftDualObj (k := k) M) n) : α = 0 := by
    obtain ⟨f,hf,rfl⟩ := (dualResolution (k := k) P).extMk_surjective α (n+1) rfl
    have hzero := (dualResolution_above P d h n hn).eq_of_tgt f 0
    subst f
    exact (dualResolution (k := k) P).extMk_zero _ _
  exact ⟨fun α β => (hz α).trans (hz β).symm⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

def doubleDualRegularEquiv : R ≃ₗ[R] LeftDual (k := k) (dualRightObj (k := k) (R := R)) where
  __ := ((Module.evalEquiv k R).trans (dualRightUnderlying (k := k) (R := R)).dualMap).toAddEquiv
  map_smul' r x := by
    apply LeftDual.ext
    intro φ
    change (show DualBimodule k R from φ) (r*x) = (show DualBimodule k R from (MulOpposite.op r) • φ) x
    rfl

def doubleDualRegularIso : ModuleCat.of R R ≅ leftDualObj (k := k) (dualRightObj (k := k) (R := R)) :=
  doubleDualRegularEquiv.toModuleIso

namespace Construction
variable [CharP k 2] (q : k)

lemma b_regular_ext_zero (hq : q ≠ 0) (V : ModuleCat (B q)) (n : ℕ) (hn : 4 < n) :
    Subsingleton (Abelian.Ext V (ModuleCat.of (B q) (B q)) n) := by
  let : Subsingleton (Abelian.Ext V (leftDualObj (k := k) (dualRightObj (k := k) (R := B q))) n) :=
    dualResolution_ext_zero (bDualRightResolution q hq) 4 (bDualRight_above q hq) V n hn
  exact (extIso (k := k) (Iso.refl V) (doubleDualRegularIso (k := k) (R := B q)) n).injective.subsingleton

end Construction
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R M : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [FiniteDimensional k M] [Module.Injective R M]

omit [FiniteDimensional k R] in

lemma finite_injective_retract_dual :
    ∃ (n : ℕ) (i : M →ₗ[R] (Fin n → DualBimodule k R))
      (p : (Fin n → DualBimodule k R) →ₗ[R] M), p.comp i = LinearMap.id := by
  let i := finiteCoinducedEmbedding (k := k) (R := R) (M := M)
  obtain ⟨s,hs⟩ := Module.Injective.extension_property R M M _ i
    finiteCoinducedEmbedding_injective LinearMap.id
  exact ⟨_,i,s,hs⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

lemma finiteInjective_inAdd (M : ModuleCat R) [FiniteDimensional k M] [Injective M] :
    InAdd (Enveloping.dualLeftObj (k := k) (R := R)) M := by
  let : Module.Injective R M := Module.injective_module_of_injective_object R M
  obtain ⟨n,i,p,hp⟩ := finite_injective_retract_dual (k := k) (R := R) (M := M)
  let e := ModuleCat.biproductIsoPi (fun _ : Fin n => Enveloping.dualLeftObj (k := k) (R := R))
  refine ⟨n,⟨{i := ModuleCat.ofHom i ≫ e.inv, r := e.hom ≫ ModuleCat.ofHom p, retract := ?_}⟩⟩
  erw [Category.assoc,← Category.assoc e.inv,e.inv_hom_id,Category.id_comp]
  exact ModuleCat.hom_ext hp

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def bRegularLeftObj : ModuleCat (B q) := ModuleCat.of (B q) (B q)

instance : FiniteDimensional k (bRegularLeftObj q) :=
  moduleCatFinite (k := k) (R := B q) (B q)

lemma b_injectiveDimension (hq : q ≠ 0) : HasInjectiveDimensionLE (bRegularLeftObj q) 4 := by
  apply HasInjectiveDimensionLT.mk
  intro n hn V e
  let : Subsingleton (Abelian.Ext V (bRegularLeftObj q) n) := b_regular_ext_zero q hq V n (by omega)
  exact Subsingleton.elim _ _

lemma b_iterate_injective (hq : q ≠ 0) :
    Injective ((LeftCoinduced.iterate (k := k) 4).obj (bRegularLeftObj q)) := by
  let := b_injectiveDimension q hq
  exact LeftCoinduced.iterate_injective _ 4

lemma b_iterate_inAdd (hq : q ≠ 0) :
    InAdd (Enveloping.dualLeftObj (k := k) (R := B q))
      ((LeftCoinduced.iterate (k := k) 4).obj (bRegularLeftObj q)) := by
  let := b_iterate_injective q hq
  exact finiteInjective_inAdd _

omit [CharP k 2] in
lemma b_coindTerm_inAdd (n : ℕ) :
    InAdd (Enveloping.dualLeftObj (k := k) (R := B q))
      ((LeftCoinduced.J (k := k)).obj
        ((LeftCoinduced.iterate (k := k) n).obj (bRegularLeftObj q))) :=
  by
    exact finiteInjective_inAdd _

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable [FiniteDimensional k R]

instance rightFree_preservesFiniteColimits : PreservesFiniteColimits (rightFreeFunctor (k := k) (R := R) (S := S)) :=
  inferInstanceAs (PreservesFiniteColimits ((OuterTensor.bifunctor k R Sᵐᵒᵖ).flip.obj (rightRegularObj (S := S))))
instance rightFree_preservesFiniteLimits : PreservesFiniteLimits (rightFreeFunctor (k := k) (R := R) (S := S)) :=
  inferInstanceAs (PreservesFiniteLimits ((OuterTensor.bifunctor k R Sᵐᵒᵖ).flip.obj (rightRegularObj (S := S))))

def coindCokerTensorIso (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.C (k := k)).obj M) ≅
      (coindCoker (k := k)).obj (rightFreeObj (k := k) (S := S) M) := by
  let F := rightFreeFunctor (k := k) (R := R) (S := S)
  have h := LeftCoinduced.short_exact (k := k) M
  let := h.mono_f
  let := h.epi_g
  have hF : ((LeftCoinduced.short (k := k) M).map F).ShortExact := h.map F
  refine CokernelCofork.mapIsoOfIsColimit hF.gIsCokernel
    (coindShort_exact (rightFreeObj (k := k) (S := S) M)).gIsCokernel ?_
  refine Arrow.isoMk (Iso.refl _) (coindTensorIso M) ?_
  simpa only [F, LeftCoinduced.short, coindShort, ShortComplex.map, Arrow.mk,
    Iso.refl_hom, Category.id_comp] using (coindTensor_unit (k := k) (S := S) M).symm

def coindIterateTensorIso (M : ModuleCat R) : ∀ n : ℕ,
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.iterate (k := k) n).obj M) ≅
      (coindIterate (k := k) n).obj (rightFreeObj (k := k) (S := S) M)
  | 0 => Iso.refl _
  | n+1 => coindCokerTensorIso ((LeftCoinduced.iterate (k := k) n).obj M) ≪≫
      (coindCoker (k := k)).mapIso (coindIterateTensorIso M n)

def coindTermTensorIso (M : ModuleCat R) (n : ℕ) :
    rightFreeObj (k := k) (S := S)
      ((LeftCoinduced.J (k := k)).obj ((LeftCoinduced.iterate (k := k) n).obj M)) ≅
      coindTerm (rightFreeObj (k := k) (S := S) M) n :=
  coindTensorIso ((LeftCoinduced.iterate (k := k) n).obj M) ≪≫
    (coindEndo (k := k)).mapIso (coindIterateTensorIso M n)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def leftRegularObj : ModuleCat R := ModuleCat.of R R

def leftRegularUnderlying : leftRegularObj (R := R) ≃ₗ[k] R :=
  moduleCatUnderlyingEquiv (k := k) (R := R) R

def rightRegularUnderlying : rightRegularObj (S := S) ≃ₗ[k] Sᵐᵒᵖ :=
  moduleCatUnderlyingEquiv (k := k) (R := Sᵐᵒᵖ) Sᵐᵒᵖ

def regularOuterUnderlying :
    rightFreeObj (k := k) (S := S) (leftRegularObj (R := R)) ≃ₗ[k] Alg k R S :=
  (rightFreeUnderlying _).trans
    (TensorProduct.congr (leftRegularUnderlying (k := k) (R := R))
      (rightRegularUnderlying (k := k) (S := S)))

lemma regularOuterUnderlying_tmul (r : leftRegularObj (R := R)) (s : rightRegularObj (S := S)) :
    regularOuterUnderlying (k := k) (r ⊗ₜ[k] s) = (show R from r) ⊗ₜ[k] (show Sᵐᵒᵖ from s) := rfl

def regularOuterEquiv :
    rightFreeObj (k := k) (S := S) (leftRegularObj (R := R)) ≃ₗ[Alg k R S] Alg k R S where
  __ := (regularOuterUnderlying (k := k) (R := R) (S := S)).toAddEquiv
  map_smul' a z := by
    change regularOuterUnderlying (OuterTensor.action k R Sᵐᵒᵖ _ _ a z) =
      a * regularOuterUnderlying z
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => erw [map_add,LinearMap.add_apply,map_add,ha,hb,add_mul]
    | tmul a b =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => erw [map_add,map_add,hx,hy,map_add,mul_add]
      | tmul x y =>
        change (a*(show R from x)) ⊗ₜ[k] (b*(show Sᵐᵒᵖ from y)) =
          (a ⊗ₜ[k] b) * ((show R from x) ⊗ₜ[k] (show Sᵐᵒᵖ from y))
        exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

def regularOuterIso :
    rightFreeObj (k := k) (S := S) (leftRegularObj (R := R)) ≅ ModuleCat.of (Alg k R S) (Alg k R S) :=
  (regularOuterEquiv (k := k) (R := R) (S := S)).toModuleIso

lemma finiteProjective_inAdd_outer (M : ModuleCat (Alg k R S))
    [Module.Finite (Alg k R S) M] [Module.Projective (Alg k R S) M] :
    InAdd (rightFreeObj (k := k) (S := S) (leftRegularObj (R := R))) M := by
  obtain ⟨n,⟨r⟩⟩ := finiteProjective_inAdd M
  let e := biproduct.mapIso (fun _ : Fin n => (regularOuterIso (k := k) (R := R) (S := S)).symm)
  exact ⟨n,⟨r.trans e.retract⟩⟩

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma InAdd.trans {W V X : C} (h : InAdd W V) (h' : InAdd V X) : InAdd W X := by
  classical
  obtain ⟨n,⟨r⟩⟩ := h
  obtain ⟨m,⟨s⟩⟩ := h'
  let t : Retract (⨁ fun _ : Fin m => V) (⨁ fun _ : Fin m => ⨁ fun _ : Fin n => W) :=
    { i := biproduct.map (fun _ => r.i)
      r := biproduct.map (fun _ => r.r)
      retract := by
        apply biproduct.hom_ext
        intro j
        simp only [Category.assoc,biproduct.map_π,biproduct.map_π_assoc,Category.id_comp,
          r.retract,Category.comp_id] }
  let e := biproductBiproductIso (fun _ : Fin m => Fin n) (fun _ _ => W)
  let d := biproduct.whiskerEquiv (f := fun _ : Σ _ : Fin m, Fin n => W)
    (g := fun _ : Fin (Fintype.card (Σ _ : Fin m, Fin n)) => W)
    (Fintype.equivFin _) (fun _ => Iso.refl _)
  exact ⟨_,⟨s.trans (t.trans (e.retract.trans d.retract))⟩⟩

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma b_outerCoindTerm_inAdd (n : ℕ) :
    InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q))
      (Enveloping.coindTerm
        (Enveloping.rightFreeObj (k := k) (S := B q) (bRegularLeftObj q)) n) :=
  ((b_coindTerm_inAdd q n).map (Enveloping.rightFreeFunctor (k := k) (S := B q))).iso
    (Enveloping.coindTermTensorIso (bRegularLeftObj q) n).symm

lemma b_outerIterate_inAdd (hq : q ≠ 0) :
    InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q))
      ((Enveloping.coindIterate (k := k) 4).obj
        (Enveloping.rightFreeObj (k := k) (S := B q) (bRegularLeftObj q))) :=
  ((b_iterate_inAdd q hq).map (Enveloping.rightFreeFunctor (k := k) (S := B q))).iso
    (Enveloping.coindIterateTensorIso (bRegularLeftObj q) 4).symm

theorem b_projective_coinduced_terms (hq : q ≠ 0)
    (L : ModuleCat (Enveloping.Alg k (B q) (B q)))
    [Module.Finite (Enveloping.Alg k (B q) (B q)) L]
    [Module.Projective (Enveloping.Alg k (B q) (B q)) L] :
    (∀ n : ℕ, InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q))
      (Enveloping.coindTerm L n)) ∧
    InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q))
      ((Enveloping.coindIterate (k := k) 4).obj L) := by
  have hL : InAdd (Enveloping.rightFreeObj (k := k) (S := B q) (bRegularLeftObj q)) L :=
    Enveloping.finiteProjective_inAdd_outer L
  constructor
  · intro n
    exact (b_outerCoindTerm_inAdd q n).trans
      (hL.map (Enveloping.coindIterate (k := k) n ⋙ Enveloping.coindEndo))
  · exact (b_outerIterate_inAdd q hq).trans (hL.map (Enveloping.coindIterate (k := k) 4))

omit [CharP k 2] in

theorem b_add_two_orthogonalities
    (V : ModuleCat (Enveloping.Alg k (B q) (B q)))
    (hV : InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q)) V) (n : ℕ) :
    Subsingleton (Abelian.Ext (Enveloping.regular (k := k) (R := B q)) V (n+1)) ∧
    Subsingleton (Abelian.Ext V (Enveloping.dualRegularObj (k := k) (R := B q)) (n+1)) := by
  let := Enveloping.regular_outer_ext_zero (k := k) (R := B q) n
  let := Enveloping.outer_dual_ext_zero (k := k) (R := B q) n
  exact ⟨ext_subsingleton_inAdd_right hV (n+1),ext_subsingleton_inAdd_left hV (n+1)⟩

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open HomologicalComplex CochainComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def shortExactReplacementMap (S : ShortComplex (CochainComplex C ℤ))
    {Q : CochainComplex C ℤ} (α : S.X₃ ⟶ Q) : S.X₁ ⟶ mappingCocone (S.g ≫ α) :=
  let h := mappingCone.descShortComplex S ≫ α
  let w : mappingCone.inr S.f ≫ h = (𝟙 S.X₂) ≫ (S.g ≫ α) := by
    simp [h,← Category.assoc,mappingCone.inr_descShortComplex]
  (shiftFunctorCompIsoId (CochainComplex C ℤ) (1 : ℤ) (-1) (by omega)).inv.app S.X₁ ≫
    ((mappingCone.rotateHomotopyEquiv S.f).hom ≫
      mappingCone.map (mappingCone.inr S.f) (S.g ≫ α) (𝟙 _) h w)⟦(-1 : ℤ)⟧'

lemma shortExactReplacementMap_quasiIso (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) {Q : CochainComplex C ℤ} (α : S.X₃ ⟶ Q) [QuasiIso α] :
    QuasiIso (shortExactReplacementMap S α) := by
  have := mappingCone.quasiIso_descShortComplex hS
  have : QuasiIso (mappingCone.descShortComplex S ≫ α) := inferInstance
  dsimp only [shortExactReplacementMap]
  have := mappingCone_map_quasiIso (mappingCone.inr S.f) (S.g ≫ α) (𝟙 S.X₂)
    (mappingCone.descShortComplex S ≫ α) (by
      simp [← Category.assoc,mappingCone.inr_descShortComplex])
  have hr : QuasiIso (mappingCone.rotateHomotopyEquiv S.f).hom :=
    (mappingCone.rotateHomotopyEquiv S.f).quasiIso_hom
  have hc : QuasiIso ((mappingCone.rotateHomotopyEquiv S.f).hom ≫
      mappingCone.map (mappingCone.inr S.f) (S.g ≫ α) (𝟙 S.X₂)
        (mappingCone.descShortComplex S ≫ α) (by
          simp [← Category.assoc,mappingCone.inr_descShortComplex])) := inferInstance
  have hs := (CochainComplex.quasiIso_shift_iff _ (-1)).2 hc
  have he : QuasiIso
      ((shiftFunctorCompIsoId (CochainComplex C ℤ) (1 : ℤ) (-1) (by omega)).inv.app S.X₁) := by
    exact quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := he) (hφ' := hs)

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma InAdd.biproduct {W : C} {ι : Type} [Fintype ι] (V : ι → C)
    (h : ∀ i, InAdd W (V i)) : InAdd W (⨁ V) := by
  classical
  choose n r using h
  let s (i : ι) := (r i).some
  let t : Retract (⨁ V) (⨁ fun i : ι => ⨁ fun _ : Fin (n i) => W) :=
    { i := biproduct.map (fun i => (s i).i)
      r := biproduct.map (fun i => (s i).r)
      retract := by
        apply biproduct.hom_ext
        intro j
        simp only [Category.assoc,biproduct.map_π,biproduct.map_π_assoc,Category.id_comp,
          (s j).retract,Category.comp_id] }
  let e := biproductBiproductIso (fun i : ι => Fin (n i)) (fun _ _ => W)
  let d := biproduct.whiskerEquiv (f := fun _ : Σ i : ι, Fin (n i) => W)
    (g := fun _ : Fin (Fintype.card (Σ i : ι, Fin (n i))) => W)
    (Fintype.equivFin _) (fun _ => Iso.refl _)
  exact ⟨_,⟨t.trans (e.retract.trans d.retract)⟩⟩

lemma InAdd.biprod {W X Y : C} (hX : InAdd W X) (hY : InAdd W Y) :
    InAdd W (X ⊞ Y) := by
  have h : ∀ i, InAdd W (pairFunction X Y i) := by
    intro i
    cases i
    · exact hX
    · exact hY
  let e := biprod.uniqueUpToIso X Y
    ((Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit (pairFunction X Y)))
  exact (InAdd.biproduct _ h).iso e.symm

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

structure CoindReplacement (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) where
  complex : CochainComplex (ModuleCat (Alg k R S)) ℤ
  map : P ⟶ complex
  quasiIso : QuasiIso map

attribute [instance] CoindReplacement.quasiIso

def coindReplacement : (n : ℕ) → (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) → CoindReplacement P
  | 0, P => ⟨P,𝟙 P,inferInstance⟩
  | n+1, P =>
    let t := coindReplacement n (cokerComplex P)
    { complex := mappingCocone (coindComplexπ P ≫ t.map)
      map := shortExactReplacementMap (coindComplexShort P) t.map
      quasiIso := by
        exact @shortExactReplacementMap_quasiIso _ _ _ (coindComplexShort P)
          (coindComplexShort_exact P) _ t.map t.quasiIso }

def CoindGoodTerms (W : ModuleCat (Alg k R S)) :
    ℕ → CochainComplex (ModuleCat (Alg k R S)) ℤ → Prop
  | 0, P => ∀ i, InAdd W (P.X i)
  | n+1, P => (∀ i, InAdd W ((coindComplex P).X i)) ∧ CoindGoodTerms W n (cokerComplex P)

lemma mappingCocone_inAdd {W : ModuleCat (Alg k R S)}
    {K L : CochainComplex (ModuleCat (Alg k R S)) ℤ} (f : K ⟶ L)
    (hK : ∀ i, InAdd W (K.X i)) (hL : ∀ i, InAdd W (L.X i)) (i : ℤ) :
    InAdd W ((mappingCocone f).X i) := by
  let e : (mappingCocone f).X i ≅ K.X i ⊞ L.X (i + -1) :=
    shiftFunctorObjXIso (mappingCone f) (-1) i (i + -1) (by omega) ≪≫
      homotopyCofiber.XIsoBiprod f (i + -1) i (by change (i + -1) + 1 = i; omega)
  exact ((hK i).biprod (hL (i + -1))).iso e

lemma coindReplacement_terms (W : ModuleCat (Alg k R S)) (n : ℕ)
    (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) (h : CoindGoodTerms W n P) :
    ∀ i, InAdd W ((coindReplacement n P).complex.X i) := by
  induction n generalizing P with
  | zero => exact h
  | succ n ih =>
    exact mappingCocone_inAdd _ h.1 (ih (cokerComplex P) h.2)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

lemma mappingCocone_isZero_X {K L : CochainComplex (ModuleCat (Alg k R S)) ℤ}
    (f : K ⟶ L) (i : ℤ) (hK : IsZero (K.X i)) (hL : IsZero (L.X (i-1))) :
    IsZero ((mappingCocone f).X i) := by
  let e : (mappingCocone f).X i ≅ K.X i ⊞ L.X (i-1) :=
    shiftFunctorObjXIso (mappingCone f) (-1) i (i-1) (by omega) ≪≫
      homotopyCofiber.XIsoBiprod f (i-1) i (by change i-1+1=i; omega)
  exact IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨hK,hL⟩) e

lemma coindReplacement_bounded (n : ℕ)
    (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) (l u : ℤ)
    (hP : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∀ i, i < l ∨ u + n < i → IsZero ((coindReplacement n P).complex.X i) := by
  induction n generalizing P with
  | zero => simpa only [coindReplacement, Nat.cast_zero, add_zero] using hP
  | succ n ih =>
    intro i hi
    apply mappingCocone_isZero_X
    · exact (coindEndo (k := k)).map_isZero (hP i (by omega))
    · apply ih (cokerComplex P)
      · intro j hj
        exact (coindCoker (k := k)).map_isZero (hP j hj)
      · omega

end Tachikawa.Enveloping



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma b_coindGoodTerms (hq : q ≠ 0)
    (P : CochainComplex (ModuleCat (Enveloping.Alg k (B q) (B q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (B q) (B q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (B q) (B q)) (P.X i)) :
    Enveloping.CoindGoodTerms (Enveloping.ordinaryOuterObj (k := k) (R := B q)) 4 P := by
  have h (i : ℤ) := by
    let := hfin i
    let := hproj i
    exact b_projective_coinduced_terms q hq (P.X i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact (h i).1 0
  · intro i; exact (h i).1 1
  · intro i; exact (h i).1 2
  · intro i; exact (h i).1 3
  · intro i; exact (h i).2

theorem b_bounded_ordinary_replacement (hq : q ≠ 0)
    (P : CochainComplex (ModuleCat (Enveloping.Alg k (B q) (B q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (B q) (B q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (B q) (B q)) (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i)) :
    ∃ (P' : CochainComplex (ModuleCat (Enveloping.Alg k (B q) (B q))) ℤ) (f : P ⟶ P'),
      QuasiIso f ∧
      (∀ i, InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q)) (P'.X i)) ∧
      (∀ i, i < l ∨ u + 4 < i → IsZero (P'.X i)) := by
  refine ⟨(Enveloping.coindReplacement 4 P).complex,
    (Enveloping.coindReplacement 4 P).map, inferInstance, ?_, ?_⟩
  · exact Enveloping.coindReplacement_terms _ 4 P (b_coindGoodTerms q hq P hfin hproj)
  · exact Enveloping.coindReplacement_bounded 4 P l u hbound

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {k : Type} [Field k] [CharP k 2] (q : k)

theorem b_ordinary_factorization (hq : q ≠ 0)
    (P : CochainComplex (ModuleCat (Enveloping.Alg k (B q) (B q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (B q) (B q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (B q) (B q)) (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (v : Enveloping.regular (k := k) (R := B q) ⟶ Enveloping.dualRegularObj (k := k) (R := B q))
    (α : DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (Enveloping.regular (k := k) (R := B q))) ⟶ DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (Enveloping.dualRegularObj (k := k) (R := B q))))
    (hv : α ≫ β = DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map v)) :
    ∃ (V : ModuleCat (Enveloping.Alg k (B q) (B q)))
      (a : Enveloping.regular (k := k) (R := B q) ⟶ V)
      (b : V ⟶ Enveloping.dualRegularObj (k := k) (R := B q)),
      InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q)) V ∧ a ≫ b = v := by
  obtain ⟨P',f,hf,ht,hb⟩ := b_bounded_ordinary_replacement q hq P hfin hproj l u hbound
  let := hf
  have he : (α ≫ DerivedCategory.Q.map f) ≫ (inv (DerivedCategory.Q.map f) ≫ β) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map v) := by
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hv
  obtain ⟨a,b,hab⟩ := bounded_ordinary_factorization
    (Enveloping.regularResolution (k := k) (R := B q))
    (injectiveResolution (Enveloping.dualRegularObj (k := k) (R := B q)))
    P' l (u+4) hb ht
    (Enveloping.regular_outer_ext_zero (k := k) (R := B q))
    (Enveloping.outer_dual_ext_zero (k := k) (R := B q)) v
    (α ≫ DerivedCategory.Q.map f) (inv (DerivedCategory.Q.map f) ≫ β) he
  exact ⟨P'.X 0,a,b,ht 0,hab⟩

end Tachikawa.Construction

end

end OAI
