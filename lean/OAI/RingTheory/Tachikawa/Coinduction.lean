import OAI.RingTheory.Tachikawa.RightInduction

namespace OAI


noncomputable section
namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

lemma z_fixed_e : MulOpposite.op (e q) • dualCoeff q 4 = dualCoeff q 4 := by
  ext a
  change (e q * a) 4 = a 4
  rw [e_mul]
  rfl

lemma v_fixed_e : MulOpposite.op (e q) • dualCoeff q 6 = dualCoeff q 6 := by
  ext a
  change (e q * a) 6 = a 6
  rw [e_mul]
  rfl

def rightDualZ : eC q →ₗ[(C k q)ᵐᵒᵖ] DualBimodule k (C k q) :=
  RightCorner.lift (dualCoeff q 4) (z_fixed_e q)

def rightDualV : eC q →ₗ[(C k q)ᵐᵒᵖ] DualBimodule k (C k q) :=
  RightCorner.lift (dualCoeff q 6) (v_fixed_e q)

lemma rightDualZ_ec (a b c d u v : k) (x : C k q) :
    rightDualZ q (ec q a b c d u v) x =
      a*x 4 + d*x 0 + q*b*x 3 + c*x 2 + u*x 8 + q*v*x 7 := rfl

lemma rightDualV_ec (a b c d u v : k) (x : C k q) :
    rightDualV q (ec q a b c d u v) x =
      a*x 6 + v*x 1 + b*x 5 + c*x 5 + u*x 9 := rfl

def rightDualAug : (eC q × eC q) →ₗ[(C k q)ᵐᵒᵖ] DualBimodule k (C k q) :=
  (rightDualZ q).coprod (rightDualV q)

lemma rightDualAug_surjective (hq : q ≠ 0) : Function.Surjective (rightDualAug q) := by
  intro φ
  refine ⟨(ec q (φ (basis q 4)) (φ (basis q 3)/q) (φ (basis q 2))
    (φ (basis q 0)) (φ (basis q 8)) (φ (basis q 7)/q),
    ec q (φ (basis q 6)) (φ (basis q 5)) 0 0 (φ (basis q 9)) (φ (basis q 1))), ?_⟩
  change (_ : Module.Dual k (C k q)) = φ
  apply (basis q).ext
  intro i
  change rightDualZ q _ (basis q i) + rightDualV q _ (basis q i) = φ (basis q i)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, rightDualZ_ec, rightDualV_ec]
  fin_cases i <;> simp [basis_apply] <;> field_simp

lemma rightDualAug_apply (x y : eC q) (a : C k q) :
    rightDualAug q (x,y) a =
      x.val 0*a 4 + x.val 4*a 0 + q*x.val 2*a 3 + x.val 3*a 2 +
      x.val 5*a 8 + q*x.val 6*a 7 +
      (y.val 0*a 6 + y.val 6*a 1 + y.val 2*a 5 + y.val 3*a 5 + y.val 5*a 9) := by
  rw [← ec_eta q x, ← ec_eta q y]
  rfl

lemma rightDualAug_eq_zero_iff (hq : q ≠ 0) (x y : eC q) :
    rightDualAug q (x,y) = 0 ↔ x = 0 ∧ y.val 0 = 0 ∧
      y.val 2 + y.val 3 = 0 ∧ y.val 5 = 0 ∧ y.val 6 = 0 := by
  constructor
  · intro hh
    have h (i : Fin 10) := congrArg (fun ψ : DualBimodule k (C k q) => ψ (basis q i)) hh
    simp only [rightDualAug_apply, DualBimodule.zero_apply] at h
    have hx0 : x.val 0 = 0 := by simpa [basis_apply] using h 4
    have hx2 : x.val 2 = 0 := by simpa [basis_apply, hq] using h 3
    have hx3 : x.val 3 = 0 := by simpa [basis_apply] using h 2
    have hx4 : x.val 4 = 0 := by simpa [basis_apply] using h 0
    have hx5 : x.val 5 = 0 := by simpa [basis_apply] using h 8
    have hx6 : x.val 6 = 0 := by simpa [basis_apply, hq] using h 7
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← ec_eta q x, ec_eq_zero]
      exact ⟨hx0,hx2,hx3,hx4,hx5,hx6⟩
    · simpa [basis_apply] using h 6
    · simpa [basis_apply] using h 5
    · simpa [basis_apply] using h 9
    · simpa [basis_apply] using h 1
  · rintro ⟨rfl, hy0, hy2, hy5, hy6⟩
    ext a
    rw [rightDualAug_apply]
    change _ = 0
    simp only [Submodule.coe_zero, zero_apply, zero_mul, add_zero, zero_add, hy0, hy5, hy6]
    rw [← _root_.add_mul, hy2, zero_mul]
    simp

def rightDualD₁ : eC q →ₗ[(C k q)ᵐᵒᵖ] (eC q × eC q) :=
  (0 : eC q →ₗ[(C k q)ᵐᵒᵖ] eC q).prod (lambdaEll q 1)

variable [CharP k 2]

lemma exact_rightDualAug (hq : q ≠ 0) :
    Function.Exact (rightDualD₁ q) (rightDualAug q) := by
  rintro ⟨x,y⟩
  constructor
  · intro hh
    obtain ⟨hx, ha, hbc, hu, hv⟩ := (rightDualAug_eq_zero_iff q hq x y).mp hh
    subst x
    have hc : y.val 3 = y.val 2 := by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hbc
    refine ⟨ec q (y.val 2) (y.val 4) 0 0 0 0, ?_⟩
    apply Prod.ext
    · rfl
    · change lambdaEll q 1 _ = y
      rw [lambdaEll_ec]
      have hy := ec_eta q y
      rw [ha, hu, hv, hc] at hy
      simpa only [mul_zero, add_zero, one_mul] using hy
  · rintro ⟨z, hz⟩
    rw [← hz]
    change rightDualAug q (0, lambdaEll q 1 z) = 0
    rw [rightDualAug_eq_zero_iff q hq]
    rw [← ec_eta q z, lambdaEll_ec]
    change (0 : eC q) = 0 ∧ (0:k) = 0 ∧ z.val 0 + 1*z.val 0 = 0 ∧
      (0:k) = 0 ∧ (1+1)*z.val 5 = 0
    simp [CharTwo.add_self_eq_zero]

end Tachikawa.C

namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] [CharP k 2] (q : k)

def rightDualResObj : ℕ → ModuleCat (C k q)ᵐᵒᵖ
  | 0 => ModuleCat.of _ (eC q × eC q)
  | 1 => ModuleCat.of _ (eC q)
  | 2 => ModuleCat.of _ (fC q)
  | _+3 => ModuleCat.of _ PUnit

def rightDualResD : ∀ n, rightDualResObj q (n+1) ⟶ rightDualResObj q n
  | 0 => ModuleCat.ofHom (rightDualD₁ q)
  | 1 => ModuleCat.ofHom (lambdaU q)
  | _+2 => 0

lemma rightDualResD_exact (_hq : q ≠ 0) (n : ℕ) :
    Function.Exact (rightDualResD q (n+1)) (rightDualResD q n) := by
  rcases n with _ | _ | _ | n
  · change Function.Exact (lambdaU q) (rightDualD₁ q)
    intro x
    change (0, lambdaEll q 1 x) = (0,0) ↔ _
    rw [Prod.mk.injEq]
    simpa only [true_and] using exact_lambdaU q x
  · change Function.Exact (fun _ : PUnit => (0 : fC q)) (lambdaU q)
    intro x
    constructor
    · intro hx
      refine ⟨PUnit.unit, ?_⟩
      exact ((lambdaU_injective q) (hx.trans (map_zero (lambdaU q)).symm)).symm
    · rintro ⟨_, rfl⟩
      exact map_zero _
  · change Function.Exact (fun _ : PUnit => (0 : PUnit)) (fun _ : PUnit => (0 : fC q))
    intro x
    exact ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  · change Function.Exact (fun _ : PUnit => (0 : PUnit)) (fun _ : PUnit => (0 : PUnit))
    intro x
    exact ⟨fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩, fun _ => rfl⟩

def rightDualProjectiveResolution (hq : q ≠ 0) :
    ProjectiveResolution (ModuleCat.of (C k q)ᵐᵒᵖ (DualBimodule k (C k q))) :=
  resolutionOfExact _ (rightDualResObj q) (rightDualResD q)
    (ModuleCat.ofHom (rightDualAug q)) (rightDualResD_exact q hq)
    (exact_rightDualAug q hq) (rightDualAug_surjective q hq) (fun n => by
      rcases n with _ | _ | _ | n <;> dsimp [rightDualResObj] <;> infer_instance)

lemma rightDual_projectiveDimension (hq : q ≠ 0) :
    HasProjectiveDimensionLE (ModuleCat.of (C k q)ᵐᵒᵖ (DualBimodule k (C k q))) 2 := by
  let P := rightDualProjectiveResolution q hq
  apply HasProjectiveDimensionLT.mk
  intro i hi Y α
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective α (i+1) rfl
  have hs : Subsingleton (P.complex.X i) := by
    change Subsingleton (rightDualResObj q i)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_comm 3 n]
    exact inferInstanceAs (Subsingleton PUnit)
  have h : f = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [hs.elim x 0]
    exact map_zero _
  subst f
  exact P.extMk_zero _ _

end Tachikawa.C



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

instance : Module.Projective (C k q)ᵐᵒᵖ (C k q) :=
  Module.Projective.of_equiv (MulOpposite.opLinearEquiv (C k q)ᵐᵒᵖ).symm
instance : Module.Finite (C k q)ᵐᵒᵖ (C k q) :=
  Module.Finite.equiv (MulOpposite.opLinearEquiv (C k q)ᵐᵒᵖ).symm
instance : Module.Finite (C k q) (C.Ce q) :=
  Module.Finite.of_restrictScalars_finite k _ _
instance : Module.Finite (C k q) (C.Cf q) :=
  Module.Finite.of_restrictScalars_finite k _ _
instance : Module.Finite (C k q)ᵐᵒᵖ (C.eC q) :=
  Module.Finite.of_surjective (RightCorner.projection (C.e_idempotent q))
    (fun a => ⟨a.val, Subtype.ext a.property⟩)
instance : Module.Finite (C k q)ᵐᵒᵖ (C.fC q) :=
  Module.Finite.of_surjective (RightCorner.projection (C.f_idempotent q))
    (fun a => ⟨a.val, Subtype.ext a.property⟩)

def TLeftObj : ModuleCat (C k q) := ModuleCat.of (C k q) (C k q × DualBimodule k (C k q))
def TRightObj : ModuleCat (C k q)ᵐᵒᵖ := ModuleCat.of (C k q)ᵐᵒᵖ (C k q × DualBimodule k (C k q))

def tLeftResolution (hq : q ≠ 0) : ProjectiveResolution (TLeftObj q) :=
  Tachikawa.ProjectiveResolution.prod
    (Tachikawa.ProjectiveResolution.simpleSelf (ModuleCat.of (C k q) (C k q)))
    (C.leftDualProjectiveResolution q hq)

def tRightResolution (hq : q ≠ 0) : ProjectiveResolution (TRightObj q) :=
  Tachikawa.ProjectiveResolution.prod
    (Tachikawa.ProjectiveResolution.simpleSelf (ModuleCat.of (C k q)ᵐᵒᵖ (C k q)))
    (C.rightDualProjectiveResolution q hq)

lemma tLeftResolution_finiteC (hq : q ≠ 0) (n : ℕ) :
    Module.Finite (C k q) ((tLeftResolution q hq).complex.X n) := by
  change Module.Finite (C k q) (((Tachikawa.ProjectiveResolution.simpleSelf
      (ModuleCat.of (C k q) (C k q))).complex.X n) × C.leftDualResObj q n)
  have h : Module.Finite (C k q) (C.leftDualResObj q n) := by
    rcases n with _ | _ | _ | n
    · exact inferInstanceAs (Module.Finite (C k q) (C.Ce q × C.Ce q))
    · exact inferInstanceAs (Module.Finite (C k q) (C.Ce q))
    · exact inferInstanceAs (Module.Finite (C k q) (C.Cf q))
    · exact inferInstanceAs (Module.Finite (C k q) PUnit)
  let := h
  let : Module.Finite (C k q) ((Tachikawa.ProjectiveResolution.simpleSelf
      (ModuleCat.of (C k q) (C k q))).complex.X n) := by
    cases n with
    | zero => exact inferInstanceAs (Module.Finite (C k q) (C k q))
    | succ n => exact inferInstanceAs (Module.Finite (C k q) PUnit)
  exact Module.Finite.prod

lemma tRightResolution_finiteC (hq : q ≠ 0) (n : ℕ) :
    Module.Finite (C k q)ᵐᵒᵖ ((tRightResolution q hq).complex.X n) := by
  change Module.Finite (C k q)ᵐᵒᵖ (((Tachikawa.ProjectiveResolution.simpleSelf
      (ModuleCat.of (C k q)ᵐᵒᵖ (C k q))).complex.X n) × C.rightDualResObj q n)
  have h : Module.Finite (C k q)ᵐᵒᵖ (C.rightDualResObj q n) := by
    rcases n with _ | _ | _ | n
    · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.eC q × C.eC q))
    · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.eC q))
    · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C.fC q))
    · exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ PUnit)
  let := h
  let : Module.Finite (C k q)ᵐᵒᵖ ((Tachikawa.ProjectiveResolution.simpleSelf
      (ModuleCat.of (C k q)ᵐᵒᵖ (C k q))).complex.X n) := by
    cases n with
    | zero => exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ (C k q))
    | succ n => exact inferInstanceAs (Module.Finite (C k q)ᵐᵒᵖ PUnit)
  exact Module.Finite.prod

lemma tLeftResolution_finite (hq : q ≠ 0) (n : ℕ) :
    FiniteDimensional k ((tLeftResolution q hq).complex.X n) := by
  let := tLeftResolution_finiteC q hq n
  exact Module.Finite.trans (C k q) _

lemma tRightResolution_finite (hq : q ≠ 0) (n : ℕ) :
    FiniteDimensional k ((tRightResolution q hq).complex.X n) := by
  let := tRightResolution_finiteC q hq n
  exact Module.Finite.trans (C k q)ᵐᵒᵖ _

lemma tLeftResolution_above (hq : q ≠ 0) (n : ℕ) (hn : 2 < n) :
    IsZero ((tLeftResolution q hq).complex.X n) := by
  apply Tachikawa.ProjectiveResolution.prod_above _ _ 2 n _ _ hn
  · intro i hi
    exact Tachikawa.ProjectiveResolution.simpleSelf_above _ i (by omega)
  · intro i hi
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ i by omega)
    rw [Nat.add_comm 3 i]
    change IsZero (ModuleCat.of (C k q) PUnit)
    exact ModuleCat.isZero_of_subsingleton _

lemma tRightResolution_above (hq : q ≠ 0) (n : ℕ) (hn : 2 < n) :
    IsZero ((tRightResolution q hq).complex.X n) := by
  apply Tachikawa.ProjectiveResolution.prod_above _ _ 2 n _ _ hn
  · intro i hi
    exact Tachikawa.ProjectiveResolution.simpleSelf_above _ i (by omega)
  · intro i hi
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ i by omega)
    rw [Nat.add_comm 3 i]
    change IsZero (ModuleCat.of (C k q)ᵐᵒᵖ PUnit)
    exact ModuleCat.isZero_of_subsingleton _

abbrev ELeftObj : ModuleCat (B q) := ((OuterTensor.bifunctor k (C k q) (C k q)).obj (TLeftObj q)).obj (TLeftObj q)
abbrev ERightObj : ModuleCat ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ) :=
  ((OuterTensor.bifunctor k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ).obj (TRightObj q)).obj (TRightObj q)

def eLeftResolution (hq : q ≠ 0) : ProjectiveResolution (ELeftObj q) :=
  OuterTensor.resolution k _ _ (tLeftResolution q hq) (tLeftResolution q hq)
    (tLeftResolution_finiteC q hq) (tLeftResolution_finiteC q hq)

def eRightResolution (hq : q ≠ 0) : ProjectiveResolution (ERightObj q) :=
  OuterTensor.resolution k _ _ (tRightResolution q hq) (tRightResolution q hq)
    (tRightResolution_finiteC q hq) (tRightResolution_finiteC q hq)

lemma eLeftResolution_above (hq : q ≠ 0) (n : ℕ) (hn : 4 < n) :
    IsZero ((eLeftResolution q hq).complex.X n) :=
  OuterTensor.total_isZero_above _ _ 2 2 (tLeftResolution_above q hq) (tLeftResolution_above q hq) n hn

lemma eRightResolution_above (hq : q ≠ 0) (n : ℕ) (hn : 4 < n) :
    IsZero ((eRightResolution q hq).complex.X n) :=
  OuterTensor.total_isZero_above _ _ 2 2 (tRightResolution_above q hq) (tRightResolution_above q hq) n hn

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

abbrev inclusionC : C k q →ₐ[k] T q :=
  TrivSqZeroExt.inlAlgHom k (C k q) (DualBimodule k (C k q))
abbrev inclusionB : B q →ₐ[k] E q := Algebra.TensorProduct.map (inclusionC q) (inclusionC q)

def tLeftUnderlying : TLeftObj q ≃ₗ[k] T q where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (algebraMap k (C k q) c) • (show C k q × DualBimodule k (C k q) from x) =
      c • (show C k q × DualBimodule k (C k q) from x)
    exact IsScalarTower.algebraMap_smul (C k q) c _

lemma tLeftUnderlying_smul (r : C k q) (x : TLeftObj q) :
    tLeftUnderlying q (r • x) = inclusionC q r * tLeftUnderlying q x := by
  apply TrivSqZeroExt.ext
  · rfl
  · change r • (show C k q × DualBimodule k (C k q) from x).2 =
      r • (show C k q × DualBimodule k (C k q) from x).2 +
        MulOpposite.op (show C k q × DualBimodule k (C k q) from x).1 • (0:DualBimodule k (C k q))
    rw [smul_zero, add_zero]

def eLeftTensorEquiv : OuterTensor.Obj k (C k q) (C k q) (TLeftObj q) (TLeftObj q) ≃ₗ[k] E q :=
  TensorProduct.congr (tLeftUnderlying q) (tLeftUnderlying q)

lemma eLeftTensorEquiv_action (r : B q) :
    (eLeftTensorEquiv q).toLinearMap.comp (OuterTensor.action k (C k q) (C k q) (TLeftObj q) (TLeftObj q) r) =
      (LinearMap.mulLeft k (inclusionB q r)).comp (eLeftTensorEquiv q).toLinearMap := by
  induction r using TensorProduct.inductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    change (tLeftUnderlying q (a • x)) ⊗ₜ[k] (tLeftUnderlying q (b • y)) =
      (inclusionC q a ⊗ₜ[k] inclusionC q b) *
        ((tLeftUnderlying q x) ⊗ₜ[k] (tLeftUnderlying q y))
    rw [tLeftUnderlying_smul, tLeftUnderlying_smul, Algebra.TensorProduct.tmul_mul_tmul]
  | add r s hr hs =>
    apply LinearMap.ext
    intro x
    change eLeftTensorEquiv q ((OuterTensor.action k (C k q) (C k q) (TLeftObj q) (TLeftObj q) (r+s)) x) =
      inclusionB q (r+s) * eLeftTensorEquiv q x
    rw [map_add, map_add]
    change eLeftTensorEquiv q ((OuterTensor.action k (C k q) (C k q) (TLeftObj q) (TLeftObj q) r) x +
      (OuterTensor.action k (C k q) (C k q) (TLeftObj q) (TLeftObj q) s) x) = _
    apply ((eLeftTensorEquiv q).map_add _ _).trans
    apply Eq.trans (congrArg₂ (fun a b : E q => a+b) (LinearMap.congr_fun hr x) (LinearMap.congr_fun hs x))
    exact (add_mul (inclusionB q r) (inclusionB q s) (eLeftTensorEquiv q x)).symm

lemma eLeftTensorEquiv_smul (r : B q) (x : OuterTensor.Obj k (C k q) (C k q) (TLeftObj q) (TLeftObj q)) :
    eLeftTensorEquiv q (r • x) = inclusionB q r * eLeftTensorEquiv q x :=
  LinearMap.congr_fun (eLeftTensorEquiv_action q r) x

def eLeftRestrictionIso : ELeftObj q ≅ (AlgebraInduction.res (inclusionB q)).obj
    (ModuleCat.of (E q) (E q)) := by
  let X := ELeftObj q
  let Z := (AlgebraInduction.res (inclusionB q)).obj (ModuleCat.of (E q) (E q))
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Z) (m₁ := X.isModule) (m₂ := Z.isModule)
    { toFun := eLeftTensorEquiv q
      invFun := (eLeftTensorEquiv q).symm
      left_inv := (eLeftTensorEquiv q).left_inv
      right_inv := (eLeftTensorEquiv q).right_inv
      map_add' := (eLeftTensorEquiv q).map_add
      map_smul' := eLeftTensorEquiv_smul q }

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma cResObj_finite (n : ℕ) : Module.Finite (C k q) (C.resObj q n) := by
  cases n with
  | zero =>
    let : Module.Finite k (C.Cf q) := Module.Finite.of_injective
      ((C.Cf q).subtype.restrictScalars k) Subtype.val_injective
    exact Module.Finite.of_restrictScalars_finite k (C k q) (C.Cf q)
  | succ n =>
    let : Module.Finite k (C.Ce q) := Module.Finite.of_injective
      ((C.Ce q).subtype.restrictScalars k) Subtype.val_injective
    exact Module.Finite.of_restrictScalars_finite k (C k q) (C.Ce q)

abbrev bSimpleTensor : ModuleCat (B q) :=
  ((OuterTensor.bifunctor k (C k q) (C k q)).obj (ModuleCat.of (C k q) (C.Simple q))).obj
    (ModuleCat.of (C k q) (C.Simple q))

def bSimpleTensorResolution (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ProjectiveResolution (bSimpleTensor q) :=
  OuterTensor.resolution k (C k q) (C k q)
    (C.projectiveResolution q hp) (C.projectiveResolution q hp)
    (fun n => cResObj_finite q n) (fun n => cResObj_finite q n)

def bEvaluatedComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    HomotopyEquiv
      (Enveloping.evaluatedRegularResolution (k := k) (bSimpleTensor q)).complex
      (bSimpleTensorResolution q hp).complex :=
  Enveloping.evaluatedRegularComparison (k := k) (bSimpleTensor q) (bSimpleTensorResolution q hp)

def inducedBEvaluatedComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    HomotopyEquiv
      (((AlgebraInduction.functor (inclusionB q)).mapHomologicalComplex _).obj
        (Enveloping.evaluatedRegularResolution (k := k) (bSimpleTensor q)).complex)
      (((AlgebraInduction.functor (inclusionB q)).mapHomologicalComplex _).obj
        (bSimpleTensorResolution q hp).complex) :=
  (AlgebraInduction.functor (inclusionB q)).mapHomotopyEquiv (bEvaluatedComparison q hp)

end Tachikawa.Construction



namespace Tachikawa.HomBimodule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (X : ModuleCat R)

def representationLinear : R →ₗ[R] Base (k := k) X X where
  toFun a := (Algebra.lsmul k k X) a
  map_add' a b := map_add (Algebra.lsmul k k X) a b
  map_smul' a b := by
    apply LinearMap.ext
    intro x
    exact mul_smul a b x

def representation : Enveloping.regular (k := k) (R := R) ⟶ obj (k := k) X X :=
  Enveloping.ofBimoduleHom (representationLinear (k := k) X) (by
    intro a b
    apply LinearMap.ext
    intro x
    exact mul_smul b a.unop x)

@[simp] lemma representation_apply (a : Enveloping.regular (k := k) (R := R)) (x : X) :
    (show X →ₗ[k] X from representation X a) x = (show R from a) • x := rfl

end Tachikawa.HomBimodule



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
lemma homBase_smul {K R : Type} [Field K] [Ring R] [Algebra K R]
    (V : ModuleCat R) (f : HomBimodule.Base (k := K) V V) (c : K) (x : V) :
    f (c • x) = c • f x := (show V →ₗ[K] V from f).map_smul c x

variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

abbrev U := Enveloping.twistedRegular (sigma q H hH)
abbrev S := HomBimodule.obj (k := k) (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q))

def socleBimoduleLinear :
    HomBimodule.Base (k := k) (ModuleCat.of (E q) (X q)) (ModuleCat.of (E q) (X q)) →ₗ[E q]
      AlgebraInduction.Bimod (sigma q H hH).toAlgHom where
  toFun f := (show k from f (show X q from (1:k))) • zeta q
  map_add' f g := add_smul _ _ _
  map_smul' a f := by
    change (characterE q a * (show k from f (show X q from (1:k)))) • zeta q =
      a * ((show k from f (show X q from (1:k))) • zeta q)
    rw [mul_smul_comm, zeta_left, smul_smul, mul_comm]

def socleBimoduleMap : S q ⟶ U q H hH :=
  Enveloping.ofBimoduleHom (socleBimoduleLinear q H hH) (by
    intro a f
    change (show k from f ((characterE q a.unop) • (show X q from (1:k)))) • zeta q =
      ((show k from f (show X q from (1:k))) • zeta q) * sigma q H hH a.unop
    have hf := homBase_smul (ModuleCat.of (E q) (X q)) f (characterE q a.unop)
      (show ModuleCat.of (E q) (X q) from (show X q from (1:k)))
    change f ((characterE q (algebraMap k (E q) (characterE q a.unop))) * (1:k)) =
      (characterE q (algebraMap k (E q) (characterE q a.unop))) *
        (show k from f (1:k)) at hf
    simp only [AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply] at hf
    refine (congrArg (fun x : ModuleCat.of (E q) (X q) => (show k from x) • zeta q) hf).trans ?_
    change (characterE q a.unop * (show k from f (show X q from (1:k)))) • zeta q = _
    rw [smul_mul_assoc, zeta_right, characterE_sigma, smul_smul, mul_comm])

lemma representation_socle (a : E q) :
    Enveloping.twistedUnderlying (sigma q H hH)
      ((HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)) ≫
        socleBimoduleMap q H hH) (Enveloping.regularUnderlyingEquiv.symm a)) =
      characterE q a • zeta q := by
  change (characterE q a * 1) • zeta q = _
  rw [mul_one]

lemma socleBimoduleMap_ne_zero : socleBimoduleMap q H hH ≠ 0 := by
  intro h
  have hh := representation_socle q H hH (1:E q)
  rw [h,CategoryTheory.Limits.comp_zero] at hh
  change (0:E q) = characterE q 1 • zeta q at hh
  rw [map_one,one_smul] at hh
  exact zeta_ne_zero q hh.symm

end Tachikawa.Construction



namespace Tachikawa.LeftCoinduced
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def J : ModuleCat R ⥤ ModuleCat R :=
  ModuleCat.restrictScalars (algebraMap k R) ⋙ ModuleCat.coextendScalars (algebraMap k R)

def unit : 𝟭 (ModuleCat R) ⟶ J (k := k) :=
  ModuleCat.RestrictionCoextensionAdj.unit' (algebraMap k R)

instance coextend_additive : (ModuleCat.coextendScalars (algebraMap k R)).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro x
    rfl

instance : (J (k := k) (R := R)).Additive := inferInstanceAs
  (ModuleCat.restrictScalars (algebraMap k R) ⋙ ModuleCat.coextendScalars (algebraMap k R)).Additive

lemma unit_injective (M : ModuleCat R) : Function.Injective ((unit (k := k)).app M) := by
  intro x y h
  have h' := congrArg (fun f => ModuleCat.CoextendScalars.equiv (algebraMap k R) _ f (1:R)) h
  change (1:R) • x = (1:R) • y at h'
  simpa only [one_smul] using h'
instance (M : ModuleCat R) : Mono ((unit (k := k)).app M) :=
  (ModuleCat.mono_iff_injective _).2 (unit_injective M)
instance : Mono (unit (k := k) (R := R)) := NatTrans.mono_of_mono_app _

instance coextend_preservesInjective :
    (ModuleCat.coextendScalars (algebraMap k R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ModuleCat.restrictCoextendScalarsAdj (algebraMap k R))

instance (M : ModuleCat R) : Injective ((J (k := k)).obj M) := by
  let X := (ModuleCat.restrictScalars (algebraMap k R)).obj M
  let : Module.Injective k X := Module.injective_of_isSemisimpleRing k X
  let : Injective X := Module.injective_object_of_injective_module k X
  exact (ModuleCat.coextendScalars (algebraMap k R)).injective_obj X

def C : ModuleCat R ⥤ ModuleCat R := cokernel (unit (k := k) (R := R))

instance : (C (k := k) (R := R)).Additive := by
  constructor
  intro X Y f g
  dsimp only [C]
  let π := cokernel.π (unit (k := k) (R := R))
  let : Epi (π.app X) := inferInstance
  apply (cancel_epi (π.app X)).1
  erw [← π.naturality, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add, ← π.naturality, ← π.naturality]

def π (M : ModuleCat R) : (J (k := k)).obj M ⟶ (C (k := k)).obj M :=
  (cokernel.π (unit (k := k))).app M
instance (M : ModuleCat R) : Epi (π (k := k) M) :=
  inferInstanceAs (Epi ((cokernel.π (unit (k := k))).app M))

lemma unit_π (M : ModuleCat R) : (unit (k := k)).app M ≫ π M = 0 :=
  congrArg (fun f => f.app M) (cokernel.condition (unit (k := k)))

def short (M : ModuleCat R) : ShortComplex (ModuleCat R) := ShortComplex.mk _ _ (unit_π (k := k) M)

lemma short_exact (M : ModuleCat R) : (short (k := k) M).ShortExact := by
  let T : ShortComplex (ModuleCat R ⥤ ModuleCat R) := ShortComplex.mk (unit (k := k)) (cokernel.π _) (cokernel.condition _)
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  exact hT.map ((evaluation _ _).obj M)

def iterate : ℕ → ModuleCat R ⥤ ModuleCat R
  | 0 => 𝟭 _
  | n+1 => iterate n ⋙ C (k := k)

lemma c_dimension (M : ModuleCat R) (d : ℕ) [HasInjectiveDimensionLE M (d+1)] :
    HasInjectiveDimensionLE ((C (k := k)).obj M) d := by
  apply (short_exact (k := k) M).hasInjectiveDimensionLT_X₃ (d+1)
  · exact hasInjectiveDimensionLT_of_ge ((J (k := k)).obj M) 1 (d+1) (by omega)
  · exact inferInstanceAs (HasInjectiveDimensionLE M (d+1))

lemma iterate_dimension (M : ModuleCat R) (d n : ℕ) [HasInjectiveDimensionLE M (d+n)] :
    HasInjectiveDimensionLE ((iterate (k := k) n).obj M) d := by
  induction n generalizing d with
  | zero => exact inferInstanceAs (HasInjectiveDimensionLE M d)
  | succ n ih =>
    have h : HasInjectiveDimensionLE M ((d+1)+n) := by simpa only [Nat.add_assoc,Nat.add_comm 1 n] using (inferInstance : HasInjectiveDimensionLE M (d+(n+1)))
    let := ih (d+1)
    exact c_dimension ((iterate (k := k) n).obj M) d

lemma iterate_injective (M : ModuleCat R) (d : ℕ) [HasInjectiveDimensionLE M d] :
    Injective ((iterate (k := k) d).obj M) := by
  let : HasInjectiveDimensionLE M (0+d) := by simpa using (inferInstance : HasInjectiveDimensionLE M d)
  let := iterate_dimension (k := k) M 0 d
  exact inferInstance

end Tachikawa.LeftCoinduced



namespace Tachikawa
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (M : Type) [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

def moduleCatObj : ModuleCat R := ModuleCat.of R M

def moduleCatUnderlyingEquiv : moduleCatObj (R := R) M ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (algebraMap k R c) • (show M from x) = c • (show M from x)
    exact IsScalarTower.algebraMap_smul R c (show M from x)

lemma moduleCatFinite [FiniteDimensional k M] : FiniteDimensional k (moduleCatObj (R := R) M) :=
  Module.Finite.equiv (moduleCatUnderlyingEquiv (k := k) (R := R) M).symm

end Tachikawa



namespace Tachikawa.LeftCoinduced
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def restrictRegularEquiv :
    (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R R) ≃ₗ[k] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change algebraMap k R c * (show R from x) = c • (show R from x)
    rw [Algebra.smul_def]

def underlying (M : ModuleCat R) : (J (k := k)).obj M ≃ₗ[k] (R →ₗ[k] M) where
  toFun φ := (ModuleCat.CoextendScalars.equiv (algebraMap k R) _ φ).comp
    (restrictRegularEquiv (k := k) (R := R)).symm.toLinearMap
  invFun φ := (ModuleCat.CoextendScalars.equiv (algebraMap k R) _).symm
    (φ.comp (restrictRegularEquiv (k := k) (R := R)).toLinearMap)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c φ := by
    apply LinearMap.ext
    intro x
    change (ModuleCat.CoextendScalars.equiv (algebraMap k R) _ φ)
      (x * algebraMap k R c) = c • (ModuleCat.CoextendScalars.equiv (algebraMap k R) _ φ) x
    have h : x * algebraMap k R c = algebraMap k R c * x := Algebra.commutes c x |>.symm
    rw [h]
    exact (ModuleCat.CoextendScalars.equiv (algebraMap k R) _ φ).map_smul c x

instance J_finite [FiniteDimensional k R] (M : ModuleCat R) [FiniteDimensional k M] :
    FiniteDimensional k ((J (k := k)).obj M) := Module.Finite.equiv (underlying M).symm

instance C_finite [FiniteDimensional k R] (M : ModuleCat R) [FiniteDimensional k M] :
    FiniteDimensional k ((C (k := k)).obj M) := by
  have h := (ModuleCat.epi_iff_surjective (π (k := k) M)).1 inferInstance
  exact Module.Finite.of_surjective ((π (k := k) M).hom.restrictScalars k) h

instance iterate_finite [FiniteDimensional k R] (M : ModuleCat R) [FiniteDimensional k M] (n : ℕ) :
    FiniteDimensional k ((iterate (k := k) n).obj M) := by
  induction n with
  | zero => exact inferInstanceAs (FiniteDimensional k M)
  | succ n ih => exact inferInstanceAs (FiniteDimensional k ((C (k := k)).obj ((iterate (k := k) n).obj M)))

end Tachikawa.LeftCoinduced



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def Coind (N : ModuleCat Sᵐᵒᵖ) := R →ₗ[k] N

namespace Coind
variable (N : ModuleCat Sᵐᵒᵖ)
instance : FunLike (Coind (k := k) (R := R) N) R N := inferInstanceAs (FunLike (R →ₗ[k] N) R N)
instance : LinearMapClass (Coind (k := k) (R := R) N) k R N := inferInstanceAs (LinearMapClass (R →ₗ[k] N) k R N)
instance : AddCommGroup (Coind (k := k) (R := R) N) := inferInstanceAs (AddCommGroup (R →ₗ[k] N))
instance : Module k (Coind (k := k) (R := R) N) := inferInstanceAs (Module k (R →ₗ[k] N))
instance : Module Sᵐᵒᵖ (Coind (k := k) (R := R) N) := inferInstanceAs (Module Sᵐᵒᵖ (R →ₗ[k] N))
instance : IsScalarTower k Sᵐᵒᵖ (Coind (k := k) (R := R) N) :=
  inferInstanceAs (IsScalarTower k Sᵐᵒᵖ (R →ₗ[k] N))
instance : Module R (Coind (k := k) (R := R) N) where
  smul a f := (show R →ₗ[k] N from f).comp (LinearMap.mulRight k a)
  one_smul f := by apply LinearMap.ext; intro x; change f (x*1) = f x; rw [mul_one]
  mul_smul a b f := by
    apply LinearMap.ext; intro x; change f (x*(a*b)) = f ((x*a)*b); rw [mul_assoc]
  smul_zero a := by apply LinearMap.ext; intro x; rfl
  smul_add a f g := by apply LinearMap.ext; intro x; rfl
  add_smul a b f := by
    apply LinearMap.ext; intro x; change f (x*(a+b)) = f (x*a)+f (x*b)
    rw [mul_add,map_add]
  zero_smul f := by apply LinearMap.ext; intro x; change f (x*0) = 0; rw [mul_zero,map_zero]
instance : IsScalarTower k R (Coind (k := k) (R := R) N) where
  smul_assoc c a f := by
    apply LinearMap.ext; intro x
    change f (x*(c • a)) = c • f (x*a)
    rw [Algebra.mul_smul_comm,map_smul]
instance : SMulCommClass R Sᵐᵒᵖ (Coind (k := k) (R := R) N) where
  smul_comm _ _ _ := rfl

instance [FiniteDimensional k R] [FiniteDimensional k N] :
    FiniteDimensional k (Coind (k := k) (R := R) N) := inferInstanceAs (FiniteDimensional k (R →ₗ[k] N))

end Coind

def coindObj (N : ModuleCat Sᵐᵒᵖ) : ModuleCat (Alg k R S) :=
  ofBimodule (k := k) (R := R) (S := S) (Coind (k := k) (R := R) N)

def coindUnderlying (N : ModuleCat Sᵐᵒᵖ) : coindObj (k := k) (R := R) N ≃ₗ[k] (R →ₗ[k] N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c f := by
    change (action (k := k) (R := R) (S := S) (Coind (k := k) (R := R) N)
      (algebraMap k (Alg k R S) c)) f = c • (show R →ₗ[k] N from f)
    rw [AlgHom.commutes]
    rfl

instance (N : ModuleCat Sᵐᵒᵖ) [FiniteDimensional k R] [FiniteDimensional k N] :
    FiniteDimensional k (coindObj (k := k) (R := R) N) :=
  Module.Finite.equiv (coindUnderlying (k := k) (R := R) N).symm

variable (Q : ModuleCat (Alg k R S)) (N : ModuleCat Sᵐᵒᵖ)

def coindEvaluate (f : Q ⟶ coindObj (k := k) (R := R) N) : Obj Q →ₗ[Sᵐᵒᵖ] N where
  toFun x := (show R →ₗ[k] N from f x) 1
  map_add' x y := by
    erw [map_add]; rfl
  map_smul' s x := by
    have h := f.hom.map_smul ((1:R) ⊗ₜ[k] s) x
    change (show R →ₗ[k] N from f (((1:R) ⊗ₜ[k] s) • x)) 1 = s • _
    erw [h]
    change s • (show R →ₗ[k] N from f x) (1*1) = s • _
    rw [mul_one]

def coindExtendLeft (g : Obj Q →ₗ[Sᵐᵒᵖ] N) : Obj Q →ₗ[R] Coind (k := k) (R := R) N where
  toFun x :=
    { toFun := fun r => g (r • x)
      map_add' r s := by rw [add_smul,map_add]
      map_smul' c r := by
        change (g.restrictScalars k) ((c • r) • x) = c • g (r • x)
        rw [smul_assoc,map_smul]
        rfl }
  map_add' x y := by apply LinearMap.ext; intro r; change g (r • (x+y)) = _; rw [smul_add,map_add]; rfl
  map_smul' a x := by
    apply LinearMap.ext; intro r; change g (r • a • x) = g ((r*a) • x); rw [mul_smul]

lemma coindExtendLeft_right (g : Obj Q →ₗ[Sᵐᵒᵖ] N) (s : Sᵐᵒᵖ) (x : Obj Q) :
    coindExtendLeft Q N g (s • x) = s • coindExtendLeft Q N g x := by
  apply LinearMap.ext; intro r
  change g (r • s • x) = s • g (r • x)
  rw [smul_comm,map_smul]

def coindExtend (g : Obj Q →ₗ[Sᵐᵒᵖ] N) : Q ⟶ coindObj (k := k) (R := R) N :=
  (reassembleIso Q).inv ≫ ofBimoduleHom (coindExtendLeft Q N g) (coindExtendLeft_right Q N g)

lemma coindEvaluate_extend (g : Obj Q →ₗ[Sᵐᵒᵖ] N) :
    coindEvaluate Q N (coindExtend Q N g) = g := by
  ext x
  change g ((1:R) • x) = g x
  rw [one_smul]

lemma coindExtend_evaluate (f : Q ⟶ coindObj (k := k) (R := R) N) :
    coindExtend Q N (coindEvaluate Q N f) = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro r
  change (show R →ₗ[k] N from f (((r ⊗ₜ[k] (1:Sᵐᵒᵖ)) : Alg k R S) • x)) 1 =
    (show R →ₗ[k] N from f x) r
  rw [f.hom.map_smul]
  change (1:Sᵐᵒᵖ) • (show R →ₗ[k] N from f x) (1*r) = _
  rw [one_smul,one_mul]

def coindHomEquiv : (Q ⟶ coindObj (k := k) (R := R) N) ≃ₗ[k] (Obj Q →ₗ[Sᵐᵒᵖ] N) where
  toFun := coindEvaluate Q N
  invFun := coindExtend Q N
  left_inv := coindExtend_evaluate Q N
  right_inv := coindEvaluate_extend Q N
  map_add' f g := by ext x; rfl
  map_smul' c f := by
    ext x
    change (coindUnderlying (k := k) (R := R) N ((c • f) x)) 1 = c • _
    change (coindUnderlying (k := k) (R := R) N (c • f x)) 1 = c • _
    rw [map_smul]
    rfl

lemma coindEvaluate_natural {Q' : ModuleCat (Alg k R S)}
    (a : Q' ⟶ Q) (f : Q ⟶ coindObj (k := k) (R := R) N) :
    coindEvaluate Q' N (a ≫ f) = (coindEvaluate Q N f).comp (rightMap a) := rfl

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def coindMap {N N' : ModuleCat Sᵐᵒᵖ} (a : N ⟶ N') :
    coindObj (k := k) (R := R) N ⟶ coindObj (k := k) (R := R) N' :=
  ofBimoduleHom
    { toFun := fun f => (a.hom.restrictScalars k).comp (show R →ₗ[k] N from f)
      map_add' f g := by apply LinearMap.ext; intro x; exact map_add a.hom _ _
      map_smul' r f := by apply LinearMap.ext; intro x; rfl }
    (fun s f => by apply LinearMap.ext; intro x; exact a.hom.map_smul s (f x))

lemma coindMap_apply {N N' : ModuleCat Sᵐᵒᵖ} (a : N ⟶ N')
    (f : coindObj (k := k) (R := R) N) (r : R) :
    (coindUnderlying N' (coindMap a f)) r = a (coindUnderlying N f r) := rfl

def coindFunctor : ModuleCat Sᵐᵒᵖ ⥤ ModuleCat (Alg k R S) where
  obj := coindObj (k := k) (R := R)
  map := coindMap
  map_id N := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro f; apply LinearMap.ext; intro r; rfl
  map_comp a b := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro f; apply LinearMap.ext; intro r; rfl

instance : (coindFunctor (k := k) (R := R) (S := S)).Additive where
  map_add := by intros; apply ModuleCat.hom_ext; apply LinearMap.ext; intro f; apply LinearMap.ext; intro r; rfl

def coindEndo : ModuleCat (Alg k R S) ⥤ ModuleCat (Alg k R S) :=
  rightFunctor ⋙ coindFunctor
instance : (coindEndo (k := k) (R := R) (S := S)).Additive := inferInstanceAs
  ((rightFunctor (k := k) (R := R) (S := S) ⋙ coindFunctor).Additive)

def coindUnit (L : ModuleCat (Alg k R S)) : L ⟶ (coindEndo (k := k)).obj L :=
  coindExtend L ((rightFunctor (k := k) (R := R) (S := S)).obj L) LinearMap.id

lemma coindUnit_apply (L : ModuleCat (Alg k R S)) (z : L) (r : R) :
    (coindUnderlying _ (coindUnit L z)) r = r • (show Obj L from z) := rfl

lemma coindUnit_injective (L : ModuleCat (Alg k R S)) : Function.Injective (coindUnit (k := k) L) := by
  intro x y h
  have h' := congrArg (fun f => coindUnderlying _ f (1:R)) h
  change (1:R) • (show Obj L from x) = (1:R) • (show Obj L from y) at h'
  change (show Obj L from x) = (show Obj L from y)
  exact (one_smul R (show Obj L from x)).symm.trans
    (h'.trans (one_smul R (show Obj L from y)))

instance (L : ModuleCat (Alg k R S)) : Mono (coindUnit (k := k) L) :=
  (ModuleCat.mono_iff_injective _).2 (coindUnit_injective L)

def coindUnitNat : 𝟭 (ModuleCat (Alg k R S)) ⟶ coindEndo where
  app := coindUnit
  naturality {L L'} f := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro z
    apply LinearMap.ext; intro r
    change r • (show Obj L' from f z) = leftMap f (r • (show Obj L from z))
    exact ((leftMap f).map_smul r z).symm

def coindCoker : ModuleCat (Alg k R S) ⥤ ModuleCat (Alg k R S) :=
  cokernel (coindUnitNat (k := k) (R := R) (S := S))

instance : (coindCoker (k := k) (R := R) (S := S)).Additive := by
  constructor
  intro X Y f g
  dsimp only [coindCoker]
  let π := cokernel.π (coindUnitNat (k := k) (R := R) (S := S))
  let : Epi (π.app X) := inferInstance
  apply (cancel_epi (π.app X)).1
  erw [← π.naturality, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add, ← π.naturality, ← π.naturality]

def coindIterate : ℕ → ModuleCat (Alg k R S) ⥤ ModuleCat (Alg k R S)
  | 0 => 𝟭 _
  | n+1 => coindIterate n ⋙ coindCoker

instance (n : ℕ) : (coindIterate (k := k) (R := R) (S := S) n).Additive := by
  induction n with
  | zero => exact inferInstanceAs ((𝟭 (ModuleCat (Alg k R S))).Additive)
  | succ n ih => exact inferInstanceAs ((coindIterate (k := k) (R := R) (S := S) n ⋙ coindCoker).Additive)




instance : Mono (coindUnitNat (k := k) (R := R) (S := S)) := by
  let (L : ModuleCat (Alg k R S)) : Mono (coindUnitNat.app L) :=
    inferInstanceAs (Mono (coindUnit L))
  exact NatTrans.mono_of_mono_app _

def coindπ (L : ModuleCat (Alg k R S)) :
    (coindEndo (k := k)).obj L ⟶ (coindCoker (k := k)).obj L :=
  (cokernel.π (coindUnitNat (k := k))).app L

instance (L : ModuleCat (Alg k R S)) : Epi (coindπ (k := k) L) :=
  inferInstanceAs (Epi ((cokernel.π (coindUnitNat (k := k))).app L))

lemma coindUnit_π (L : ModuleCat (Alg k R S)) :
    coindUnit L ≫ coindπ L = 0 := by
  exact congrArg (fun f => f.app L) (cokernel.condition (coindUnitNat (k := k)))

def coindShort (L : ModuleCat (Alg k R S)) : ShortComplex (ModuleCat (Alg k R S)) :=
  ShortComplex.mk (coindUnit L) (coindπ L) (coindUnit_π L)

lemma coindShort_exact (L : ModuleCat (Alg k R S)) : (coindShort (k := k) L).ShortExact := by
  let T : ShortComplex (ModuleCat (Alg k R S) ⥤ ModuleCat (Alg k R S)) :=
    ShortComplex.mk coindUnitNat (cokernel.π _) (cokernel.condition _)
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  exact hT.map ((CategoryTheory.evaluation _ _).obj L)

lemma coindπ_surjective (L : ModuleCat (Alg k R S)) : Function.Surjective (coindπ (k := k) L) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

lemma coind_exact (L : ModuleCat (Alg k R S)) :
    Function.Exact (coindUnit (k := k) L) (coindπ L) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (coindShort_exact L).exact

variable [FiniteDimensional k R]
instance coindObj_finite (N : ModuleCat Sᵐᵒᵖ) [FiniteDimensional k N] :
    FiniteDimensional k (coindObj (k := k) (R := R) N) :=
  Module.Finite.equiv (coindUnderlying N).symm

instance rightFunctor_finite (L : ModuleCat (Alg k R S)) [FiniteDimensional k L] :
    FiniteDimensional k ((rightFunctor (k := k)).obj L) :=
  Module.Finite.equiv (moduleCatUnderlyingEquiv (k := k) (R := Sᵐᵒᵖ) (Obj L)).symm

instance coindEndo_finite (L : ModuleCat (Alg k R S)) [FiniteDimensional k L] :
    FiniteDimensional k ((coindEndo (k := k)).obj L) :=
  inferInstanceAs (FiniteDimensional k (coindObj (k := k) (R := R) ((rightFunctor (k := k)).obj L)))

instance coindCoker_finite (L : ModuleCat (Alg k R S)) [FiniteDimensional k L] :
    FiniteDimensional k ((coindCoker (k := k)).obj L) :=
  Module.Finite.of_surjective ((coindπ L).hom.restrictScalars k) (coindπ_surjective L)

instance coindIterate_finite (L : ModuleCat (Alg k R S)) [FiniteDimensional k L] (n : ℕ) :
    FiniteDimensional k ((coindIterate (k := k) n).obj L) := by
  induction n with
  | zero => exact inferInstanceAs (FiniteDimensional k L)
  | succ n ih => exact inferInstanceAs
      (FiniteDimensional k ((coindCoker (k := k)).obj ((coindIterate (k := k) n).obj L)))

def coindTerm (L : ModuleCat (Alg k R S)) (n : ℕ) : ModuleCat (Alg k R S) :=
  (coindEndo (k := k)).obj ((coindIterate n).obj L)

def coindStep (L : ModuleCat (Alg k R S)) (n : ℕ) : coindTerm L n ⟶ coindTerm L (n+1) :=
  coindπ ((coindIterate n).obj L) ≫ coindUnit ((coindIterate (n+1)).obj L)

omit [FiniteDimensional k R] in
lemma coindStep_exact (L : ModuleCat (Alg k R S)) (n : ℕ) :
    Function.Exact (coindStep L n) (coindStep L (n+1)) := by
  intro z
  constructor
  · intro hz
    change coindUnit ((coindIterate (n+2)).obj L) (coindπ ((coindIterate (n+1)).obj L) z) = 0 at hz
    have hz' : coindπ ((coindIterate (n+1)).obj L) z = 0 :=
      coindUnit_injective ((coindIterate (n+2)).obj L)
        (hz.trans ((coindUnit ((coindIterate (n+2)).obj L)).hom.map_zero).symm)
    obtain ⟨x,hx⟩ := (coind_exact _ z).1 hz'
    obtain ⟨y,hy⟩ := coindπ_surjective ((coindIterate n).obj L) x
    exact ⟨y,by change coindUnit _ (coindπ _ y) = z; rw [hy]; exact hx⟩
  · rintro ⟨y,rfl⟩
    have h := (coind_exact ((coindIterate (n+1)).obj L) (coindStep L n y)).2
      ⟨coindπ ((coindIterate n).obj L) y,rfl⟩
    change coindUnit _ (coindπ _ (coindStep L n y)) = 0
    rw [h,map_zero]

omit [FiniteDimensional k R] in
lemma coind_start_exact (L : ModuleCat (Alg k R S)) :
    Function.Exact (coindUnit L) (coindStep L 0) := by
  intro z
  change coindUnit _ (coindπ L z) = 0 ↔ _
  constructor
  · intro hz
    apply (coind_exact L z).1
    exact coindUnit_injective ((coindIterate 1).obj L)
      (hz.trans ((coindUnit ((coindIterate 1).obj L)).hom.map_zero).symm)
  · intro hz
    have h := (coind_exact L z).2 hz
    rw [h]
    exact (coindUnit ((coindIterate 1).obj L)).hom.map_zero

omit [FiniteDimensional k R] in
lemma coind_finish_exact (L : ModuleCat (Alg k R S)) (n : ℕ) :
    Function.Exact (coindStep L n) (coindπ ((coindIterate (n+1)).obj L)) := by
  intro z
  rw [coind_exact _ z]
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy⟩ := coindπ_surjective ((coindIterate n).obj L) x
    exact ⟨y,by change coindUnit _ (coindπ _ y) = z; rw [hy]; exact hx⟩
  · rintro ⟨y,rfl⟩
    exact ⟨coindπ ((coindIterate n).obj L) y,rfl⟩

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def rightRegularObj : ModuleCat Sᵐᵒᵖ := ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ

def rightRegularOne : rightRegularObj (S := S) := (1 : Sᵐᵒᵖ)

def rightFreeFunctor : ModuleCat R ⥤ ModuleCat (Alg k R S) :=
  (OuterTensor.bifunctor k R Sᵐᵒᵖ).flip.obj (rightRegularObj (S := S))

instance : (rightFreeFunctor (k := k) (R := R) (S := S)).Additive := inferInstanceAs
  (((OuterTensor.bifunctor k R Sᵐᵒᵖ).flip.obj (rightRegularObj (S := S))).Additive)

abbrev rightFreeObj (L : ModuleCat R) := (rightFreeFunctor (k := k) (S := S)).obj L
variable (L : ModuleCat R) (Q : ModuleCat (Alg k R S))

def rightFreeEvaluate (f : rightFreeObj (k := k) (S := S) L ⟶ Q) : L →ₗ[R] Obj Q where
  toFun x := f (x ⊗ₜ[k] (rightRegularOne (S := S)))
  map_add' x y := by erw [TensorProduct.add_tmul,map_add]; rfl
  map_smul' r x := by
    change f ((r • x) ⊗ₜ[k] (rightRegularOne (S := S))) =
      ((r ⊗ₜ[k] (1:Sᵐᵒᵖ)) : Alg k R S) • f (x ⊗ₜ[k] (rightRegularOne (S := S)))
    have h := f.hom.map_smul ((r ⊗ₜ[k] (1:Sᵐᵒᵖ)) : Alg k R S)
      (x ⊗ₜ[k] (rightRegularOne (S := S)))
    change f ((r • x) ⊗ₜ[k] ((1:Sᵐᵒᵖ) • rightRegularOne)) = _ at h
    simpa only [one_smul] using h

def rightFreeBilinear (g : L →ₗ[R] Obj Q) : L →ₗ[k] rightRegularObj (S := S) →ₗ[k] Obj Q where
  toFun x :=
    { toFun := fun s => (show Sᵐᵒᵖ from s) • g x
      map_add' s t := add_smul _ _ _
      map_smul' c s := by
        change ((algebraMap k Sᵐᵒᵖ c) * (show Sᵐᵒᵖ from s)) • g x = c • ((show Sᵐᵒᵖ from s) • g x)
        rw [mul_smul,IsScalarTower.algebraMap_smul] }
  map_add' x y := by ext s; change (show Sᵐᵒᵖ from s) • g (x+y) = _; rw [map_add,smul_add]; rfl
  map_smul' c x := by
    ext s
    change (show Sᵐᵒᵖ from s) • g (c • x) = c • (show Sᵐᵒᵖ from s) • g x
    rw [g.map_smul_of_tower,smul_comm]

def rightFreeExtend (g : L →ₗ[R] Obj Q) : rightFreeObj (k := k) (S := S) L ⟶ Q :=
  ModuleCat.ofHom (X := rightFreeObj (k := k) (S := S) L) (Y := Q)
  { toFun := TensorProduct.lift (rightFreeBilinear L Q g)
    map_add' := map_add _
    map_smul' a x := by
      change TensorProduct.lift (rightFreeBilinear L Q g)
          ((OuterTensor.action k R Sᵐᵒᵖ L (rightRegularObj (S := S)) a) x) =
        a • TensorProduct.lift (rightFreeBilinear L Q g) x
      induction a using TensorProduct.inductionOn with
      | add a b ha hb => erw [map_add,LinearMap.add_apply,map_add,ha,hb,add_smul]
      | tmul r s =>
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => rw [map_add,map_add,hx,hy,map_add,smul_add]
        | tmul x t =>
          change (s*(show Sᵐᵒᵖ from t)) • g (r • x) = (r ⊗ₜ[k] s) • ((show Sᵐᵒᵖ from t) • g x)
          rw [tmul_smul Q r s ((show Sᵐᵒᵖ from t) • g x)]
          rw [g.map_smul,mul_smul,smul_comm r s,smul_comm r (show Sᵐᵒᵖ from t)] }

lemma rightFreeEvaluate_extend (g : L →ₗ[R] Obj Q) :
    rightFreeEvaluate L Q (rightFreeExtend L Q g) = g := by
  ext x
  change (1:Sᵐᵒᵖ) • g x = g x
  rw [one_smul]

lemma rightFreeExtend_evaluate (f : rightFreeObj (k := k) (S := S) L ⟶ Q) :
    rightFreeExtend L Q (rightFreeEvaluate L Q f) = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext; intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => erw [map_add,map_add,hx,hy]
  | tmul x s =>
    change (((1:R) ⊗ₜ[k] (show Sᵐᵒᵖ from s)) : Alg k R S) • f (x ⊗ₜ[k] (rightRegularOne (S := S))) =
      f (x ⊗ₜ[k] s)
    erw [← f.hom.map_smul]
    congr 1
    change ((1:R) • x) ⊗ₜ[k] ((show Sᵐᵒᵖ from s) • rightRegularOne) = x ⊗ₜ[k] s
    rw [one_smul]
    congr 1
    exact mul_one (show Sᵐᵒᵖ from s)

def rightFreeHomEquiv : (rightFreeObj (k := k) (S := S) L ⟶ Q) ≃ₗ[k] (L →ₗ[R] Obj Q) where
  toFun := rightFreeEvaluate L Q
  invFun := rightFreeExtend L Q
  left_inv := rightFreeExtend_evaluate L Q
  right_inv := rightFreeEvaluate_extend L Q
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

lemma rightFreeEvaluate_natural {L' : ModuleCat R} (a : L' ⟶ L)
    (f : rightFreeObj (k := k) (S := S) L ⟶ Q) :
    rightFreeEvaluate L' Q ((rightFreeFunctor (k := k) (S := S)).map a ≫ f) =
      (rightFreeEvaluate L Q f).comp a.hom := by
  ext x
  rfl

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable [FiniteDimensional k R]

def rightFreeUnderlying (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) M ≃ₗ[k] (M ⊗[k] rightRegularObj (S := S)) :=
  moduleCatUnderlyingEquiv (k := k) (R := Alg k R S)
    (OuterTensor.Obj k R Sᵐᵒᵖ M (rightRegularObj (S := S)))

def rightFreeRestrictionUnderlying (M : ModuleCat R) :
    (rightFunctor (k := k) (S := S)).obj (rightFreeObj M) ≃ₗ[k]
      (M ⊗[k] rightRegularObj (S := S)) :=
  (moduleCatUnderlyingEquiv (k := k) (R := Sᵐᵒᵖ)
    (Obj (rightFreeObj (k := k) (S := S) M))).trans
    (rightFreeUnderlying M)

def coindTensorUnderlying (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.J (k := k)).obj M) ≃ₗ[k]
      (coindEndo (k := k)).obj (rightFreeObj (k := k) (S := S) M) :=
  (rightFreeUnderlying _).trans
    ((TensorProduct.congr (LeftCoinduced.underlying M) (LinearEquiv.refl k _)).trans
      ((rTensorHomEquivHomRTensor k R M (rightRegularObj (S := S))).trans
        (((rightFreeRestrictionUnderlying M).symm.congrRight).trans
          (coindUnderlying _).symm)))

lemma coindTensorUnderlying_tmul (M : ModuleCat R)
    (φ : (LeftCoinduced.J (k := k)).obj M) (s : rightRegularObj (S := S)) (r : R) :
    (coindUnderlying _ (coindTensorUnderlying (S := S) M (φ ⊗ₜ[k] s))) r =
      (LeftCoinduced.underlying M φ r) ⊗ₜ[k] s := by
  change rTensorHomEquivHomRTensor k R M (rightRegularObj (S := S))
    ((LeftCoinduced.underlying M φ) ⊗ₜ[k] s) r = _
  rw [rTensorHomEquivHomRTensor_apply]
  rfl

def coindTensorEquiv (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.J (k := k)).obj M) ≃ₗ[Alg k R S]
      (coindEndo (k := k)).obj (rightFreeObj (k := k) (S := S) M) where
  __ := (coindTensorUnderlying M).toAddEquiv
  map_smul' a z := by
    apply (coindUnderlying _).injective
    change (coindUnderlying _ (coindTensorUnderlying M (OuterTensor.action k R Sᵐᵒᵖ _ _ a z))) =
      (action (k := k) (R := R) (S := S)
        (Coind (k := k) (R := R) ((rightFunctor (k := k)).obj (rightFreeObj M))) a)
          (coindUnderlying _ (coindTensorUnderlying M z))
    induction a using TensorProduct.inductionOn with
    | add a b ha hb =>
      erw [map_add,LinearMap.add_apply,map_add,map_add,map_add,LinearMap.add_apply,ha,hb]
      rfl
    | tmul a b =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy =>
        let forward := (coindUnderlying ((rightFunctor (k := k)).obj
          (rightFreeObj (S := S) M))).toLinearMap.comp (coindTensorUnderlying M).toLinearMap
        let outer := OuterTensor.action k R Sᵐᵒᵖ
          ((LeftCoinduced.J (k := k)).obj M) (rightRegularObj (S := S)) (a ⊗ₜ[k] b)
        let target := action (k := k) (R := R) (S := S)
          (Coind (k := k) (R := R) ((rightFunctor (k := k)).obj (rightFreeObj (S := S) M)))
            (a ⊗ₜ[k] b)
        change forward (outer (x+y)) = target (forward (x+y))
        change forward (outer x) = target (forward x) at hx
        change forward (outer y) = target (forward y) at hy
        exact (congrArg forward (outer.map_add x y)).trans
          ((forward.map_add _ _).trans
            ((congrArg₂ (· + ·) hx hy).trans
              ((target.map_add _ _).symm.trans
                (congrArg target (forward.map_add x y).symm))))
      | tmul φ s =>
        apply LinearMap.ext
        intro r
        rw [show OuterTensor.action k R Sᵐᵒᵖ _ _ (a ⊗ₜ[k] b) (φ ⊗ₜ[k] s) =
          (a • φ) ⊗ₜ[k] (b • s) from rfl,coindTensorUnderlying_tmul]
        change (LeftCoinduced.underlying M (a • φ) r) ⊗ₜ[k] (b • s) =
          b • (coindUnderlying _ (coindTensorUnderlying M (φ ⊗ₜ[k] s)) (r*a))
        rw [coindTensorUnderlying_tmul]
        change ((LeftCoinduced.underlying M φ) (r*a)) ⊗ₜ[k] (b • s) =
          ((1:R) • ((LeftCoinduced.underlying M φ) (r*a))) ⊗ₜ[k] (b • s)
        rw [one_smul]

def coindTensorIso (M : ModuleCat R) :
    rightFreeObj (k := k) (S := S) ((LeftCoinduced.J (k := k)).obj M) ≅
      (coindEndo (k := k)).obj (rightFreeObj (k := k) (S := S) M) :=
  (coindTensorEquiv M).toModuleIso

lemma coindTensor_unit (M : ModuleCat R) :
    (rightFreeFunctor (k := k) (S := S)).map ((LeftCoinduced.unit (k := k)).app M) ≫
      (coindTensorIso M).hom = coindUnit (rightFreeObj M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => erw [map_add,map_add,hx,hy]
  | tmul x s =>
    apply (coindUnderlying _).injective
    apply LinearMap.ext
    intro r
    change coindUnderlying _ (coindTensorUnderlying M
      (((LeftCoinduced.unit (k := k)).app M x) ⊗ₜ[k] s)) r = _
    rw [coindTensorUnderlying_tmul]
    change (r • x) ⊗ₜ[k] s = (r • x) ⊗ₜ[k] ((1:Sᵐᵒᵖ) • s)
    rw [one_smul]

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (M : FiniteModule k (Alg k R S))

def leftResolution : ProjectiveResolution (ModuleCat.of R (Obj M.obj)) :=
  resolutionOfExact _ (fun n => ModuleCat.of R (Obj (ModuleCat.of (Alg k R S) (M.posTerm n))))
    (fun n => ModuleCat.ofHom (leftMap (ModuleCat.ofHom (M.posDifferential n))))
    (ModuleCat.ofHom (leftMap (ModuleCat.ofHom M.cover.map)))
    M.pos_exact M.pos_augmentation_exact M.cover.surjective
    (fun n => by
      have := freeLeftProjective (k := k) (R := R) (S := S) (M.positive n).cover.rank
      infer_instance)

def rightResolution : ProjectiveResolution (ModuleCat.of Sᵐᵒᵖ (Obj M.obj)) :=
  resolutionOfExact _ (fun n => ModuleCat.of Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k R S) (M.posTerm n))))
    (fun n => ModuleCat.ofHom (rightMap (ModuleCat.ofHom (M.posDifferential n))))
    (ModuleCat.ofHom (rightMap (ModuleCat.ofHom M.cover.map)))
    M.pos_exact M.pos_augmentation_exact M.cover.surjective
    (fun n => by
      have := freeRightProjective (k := k) (R := R) (S := S) (M.positive n).cover.rank
      infer_instance)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

lemma coind_ext_zero (M : FiniteModule k (Alg k R S))
    [Module.Projective Sᵐᵒᵖ (Obj M.obj)] (N : ModuleCat Sᵐᵒᵖ) (n : ℕ) :
    Subsingleton (Ext M.obj (coindObj (k := k) (R := R) N) (n+1)) := by
  let P := M.projectiveResolution
  let Q := rightResolution M
  have hd (i : ℕ) : P.complex.d (i+1) i = ModuleCat.ofHom (M.posDifferential i) := by
    dsimp [P, FiniteModule.projectiveResolution, resolutionOfExact]
    exact ChainComplex.of_d _ _ _
  have he (i : ℕ) : Q.complex.d (i+1) i =
      ModuleCat.ofHom (rightMap (ModuleCat.ofHom (M.posDifferential i))) := by
    dsimp [Q, rightResolution, resolutionOfExact]
    exact ChainComplex.of_d _ _ _
  let : Subsingleton (Ext (ModuleCat.of Sᵐᵒᵖ (Obj M.obj)) N (n+1)) :=
    Ext.subsingleton_of_projective _ _ n
  apply ext_subsingleton_of_boundaries P n
  intro f hf
  let f' : Q.complex.X (n+1) ⟶ N :=
    ModuleCat.ofHom (coindEvaluate (P.complex.X (n+1)) N f)
  have hf' : Q.complex.d (n+2) (n+1) ≫ f' = 0 := by
    rw [he]
    apply ModuleCat.hom_ext
    change (coindEvaluate _ N f).comp (rightMap (ModuleCat.ofHom (M.posDifferential (n+1)))) = 0
    erw [← coindEvaluate_natural]
    rw [hd (n+1)] at hf
    erw [hf]
    exact (coindHomEquiv _ N).map_zero
  obtain ⟨g,hg⟩ := boundaries_of_ext_subsingleton Q n f' hf'
  let g' : P.complex.X n ⟶ coindObj (k := k) (R := R) N :=
    coindExtend _ N g.hom
  refine ⟨g', ?_⟩
  apply (coindHomEquiv _ N).injective
  change coindEvaluate _ N (P.complex.d (n+1) n ≫ g') = coindEvaluate _ N f
  rw [coindEvaluate_natural,show coindEvaluate _ N g' = g.hom from coindEvaluate_extend _ _ _]
  rw [hd]
  rw [he] at hg
  exact ModuleCat.hom_ext_iff.mp hg

lemma regular_coind_ext_zero (N : ModuleCat Rᵐᵒᵖ) (n : ℕ) :
    Subsingleton (Ext (regular (k := k) (R := R))
      (coindObj (k := k) (R := R) N) (n+1)) := by
  let : Module.Projective Rᵐᵒᵖ R :=
    Module.Projective.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  let : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) :=
    Module.Projective.of_equiv (regularRightEquiv (k := k) (R := R)).symm
  let M := regularFinite (k := k) (R := R)
  let : Module.Projective Rᵐᵒᵖ (Obj M.obj) :=
    show Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) from inferInstance
  exact coind_ext_zero M N n

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def dualLeftObj : ModuleCat R := ModuleCat.of R (DualBimodule k R)

def dualLeftUnderlying : dualLeftObj (k := k) (R := R) ≃ₗ[k] Module.Dual k R :=
  moduleCatUnderlyingEquiv (k := k) (R := R) (DualBimodule k R)

instance [FiniteDimensional k R] : FiniteDimensional k (dualLeftObj (k := k) (R := R)) :=
  Module.Finite.equiv (dualLeftUnderlying (k := k) (R := R)).symm
instance [FiniteDimensional k R] : Module.Finite R (dualLeftObj (k := k) (R := R)) :=
  Module.Finite.of_restrictScalars_finite k R _

def dualRegularObj : ModuleCat (Alg k R R) :=
  ofBimodule (k := k) (R := R) (S := R) (DualBimodule k R)

def dualRegularLeftEquiv : Obj (dualRegularObj (k := k) (R := R)) ≃ₗ[R] DualBimodule k R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r • ((1:Rᵐᵒᵖ) • (show DualBimodule k R from x)) = r • (show DualBimodule k R from x)
    rw [one_smul]

instance dualRegularLeftInjective : Module.Injective R (Obj (dualRegularObj (k := k) (R := R))) :=
  Module.Baer.injective (Module.Baer.of_equiv (dualRegularLeftEquiv (k := k) (R := R)).symm
    (Module.Baer.of_injective inferInstance))

variable [FiniteDimensional k R] (N : ModuleCat Sᵐᵒᵖ)

def dualOuterUnderlying :
    OuterTensor.Obj k R Sᵐᵒᵖ (dualLeftObj (k := k) (R := R)) N ≃ₗ[k]
      (R →ₗ[k] N) :=
  (TensorProduct.congr (dualLeftUnderlying (k := k) (R := R)) (LinearEquiv.refl k N)).trans
    (dualTensorHomEquiv k R N)

lemma dualOuterUnderlying_tmul (φ : dualLeftObj (k := k) (R := R)) (x : N) (r : R) :
    dualOuterUnderlying N (φ ⊗ₜ[k] x) r = (dualLeftUnderlying φ r) • x := rfl

def dualOuterEquiv :
    OuterTensor.Obj k R Sᵐᵒᵖ (dualLeftObj (k := k) (R := R)) N ≃ₗ[Alg k R S]
      coindObj (k := k) (R := R) N where
  __ := ((dualOuterUnderlying N).trans (coindUnderlying N).symm).toAddEquiv
  map_smul' a z := by
    apply (coindUnderlying N).injective
    change dualOuterUnderlying N ((OuterTensor.action k R Sᵐᵒᵖ _ N a) z) =
      action (k := k) (R := R) (S := S) (Coind (k := k) (R := R) N) a (dualOuterUnderlying N z)
    induction a using TensorProduct.inductionOn with
    | add a b ha hb =>
      erw [map_add,LinearMap.add_apply,map_add,map_add,LinearMap.add_apply,ha,hb]
      rfl
    | tmul r s =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => erw [map_add,map_add,map_add,hx,hy,map_add]; rfl
      | tmul φ x =>
        apply LinearMap.ext; intro c
        change (show Module.Dual k R from φ) (c*r) • (s • x) =
          s • ((show Module.Dual k R from φ) (c*r) • x)
        exact smul_comm _ _ _

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R]

instance rightRegularProjective : Module.Projective Sᵐᵒᵖ (rightRegularObj (S := S)) :=
  inferInstanceAs (Module.Projective Sᵐᵒᵖ Sᵐᵒᵖ)
instance rightRegularFinite : Module.Finite Sᵐᵒᵖ (rightRegularObj (S := S)) :=
  inferInstanceAs (Module.Finite Sᵐᵒᵖ Sᵐᵒᵖ)

omit [FiniteDimensional k R] in
lemma rightFree_map_exact {A B C : ModuleCat R} (f : A ⟶ B) (g : B ⟶ C)
    (h : Function.Exact f g) :
    Function.Exact ((rightFreeFunctor (k := k) (S := S)).map f)
      ((rightFreeFunctor (k := k) (S := S)).map g) :=
  Module.Flat.rTensor_exact (rightRegularObj (S := S))
    (show Function.Exact (f.hom.restrictScalars k) (g.hom.restrictScalars k) from h)

omit [FiniteDimensional k R] in
lemma rightFree_map_surjective {A B : ModuleCat R} (f : A ⟶ B) (h : Function.Surjective f) :
    Function.Surjective ((rightFreeFunctor (k := k) (S := S)).map f) :=
  LinearMap.rTensor_surjective (rightRegularObj (S := S))
    (show Function.Surjective (f.hom.restrictScalars k) from h)

variable (M : FiniteModule k R)

def rightFreeResolution : ProjectiveResolution (rightFreeObj (k := k) (S := S) M.obj) := by
  let F := rightFreeFunctor (k := k) (R := R) (S := S)
  apply resolutionOfExact _ (fun n => F.obj (ModuleCat.of R (M.posTerm n)))
    (fun n => F.map (ModuleCat.ofHom (M.posDifferential n)))
    (F.map (ModuleCat.ofHom M.cover.map))
  · intro n
    exact rightFree_map_exact _ _ (M.pos_exact n)
  · exact rightFree_map_exact _ _ M.pos_augmentation_exact
  · exact rightFree_map_surjective _ M.cover.surjective
  · intro n
    let : Module.Projective (Alg k R S) (F.obj (ModuleCat.of R (M.posTerm n))) :=
      OuterTensor.projective k R Sᵐᵒᵖ (ModuleCat.of R (M.posTerm n))
        (rightRegularObj (S := S))
    infer_instance

lemma rightFreeResolution_d (n : ℕ) :
    (rightFreeResolution (S := S) M).complex.d (n+1) n =
      (rightFreeFunctor (k := k) (S := S)).map (ModuleCat.ofHom (M.posDifferential n)) := by
  dsimp [rightFreeResolution, resolutionOfExact]
  exact ChainComplex.of_d _ _ _

lemma rightFree_ext_zero (Q : ModuleCat (Alg k R S)) [Module.Injective R (Obj Q)] (n : ℕ) :
    Subsingleton (Ext (rightFreeObj (k := k) (S := S) M.obj) Q (n+1)) := by
  let P := M.projectiveResolution
  let T := rightFreeResolution (S := S) M
  have hd (i : ℕ) : P.complex.d (i+1) i = ModuleCat.ofHom (M.posDifferential i) := by
    dsimp [P, FiniteModule.projectiveResolution, resolutionOfExact]
    exact ChainComplex.of_d _ _ _
  let : Injective (ModuleCat.of R (Obj Q)) := Module.injective_object_of_injective_module R (Obj Q)
  let : Subsingleton (Ext M.obj (ModuleCat.of R (Obj Q)) (n+1)) :=
    Ext.subsingleton_of_injective _ _ n
  apply ext_subsingleton_of_boundaries T n
  intro f hf
  let f' : P.complex.X (n+1) ⟶ ModuleCat.of R (Obj Q) :=
    ModuleCat.ofHom (rightFreeEvaluate (P.complex.X (n+1)) Q f)
  have hf' : P.complex.d (n+2) (n+1) ≫ f' = 0 := by
    rw [hd]
    apply ModuleCat.hom_ext
    change (rightFreeEvaluate _ Q f).comp (M.posDifferential (n+1)) = 0
    rw [rightFreeResolution_d] at hf
    exact congrArg (rightFreeEvaluate (ModuleCat.of R (M.posTerm (n+2))) Q) hf
  obtain ⟨g,hg⟩ := boundaries_of_ext_subsingleton P n f' hf'
  let g' : T.complex.X n ⟶ Q := rightFreeExtend _ Q g.hom
  refine ⟨g', ?_⟩
  apply (rightFreeHomEquiv _ Q).injective
  change rightFreeEvaluate _ Q (T.complex.d (n+1) n ≫ g') = rightFreeEvaluate _ Q f
  erw [rightFreeResolution_d, rightFreeEvaluate_natural]
  rw [show rightFreeEvaluate _ Q g' = g.hom from rightFreeEvaluate_extend _ _ _]
  rw [hd] at hg
  exact ModuleCat.hom_ext_iff.mp hg

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

def ordinaryOuterObj : ModuleCat (Alg k R R) :=
  rightFreeObj (k := k) (S := R) (dualLeftObj (k := k) (R := R))

lemma regular_outer_ext_zero (n : ℕ) :
    Subsingleton (Ext (regular (k := k) (R := R)) (ordinaryOuterObj (k := k) (R := R)) (n+1)) := by
  let e : ordinaryOuterObj (k := k) (R := R) ≅
      coindObj (k := k) (R := R) (rightRegularObj (S := R)) :=
    (dualOuterEquiv (rightRegularObj (S := R))).toModuleIso
  let := regular_coind_ext_zero (k := k) (R := R) (rightRegularObj (S := R)) n
  exact Function.Injective.subsingleton (extIso (k := k) (Iso.refl _) e (n+1)).injective

def dualLeftFinite : FiniteModule k R := ⟨dualLeftObj (k := k) (R := R), inferInstance⟩

lemma outer_dual_ext_zero (n : ℕ) :
    Subsingleton (Ext (ordinaryOuterObj (k := k) (R := R)) (dualRegularObj (k := k) (R := R)) (n+1)) :=
  rightFree_ext_zero (dualLeftFinite (k := k) (R := R)) (dualRegularObj (k := k) (R := R)) n

theorem two_orthogonalities (n : ℕ) :
    Subsingleton (Ext (regular (k := k) (R := R)) (ordinaryOuterObj (k := k) (R := R)) (n+1)) ∧
    Subsingleton (Ext (ordinaryOuterObj (k := k) (R := R)) (dualRegularObj (k := k) (R := R)) (n+1)) :=
  ⟨regular_outer_ext_zero n, outer_dual_ext_zero n⟩

end Tachikawa.Enveloping

end

end OAI
