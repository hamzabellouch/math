import OAI.RingTheory.Tachikawa.Induction

namespace OAI


noncomputable section
namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)

def restrictedLeftResolution :
    ProjectiveResolution ((AlgebraInduction.res (inclusionB q)).obj (ModuleCat.of (E q) (E q))) :=
  Tachikawa.transportResolution (eLeftResolution q hq) (eLeftRestrictionIso q)

lemma restrictedLeftResolution_above (n : ℕ) (hn : 4 < n) :
    IsZero ((restrictedLeftResolution q hq).complex.X n) := eLeftResolution_above q hq n hn

def restrictedRightResolution :
    ProjectiveResolution ((AlgebraInduction.res (inclusionB q).op).obj
      (ModuleCat.of (E q)ᵐᵒᵖ (E q)ᵐᵒᵖ)) :=
  Tachikawa.transportResolution
    ((opTensorRestriction q).mapProjectiveResolution (eRightResolution q hq))
    (eRightRestrictionIso q)

lemma restrictedRightResolution_above (n : ℕ) (hn : 4 < n) :
    IsZero ((restrictedRightResolution q hq).complex.X n) :=
  (opTensorRestriction q).map_isZero (eRightResolution_above q hq n hn)

include hq in
lemma c5_left_projective : Module.Projective (E q)
    (Enveloping.Obj (Enveloping.inducedCokerFive (inclusionB q)).obj) :=
  Enveloping.inducedCoker_left_projective (inclusionB q) (restrictedLeftResolution q hq) 4
    (restrictedLeftResolution_above q hq 5 (by omega))

include hq in
lemma c5_right_projective : Module.Projective (E q)ᵐᵒᵖ
    (Enveloping.Obj (Enveloping.inducedCokerFive (inclusionB q)).obj) :=
  Enveloping.inducedCoker_right_projective (inclusionB q) (restrictedRightResolution q hq) 4
    (restrictedRightResolution_above q hq 5 (by omega))

abbrev Y : FiniteModule k (Enveloping.Alg k (E q) (E q)) :=
  Enveloping.inducedY (inclusionB q) (formE q)

include hq in
lemma Y_side_projective : Module.Projective (E q) (Enveloping.Obj (Y q).obj) ∧
    Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (Y q).obj) := by
  let := c5_left_projective q hq
  let := c5_right_projective q hq
  exact Enveloping.negative_side_projective (formE q) (formE q)
    (Enveloping.inducedCokerFive (inclusionB q)) 4

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q : k)

def cSimpleCanon : ModuleCat (C k q) := ModuleCat.of (C k q) (C.Simple q)

omit [CharP k 2] in
def cSimpleUnderlying : cSimpleCanon q ≃ₗ[k] k where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change C.character q (algebraMap k (C k q) c) * (show k from x) = c * (show k from x)
    rw [AlgHom.commutes]
    simp

omit [CharP k 2] in
def bSimpleTensorUnderlying : OuterTensor.Obj k (C k q) (C k q)
    (cSimpleCanon q) (cSimpleCanon q) ≃ₗ[k] k :=
  (TensorProduct.congr (cSimpleUnderlying q) (cSimpleUnderlying q)).trans (TensorProduct.lid k k)

omit [CharP k 2] in
lemma bSimpleTensorUnderlying_smul (a : B q)
    (x : OuterTensor.Obj k (C k q) (C k q)
      (cSimpleCanon q) (cSimpleCanon q)) :
    bSimpleTensorUnderlying q (a • x) = characterB q a * bSimpleTensorUnderlying q x := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [add_smul, map_add, ha, hb, add_mul]
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => erw [smul_add, map_add, hx, hy, map_add, mul_add]
    | tmul x y =>
      change (C.character q a * cSimpleUnderlying q x) *
        (C.character q b * cSimpleUnderlying q y) =
        (C.character q a * C.character q b) * (cSimpleUnderlying q x * cSimpleUnderlying q y)
      ring

omit [CharP k 2] in

def bSimpleTensorRestrictionEquiv : bSimpleTensor q ≃ₗ[B q]
    (AlgebraInduction.res (inclusionB q)).obj (ModuleCat.of (E q) (X q)) where
  toFun := bSimpleTensorUnderlying q
  invFun := (bSimpleTensorUnderlying q).symm
  left_inv := (bSimpleTensorUnderlying q).left_inv
  right_inv := (bSimpleTensorUnderlying q).right_inv
  map_add' := (bSimpleTensorUnderlying q).map_add
  map_smul' a x := by
    change bSimpleTensorUnderlying q (a • x) =
      characterE q (inclusionB q a) * bSimpleTensorUnderlying q x
    rw [character_inclusion]
    exact bSimpleTensorUnderlying_smul q a x

omit [CharP k 2] in
def bSimpleTensorRestrictionIso : bSimpleTensor q ≅
    (AlgebraInduction.res (inclusionB q)).obj (ModuleCat.of (E q) (X q)) :=
  LinearEquiv.toModuleIso (bSimpleTensorRestrictionEquiv q)

def restrictedXResolution (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ProjectiveResolution ((AlgebraInduction.res (inclusionB q)).obj (ModuleCat.of (E q) (X q))) :=
  Tachikawa.transportResolution (bSimpleTensorResolution q hp) (bSimpleTensorRestrictionIso q)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def evaluatedKComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    HomotopyEquiv
      (((Enveloping.evaluation (k := k) (ModuleCat.of (E q) (X q))).mapHomologicalComplex _).obj
        (Enveloping.inducedRegularComplex (inclusionB q)))
      (((AlgebraInduction.functor (inclusionB q)).mapHomologicalComplex _).obj
        (bSimpleTensorResolution q hp).complex) :=
  Enveloping.evaluatedInducedRegularComparison (inclusionB q)
    (ModuleCat.of (E q) (X q)) (restrictedXResolution q hp)

end Tachikawa.Construction



namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

abbrev inclusion : R →ₐ[k] TrivialExtension k R :=
  TrivSqZeroExt.inlAlgHom k R (DualBimodule k R)

def tensorGenerators (M : ModuleCat.{0} R) : M ⟶
    (AlgebraInduction.res (inclusion (k := k) (R := R))).obj
      ((functor (k := k) (R := R)).obj M) :=
  ModuleCat.ofHom
    (X := M)
    (Y := (AlgebraInduction.res (inclusion (k := k) (R := R))).obj
      ((functor (k := k) (R := R)).obj M))
    { toFun := fun m => (show Obj k R M from (m,0))
      map_add' := by
        intro x y
        apply Prod.ext
        · rfl
        · exact (zero_add _).symm
      map_smul' := by
        intro r m
        change (r • m, (0 : Nakayama k R M)) =
          (TrivSqZeroExt.inl r : TrivialExtension k R) • (show Obj k R M from (m,0))
        rw [inl_smul]
        apply Prod.ext
        · rfl
        · exact (smul_zero r).symm }

def tensorComparison (M : ModuleCat.{0} R) :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M ⟶
      (functor (k := k) (R := R)).obj M :=
  AlgebraInduction.extend (inclusion (k := k) (R := R)) (tensorGenerators M)

@[simp] lemma tensorComparison_mk (M : ModuleCat.{0} R)
    (a : AlgebraInduction.Bimod (inclusion (k := k) (R := R))) (m : M) :
    tensorComparison (k := k) M (BalancedTensor.mk a m) =
      (show TrivialExtension k R from a) • unit m := rfl

def tensorPure (M : ModuleCat.{0} R) :
    AlgebraInduction.Bimod (inclusion (k := k) (R := R)) →ₗ[TrivialExtension k R]
      M →ₗ[k] BalancedTensor.T (k := k) (R := R) (S := TrivialExtension k R)
        (M := AlgebraInduction.Bimod (inclusion (k := k) (R := R))) (N := M) :=
  BalancedTensor.mk

lemma tensorPure_inr_smul (M : ModuleCat.{0} R) (r : R) (φ : DualBimodule k R) (m : M) :
    tensorPure (k := k) M
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr (r • φ) : TrivialExtension k R)) m =
    (TrivSqZeroExt.inl r : TrivialExtension k R) • tensorPure (k := k) M
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) m := by
  have h := LinearMap.congr_fun ((tensorPure (k := k) M).map_smul
    (TrivSqZeroExt.inl r : TrivialExtension k R)
    (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (TrivSqZeroExt.inr φ : TrivialExtension k R))) m
  have hr : (TrivSqZeroExt.inl r : TrivialExtension k R) •
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) =
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr (r • φ) : TrivialExtension k R)) :=
    TrivSqZeroExt.inl_mul_inr r φ
  rw [hr] at h
  exact h

def lowerBilinear (M : ModuleCat.{0} R) : DualBimodule k R →ₗ[R] M →ₗ[k]
    (AlgebraInduction.res (inclusion (k := k) (R := R))).obj ((AlgebraInduction.functor (inclusion (k := k))).obj M) where
  toFun φ :=
    { toFun := fun m => tensorPure (k := k) M (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) m
      map_add' := fun x y => (tensorPure (k := k) M _).map_add x y
      map_smul' := by
        intro c x
        change tensorPure (k := k) M _ (c • x) = (algebraMap k (TrivialExtension k R) c) • tensorPure (k := k) M _ x
        rw [IsScalarTower.algebraMap_smul]
        exact (tensorPure (k := k) M _).map_smul c x }
  map_add' φ ψ := by
    apply LinearMap.ext
    intro m
    change tensorPure (k := k) M (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
      (TrivSqZeroExt.inr (φ+ψ) : TrivialExtension k R)) m = _
    rw [TrivSqZeroExt.inr_add]
    exact LinearMap.congr_fun ((tensorPure (k := k) M).map_add _ _) m
  map_smul' r φ := by
    apply LinearMap.ext
    intro m
    exact tensorPure_inr_smul M r φ m

lemma lowerBilinear_balanced (M : ModuleCat.{0} R) (r : R) (φ : DualBimodule k R) (m : M) :
    lowerBilinear (k := k) M (MulOpposite.op r • φ) m = lowerBilinear (k := k) M φ (r • m) := by
  have h := BalancedTensor.balance (k := k) (R := R) (S := TrivialExtension k R)
    r (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (TrivSqZeroExt.inr φ : TrivialExtension k R)) m
  have hr : MulOpposite.op r •
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr φ : TrivialExtension k R)) =
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        (TrivSqZeroExt.inr (MulOpposite.op r • φ) : TrivialExtension k R)) :=
    TrivSqZeroExt.inr_mul_inl r φ
  rw [hr] at h
  exact h

def lowerTensor (M : ModuleCat.{0} R) :
    BalancedTensor.T (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M) →ₗ[R]
    (AlgebraInduction.res (inclusion (k := k) (R := R))).obj ((AlgebraInduction.functor (inclusion (k := k))).obj M) :=
  BalancedTensor.lift (lowerBilinear (k := k) M) (lowerBilinear_balanced M)

variable [FiniteDimensional k R] (M : ModuleCat.{0} R) [FiniteDimensional k M]

def tensorInverse (x : Obj k R M) :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M :=
  AlgebraInduction.unit (inclusion (k := k) (R := R)) M x.1 +
    lowerTensor (k := k) M ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2)

omit [FiniteDimensional k R] [FiniteDimensional k M] in
lemma tensorComparison_lower (z : BalancedTensor.T (k := k) (R := R) (S := R)
    (M := DualBimodule k R) (N := M)) :
    tensorComparison (k := k) M (lowerTensor (k := k) M z) = (0, Nakayama.evaluation z) := by
  induction z using BalancedTensor.induction_on with
  | h0 => rfl
  | ht φ m =>
    apply Prod.ext
    · change (0:R) • m = 0
      simp
    · change Nakayama.evaluationBilinear φ m + (0:R) • (0 : Nakayama k R M) = _
      rw [zero_smul, add_zero]
      rfl
  | ha x y hx hy =>
    erw [map_add, map_add, hx, hy, map_add]
    apply Prod.ext
    · exact zero_add _
    · rfl

lemma tensorComparison_inverse (x : Obj k R M) :
    tensorComparison (k := k) M (tensorInverse (k := k) M x) = x := by
  change tensorComparison (k := k) M (AlgebraInduction.unit (inclusion (k := k) (R := R)) M x.1 +
    lowerTensor (k := k) M ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2)) = x
  erw [map_add, tensorComparison_lower]
  have he := (Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).apply_symm_apply x.2
  change Nakayama.evaluation ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2) = x.2 at he
  rw [he]
  change (1 : TrivialExtension k R) • unit x.1 + (0,x.2) = x
  erw [one_smul]
  apply Prod.ext
  · exact add_zero _
  · exact zero_add _

lemma tensorInverse_zero : tensorInverse (k := k) M 0 = 0 := by
  change AlgebraInduction.unit (inclusion (k := k) (R := R)) M 0 + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm 0) = 0
  simp

lemma tensorInverse_add (x y : Obj k R M) :
    tensorInverse (k := k) M (x+y) = tensorInverse (k := k) M x + tensorInverse (k := k) M y := by
  change AlgebraInduction.unit (inclusion (k := k) (R := R)) M (x.1+y.1) + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm (x.2+y.2)) = _
  simp only [map_add]
  change _ = (AlgebraInduction.unit (inclusion (k := k) (R := R)) M x.1 + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm x.2)) +
    (AlgebraInduction.unit (inclusion (k := k) (R := R)) M y.1 + lowerTensor (k := k) M
    ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm y.2))
  abel

lemma tensorInverse_comparison (z : (AlgebraInduction.functor
    (inclusion (k := k) (R := R))).obj M) :
    tensorInverse (k := k) M (tensorComparison (k := k) M z) = z := by
  induction z using BalancedTensor.induction_on with
  | h0 =>
    exact (congrArg (tensorInverse (k := k) M)
      (tensorComparison (k := k) M).hom.map_zero).trans (tensorInverse_zero M)
  | ha x y hx hy =>
    erw [map_add, tensorInverse_add, hx, hy]
    rfl
  | ht a m =>
    have he : (tensorComparison (k := k) M (BalancedTensor.mk a m) : Obj k R M) =
        ((show TrivialExtension k R from a).fst • m,
          Nakayama.evaluationBilinear (show TrivialExtension k R from a).snd m) := by
      apply Prod.ext
      · rfl
      · change Nakayama.evaluationBilinear _ m + _ • (0 : Nakayama k R M) = _
        rw [smul_zero, add_zero]
    rw [he]
    change AlgebraInduction.unit (inclusion (k := k) (R := R)) M ((show TrivialExtension k R from a).fst • m) +
      lowerTensor (k := k) M ((Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm
        (Nakayama.evaluationBilinear (show TrivialExtension k R from a).snd m)) = _
    have hinv : (Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm
        (Nakayama.evaluationBilinear (show TrivialExtension k R from a).snd m) =
        BalancedTensor.mk (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M) (show TrivialExtension k R from a).snd m := by
      have h := (Nakayama.evaluationEquiv (k := k) (R := R) (M := M)).symm_apply_apply
        (BalancedTensor.mk (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M) (show TrivialExtension k R from a).snd m)
      exact h
    rw [hinv]
    change BalancedTensor.mk (k := k) (R := R) (S := TrivialExtension k R)
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (1 : TrivialExtension k R)) ((show TrivialExtension k R from a).fst • m) +
      BalancedTensor.mk (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        TrivSqZeroExt.inr (show TrivialExtension k R from a).snd) m = _
    rw [← BalancedTensor.balance]
    change BalancedTensor.mk (k := k) (R := R) (S := TrivialExtension k R)
      (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from (1 : TrivialExtension k R) * TrivSqZeroExt.inl
        (show TrivialExtension k R from a).fst) m +
      BalancedTensor.mk (show AlgebraInduction.Bimod (inclusion (k := k) (R := R)) from
        TrivSqZeroExt.inr (show TrivialExtension k R from a).snd) m = _
    erw [one_mul]
    erw [← LinearMap.add_apply, ← map_add]
    exact congrArg (fun t : AlgebraInduction.Bimod (inclusion (k := k) (R := R)) =>
      BalancedTensor.mk (k := k) (R := R) (S := TrivialExtension k R) t m)
      (TrivSqZeroExt.inl_fst_add_inr_snd_eq (show TrivialExtension k R from a))

def tensorComparisonEquiv :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M ≃ₗ[TrivialExtension k R]
      (functor (k := k) (R := R)).obj M :=
  LinearEquiv.ofBijective (tensorComparison (k := k) M).hom
    ⟨Function.LeftInverse.injective (tensorInverse_comparison M),
      Function.RightInverse.surjective (tensorComparison_inverse M)⟩

def tensorComparisonIso :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M ≅
      (functor (k := k) (R := R)).obj M :=
  LinearEquiv.toModuleIso (tensorComparisonEquiv M)

end Tachikawa.TrivialInduction



namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

lemma tensorComparison_natural {M N : ModuleCat.{0} R} (f : M ⟶ N) :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).map f ≫
      tensorComparison (k := k) N =
    tensorComparison (k := k) M ≫ (functor (k := k)).map f := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro a m
  change (show TrivialExtension k R from a) • unit (f m) =
    map (k := k) (R := R) f.hom ((show TrivialExtension k R from a) • unit m)
  rw [map_smul, map_unit]

variable [FiniteDimensional k R]

def tensorComplexIso {ι : Type} {c : ComplexShape ι}
    (P : HomologicalComplex (ModuleCat.{0} R) c)
    [∀ i, FiniteDimensional k (P.X i)] :
    (((AlgebraInduction.functor (inclusion (k := k) (R := R))).mapHomologicalComplex c).obj P) ≅
      (((functor (k := k) (R := R)).mapHomologicalComplex c).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => tensorComparisonIso (P.X i)) (fun i j _ => (tensorComparison_natural (P.d i j)).symm)

end Tachikawa.TrivialInduction



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma resObj_finite_k (n : ℕ) : Module.Finite k (resObj q n) := by
  have hf : Module.Finite (C k q) (resObj q n) := by
    cases n with
    | zero =>
      let : Module.Finite k (Cf q) := Module.Finite.of_injective
        ((Cf q).subtype.restrictScalars k) Subtype.val_injective
      exact Module.Finite.of_restrictScalars_finite k (C k q) (Cf q)
    | succ n =>
      let : Module.Finite k (Ce q) := Module.Finite.of_injective
        ((Ce q).subtype.restrictScalars k) Subtype.val_injective
      exact Module.Finite.of_restrictScalars_finite k (C k q) (Ce q)
  let := hf
  exact Module.Finite.trans (C k q) (resObj q n)

lemma projectiveResolution_d (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    (projectiveResolution q hp).complex.d (n+1) n = resD q n := by
  dsimp only [projectiveResolution, resolutionOfExact]
  exact ChainComplex.of_d _ _ _

def inducedJComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (((AlgebraInduction.functor (TrivialInduction.inclusion (k := k) (R := C k q))).mapHomologicalComplex _).obj
      (projectiveResolution q hp).complex) ≅ inducedComplex q hp := by
  letI : ∀ n, Module.Finite k ((projectiveResolution q hp).complex.X n) :=
    fun n => resObj_finite_k q n
  refine (TrivialInduction.tensorComplexIso (projectiveResolution q hp).complex) ≪≫ ?_
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro i j hij
  have h : j+1 = i := by simpa using hij
  subst i
  symm
  change ModuleCat.ofHom (TrivialInduction.map (k := k) (R := C k q)
    ((projectiveResolution q hp).complex.d (j+1) j).hom) = _
  rw [projectiveResolution_d, inducedComplex_d]
  rfl

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev balancedInducedResolution (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :=
  ((AlgebraInduction.functor (TrivialInduction.inclusion (k := k) (R := C k q))).mapHomologicalComplex _).obj
    (projectiveResolution q hp).complex

def inducedJTensorComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    mapBifunctor (balancedInducedResolution q hp) (balancedInducedResolution q hp)
      (OuterTensor.bifunctor k (T q) (T q)) (.down ℕ) ≅
    mapBifunctor (inducedComplex q hp) (inducedComplex q hp)
      (OuterTensor.bifunctor k (T q) (T q)) (.down ℕ) := by
  let F := (OuterTensor.bifunctor k (T q) (T q)).map₂HomologicalComplex
    (.down ℕ) (.down ℕ) (.down ℕ)
  exact ((F.mapIso (inducedJComparison q hp)).app (balancedInducedResolution q hp)) ≪≫
    ((F.obj (inducedComplex q hp)).mapIso (inducedJComparison q hp))

end Tachikawa.C



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T)
  (P : ChainComplex (ModuleCat A) ℕ) (Q : ChainComplex (ModuleCat B) ℕ)

abbrev outerDouble := ((bifunctor k A B).mapBifunctorHomologicalComplex
  (.down ℕ) (.down ℕ)).obj P |>.obj Q

abbrev inducedOuterDouble :=
  ((bifunctor k S T).mapBifunctorHomologicalComplex (.down ℕ) (.down ℕ)).obj
    (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj P) |>.obj
    (((AlgebraInduction.functor ψ).mapHomologicalComplex _).obj Q)

def inductionDoubleComparison :
    TotalMap.map₂ (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ))
      (outerDouble P Q) ⟶ inducedOuterDouble φ ψ P Q :=
  HomologicalComplex₂.homMk (fun ij => inductionComparison φ ψ (P.X ij.1) (Q.X ij.2))
    (by
      intro i i' j _
      have h := (inductionComparison_natural φ ψ (P.X i) (Q.X j)
        (P.d i i') (𝟙 (Q.X j))).symm
      rw [(AlgebraInduction.functor ψ).map_id] at h
      exact h)
    (by
      intro i j j' _
      have h := (inductionComparison_natural φ ψ (P.X i) (Q.X j)
        (𝟙 (P.X i)) (Q.d j j')).symm
      rw [(AlgebraInduction.functor φ).map_id] at h
      exact h)

instance inductionDoubleComparison_isIso : IsIso (inductionDoubleComparison φ ψ P Q) := by
  have (i j : ℕ) : IsIso (((inductionDoubleComparison φ ψ P Q).f i).f j) := by
    change IsIso (inductionComparison φ ψ (P.X i) (Q.X j))
    rw [← inductionIso_hom]
    infer_instance
  have (i : ℕ) : IsIso ((inductionDoubleComparison φ ψ P Q).f i) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact HomologicalComplex.Hom.isIso_of_components _

def inductionTotalIso :
    ((AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).mapHomologicalComplex _).obj
      (mapBifunctor P Q (bifunctor k A B) (.down ℕ)) ≅
    mapBifunctor
      (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj P)
      (((AlgebraInduction.functor ψ).mapHomologicalComplex _).obj Q)
      (bifunctor k S T) (.down ℕ) := by
  let F := AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)
  letI : PreservesColimits F :=
    (AlgebraInduction.adjunction (Algebra.TensorProduct.map φ ψ)).leftAdjoint_preservesColimits
  exact (TotalMap.iso F (outerDouble P Q) (.down ℕ)).symm ≪≫
    HomologicalComplex₂.total.mapIso (asIso (inductionDoubleComparison φ ψ P Q)) (.down ℕ)

end Tachikawa.OuterTensor



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def inducedBToJComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    (((AlgebraInduction.functor (inclusionB q)).mapHomologicalComplex _).obj
      (bSimpleTensorResolution q hp).complex) ≅
    mapBifunctor (C.inducedComplex q hp) (C.inducedComplex q hp)
      (OuterTensor.bifunctor k (T q) (T q)) (.down ℕ) :=
  OuterTensor.inductionTotalIso (inclusionC q) (inclusionC q)
    (C.projectiveResolution q hp).complex (C.projectiveResolution q hp).complex ≪≫
    C.inducedJTensorComparison q hp

def evaluatedKJComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    HomotopyEquiv
      (((Enveloping.evaluation (k := k) (ModuleCat.of (E q) (X q))).mapHomologicalComplex _).obj
        (Enveloping.inducedRegularComplex (inclusionB q)))
      (mapBifunctor (C.inducedComplex q hp) (C.inducedComplex q hp)
        (OuterTensor.bifunctor k (T q) (T q)) (.down ℕ)) :=
  (evaluatedKComparison q hp).trans (HomotopyEquiv.ofIso (inducedBToJComparison q hp))

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def homOfLinear {M N : ModuleCat.{0} (Alg k R S)} (f : M →ₗ[k] N)
    (hf : ∀ (r : R) (s : Sᵐᵒᵖ) (x : M), f ((r ⊗ₜ[k] s) • x) = (r ⊗ₜ[k] s) • f x) :
    M ⟶ N := ModuleCat.ofHom (X := M) (Y := N)
  { toFun := f
    map_add' := f.map_add
    map_smul' a x := by
      induction a using TensorProduct.inductionOn with
      | add a b ha hb => simp only [add_smul,map_add,ha,hb]
      | tmul r s => exact hf r s x }

end Tachikawa.Enveloping



namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def resUnderlyingEquiv (φ : R →ₐ[k] S) (M : ModuleCat.{0} S) :
    (res φ).obj M ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change φ (algebraMap k R c) • (show M from x) = c • (show M from x)
    rw [φ.commutes]
    rfl

instance resFinite (φ : R →ₐ[k] S) (M : ModuleCat.{0} S) [FiniteDimensional k M] :
    FiniteDimensional k ((res φ).obj M) :=
  Module.Finite.equiv (resUnderlyingEquiv φ M).symm

end Tachikawa.AlgebraInduction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def restrictedRegularMap (φ : R →ₐ[k] S) : regular (k := k) (R := R) ⟶
    (AlgebraInduction.res (envelopingMap φ)).obj (regular (k := k) (R := S)) :=
  homOfLinear
    ((AlgebraInduction.resUnderlyingEquiv (envelopingMap φ) (regular (k := k) (R := S))).symm.toLinearMap.comp
      (regularUnderlyingEquiv.symm.toLinearMap.comp
        (φ.toLinearMap.comp regularUnderlyingEquiv.toLinearMap))) (by
    intro r s x
    change φ (r * ((show R from x) * s.unop)) =
      φ r * (φ (show R from x) * φ s.unop)
    exact (φ.map_mul r ((show R from x) * s.unop)).trans
      (congrArg (fun z : S => φ r * z) (φ.map_mul (show R from x) s.unop)))

lemma restrictedRegularMap_apply (φ : R →ₐ[k] S) (x : R) :
    regularUnderlyingEquiv ((AlgebraInduction.resUnderlyingEquiv (envelopingMap φ)
      (regular (k := k) (R := S))) (restrictedRegularMap φ (regularUnderlyingEquiv.symm x))) = φ x := rfl

end Tachikawa.Enveloping



namespace Tachikawa.AlgebraInduction
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)
variable {ι : Type} (c : ComplexShape ι)

abbrev complexInduction := (functor φ).mapHomologicalComplex c
abbrev complexRestriction := (res φ).mapHomologicalComplex c

def complexUnit (P : HomologicalComplex (ModuleCat.{0} R) c) :
    P ⟶ (complexRestriction φ c).obj ((complexInduction φ c).obj P) where
  f i := unit φ (P.X i)
  comm' i j _ := (unit_naturality φ (P.d i j)).symm

def complexExtend {P : HomologicalComplex (ModuleCat.{0} R) c}
    {Q : HomologicalComplex (ModuleCat.{0} S) c}
    (f : P ⟶ (complexRestriction φ c).obj Q) :
    (complexInduction φ c).obj P ⟶ Q where
  f i := extend φ (f.f i)
  comm' i j _ := by
    apply (homEquiv φ (P.X i) (Q.X j)).injective
    change unit φ (P.X i) ≫ (res φ).map (extend φ (f.f i) ≫ Q.d i j) =
      unit φ (P.X i) ≫ (res φ).map ((functor φ).map (P.d i j) ≫ extend φ (f.f j))
    rw [Functor.map_comp,Functor.map_comp,← Category.assoc,unit_extend,
      ← Category.assoc,← unit_naturality,Category.assoc,unit_extend]
    exact f.comm i j

lemma complexUnit_extend {P : HomologicalComplex (ModuleCat.{0} R) c}
    {Q : HomologicalComplex (ModuleCat.{0} S) c}
    (f : P ⟶ (complexRestriction φ c).obj Q) :
    complexUnit φ c P ≫ (complexRestriction φ c).map (complexExtend φ c f) = f := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact unit_extend φ (f.f i)

end Tachikawa.AlgebraInduction



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] (φ : R →ₐ[k] S)

abbrev inducedRegularCochain : CochainComplex (ModuleCat.{0} (Alg k S S)) ℤ :=
  (AlgebraInduction.complexInduction (envelopingMap φ) (.up ℤ)).obj
    (regularResolution (k := k) (R := R)).cochainComplex

def regularPreAugmentation : (regularResolution (k := k) (R := R)).cochainComplex ⟶
    (AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj (regular (k := k) (R := S))) :=
  (regularResolution (k := k) (R := R)).π' ≫
    (CochainComplex.singleFunctor _ 0).map (restrictedRegularMap φ) ≫
      (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).inv.app _

def inducedRegularAugmentation : inducedRegularCochain φ ⟶
    (CochainComplex.singleFunctor _ 0).obj (regular (k := k) (R := S)) :=
  AlgebraInduction.complexExtend (envelopingMap φ) (.up ℤ) (regularPreAugmentation φ)

lemma induced_regular_square {U : ModuleCat.{0} (Alg k S S)} {N : ModuleCat.{0} (Alg k R R)}
    (v : regular (k := k) (R := S) ⟶ U)
    (b : (AlgebraInduction.res (envelopingMap φ)).obj U ⟶ N) :
    AlgebraInduction.complexUnit (envelopingMap φ) (.up ℤ)
      (regularResolution (k := k) (R := R)).cochainComplex ≫
    (AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).map
      (inducedRegularAugmentation φ ≫ (CochainComplex.singleFunctor _ 0).map v) ≫
    (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app U ≫
    (CochainComplex.singleFunctor _ 0).map b =
    (regularResolution (k := k) (R := R)).π' ≫
      (CochainComplex.singleFunctor _ 0).map
        (restrictedRegularMap φ ≫ (AlgebraInduction.res (envelopingMap φ)).map v ≫ b) := by
  rw [Functor.map_comp]
  rw [← Category.assoc,← Category.assoc,← Category.assoc]
  dsimp only [inducedRegularAugmentation]
  rw [AlgebraInduction.complexUnit_extend]
  dsimp only [regularPreAugmentation]
  simp only [Category.assoc]
  have hn : (AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).map
      ((CochainComplex.singleFunctor _ 0).map v) ≫
      (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app U =
      (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.app _ ≫
      (CochainComplex.singleFunctor _ 0).map ((AlgebraInduction.res (envelopingMap φ)).map v) :=
    (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).hom.naturality v
  rw [← Category.assoc ((AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).map
    ((CochainComplex.singleFunctor _ 0).map v)), hn]
  simp only [Iso.inv_hom_id_app_assoc,Functor.map_comp,Category.assoc]

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

lemma kProjective_chain_representative (K L : CochainComplex C ℤ) [K.IsKProjective]
    (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = a := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨b,hb⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (.up ℤ)).obj L)).surjective
      ((e.app K).hom ≫ a ≫ (e.app L).inv)
  obtain ⟨f,rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective b
  refine ⟨f,?_⟩
  have ht := congrArg (fun t => (e.app K).inv ≫ t ≫ (e.app L).hom) hb
  change e.inv.app K ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫ e.hom.app L =
    e.inv.app K ≫ (e.hom.app K ≫ a ≫ e.inv.app L) ≫ e.hom.app L at ht
  simpa [e] using ht

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R] {M : ModuleCat.{0} R}

lemma finite_resolution_cochain (P : ProjectiveResolution M)
    (hfin : ∀ n, Module.Finite R (P.complex.X n)) (i : ℤ) :
    Module.Finite R (P.cochainComplex.X i) := by
  by_cases hi : i ≤ 0
  · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hi
    let := hfin n
    exact Module.Finite.equiv (P.cochainComplexXIso (-(n:ℤ)) n).toLinearEquiv.symm
  · let := ModuleCat.isZero_iff_subsingleton.mp
      (P.cochainComplex.isZero_of_isStrictlyLE 0 i (by omega))
    infer_instance

namespace Enveloping
open scoped TensorProduct
variable {k S : Type} [Field k] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S] (φ : R →ₐ[k] S)

instance inducedRegularCochain_finite (i : ℤ) :
    Module.Finite (Alg k S S) ((inducedRegularCochain φ).X i) := by
  let P := regularResolution (k := k) (R := R)
  let : Module.Finite (Alg k R R) (P.cochainComplex.X i) :=
    finite_resolution_cochain P (fun _ => inferInstance) i
  let : FiniteDimensional k (P.cochainComplex.X i) := Module.Finite.trans (Alg k R R) _
  let : FiniteDimensional k ((AlgebraInduction.functor (envelopingMap φ)).obj
    (P.cochainComplex.X i)) := inferInstance
  change Module.Finite (Alg k S S) ((AlgebraInduction.functor (envelopingMap φ)).obj
    (P.cochainComplex.X i))
  exact Module.Finite.of_restrictScalars_finite k _ _

instance inducedRegularCochain_projective (i : ℤ) :
    Projective ((inducedRegularCochain φ).X i) := by
  let P := regularResolution (k := k) (R := R)
  let : Module.Finite (Alg k R R) (P.cochainComplex.X i) :=
    finite_resolution_cochain P (fun _ => inferInstance) i
  change Projective ((AlgebraInduction.functor (envelopingMap φ)).obj (P.cochainComplex.X i))
  infer_instance

instance inducedRegularCochain_bounded : (inducedRegularCochain φ).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (AlgebraInduction.functor (envelopingMap φ)).map_isZero
    ((regularResolution (k := k) (R := R)).cochainComplex.isZero_of_isStrictlyLE 0 i hi)

instance inducedRegularCochain_isKProjective : (inducedRegularCochain φ).IsKProjective :=
  CochainComplex.isKProjective_of_projective _ 0

end Enveloping
end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex

def negUpDown : (ComplexShape.up ℤ).Embedding (.down ℤ) where
  f i := -i
  injective_f := neg_injective
  rel h := by change _+1=_ at h; change _+1=_; omega

instance : negUpDown.IsRelIff where
  rel' := by intro i j h; change (-j)+1=(-i) at h; change i+1=j; omega

def negDownUp : (ComplexShape.down ℤ).Embedding (.up ℤ) where
  f i := -i
  injective_f := neg_injective
  rel h := by change _+1=_ at h; change _+1=_; omega

instance : negDownUp.IsRelIff where
  rel' := by intro i j h; change (-i)+1=(-j) at h; change j+1=i; omega

variable {C : Type*} [Category C] [Preadditive C]

abbrev reflectChain (K : ChainComplex C ℤ) : CochainComplex C ℤ := K.restriction negUpDown
abbrev reflectCochain (K : CochainComplex C ℤ) : ChainComplex C ℤ := K.restriction negDownUp
abbrev reflectChainMap {K L : ChainComplex C ℤ} (f : K ⟶ L) : reflectChain K ⟶ reflectChain L :=
  restrictionMap f negUpDown
abbrev reflectCochainMap {K L : CochainComplex C ℤ} (f : K ⟶ L) : reflectCochain K ⟶ reflectCochain L :=
  restrictionMap f negDownUp

lemma complex_d_transport (K : CochainComplex C ℤ) {i i' j j' : ℤ}
    (hi : i = i') (hj : j = j') :
    eqToHom (congrArg K.X hi) ≫ K.d i' j' = K.d i j ≫ eqToHom (congrArg K.X hj) := by
  subst i'; subst j'; simp

def reflectCochainIso (K : CochainComplex C ℤ) : reflectChain (reflectCochain K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => eqToIso (by change K.X (- -i) = K.X i; rw [neg_neg]))
    (by intro i j h; exact complex_d_transport K (neg_neg i) (neg_neg j))

lemma reflectCochainIso_natural {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    reflectChainMap (reflectCochainMap f) ≫ (reflectCochainIso L).hom =
      (reflectCochainIso K).hom ≫ f := by
  ext i
  change f.f (- -i) ≫ eqToHom (show L.X (- -i) = L.X i by simp) =
    eqToHom (show K.X (- -i) = K.X i by simp) ≫ f.f i
  simp

def reflectChainHomotopy {K L : ChainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (reflectChainMap f) (reflectChainMap g) where
  hom i j := h.hom (-i) (-j)
  zero i j hij := h.zero _ _ (by change ¬ (-i)+1=(-j); change ¬ j+1=i at hij; omega)
  comm i := by
    have hh := h.comm (-i)
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (-i) (-i-1) by change (-i-1)+1=(-i); omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (-i+1) (-i) by rfl)] at hh
    erw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i-1) i by change (i-1)+1=i; omega)]
    change f.f (-i) = K.d (-i) (-(i+1)) ≫ h.hom (-(i+1)) (-i) +
      h.hom (-i) (-(i-1)) ≫ L.d (-(i-1)) (-i) + g.f (-i)
    have hi : -(i+1) = -i-1 := by omega
    have hj : -(i-1) = -i+1 := by omega
    rw [hi,hj]
    exact hh

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits

lemma chainInt_exactAt_iff {R : Type} [Ring R] (P : ChainComplex (ModuleCat.{0} R) ℤ)
    (n : ℤ) : P.ExactAt n ↔ Function.Exact (P.d (n+1) n) (P.d n (n-1)) := by
  rw [P.exactAt_iff' (n+1) n (n-1) ((ComplexShape.down ℤ).prev_eq' (by rfl))
    ((ComplexShape.down ℤ).next_eq' (by change (n-1)+1=n; omega))]
  exact ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _

lemma chainNat_exactAt_iff {R : Type} [Ring R] (P : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (hn : 0 < n) : P.ExactAt n ↔ Function.Exact (P.d (n+1) n) (P.d n (n-1)) := by
  rw [P.exactAt_iff' (n+1) n (n-1) ((ComplexShape.down ℕ).prev_eq' (by rfl))
    ((ComplexShape.down ℕ).next_eq' (by change n-1+1=n; omega))]
  exact ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _

namespace Construction
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)

include hq in

lemma inducedRegularComplex_exact (n : ℕ) (hn : 4 < n) :
    Function.Exact ((Enveloping.inducedRegularComplex (inclusionB q)).d (n+1) n)
      ((Enveloping.inducedRegularComplex (inclusionB q)).d n (n-1)) := by
  let Q := restrictedLeftResolution q hq
  let F := AlgebraInduction.functor (inclusionB q)
  let e := Enveloping.inducedLeftHomotopy (inclusionB q) Q
  have hz : IsZero (((F.mapHomologicalComplex (.down ℕ)).obj Q.complex).X n) :=
    F.map_isZero (restrictedLeftResolution_above q hq n hn)
  have he : (Enveloping.leftComplex (Enveloping.inducedRegularComplex (inclusionB q))).ExactAt n :=
    (exactAt_iff_of_quasiIsoAt e.hom n).mpr (ExactAt.of_isZero hz)
  have hf := (chainNat_exactAt_iff
    (Enveloping.leftComplex (Enveloping.inducedRegularComplex (inclusionB q))) n (by omega)).mp he
  exact hf

end Construction
end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R S : Type} [Ring R] [Ring S]

lemma resolution_reflect_exact {M : ModuleCat.{0} R} (P : ProjectiveResolution M)
    (F : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] (n : ℕ) (hn : 0 < n)
    (h : Function.Exact (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).d (n+1) n)
      (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).d n (n-1))) :
    Function.Exact ((reflectCochain ((F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)).d
      ((n:ℤ)+1) n)
      ((reflectCochain ((F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)).d n ((n:ℤ)-1)) := by
  let K := (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex
  let L := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  let A : ShortComplex (ModuleCat.{0} S) :=
    ShortComplex.mk (K.d (-((n:ℤ)+1)) (-(n:ℤ))) (K.d (-(n:ℤ)) (-((n:ℤ)-1))) (by simp)
  let B : ShortComplex (ModuleCat.{0} S) :=
    ShortComplex.mk (L.d (n+1) n) (L.d n (n-1)) (by simp)
  let e₁ := F.mapIso (P.cochainComplexXIso (-((n:ℤ)+1)) (n+1) (by omega))
  let e₂ := F.mapIso (P.cochainComplexXIso (-(n:ℤ)) n)
  let e₃ := F.mapIso (P.cochainComplexXIso (-((n:ℤ)-1)) (n-1) (by omega))
  have h₁ : e₁.hom ≫ B.f = A.f ≫ e₂.hom := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [P.cochainComplex_d (-((n:ℤ)+1)) (-(n:ℤ)) (n+1) n (by omega) rfl]
    simp only [← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h₂ : e₂.hom ≫ B.g = A.g ≫ e₃.hom := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [P.cochainComplex_d (-(n:ℤ)) (-((n:ℤ)-1)) n (n-1) rfl (by omega)]
    simp only [← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : B.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact B).mpr h
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact A).mp
    (ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂).symm he)

namespace Enveloping
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] (φ : R →ₐ[k] S)
lemma inducedReflect_exact (n : ℕ) (hn : 0 < n)
    (h : Function.Exact ((inducedRegularComplex φ).d (n+1) n)
      ((inducedRegularComplex φ).d n (n-1))) :
    Function.Exact ((reflectCochain (inducedRegularCochain φ)).d ((n:ℤ)+1) n)
      ((reflectCochain (inducedRegularCochain φ)).d n ((n:ℤ)-1)) :=
  resolution_reflect_exact (regularResolution (k := k) (R := R))
    (AlgebraInduction.functor (envelopingMap φ)) n hn h
end Enveloping
namespace Construction
variable {k : Type} [Field k] [CharP k 2] (q : k) (hq : q ≠ 0)
include hq in
lemma inducedRegularCochain_reflect_exact (n : ℕ) (hn : 4 < n) :
    Function.Exact ((reflectCochain (Enveloping.inducedRegularCochain (inclusionB q))).d
      ((n:ℤ)+1) n)
      ((reflectCochain (Enveloping.inducedRegularCochain (inclusionB q))).d n ((n:ℤ)-1)) :=
  Enveloping.inducedReflect_exact (inclusionB q) n (by omega)
       (inducedRegularComplex_exact q hq n hn)
end Construction
end Tachikawa

end

end OAI
