import OAI.RingTheory.Tachikawa.StableShift

namespace OAI


noncomputable section
namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def Bimod (_φ : R →ₐ[k] S) := S
instance (φ : R →ₐ[k] S) : AddCommGroup (Bimod φ) := inferInstanceAs (AddCommGroup S)
instance (φ : R →ₐ[k] S) : Module S (Bimod φ) := inferInstanceAs (Module S S)
instance (φ : R →ₐ[k] S) : Module k (Bimod φ) := inferInstanceAs (Module k S)
instance (φ : R →ₐ[k] S) : IsScalarTower k S (Bimod φ) := inferInstanceAs (IsScalarTower k S S)
instance (φ : R →ₐ[k] S) : Module Rᵐᵒᵖ (Bimod φ) :=
  Module.compHom S φ.op.toRingHom
instance (φ : R →ₐ[k] S) : SMulCommClass S Rᵐᵒᵖ (Bimod φ) where
  smul_comm s r x := (mul_assoc s x (φ r.unop)).symm
instance (φ : R →ₐ[k] S) : IsScalarTower k Rᵐᵒᵖ (Bimod φ) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change (show S from x) * φ (algebraMap k R c) = c • (show S from x)
    rw [φ.commutes, Algebra.smul_def, Algebra.commutes]
instance (φ : R →ₐ[k] S) : Module.Projective S (Bimod φ) :=
  inferInstanceAs (Module.Projective S S)
instance (φ : R →ₐ[k] S) [FiniteDimensional k S] : FiniteDimensional k (Bimod φ) :=
  inferInstanceAs (FiniteDimensional k S)

variable (φ : R →ₐ[k] S)
abbrev functor : ModuleCat.{0} R ⥤ ModuleCat.{0} S :=
  BalancedTensor.functor (k := k) (R := R) (S := S) (M := Bimod φ)
abbrev res : ModuleCat.{0} S ⥤ ModuleCat.{0} R := ModuleCat.restrictScalars φ.toRingHom

lemma mk_one_smul (N : ModuleCat.{0} R) (s : S) (n : N) :
    BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from s) n =
      s • BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n := by
  have h := LinearMap.congr_fun ((BalancedTensor.mk (k := k) (R := R) (S := S) (N := N)).map_smul s (show Bimod φ from (1 : S))) n
  have hs : s • (show Bimod φ from (1 : S)) = (show Bimod φ from s) := mul_one s
  rw [hs] at h
  exact h

def unit (N : ModuleCat.{0} R) : N ⟶ (res φ).obj ((functor φ).obj N) := ModuleCat.ofHom (Y := (res φ).obj ((functor φ).obj N))
  { toFun := fun n => BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n
    map_add' := by intro x y; exact (BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S))).map_add x y
    map_smul' := by
      intro r n
      change BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) (r • n) =
        φ r • BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n
      rw [← BalancedTensor.balance]
      change BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 * φ r : S)) n = _
      rw [one_mul]
      exact mk_one_smul φ N (φ r) n }

def extend {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : N ⟶ (res φ).obj P) :
    (functor φ).obj N ⟶ P := ModuleCat.ofHom (BalancedTensor.lift
  { toFun := fun s =>
      { toFun := fun n => (show S from s) • (show P from f n)
        map_add' := by
          intro x y
          exact (congrArg (fun z : P => (show S from s) • z) (f.hom.map_add x y)).trans
            (smul_add (show S from s) (show P from f x) (show P from f y))
        map_smul' := by
          intro c n
          have hc := f.hom.map_smul (algebraMap k R c) n
          change (show P from f ((algebraMap k R c) • n)) = φ (algebraMap k R c) • (show P from f n) at hc
          rw [IsScalarTower.algebraMap_smul, φ.commutes, IsScalarTower.algebraMap_smul] at hc
          change (show S from s) • (show P from f (c • n)) = c • ((show S from s) • (show P from f n))
          rw [hc, smul_comm] }
    map_add' := by intro s t; ext n; exact add_smul (show S from s) (show S from t) (show P from f n)
    map_smul' := by intro s t; ext n; exact mul_smul s (show S from t) (show P from f n) }
  (by
    intro r s n
    change ((show S from s) * φ r) • f n = (show S from s) • (show P from f (r • n))
    rw [mul_smul, f.hom.map_smul]
    rfl))

@[simp] lemma extend_mk {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : N ⟶ (res φ).obj P)
    (s : Bimod φ) (n : N) : extend φ f (BalancedTensor.mk s n) = (show S from s) • (show P from f n) := rfl

lemma unit_extend {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : N ⟶ (res φ).obj P) :
    unit φ N ≫ (res φ).map (extend φ f) = f := by
  ext n
  change (1:S) • f n = f n
  exact one_smul S (f n)

lemma extend_unit {N : ModuleCat.{0} R} {P : ModuleCat.{0} S} (f : (functor φ).obj N ⟶ P) :
    extend φ (unit φ N ≫ (res φ).map f) = f := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro s n
  change (show S from s) • f.hom (BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n) =
    f.hom (BalancedTensor.mk s n)
  trans f.hom ((show S from s) • BalancedTensor.mk (k := k) (R := R) (S := S) (show Bimod φ from (1 : S)) n)
  · exact (f.hom.map_smul _ _).symm
  exact congrArg f.hom (mk_one_smul φ N (show S from s) n).symm

def homEquiv (N : ModuleCat.{0} R) (P : ModuleCat.{0} S) :
    ((functor φ).obj N ⟶ P) ≃ (N ⟶ (res φ).obj P) where
  toFun f := unit φ N ≫ (res φ).map f
  invFun := extend φ
  left_inv := extend_unit φ
  right_inv := unit_extend φ

lemma unit_naturality {N N' : ModuleCat.{0} R} (f : N ⟶ N') :
    f ≫ unit φ N' = unit φ N ≫ (res φ).map ((functor φ).map f) := by
  ext n
  rfl

instance (N : ModuleCat.{0} R) [Module.Finite R N] [Module.Projective R N] :
    Module.Projective S ((functor φ).obj N) := BalancedTensor.map_projective

def underlyingEquiv (N : ModuleCat.{0} R) :
    ((functor φ).obj N) ≃ₗ[k]
      BalancedTensor.T (k := k) (R := R) (S := S) (M := Bimod φ) (N := N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := IsScalarTower.algebraMap_smul S c
    (show BalancedTensor.T (k := k) (R := R) (S := S) (M := Bimod φ) (N := N) from x)

instance [FiniteDimensional k S] (N : ModuleCat.{0} R) [FiniteDimensional k N] :
    FiniteDimensional k ((functor φ).obj N) := Module.Finite.equiv (underlyingEquiv φ N).symm

end Tachikawa.AlgebraInduction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def regular : ModuleCat (Alg k R R) := ofBimodule (k := k) (R := R) (S := R) R

def regularUnderlyingEquiv : regular (k := k) (R := R) ≃ₗ[k] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (action (k := k) (R := R) (S := R) R (algebraMap k (Alg k R R) c)) (show R from x) = c • (show R from x)
    rw [AlgHom.commutes]
    rfl

def regularLeftEquiv : Obj (regular (k := k) (R := R)) ≃ₗ[R] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r * ((show R from x) * 1) = r * (show R from x)
    rw [mul_one]

def regularRightEquiv : Obj (regular (k := k) (R := R)) ≃ₗ[Rᵐᵒᵖ] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change 1 * ((show R from x) * r.unop) = (show R from x) * r.unop
    rw [one_mul]

instance [FiniteDimensional k R] : FiniteDimensional k (regular (k := k) (R := R)) :=
  Module.Finite.equiv regularUnderlyingEquiv.symm

variable [FiniteDimensional k R]

def regularFinite : FiniteModule k (Alg k R R) :=
  ⟨regular, Module.Finite.of_restrictScalars_finite k (Alg k R R) _⟩

def regularResolution : ProjectiveResolution (regular (k := k) (R := R)) :=
  (regularFinite (k := k) (R := R)).projectiveResolution

instance (n : ℕ) : Module.Finite (Alg k R R)
    ((regularResolution (k := k) (R := R)).complex.X n) := by
  change Module.Finite (Alg k R R) ((regularFinite (k := k) (R := R)).posTerm n)
  infer_instance

instance (n : ℕ) : Module.Projective R
    (Obj ((regularResolution (k := k) (R := R)).complex.X n)) :=
  projective_left _

instance (n : ℕ) : Module.Projective Rᵐᵒᵖ
    (Obj ((regularResolution (k := k) (R := R)).complex.X n)) :=
  projective_right _

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

def twistedRegular : ModuleCat (Alg k R R) :=
  ofBimodule (k := k) (R := R) (S := R) (AlgebraInduction.Bimod σ.toAlgHom)

def twistedUnderlying : twistedRegular σ ≃ₗ[k] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change action (k := k) (R := R) (S := R)
      (AlgebraInduction.Bimod σ.toAlgHom) (algebraMap k (Alg k R R) c) x = c • (show R from x)
    rw [AlgHom.commutes]
    rfl

def twistedLeftEquiv : Obj (twistedRegular σ) ≃ₗ[R] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change r * ((show R from x) * σ 1) = r * (show R from x)
    rw [map_one,mul_one]

def twistedRightEquiv : Obj (twistedRegular σ) ≃ₗ[Rᵐᵒᵖ] R where
  toFun := fun x => σ.symm (show R from x)
  invFun := fun x => σ x
  left_inv x := σ.apply_symm_apply x
  right_inv x := σ.symm_apply_apply x
  map_add' x y := map_add σ.symm x y
  map_smul' r x := by
    change σ.symm (1 * ((show R from x) * σ r.unop)) = σ.symm (show R from x) * r.unop
    rw [one_mul,map_mul,AlgEquiv.symm_apply_apply]

instance [FiniteDimensional k R] : FiniteDimensional k (twistedRegular σ) :=
  Module.Finite.equiv (twistedUnderlying σ).symm

instance : Module.Projective R (Obj (twistedRegular σ)) :=
  Module.Projective.of_equiv (twistedLeftEquiv σ).symm
instance : Module.Projective Rᵐᵒᵖ (Obj (twistedRegular σ)) := by
  let : Module.Projective Rᵐᵒᵖ R :=
    Module.Projective.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  exact Module.Projective.of_equiv (twistedRightEquiv σ).symm

lemma twisted_left_smul (a : R) (x : Obj (twistedRegular σ)) :
    (show R from a • x) = a * (show R from x) := by
  change a * ((show R from x) * σ 1) = _
  rw [map_one,mul_one]
lemma twisted_right_smul (a : Rᵐᵒᵖ) (x : Obj (twistedRegular σ)) :
    (show R from a • x) = (show R from x) * σ a.unop := by
  change 1 * ((show R from x) * σ a.unop) = _
  rw [one_mul]

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (σ : R ≃ₐ[k] R) (X : ModuleCat R)

def twistedEvalBilinear : Obj (twistedRegular σ) →ₗ[R] X →ₗ[k] X where
  toFun m :=
    { toFun := fun x => (twistedLeftEquiv σ m) • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => smul_comm _ c x }
  map_add' m n := by ext x; exact add_smul _ _ x
  map_smul' r m := by
    ext x
    change (twistedLeftEquiv σ (r • m)) • x = r • ((twistedLeftEquiv σ m) • x)
    rw [map_smul,smul_eq_mul,mul_smul]

variable (hσ : ∀ r : R, ∀ x : X, σ r • x = r • x)
include hσ

def twistedEval : evalObj X (twistedRegular σ) ⟶ X :=
  ModuleCat.ofHom (BalancedTensor.lift (twistedEvalBilinear σ X) (by
    intro r m x
    change (twistedLeftEquiv σ (MulOpposite.op r • m)) • x =
      twistedLeftEquiv σ m • (r • x)
    change (1 * ((show R from m) * σ r)) • x = (show R from m) • (r • x)
    rw [one_mul,mul_smul,hσ]))

lemma twistedTensor_move (r : R) (x : X) :
    BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Obj (twistedRegular σ)) (N := X) (show Obj (twistedRegular σ) from r) x =
    BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (r • x) := by
  have hb := BalancedTensor.balance (k := k) (S := R)
    (M := Obj (twistedRegular σ)) (N := X) (σ.symm r)
    (show Obj (twistedRegular σ) from (1:R)) x
  have hm : MulOpposite.op (σ.symm r) • (show Obj (twistedRegular σ) from (1:R)) =
      (show Obj (twistedRegular σ) from r) := by
    change 1 * (1 * σ (σ.symm r)) = r
    rw [σ.apply_symm_apply,one_mul,one_mul]
  rw [hm] at hb
  have hh : σ.symm r • x = r • x := by
    have := hσ (σ.symm r) x
    rw [σ.apply_symm_apply] at this
    exact this.symm
  rw [hh] at hb
  exact hb

def twistedEvalInv : X ⟶ evalObj X (twistedRegular σ) :=
  ModuleCat.ofHom
    { toFun := fun x => BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (r • x) =
          r • BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) x
        rw [← twistedTensor_move σ X hσ r x]
        have hm : r • (show Obj (twistedRegular σ) from (1:R)) =
            (show Obj (twistedRegular σ) from r) := by
          change r * (1 * σ 1) = r
          rw [map_one,mul_one,mul_one]
        conv_lhs => rw [← hm]
        rw [LinearMap.map_smul]
        rfl }

def twistedEvalIso : evalObj X (twistedRegular σ) ≅ X where
  hom := twistedEval σ X hσ
  inv := twistedEvalInv σ X hσ
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R))
      ((show R from m) • x) = BalancedTensor.mk m x
    exact (twistedTensor_move σ X hσ (show R from m) x).symm
  inv_hom_id := by
    apply ModuleCat.hom_ext
    ext x
    change (1:R) • x = x
    exact one_smul R x

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
namespace SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] (t : SymmetrizingForm (k := k) (R := R))
  (σ : R ≃ₐ[k] R)

abbrev twistFunctor := AlgebraInduction.res σ.symm.toAlgHom

def freeTwistIso (ι : Type) :
    (twistFunctor σ).obj (ModuleCat.of R (ι → R)) ≅ ModuleCat.of R (ι → R) where
  hom := ModuleCat.ofHom (X := (twistFunctor σ).obj (ModuleCat.of R (ι → R)))
    (Y := ModuleCat.of R (ι → R))
    { toFun x i := σ (x i)
      map_add' x y := by ext i; exact map_add σ _ _
      map_smul' r x := by
        ext i
        change σ (σ.symm r * x i) = r * σ (x i)
        rw [map_mul,AlgEquiv.apply_symm_apply] }
  inv := ModuleCat.ofHom (X := ModuleCat.of R (ι → R))
    (Y := (twistFunctor σ).obj (ModuleCat.of R (ι → R)))
    { toFun x i := σ.symm (x i)
      map_add' x y := by
        change (fun i => σ.symm (x i+y i)) = fun i => σ.symm (x i)+σ.symm (y i)
        funext i
        exact map_add σ.symm _ _
      map_smul' r x := by
        change (fun i => σ.symm (r * x i)) = fun i => σ.symm r * σ.symm (x i)
        funext i
        rw [map_mul] }
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (fun i => σ.symm (σ (x i))) = x
    funext i
    exact AlgEquiv.symm_apply_apply σ _
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (fun i => σ (σ.symm (x i))) = x
    funext i
    exact AlgEquiv.apply_symm_apply σ _

variable (ι : Type) [Fintype ι] [DecidableEq ι] (N : ModuleCat R)

def twistToFree (g : N →ₗ[R] (ι → R)) :
    (twistFunctor σ).obj N →ₗ[R] (ι → R) :=
  ((twistFunctor σ).map (ModuleCat.ofHom g) ≫ (freeTwistIso σ ι).hom).hom

def twistFromFree (f : (ι → R) →ₗ[R] N) :
    (ι → R) →ₗ[R] (twistFunctor σ).obj N :=
  ((freeTwistIso σ ι).inv ≫ (twistFunctor σ).map (ModuleCat.ofHom f)).hom

omit [FiniteDimensional k R] [Fintype ι] in
lemma twistFromFree_single (f : (ι → R) →ₗ[R] N) (i : ι) :
    twistFromFree σ ι N f (Pi.single i 1) = f (Pi.single i 1) := by
  change f (fun j => σ.symm ((Pi.single i (1:R) : ι → R) j)) = _
  congr 1
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

lemma freeHomDual_twist (c : k) (hc : ∀ r, t.linear (σ r) = c * t.linear r)
    (g : N →ₗ[R] (ι → R)) (f : (ι → R) →ₗ[R] N) :
    t.freeHomDual ι (twistToFree σ ι N g) (twistFromFree σ ι N f) =
      c * t.freeHomDual ι g f := by
  simp only [freeHomDual_apply,twistFromFree_single]
  change (∑ i, t.linear (σ (g (f (Pi.single i 1)) i))) = _
  simp only [hc,Finset.mul_sum]

end SymmetrizingForm
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (σ : R ≃ₐ[k] R)

abbrev twistedTensorFunctor : ModuleCat.{0} R ⥤ ModuleCat.{0} R :=
  BalancedTensor.functor (k := k) (R := R) (S := R) (M := Obj (twistedRegular σ))

lemma twistedTensor_move_general (X : ModuleCat R) (r : R) (x : X) :
    BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Obj (twistedRegular σ)) (N := X) (show Obj (twistedRegular σ) from r) x =
    BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (σ.symm r • x) := by
  have hb := BalancedTensor.balance (k := k) (S := R)
    (M := Obj (twistedRegular σ)) (N := X) (σ.symm r)
    (show Obj (twistedRegular σ) from (1:R)) x
  have hm : MulOpposite.op (σ.symm r) • (show Obj (twistedRegular σ) from (1:R)) =
      (show Obj (twistedRegular σ) from r) := by
    change 1 * (1 * σ (σ.symm r)) = r
    rw [σ.apply_symm_apply,one_mul,one_mul]
  rw [hm] at hb
  exact hb

def twistedTensorMap (X : ModuleCat R) :
    (twistedTensorFunctor σ).obj X ⟶ (SymmetrizingForm.twistFunctor σ).obj X :=
  ModuleCat.ofHom (Y := (SymmetrizingForm.twistFunctor σ).obj X)
    (BalancedTensor.lift (k := k) (R := R) (S := R)
      (M := Obj (twistedRegular σ)) (N := X)
      (P := (SymmetrizingForm.twistFunctor σ).obj X)
      { toFun := fun m =>
          { toFun := fun x => σ.symm (show R from m) • x
            map_add' := fun x y => smul_add _ x y
            map_smul' := fun c x => by
              change σ.symm (show R from m) • ((algebraMap k R c) • x) =
                σ.symm (algebraMap k R c) • (σ.symm (show R from m) • x)
              rw [σ.symm.commutes,IsScalarTower.algebraMap_smul R,
                IsScalarTower.algebraMap_smul R]
              exact smul_comm _ _ _ }
        map_add' := fun m n => by ext x; exact (congrArg (fun r => r • x) (map_add σ.symm _ _)).trans (add_smul _ _ _)
        map_smul' := fun r m => by
          ext x
          change σ.symm (show R from r • m) • x = σ.symm r • (σ.symm (show R from m) • x)
          rw [twisted_left_smul,map_mul,mul_smul] }
      (by
        intro r m x
        change σ.symm (show R from MulOpposite.op r • m) • x = σ.symm (show R from m) • (r • x)
        rw [twisted_right_smul,map_mul,σ.symm_apply_apply,mul_smul]
        rfl))

def twistedTensorInv (X : ModuleCat R) :
    (SymmetrizingForm.twistFunctor σ).obj X ⟶ (twistedTensorFunctor σ).obj X :=
  ModuleCat.ofHom (X := (SymmetrizingForm.twistFunctor σ).obj X)
    { toFun := fun x => BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (show X from x)
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (σ.symm r • (show X from x)) =
          r • BalancedTensor.mk (show Obj (twistedRegular σ) from (1:R)) (show X from x)
        rw [← twistedTensor_move_general]
        have hm : r • (show Obj (twistedRegular σ) from (1:R)) =
            (show Obj (twistedRegular σ) from r) := by
          change r * (1 * σ 1) = r
          rw [map_one,mul_one,mul_one]
        conv_lhs => rw [← hm]
        rw [LinearMap.map_smul]
        rfl }

def twistedTensorIso (X : ModuleCat R) :
    (twistedTensorFunctor σ).obj X ≅ (SymmetrizingForm.twistFunctor σ).obj X where
  hom := twistedTensorMap σ X
  inv := twistedTensorInv σ X
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext (k := k) (R := R) (S := R)
    intro m x
    change BalancedTensor.mk (k := k) (R := R) (S := R) (N := X)
      (show Obj (twistedRegular σ) from (1:R))
      (σ.symm (show R from m) • x) = BalancedTensor.mk m x
    exact (twistedTensor_move_general σ X (show R from m) x).symm
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change σ.symm (1:R) • (show X from x) = x
    rw [map_one,one_smul]

def twistedTensorNatIso : twistedTensorFunctor σ ≅ SymmetrizingForm.twistFunctor σ :=
  NatIso.ofComponents (twistedTensorIso σ) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change σ.symm (show R from m) • f x = f (σ.symm (show R from m) • x)
    exact (f.hom.map_smul _ _).symm)

end Tachikawa.Enveloping

end

end OAI
