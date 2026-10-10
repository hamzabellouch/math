import OAI.RingTheory.Tachikawa.Bimodule

namespace OAI


noncomputable section
namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R)

def rightEvaluation : ModuleCat Rᵐᵒᵖ ⥤ ModuleCat k where
  obj M := ModuleCat.of k (BalancedTensor.T (k := k) (R := R) (S := k) (M := M) (N := X))
  map f := ModuleCat.ofHom (BalancedTensor.mapLeft (k := k) (R := R) (S := k) (N := X)
    (f.hom.restrictScalars k) f.hom.map_smul)
  map_id M := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl

instance : (rightEvaluation (k := k) X).Additive where
  map_add {M N f g} := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (k := k) (R := R) (S := k) ((f m) + (g m)) x = _
    exact congrArg (fun h : X →ₗ[k] _ => h x) ((BalancedTensor.mk (k := k) (R := R)
      (S := k) (M := N) (N := X)).map_add (f m) (g m))

def rightObjEquiv (M : ModuleCat (Alg k S R)) :
    Obj M ≃ₗ[Rᵐᵒᵖ] (rightFunctor.obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rightEvaluationEquiv (M : ModuleCat (Alg k S R)) :
    evalType X M ≃ₗ[k] (rightEvaluation (k := k) X).obj (rightFunctor.obj M) := by
  let e := (rightObjEquiv (k := k) M).restrictScalars k
  let f := BalancedTensor.mapLeft (k := k) (R := R) (S := k) (N := X)
    e.toLinearMap (rightObjEquiv (k := k) M).map_smul
  let g := BalancedTensor.mapLeft (k := k) (R := R) (S := k) (N := X)
    e.symm.toLinearMap (rightObjEquiv (k := k) M).symm.map_smul
  let t : BalancedTensor.T (k := k) (R := R) (S := k) (M := Obj M) (N := X) ≃ₗ[k]
      (rightEvaluation (k := k) X).obj (rightFunctor.obj M) :=
    { f with
      invFun := g
      left_inv x := by
        change g (f x) = x
        induction x using BalancedTensor.induction_on with
        | h0 => simp only [map_zero]
        | ht m x => rfl
        | ha x y hx hy => simp only [map_add, hx, hy]
      right_inv x := by
        change f (g x) = x
        induction x using BalancedTensor.induction_on with
        | h0 => simp only [map_zero]
        | ht m x => rfl
        | ha x y hx hy => simp only [map_add, hx, hy] }
  exact BalancedTensor.restrictEquiv.trans t

@[simp] lemma rightEvaluationEquiv_mk (M : ModuleCat (Alg k S R)) (m : Obj M) (x : X) :
    rightEvaluationEquiv (k := k) X M (BalancedTensor.mk m x) =
      BalancedTensor.mk (k := k) (R := R) (S := k) (N := X)
        (show rightFunctor.obj M from m) x := rfl

def evalScalarEquiv (M : ModuleCat (Alg k S R)) :
    (ModuleCat.restrictScalars (algebraMap k S)).obj (evalObj X M) ≃ₗ[k] evalType X M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (algebraMap k S c) • (show evalType X M from x) = c • (show evalType X M from x)
    exact IsScalarTower.algebraMap_smul S c (show evalType X M from x)

def rightEvaluationComparisonIso (M : ModuleCat (Alg k S R)) :
    (ModuleCat.restrictScalars (algebraMap k S)).obj (evalObj X M) ≅
      (rightEvaluation (k := k) X).obj (rightFunctor.obj M) :=
  LinearEquiv.toModuleIso ((evalScalarEquiv X M).trans (rightEvaluationEquiv (k := k) X M))

def rightEvaluationComparison :
    evaluation (k := k) (S := S) X ⋙ ModuleCat.restrictScalars (algebraMap k S) ≅
      rightFunctor (k := k) (R := S) (S := R) ⋙ rightEvaluation (k := k) X :=
  NatIso.ofComponents (rightEvaluationComparisonIso X) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change rightEvaluationEquiv X N
      (BalancedTensor.mapLeft (k := k) (R := R) (S := S) (N := X)
        (leftMap f) (fun r m => (rightMap f).map_smul r m) (show evalType X M from x)) =
      ((rightEvaluation (k := k) X).map (rightFunctor.map f)).hom
        (rightEvaluationEquiv X M x)
    induction (show evalType X M from x) using BalancedTensor.induction_on with
    | h0 => simp only [map_zero]
    | ht m y => rfl
    | ha x y hx hy => simp only [map_add, hx, hy])

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (X : ModuleCat R)

def regularEvalBilinear : Obj (regular (k := k) (R := R)) →ₗ[R] X →ₗ[k] X where
  toFun m :=
    { toFun := fun x => regularLeftEquiv m • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => smul_comm _ c x }
  map_add' m n := by ext x; exact add_smul _ _ x
  map_smul' r m := by
    ext x
    change (regularLeftEquiv (r • m)) • x = r • (regularLeftEquiv m • x)
    rw [map_smul,smul_eq_mul,mul_smul]

def regularEval : evalObj X (regular (k := k) (R := R)) ⟶ X :=
  ModuleCat.ofHom (BalancedTensor.lift (regularEvalBilinear X) (by
    intro r m x
    change (1 * ((show R from m) * r)) • x = (show R from m) • (r • x)
    rw [one_mul,mul_smul]))

lemma regularTensor_move (r : R) (x : X) :
    BalancedTensor.mk (k := k) (R := R) (S := R)
      (M := Obj (regular (k := k) (R := R))) (N := X)
      (show Obj (regular (k := k) (R := R)) from r) x =
    BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) (r • x) := by
  have hb := BalancedTensor.balance (k := k) (S := R)
    (M := Obj (regular (k := k) (R := R))) (N := X) r
    (show Obj (regular (k := k) (R := R)) from (1:R)) x
  have hm : MulOpposite.op r • (show Obj (regular (k := k) (R := R)) from (1:R)) =
      (show Obj (regular (k := k) (R := R)) from r) := by
    change 1 * (1 * r) = r
    rw [one_mul,one_mul]
  rw [hm] at hb
  exact hb

def regularEvalInv : X ⟶ evalObj X (regular (k := k) (R := R)) :=
  ModuleCat.ofHom
    { toFun := fun x => BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        change BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) (r • x) =
          r • BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R)) x
        rw [← regularTensor_move X r x]
        have hm : r • (show Obj (regular (k := k) (R := R)) from (1:R)) =
            (show Obj (regular (k := k) (R := R)) from r) := by
          change r * (1 * 1) = r
          rw [one_mul,mul_one]
        conv_lhs => rw [← hm]
        rw [LinearMap.map_smul]
        rfl }

def regularEvalIso : evalObj X (regular (k := k) (R := R)) ≅ X where
  hom := regularEval X
  inv := regularEvalInv X
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (show Obj (regular (k := k) (R := R)) from (1:R))
      ((show R from m) • x) = BalancedTensor.mk m x
    exact (regularTensor_move X (show R from m) x).symm
  inv_hom_id := by
    apply ModuleCat.hom_ext
    ext x
    change (1:R) • x = x
    exact one_smul R x

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

abbrev leftIndObj (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) : ModuleCat (Alg k S U) :=
  ofBimodule (k := k) (R := S) (S := U)
    (BalancedTensor.T (k := k) (R := R) (S := S) (M := AlgebraInduction.Bimod φ) (N := Obj M))

def leftIndMap (φ : R →ₐ[k] S) {M N : ModuleCat (Alg k R U)} (f : M ⟶ N) :
    leftIndObj φ M ⟶ leftIndObj φ N :=
  ofBimoduleHom (BalancedTensor.mapRight (k := k) (S := S) (M := AlgebraInduction.Bimod φ) (leftMap f))
    (by
      intro u x
      induction x using BalancedTensor.induction_on with
      | h0 => simp only [smul_zero, map_zero]
      | ht s m =>
        change BalancedTensor.mk (k := k) (R := R) (S := S) s (show Obj N from f (u • m)) =
          BalancedTensor.mk s (u • (show Obj N from f m))
        exact congrArg (BalancedTensor.mk s) ((rightMap f).map_smul u m)
      | ha x y hx hy => simp only [smul_add, map_add, hx, hy])

def leftIndFunctor (φ : R →ₐ[k] S) : ModuleCat (Alg k R U) ⥤ ModuleCat (Alg k S U) where
  obj := leftIndObj φ
  map := leftIndMap φ
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | h0 => rfl
    | ht s m => rfl
    | ha x y hx hy =>
      exact ((leftIndMap φ (𝟙 M)).hom.map_add x y).trans
        ((congrArg₂ (fun x y => x+y) hx hy).trans ((ModuleCat.Hom.hom (𝟙 (leftIndObj φ M))).map_add x y).symm)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | h0 => rfl
    | ht s m => rfl
    | ha x y hx hy =>
      exact ((leftIndMap φ (f ≫ g)).hom.map_add x y).trans
        ((congrArg₂ (fun x y => x+y) hx hy).trans ((leftIndMap φ f ≫ leftIndMap φ g).hom.map_add x y).symm)

instance (φ : R →ₐ[k] S) : (leftIndFunctor (U := U) φ).Additive where
  map_add {_X _Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (leftIndMap φ (f + g)).hom x = ((leftIndMap φ f) + (leftIndMap φ g)).hom x
    induction x using BalancedTensor.induction_on (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj _X) with
    | h0 => rfl
    | ht s m =>
      exact (BalancedTensor.mk (k := k) (R := R) (S := S)
        (M := AlgebraInduction.Bimod φ) (N := Obj _Y) s).map_add (f m) (g m)
    | ha x y hx hy =>
      exact ((leftIndMap φ (f+g)).hom.map_add x y).trans
        ((congrArg₂ (fun x y => x+y) hx hy).trans ((leftIndMap φ f + leftIndMap φ g).hom.map_add x y).symm)

def leftIndUnderlyingIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    (leftFunctor (k := k) (R := S) (S := U)).obj (leftIndObj φ M) ≅
      (AlgebraInduction.functor φ).obj ((leftFunctor (k := k) (R := R) (S := U)).obj M) :=
  LinearEquiv.toModuleIso
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' s x := by
      change (action (k := k) (R := S) (S := U)
        (BalancedTensor.T (k := k) (R := R) (S := S)
          (M := AlgebraInduction.Bimod φ) (N := Obj M)) (s ⊗ₜ[k] (1:Uᵐᵒᵖ))) x = _
      change s • ((1:Uᵐᵒᵖ) • (show BalancedTensor.T (k := k) (R := R) (S := S)
        (M := AlgebraInduction.Bimod φ) (N := Obj M) from x)) = _
      rw [one_smul]
      rfl }

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k U R : Type} [Field k] [Ring U] [Ring R] [Algebra k U] [Algebra k R]

def RightObj (M : ModuleCat (Alg k U R)) := (rightFunctor (k := k) (R := U) (S := R)).obj M
instance (M : ModuleCat (Alg k U R)) : AddCommGroup (RightObj M) :=
  inferInstanceAs (AddCommGroup ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance (M : ModuleCat (Alg k U R)) : Module Rᵐᵒᵖ (RightObj M) :=
  inferInstanceAs (Module Rᵐᵒᵖ ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance (M : ModuleCat (Alg k U R)) : Module k (RightObj M) :=
  inferInstanceAs (Module k ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance (M : ModuleCat (Alg k U R)) : IsScalarTower k Rᵐᵒᵖ (RightObj M) :=
  inferInstanceAs (IsScalarTower k Rᵐᵒᵖ ((rightFunctor (k := k) (R := U) (S := R)).obj M))
instance (M : ModuleCat (Alg k U R)) : Module U (RightObj M) :=
  inferInstanceAs (Module U (Obj M))
instance (M : ModuleCat (Alg k U R)) : SMulCommClass U Rᵐᵒᵖ (RightObj M) :=
  inferInstanceAs (SMulCommClass U Rᵐᵒᵖ (Obj M))
instance (M : ModuleCat (Alg k U R)) : IsScalarTower k U (RightObj M) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change (algebraMap k U c) • (show Obj M from x) =
      (algebraMap k Rᵐᵒᵖ c) • (show Obj M from x)
    rw [IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]

def rightObjMap {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) : RightObj M →ₗ[Rᵐᵒᵖ] RightObj N :=
  rightMap f

def rightObjLeftMap {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) : RightObj M →ₗ[U] RightObj N :=
  leftMap f

end Tachikawa.Enveloping



namespace Tachikawa.BalancedTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U M N : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N] [Module U N]
  [IsScalarTower k R N] [IsScalarTower k U N] [SMulCommClass U R N]

def commutingAction : U →+* Module.End S (T (k := k) (R := R) (S := S) (M := M) (N := N)) where
  toFun u := mapRight ((Algebra.lsmul k R N) u)
  map_one' := by
    change mapRight (k := k) (S := S) (M := M) ((Algebra.lsmul k R N) 1) = LinearMap.id
    rw [map_one]
    exact mapRight_id
  map_mul' u v := by
    change mapRight (k := k) (S := S) (M := M) ((Algebra.lsmul k R N) (u*v)) = _
    rw [map_mul]
    exact mapRight_comp _ _
  map_zero' := by rw [map_zero]; exact mapRight_zero
  map_add' u v := by rw [map_add]; exact mapRight_add _ _

end Tachikawa.BalancedTensor



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

def RightIndType (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :=
  BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)

instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : AddCommGroup (RightIndType φ M) :=
  inferInstanceAs (AddCommGroup (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : Module k (RightIndType φ M) :=
  inferInstanceAs (Module k (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : Module Sᵐᵒᵖ (RightIndType φ M) :=
  inferInstanceAs (Module Sᵐᵒᵖ (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : IsScalarTower k Sᵐᵒᵖ (RightIndType φ M) :=
  inferInstanceAs (IsScalarTower k Sᵐᵒᵖ (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)))
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : Module U (RightIndType φ M) :=
  show Module U (BalancedTensor.T (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)) from
  Module.compHom _ (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M))
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : IsScalarTower k U (RightIndType φ M) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
    | h0 => exact (smul_zero (algebraMap k U c) : (algebraMap k U c) • (0 : RightIndType φ M) = 0).trans (smul_zero c).symm
    | ht s m =>
      change BalancedTensor.mk s ((algebraMap k U c) • m) = c • BalancedTensor.mk s m
      rw [IsScalarTower.algebraMap_smul]
      exact (BalancedTensor.mk s).map_smul c m
    | ha x y hx hy =>
      change ((algebraMap k U c) • (show RightIndType φ M from x+y)) = c • (show RightIndType φ M from x+y)
      exact (smul_add (algebraMap k U c) (show RightIndType φ M from x) (show RightIndType φ M from y)).trans
        ((congrArg₂ (fun x y : RightIndType φ M => x+y) hx hy).trans
          (smul_add c (show RightIndType φ M from x) (show RightIndType φ M from y)).symm)
instance (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : SMulCommClass U Sᵐᵒᵖ (RightIndType φ M) where
  smul_comm u s x := by
    change (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) u) (s • x) =
      s • (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) u) x
    exact (BalancedTensor.commutingAction (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (U := U) (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) u).map_smul s x

abbrev rightIndObj (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) : ModuleCat (Alg k U S) :=
  ofBimodule (k := k) (R := U) (S := S) (RightIndType φ M)

abbrev rightEnvelopingMap (φ : R →ₐ[k] S) : Alg k U R →ₐ[k] Alg k U S :=
  Algebra.TensorProduct.map (AlgHom.id k U) φ.op




lemma rightInd_smul_mk (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) (u : U)
    (s : AlgebraInduction.Bimod φ.op) (m : RightObj M) :
    u • (show RightIndType φ M from BalancedTensor.mk s m) =
      (show RightIndType φ M from BalancedTensor.mk s (u • m)) := rfl

lemma rightInd_smul_tmul (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R))
    (u : U) (s : Sᵐᵒᵖ) (x : RightIndType φ M) :
    (u ⊗ₜ[k] s) • (show rightIndObj φ M from x) = (show RightIndType φ M from u • s • x) := rfl

def rightIndUnit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj (rightIndObj φ M) :=
  ModuleCat.ofHom (X := M)
    (Y := (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj (rightIndObj φ M))
  { toFun := fun m => BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ)) (show RightObj M from m)
    map_add' := by intro m n; exact (BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (N := RightObj M) (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ))).map_add m n
    map_smul' a m := by
      let t : RightObj M →ₗ[k] RightIndType φ M := BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
        (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ))
      change t (show RightObj M from a • m) =
        (action (k := k) (R := U) (S := S) (RightIndType φ M) (rightEnvelopingMap φ a)) (t m)
      induction a using TensorProduct.inductionOn with
      | tmul u r =>
        change t (show RightObj M from (u ⊗ₜ[k] r) • m) = u • (φ.op r • t m)
        rw [smul_comm u (φ.op r)]
        change t (show RightObj M from (u ⊗ₜ[k] r) • m) = φ.op r • t (u • (show RightObj M from m))
        trans t (r • u • (show RightObj M from m))
        · apply congrArg t
          exact (tmul_smul M u r m).trans (smul_comm u r (show RightObj M from m))
        exact (AlgebraInduction.unit φ.op (ModuleCat.of Rᵐᵒᵖ (RightObj M))).hom.map_smul r (u • (show RightObj M from m))
      | add a b ha hb =>
        rw [map_add, map_add]
        exact (congrArg (fun x : M => t (show RightObj M from x)) (add_smul a b m)).trans
          ((t.map_add _ _).trans (congrArg₂ (fun x y => x+y) ha hb)) }




def rightIndMapLinear (φ : R →ₐ[k] S) {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) :
    RightIndType φ M →ₗ[U] RightIndType φ N where
  toFun := BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ) (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)
  map_add' := (BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)).map_add
  map_smul' u x := by
    induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
    | h0 => rfl
    | ht s m =>
      change BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ) s (show RightObj N from f (u • m)) =
        BalancedTensor.mk s (u • (show RightObj N from f m))
      exact congrArg (BalancedTensor.mk s) ((rightObjLeftMap f).map_smul u m)
    | ha x y hx hy =>
      let g : RightIndType φ M →ₗ[k] RightIndType φ N :=
        (BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ)
          (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)).restrictScalars k
      change g (u • (show RightIndType φ M from x+y)) = u • g (x+y)
      exact (congrArg g (smul_add u (show RightIndType φ M from x) (show RightIndType φ M from y))).trans
        ((g.map_add _ _).trans ((congrArg₂ (fun x y : RightIndType φ N => x+y) hx hy).trans
          ((smul_add u (g x) (g y)).symm.trans
            (congrArg (fun z : RightIndType φ N => u • z) (g.map_add x y).symm))))

def rightIndMap (φ : R →ₐ[k] S) {M N : ModuleCat (Alg k U R)} (f : M ⟶ N) :
    rightIndObj φ M ⟶ rightIndObj φ N :=
  ofBimoduleHom (rightIndMapLinear φ f) (by
    intro s x
    exact (BalancedTensor.mapRight (k := k) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (rightObjMap f)).map_smul s x)

lemma rightInd_hom_ext (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    {f g : rightIndObj φ M ⟶ N}
    (h : ∀ (s : AlgebraInduction.Bimod φ.op) (m : RightObj M),
      f (BalancedTensor.mk s m) = g (BalancedTensor.mk s m)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
  | h0 => exact f.hom.map_zero.trans g.hom.map_zero.symm
  | ht s m => exact h s m
  | ha x y hx hy =>
    exact (f.hom.map_add x y).trans
      ((congrArg₂ (fun x y => x+y) hx hy).trans (g.hom.map_add x y).symm)

def rightIndFunctor (φ : R →ₐ[k] S) : ModuleCat (Alg k U R) ⥤ ModuleCat (Alg k U S) where
  obj := rightIndObj φ
  map := rightIndMap φ
  map_id M := by apply rightInd_hom_ext φ; intro s m; rfl
  map_comp f g := by apply rightInd_hom_ext φ; intro s m; rfl

instance (φ : R →ₐ[k] S) : (rightIndFunctor (U := U) φ).Additive where
  map_add {_X _Y f g} := by
    apply rightInd_hom_ext φ
    intro s m
    exact (BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj _Y) s).map_add (f m) (g m)

def rightIndUnderlyingIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    (rightFunctor (k := k) (R := U) (S := S)).obj (rightIndObj φ M) ≅
      (AlgebraInduction.functor φ.op).obj ((rightFunctor (k := k) (R := U) (S := R)).obj M) :=
  LinearEquiv.toModuleIso
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' s x := by
      change (1:U) • (s • (show RightIndType φ M from x)) = s • (show RightIndType φ M from x)
      rw [one_smul] }

def rightIndUnderlyingComparison (φ : R →ₐ[k] S) :
    rightIndFunctor (U := U) φ ⋙ rightFunctor ≅ rightFunctor ⋙ AlgebraInduction.functor φ.op :=
  NatIso.ofComponents (rightIndUnderlyingIso φ) (by intro M N f; ext x; rfl)




def rightIndResMap (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    ModuleCat.of Rᵐᵒᵖ (RightObj M) ⟶ (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ (RightObj N)) :=
  ModuleCat.ofHom (X := ModuleCat.of Rᵐᵒᵖ (RightObj M))
    (Y := (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ (RightObj N)))
  { toFun := fun m => (show RightObj N from f m)
    map_add' := f.hom.map_add
    map_smul' r m := by
      have h := f.hom.map_smul ((1:U) ⊗ₜ[k] r) m
      change (show N from f (((1:U) ⊗ₜ[k] r) • (show M from m))) =
        (rightEnvelopingMap φ ((1:U) ⊗ₜ[k] r)) • (show N from f m) at h
      exact h }

lemma rightIndResMap_left (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) (u : U) (m : RightObj M) :
    (show RightObj N from f (u • m)) = u • (show RightObj N from f m) := by
  have h := f.hom.map_smul (u ⊗ₜ[k] (1:Rᵐᵒᵖ)) m
  change (show N from f ((u ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (show M from m))) =
    rightEnvelopingMap φ (u ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (show N from f m) at h
  change (show N from f ((u ⊗ₜ[k] (1:Rᵐᵒᵖ)) • (show M from m))) =
    (u ⊗ₜ[k] (1:Sᵐᵒᵖ)) • (show N from f m)
  simpa only [rightEnvelopingMap, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using h

def rightIndExtendRightLinear (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    RightIndType φ M →ₗ[Sᵐᵒᵖ] RightObj N :=
  (AlgebraInduction.extend φ.op (rightIndResMap φ f)).hom

lemma rightIndExtendRightLinear_left (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) (u : U) (x) :
    rightIndExtendRightLinear φ f (u • x) = u • rightIndExtendRightLinear φ f x := by
  induction x using BalancedTensor.induction_on (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
    (M := AlgebraInduction.Bimod φ.op) (N := RightObj M) with
  | h0 =>
    exact (congrArg (rightIndExtendRightLinear φ f) (smul_zero u)).trans
      ((rightIndExtendRightLinear φ f).map_zero.trans (smul_zero u).symm)
  | ht s m =>
    change (show Sᵐᵒᵖ from s) • (show RightObj N from f (u • m)) =
      u • ((show Sᵐᵒᵖ from s) • (show RightObj N from f m))
    rw [rightIndResMap_left φ f]
    exact (smul_comm u (show Sᵐᵒᵖ from s) (show RightObj N from f m)).symm
  | ha x y hx hy =>
    change rightIndExtendRightLinear φ f (u • (show RightIndType φ M from x+y)) = _
    exact (congrArg (rightIndExtendRightLinear φ f)
      (smul_add u (show RightIndType φ M from x) (show RightIndType φ M from y))).trans
      (((rightIndExtendRightLinear φ f).map_add _ _).trans
        ((congrArg₂ (fun x y : RightObj N => x+y) hx hy).trans
          ((smul_add u _ _).symm.trans (congrArg (fun x : RightObj N => u • x)
            ((rightIndExtendRightLinear φ f).map_add x y).symm))))

def rightIndExtendLinear (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    RightIndType φ M →ₗ[U] RightObj N where
  toFun := rightIndExtendRightLinear φ f
  map_add' := (rightIndExtendRightLinear φ f).map_add
  map_smul' := rightIndExtendRightLinear_left φ f

def rightReassembleIso (M : ModuleCat (Alg k U S)) :
    ofBimodule (k := k) (R := U) (S := S) (RightObj M) ≅ M :=
  LinearEquiv.toModuleIso (show (ofBimodule (k := k) (R := U) (S := S) (RightObj M)) ≃ₗ[Alg k U S] M from
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' a x := by
      change (show M from (action (k := k) (R := U) (S := S) (RightObj M) a) x) = a • (show M from x)
      induction a using TensorProduct.inductionOn with
      | tmul r s => exact (tmul_smul M r s x).symm
      | add a b ha hb =>
        rw [map_add, add_smul]
        exact congrArg₂ (fun x y : M => x+y) ha hb })

def rightIndExtend (φ : R →ₐ[k] S) {M : ModuleCat (Alg k U R)} {N : ModuleCat (Alg k U S)}
    (f : M ⟶ (AlgebraInduction.res (rightEnvelopingMap (U := U) φ)).obj N) :
    rightIndObj φ M ⟶ N :=
  ofBimoduleHom (rightIndExtendLinear φ f)
    (fun s x => (rightIndExtendRightLinear φ f).map_smul s x) ≫ (rightReassembleIso N).hom




def rightIndComparisonHom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M ⟶ rightIndObj φ M :=
  AlgebraInduction.extend (k := k) (R := Alg k U R) (S := Alg k U S)
    (N := M) (P := rightIndObj φ M) (rightEnvelopingMap φ) (rightIndUnit φ M)

def rightIndComparisonInv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    rightIndObj φ M ⟶ (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M :=
  rightIndExtend (k := k) (R := R) (S := S) (U := U) φ (M := M)
    (N := (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M)
    (AlgebraInduction.unit (k := k) (R := Alg k U R) (S := Alg k U S)
      (rightEnvelopingMap (U := U) φ) M)

lemma rightIndComparison_inv_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) (m : M) :
    rightIndComparisonInv φ M (rightIndUnit φ M m) =
      AlgebraInduction.unit (k := k) (R := Alg k U R) (S := Alg k U S) (rightEnvelopingMap φ) M m := by
  change (1:Sᵐᵒᵖ) • (show RightObj ((AlgebraInduction.functor (k := k) (rightEnvelopingMap (U := U) φ)).obj M) from
    AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m) = _
  exact one_smul _ _

lemma rightIndComparison_hom_unit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) (m : M) :
    rightIndComparisonHom φ M (AlgebraInduction.unit (k := k) (R := Alg k U R)
      (S := Alg k U S) (rightEnvelopingMap φ) M m) = rightIndUnit φ M m := by
  change (1:Alg k U S) • (show rightIndObj φ M from rightIndUnit φ M m) = _
  exact one_smul _ _

lemma rightIndComparison_hom_inv (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    rightIndComparisonHom φ M ≫ rightIndComparisonInv φ M = 𝟙 _ := by
  apply (AlgebraInduction.homEquiv (k := k) (R := Alg k U R) (S := Alg k U S)
    (rightEnvelopingMap φ) M _).injective
  ext m
  change rightIndComparisonInv φ M (rightIndComparisonHom φ M
    (AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m)) =
      AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m
  rw [rightIndComparison_hom_unit, rightIndComparison_inv_unit]

lemma rightIndComparison_inv_hom (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    rightIndComparisonInv φ M ≫ rightIndComparisonHom φ M = 𝟙 _ := by
  apply rightInd_hom_ext φ
  intro s m
  have h := (rightObjMap (rightIndComparisonHom φ M)).map_smul (show Sᵐᵒᵖ from s)
    (show RightObj ((AlgebraInduction.functor (k := k) (rightEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m)
  change rightIndComparisonHom φ M ((show Sᵐᵒᵖ from s) •
    (show RightObj ((AlgebraInduction.functor (k := k) (rightEnvelopingMap (U := U) φ)).obj M) from
      AlgebraInduction.unit (k := k) (rightEnvelopingMap (U := U) φ) M m)) = _
  apply h.trans
  apply Eq.trans (congrArg (fun x : RightObj (rightIndObj φ M) => (show Sᵐᵒᵖ from s) • x)
    (rightIndComparison_hom_unit φ M m))
  change (1:U) • ((show Sᵐᵒᵖ from s) •
    (show RightIndType φ M from BalancedTensor.mk (k := k) (R := Rᵐᵒᵖ) (S := Sᵐᵒᵖ)
      (M := AlgebraInduction.Bimod φ.op) (N := RightObj M)
      (show AlgebraInduction.Bimod φ.op from (1:Sᵐᵒᵖ)) m)) = BalancedTensor.mk s m
  rw [one_smul]
  exact (AlgebraInduction.mk_one_smul φ.op (ModuleCat.of Rᵐᵒᵖ (RightObj M)) (show Sᵐᵒᵖ from s) m).symm

def rightIndComparisonIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    (AlgebraInduction.functor (rightEnvelopingMap (U := U) φ)).obj M ≅ rightIndObj φ M where
  hom := rightIndComparisonHom φ M
  inv := rightIndComparisonInv φ M
  hom_inv_id := rightIndComparison_hom_inv φ M
  inv_hom_id := rightIndComparison_inv_hom φ M

def rightIndComparison (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (rightEnvelopingMap (U := U) φ) ≅ rightIndFunctor φ :=
  NatIso.ofComponents (rightIndComparisonIso φ) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro a m
    change (show Alg k U S from a) • (show rightIndObj φ N from rightIndUnit φ N (f m)) =
      rightIndMap φ f ((show Alg k U S from a) • (show rightIndObj φ M from rightIndUnit φ M m))
    exact ((rightIndMap φ f).hom.map_smul (show Alg k U S from a)
      (show rightIndObj φ M from rightIndUnit φ M m)).symm)

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
variable {R : Type} [Ring R]

lemma exact_prodMap {A B C D E F : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    [Module R A] [Module R B] [Module R C] [Module R D] [Module R E] [Module R F]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (f' : D →ₗ[R] E) (g' : E →ₗ[R] F)
    (h : Function.Exact f g) (h' : Function.Exact f' g') :
    Function.Exact (f.prodMap f') (g.prodMap g') := by
  rintro ⟨b,e⟩
  change (g b,g' e) = (0,0) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hb,he⟩
    obtain ⟨a,rfl⟩ := (h b).mp hb
    obtain ⟨d,rfl⟩ := (h' e).mp he
    exact ⟨(a,d),rfl⟩
  · rintro ⟨⟨a,d⟩,hh⟩
    cases hh
    exact ⟨h.apply_apply_eq_zero a,h'.apply_apply_eq_zero d⟩

namespace ProjectiveResolution
variable {M N : ModuleCat.{0} R} (P : CategoryTheory.ProjectiveResolution M)
    (Q : CategoryTheory.ProjectiveResolution N)

lemma function_exact_succ (n : ℕ) :
    Function.Exact (P.complex.d (n+2) (n+1)) (P.complex.d (n+1) n) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ n)

lemma function_exact_zero : Function.Exact (P.complex.d 1 0) (P.π.f 0) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀

def prod : CategoryTheory.ProjectiveResolution (ModuleCat.of R (M × N)) :=
  resolutionOfExact _ (fun n => ModuleCat.of R (P.complex.X n × Q.complex.X n))
    (fun n => ModuleCat.ofHom ((P.complex.d (n+1) n).hom.prodMap (Q.complex.d (n+1) n).hom))
    (ModuleCat.ofHom ((P.π.f 0).hom.prodMap (Q.π.f 0).hom))
    (fun n => exact_prodMap _ _ _ _ (function_exact_succ P n) (function_exact_succ Q n))
    (exact_prodMap _ _ _ _ (function_exact_zero P) (function_exact_zero Q))
    (by
      rintro ⟨m,n⟩
      obtain ⟨p,hp⟩ := (ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance m
      obtain ⟨q,hq⟩ := (ModuleCat.epi_iff_surjective (Q.π.f 0)).mp inferInstance n
      exact ⟨(p,q),Prod.ext hp hq⟩)
    (fun n => by infer_instance)

end ProjectiveResolution
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace ProjectiveResolution
variable (M : ModuleCat.{0} R) [Projective M]

def simpleTerm : ℕ → ModuleCat R
  | 0 => M
  | _+1 => ModuleCat.of R PUnit

def simpleAug : simpleTerm M 0 ⟶ M := 𝟙 M

def simpleSelf : CategoryTheory.ProjectiveResolution M :=
  resolutionOfExact M (simpleTerm M) (fun _ => 0) (simpleAug M)
    (by
      intro n x
      refine ⟨fun _ => ⟨PUnit.unit, ?_⟩, fun _ => rfl⟩
      change (0 : PUnit) = x
      exact Subsingleton.elim _ _)
    (by intro x; exact ⟨fun hx => ⟨PUnit.unit,hx.symm⟩,fun ⟨_,hx⟩ => hx.symm⟩)
    (Function.surjective_id)
    (by intro n; cases n <;> dsimp [simpleTerm] <;> infer_instance)

lemma simpleSelf_above (n : ℕ) (hn : 0 < n) : IsZero ((simpleSelf M).complex.X n) := by
  cases n with
  | zero => omega
  | succ n =>
    change IsZero (ModuleCat.of R PUnit)
    exact ModuleCat.isZero_of_subsingleton _

lemma simpleSelf_finite [FiniteDimensional k M] (n : ℕ) :
    FiniteDimensional k ((simpleSelf M).complex.X n) := by
  cases n with
  | zero => exact inferInstanceAs (FiniteDimensional k M)
  | succ n => exact inferInstanceAs (FiniteDimensional k PUnit)

variable {M} {N : ModuleCat.{0} R} (P : CategoryTheory.ProjectiveResolution M)
    (Q : CategoryTheory.ProjectiveResolution N)

omit [Projective M] in
lemma prod_above (b n : ℕ) (hP : ∀ i, b < i → IsZero (P.complex.X i))
    (hQ : ∀ i, b < i → IsZero (Q.complex.X i)) (hn : b < n) :
    IsZero ((prod P Q).complex.X n) := by
  let := ModuleCat.subsingleton_of_isZero (hP n hn)
  let := ModuleCat.subsingleton_of_isZero (hQ n hn)
  change IsZero (ModuleCat.of R (P.complex.X n × Q.complex.X n))
  exact ModuleCat.isZero_of_subsingleton _

omit [Projective M] in
lemma prod_finite (hP : ∀ n, FiniteDimensional k (P.complex.X n))
    (hQ : ∀ n, FiniteDimensional k (Q.complex.X n)) (n : ℕ) :
    FiniteDimensional k ((prod P Q).complex.X n) := by
  let := hP n
  let := hQ n
  change FiniteDimensional k (P.complex.X n × Q.complex.X n)
  infer_instance

end ProjectiveResolution
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def leftResolutionOf {M : ModuleCat (Alg k R S)} (P : CategoryTheory.ProjectiveResolution M)
    (hP : ∀ n, Module.Finite (Alg k R S) (P.complex.X n)) :
    CategoryTheory.ProjectiveResolution (leftFunctor.obj M) where
  complex := (leftFunctor.mapHomologicalComplex _).obj P.complex
  projective n := by
    let := hP n
    let : Module.Projective R (Obj (P.complex.X n)) := projective_left _
    change Projective (ModuleCat.of R (Obj (P.complex.X n)))
    infer_instance
  π := (leftFunctor.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

def rightResolutionOf {M : ModuleCat (Alg k R S)} (P : CategoryTheory.ProjectiveResolution M)
    (hP : ∀ n, Module.Finite (Alg k R S) (P.complex.X n)) :
    CategoryTheory.ProjectiveResolution (rightFunctor.obj M) where
  complex := (rightFunctor.mapHomologicalComplex _).obj P.complex
  projective n := by
    let := hP n
    let : Module.Projective Sᵐᵒᵖ (Obj (P.complex.X n)) := projective_right _
    change Projective (ModuleCat.of Sᵐᵒᵖ (Obj (P.complex.X n)))
    infer_instance
  π := (rightFunctor.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] {M : C} [Projective M]

lemma map_resolution_quasiIso (P : ProjectiveResolution M) :
    QuasiIso ((F.mapHomologicalComplex _).map P.π) := by
  let e := ProjectiveResolution.homotopyEquiv P (ProjectiveResolution.self M)
  have h : e.hom = P.π := by
    simpa only [e, ProjectiveResolution.self, Category.comp_id] using
      ProjectiveResolution.homotopyEquiv_hom_π P (ProjectiveResolution.self M)
  rw [← h]
  exact (F.mapHomotopyEquiv e).quasiIso_hom

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] {ι : Type*} {c : ComplexShape ι}

lemma quasiIso_map_natIso (e : F ≅ G) {K L : HomologicalComplex C c} (f : K ⟶ L) :
    QuasiIso ((F.mapHomologicalComplex c).map f) ↔ QuasiIso ((G.mapHomologicalComplex c).map f) := by
  let i := NatIso.mapHomologicalComplex e c
  have h := i.hom.naturality f
  rw [← quasiIso_iff_comp_right ((F.mapHomologicalComplex c).map f) (i.hom.app L), h,
    quasiIso_iff_comp_left (i.hom.app K)]

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

instance regular_right_projective : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) := by
  let : Module.Projective Rᵐᵒᵖ R := Module.Projective.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ).symm
  exact Module.Projective.of_equiv (regularRightEquiv (k := k) (R := R)).symm

instance regular_left_projective : Module.Projective R (Obj (regular (k := k) (R := R))) :=
  Module.Projective.of_equiv (regularLeftEquiv (k := k) (R := R)).symm

instance rightFunctor_reflectsIsomorphisms :
    (rightFunctor (k := k) (R := R) (S := S)).ReflectsIsomorphisms := by
  rw [rightFunctor_eq]
  infer_instance

instance leftFunctor_reflectsIsomorphisms :
    (leftFunctor (k := k) (R := R) (S := S)).ReflectsIsomorphisms := by
  rw [leftFunctor_eq]
  infer_instance

omit [FiniteDimensional k S] in
lemma right_induction_regular_quasiIso (φ : R →ₐ[k] S) :
    QuasiIso (((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
      (regularResolution (k := k) (R := R)).π) := by
  let P := regularResolution (k := k) (R := R)
  let Q := rightResolutionOf P (fun n => inferInstance)
  let : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) := regular_right_projective
  let : Projective ((rightFunctor (k := k) (R := R) (S := R)).obj
      (regular (k := k) (R := R))) := by
    change Projective (ModuleCat.of Rᵐᵒᵖ (Obj (regular (k := k) (R := R))))
    exact ModuleCat.projective_of_categoryTheory_projective _
  let I := AlgebraInduction.functor φ.op
  let T := rightFunctor (k := k) (R := R) (S := R)
  let T' := rightFunctor (k := k) (R := R) (S := S)
  let J := AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)
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
  have hB : QuasiIso (((rightIndFunctor (U := R) φ ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (rightIndUnderlyingComparison (U := R) φ) P.π).mpr hI
  have hJ : QuasiIso (((J ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (Functor.isoWhiskerRight (rightIndComparison (U := R) φ) T') P.π).mpr hB
  exact (quasiIso_map_iff_of_preservesHomology
    ((J.mapHomologicalComplex _).map P.π) T').mp hJ

def rightInducedResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).obj
      (regular (k := k) (R := R))) where
  complex := ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).mapHomologicalComplex _).obj
    (regularResolution (k := k) (R := R)).complex
  projective n := by
    change Projective ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
    exact ModuleCat.projective_of_categoryTheory_projective _
  π := ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
    (regularResolution (k := k) (R := R)).π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := by
    let := right_induction_regular_quasiIso φ
    infer_instance

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (X : ModuleCat.{0} R)

lemma regular_evaluation_quasiIso :
    QuasiIso (((evaluation (k := k) X).mapHomologicalComplex _).map
      (regularResolution (k := k) (R := R)).π) := by
  let P := regularResolution (k := k) (R := R)
  let Q := rightResolutionOf P (fun n => inferInstance)
  let : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) := regular_right_projective
  let : Projective ((rightFunctor (k := k) (R := R) (S := R)).obj
      (regular (k := k) (R := R))) := by
    change Projective (ModuleCat.of Rᵐᵒᵖ (Obj (regular (k := k) (R := R))))
    exact ModuleCat.projective_of_categoryTheory_projective _
  let I := rightEvaluation (k := k) X
  let T := rightFunctor (k := k) (R := R) (S := R)
  let T' : ModuleCat.{0} R ⥤ ModuleCat.{0} k := ModuleCat.restrictScalars (algebraMap k R)
  let : CategoryTheory.Limits.PreservesFiniteLimits T' :=
    inferInstanceAs (CategoryTheory.Limits.PreservesFiniteLimits
      (AlgebraInduction.res (k := k) (Algebra.ofId k R)))
  let : CategoryTheory.Limits.PreservesFiniteColimits T' :=
    inferInstanceAs (CategoryTheory.Limits.PreservesFiniteColimits
      (AlgebraInduction.res (k := k) (Algebra.ofId k R)))
  let J := evaluation (k := k) (S := R) X
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
  have hJ :=
    (Tachikawa.quasiIso_map_natIso (rightEvaluationComparison (k := k) (S := R) X) P.π).mpr hI
  change QuasiIso ((T'.mapHomologicalComplex _).map ((J.mapHomologicalComplex _).map P.π)) at hJ
  exact (quasiIso_map_iff_of_preservesHomology
    ((J.mapHomologicalComplex _).map P.π) T').mp hJ

def evaluatedRegularResolution : ProjectiveResolution X where
  complex := ((evaluation (k := k) X).mapHomologicalComplex _).obj
    (regularResolution (k := k) (R := R)).complex
  projective n := by
    change Projective (evalObj X ((regularResolution (k := k) (R := R)).complex.X n))
    infer_instance
  π := ((evaluation (k := k) X).mapHomologicalComplex _).map
    (regularResolution (k := k) (R := R)).π ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (evaluation (k := k) (S := R) X) (ComplexShape.down ℕ) 0).hom.app _ ≫
        (ChainComplex.single₀ (ModuleCat R)).map (regularEvalIso (k := k) X).hom
  quasiIso := by
    let := regular_evaluation_quasiIso (k := k) X
    let : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex
        (evaluation (k := k) (S := R) X) (ComplexShape.down ℕ) 0).hom.app
          (regular (k := k) (R := R))) := inferInstance
    have regularQuasiIso : QuasiIso ((ChainComplex.single₀ (ModuleCat R)).map
        (regularEvalIso (k := k) X).hom) := quasiIso_of_isIso _
    let : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex
        (evaluation (k := k) (S := R) X) (ComplexShape.down ℕ) 0).hom.app
          (regular (k := k) (R := R)) ≫ (ChainComplex.single₀ (ModuleCat R)).map
            (regularEvalIso (k := k) X).hom) := quasiIso_comp _ _ (hφ' := regularQuasiIso)
    exact quasiIso_comp _ _

def evaluatedRegularComparison (P : ProjectiveResolution X) :
    HomotopyEquiv (evaluatedRegularResolution (k := k) X).complex P.complex :=
  ProjectiveResolution.homotopyEquiv _ _

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S) (X : ModuleCat.{0} S)

def inductionEvaluation :
    AlgebraInduction.functor (envelopingMap φ) ⋙ evaluation (k := k) (S := S) X ≅
      evaluation (k := k) (S := R) ((AlgebraInduction.res φ).obj X) ⋙
        AlgebraInduction.functor φ := by
  let a := (AlgebraInduction.adjunction (envelopingMap φ)).comp
    (evaluationAdjunction (k := k) (S := S) X)
  let b := (evaluationAdjunction (k := k) (S := R) ((AlgebraInduction.res φ).obj X)).comp
    (AlgebraInduction.adjunction φ)
  exact Adjunction.leftAdjointUniq (a.ofNatIsoRight (homBimoduleRestriction φ X)) b

variable [FiniteDimensional k R] [FiniteDimensional k S]

def evaluatedInducedRegularIso :
    ((evaluation (k := k) (S := S) X).mapHomologicalComplex _).obj (inducedRegularComplex φ) ≅
      ((AlgebraInduction.functor φ).mapHomologicalComplex _).obj
        (evaluatedRegularResolution (k := k) ((AlgebraInduction.res φ).obj X)).complex :=
  (NatIso.mapHomologicalComplex (inductionEvaluation φ X) (ComplexShape.down ℕ)).app
    (regularResolution (k := k) (R := R)).complex

def evaluatedInducedRegularComparison (P : ProjectiveResolution ((AlgebraInduction.res φ).obj X)) :
    HomotopyEquiv
      (((evaluation (k := k) (S := S) X).mapHomologicalComplex _).obj (inducedRegularComplex φ))
      (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj P.complex) :=
  (HomotopyEquiv.ofIso (evaluatedInducedRegularIso φ X)).trans
    ((AlgebraInduction.functor φ).mapHomotopyEquiv
      (evaluatedRegularComparison (k := k) ((AlgebraInduction.res φ).obj X) P))

end Tachikawa.Enveloping

end

end OAI
