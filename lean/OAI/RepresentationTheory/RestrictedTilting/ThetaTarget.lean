import Mathlib

namespace OAI

 

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof.ThetaTarget
section

universe u

section PolynomialAction
variable {k : Type u} [CommRing k] {ι : Type*} [Fintype ι]

 
noncomputable def linearChange (A : Matrix ι ι k) :
    MvPolynomial ι k →ₐ[k] MvPolynomial ι k :=
  MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (A j i) * MvPolynomial.X j)

@[simp] lemma linearChange_X (A : Matrix ι ι k) (i : ι) :
    linearChange A (MvPolynomial.X i) =
      ∑ j, MvPolynomial.C (A j i) * MvPolynomial.X j := by
  simp [linearChange]

@[simp] lemma linearChange_C (A : Matrix ι ι k) (x : k) :
    linearChange A (MvPolynomial.C x) = MvPolynomial.C x := by
  simp [linearChange]

variable [DecidableEq ι]

@[simp] lemma linearChange_one : linearChange (1 : Matrix ι ι k) = AlgHom.id k _ := by
  ext i : 1
  simp [linearChange, Matrix.one_apply]

omit [DecidableEq ι] in
lemma linearChange_mul (A B : Matrix ι ι k) :
    linearChange (A * B) = (linearChange A).comp (linearChange B) := by
  ext i : 1
  simp only [AlgHom.comp_apply, linearChange_X, map_sum, map_mul, linearChange_C,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  ring

omit [DecidableEq ι] in
lemma linearChange_homogeneous (A : Matrix ι ι k) {f : MvPolynomial ι k} {n : ℕ}
    (hf : f.IsHomogeneous n) : (linearChange A f).IsHomogeneous n := by
  change (MvPolynomial.eval₂ MvPolynomial.C
    (fun i => ∑ j, MvPolynomial.C (A j i) * MvPolynomial.X j) f).IsHomogeneous n
  simpa only [one_mul] using
    hf.eval₂ MvPolynomial.C
      (fun i => ∑ j, MvPolynomial.C (A j i) * MvPolynomial.X j)
      (fun x => MvPolynomial.isHomogeneous_C ι x)
      (fun i => MvPolynomial.IsHomogeneous.sum _ _ _
        (fun j _ => (MvPolynomial.isHomogeneous_X k j).C_mul (A j i)))

noncomputable def homogeneousRepresentation (n : ℕ) :
    Representation k (Matrix ι ι k) (MvPolynomial.homogeneousSubmodule ι k n) where
  toFun A := (linearChange A).toLinearMap.restrict (fun _ hf => linearChange_homogeneous A hf)
  map_one' := by
    ext f : 1
    apply Subtype.ext
    change linearChange 1 f.val = f.val
    rw [linearChange_one]
    rfl
  map_mul' A B := by
    ext f : 1
    apply Subtype.ext
    change linearChange (A * B) f.val = linearChange A (linearChange B f.val)
    rw [linearChange_mul]
    rfl

end PolynomialAction

variable (k : Type u) [Field k]

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) k

 
def IsRational {M : Type u} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) : Prop :=
  ∀ (v : M) (l : M →ₗ[k] k),
    ∃ P : MvPolynomial (Fin 2 × Fin 2) k,
      ∀ g : SL2 k, l (ρ g v) = MvPolynomial.eval (fun ij => g ij.1 ij.2) P

 
noncomputable def dualMatrix : SL2 k →* Matrix (Fin 2) (Fin 2) k where
  toFun g := ((g⁻¹ : SL2 k) : Matrix (Fin 2) (Fin 2) k).transpose
  map_one' := by simp
  map_mul' g h := by
    simp [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

instance homogeneous_finite (n : ℕ) :
    Module.Finite k (MvPolynomial.homogeneousSubmodule (Fin 2) k n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) k n)

 
noncomputable def costandard (n : ℕ) : FDRep k (SL2 k) :=
  FDRep.of ((homogeneousRepresentation n).comp (dualMatrix k))

 
inductive HasGoodFiltration : FDRep k (SL2 k) → Prop
  | zero (V) (hV : IsZero V) : HasGoodFiltration V
  | step {A B} (n : ℕ) (f : A ⟶ B) (g : B ⟶ costandard k n)
      (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
      (hA : HasGoodFiltration A) : HasGoodFiltration B

 

def IsTilting (V : FDRep k (SL2 k)) : Prop :=
  IsRational k V.ρ ∧ HasGoodFiltration k V ∧ HasGoodFiltration k Vᘁ

 
noncomputable def steinberg (p m : ℕ) : FDRep k (SL2 k) :=
  costandard k (p ^ m - 1)

 
def unipotent (t : k) : SL2 k :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

lemma unipotent_zero : unipotent k 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent]

lemma unipotent_add (t s : k) : unipotent k (t + s) = unipotent k t * unipotent k s := by
  apply Subtype.ext
  change !![1, t + s; 0, 1] = !![1, t; 0, 1] * !![1, s; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

 
def elementaryEmbedding (p r : ℕ) (l : (Fin r → ZMod p) →+ k) :
    Multiplicative (Fin r → ZMod p) →* SL2 k where
  toFun a := unipotent k (l a.toAdd)
  map_one' := by simp [unipotent_zero]
  map_mul' a b := by simp [unipotent_add]

noncomputable def restrictElementary (p r : ℕ) (l : (Fin r → ZMod p) →+ k) :
    FDRep k (SL2 k) ⥤ FDRep k (Multiplicative (Fin r → ZMod p)) :=
  Action.res (FGModuleCat k) (elementaryEmbedding k p r l)

end

 

section

universe u

 
structure FiniteSymmetricTensorCategory (k : Type u) [Field k] where
  Obj : Type (u + 1)
  [category : Category.{u} Obj]
  [abelian : Abelian Obj]
  [linear : Linear k Obj]
  [monoidal : MonoidalCategory Obj]
  [monoidalPreadditive : MonoidalPreadditive Obj]
  [monoidalLinear : MonoidalLinear k Obj]
  [symmetric : SymmetricCategory Obj]
  [rigid : RigidCategory Obj]
  essentiallySmall : EssentiallySmall.{u} Obj
  finiteHom : ∀ X Y : Obj, Module.Finite k (X ⟶ Y)
  artinian : ∀ X : Obj, IsArtinianObject X
  noetherian : ∀ X : Obj, IsNoetherianObject X
  finiteSimple : ∃ (m : ℕ) (S : Fin m → Obj),
    (∀ i, Simple (S i)) ∧ ∀ X : Obj, Simple X → ∃ i, Nonempty (S i ≅ X)
  enoughProjectives : EnoughProjectives Obj
  unitScalars : Function.Bijective (algebraMap k (End (𝟙_ Obj)))
  tensorLeftExact : ∀ X : Obj,
    PreservesFiniteLimits (tensorLeft X) ∧ PreservesFiniteColimits (tensorLeft X)
  tensorRightExact : ∀ X : Obj,
    PreservesFiniteLimits (tensorRight X) ∧ PreservesFiniteColimits (tensorRight X)

attribute [instance] FiniteSymmetricTensorCategory.category
  FiniteSymmetricTensorCategory.abelian FiniteSymmetricTensorCategory.linear
  FiniteSymmetricTensorCategory.monoidal FiniteSymmetricTensorCategory.monoidalPreadditive
  FiniteSymmetricTensorCategory.monoidalLinear FiniteSymmetricTensorCategory.symmetric
  FiniteSymmetricTensorCategory.rigid

 
abbrev Tilting (k : Type u) [Field k] :=
  ObjectProperty.FullSubcategory (IsTilting k)

abbrev tiltingInclusion (k : Type u) [Field k] : Tilting k ⥤ FDRep k (SL2 k) :=
  ObjectProperty.ι (IsTilting k)

 

class TiltingTensorStructure (k : Type u) [Field k] where
  [monoidal : MonoidalCategory (Tilting k)]
  [monoidalPreadditive : MonoidalPreadditive (Tilting k)]
  [monoidalLinear : MonoidalLinear k (Tilting k)]
  [symmetric : SymmetricCategory (Tilting k)]
  [rigid : RigidCategory (Tilting k)]
  [inclusionBraided : (tiltingInclusion k).Braided]

attribute [instance_reducible, instance] TiltingTensorStructure.monoidal
  TiltingTensorStructure.symmetric TiltingTensorStructure.rigid
  TiltingTensorStructure.inclusionBraided
attribute [instance] TiltingTensorStructure.monoidalPreadditive
  TiltingTensorStructure.monoidalLinear

 

noncomputable def steinbergIdeal (k : Type u) [Field k] (p n : ℕ) (A B : Tilting k) :
    Submodule k (A ⟶ B) :=
  Submodule.span k {f | ∃ X : Tilting k,
    ∃ a : A.obj ⟶ steinberg k p n ⊗ X.obj,
    ∃ b : steinberg k p n ⊗ X.obj ⟶ B.obj, f.hom = a ≫ b}

 
structure TiltingFunctor (k : Type u) [Field k] [TiltingTensorStructure k]
    (D : FiniteSymmetricTensorCategory k) where
  toFunctor : Tilting k ⥤ D.Obj
  [additive : toFunctor.Additive]
  [linear : toFunctor.Linear k]
  [braided : toFunctor.Braided]

attribute [instance] TiltingFunctor.additive TiltingFunctor.linear TiltingFunctor.braided

 
structure ExactTensorFunctor {k : Type u} [Field k]
    (C D : FiniteSymmetricTensorCategory k) where
  toFunctor : C.Obj ⥤ D.Obj
  [additive : toFunctor.Additive]
  [linear : toFunctor.Linear k]
  [braided : toFunctor.Braided]
  exact : ∀ S : ShortComplex C.Obj, S.ShortExact → (S.map toFunctor).ShortExact

attribute [instance] ExactTensorFunctor.additive ExactTensorFunctor.linear
  ExactTensorFunctor.braided

 
structure FiberFunctor {k : Type u} [Field k]
    (C D : FiniteSymmetricTensorCategory k) extends ExactTensorFunctor C D where
  faithful : toFunctor.Faithful

 

def MonoidallyIsomorphic {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] : Prop :=
  ∃ e : F ≅ G, e.hom.IsMonoidal

 
def HasSteinbergKernel (k : Type u) [Field k] [TiltingTensorStructure k]
    (p n : ℕ) {D : FiniteSymmetricTensorCategory k} (F : TiltingFunctor k D) : Prop :=
  ∀ (A B : Tilting k) (f : A ⟶ B), F.toFunctor.map f = 0 ↔ f ∈ steinbergIdeal k p n A B

 

structure VerlindePresentation (k : Type u) [Field k] [TiltingTensorStructure k]
    (p n : ℕ) (W : FiniteSymmetricTensorCategory k) where
  sigma : TiltingFunctor k W
  full : sigma.toFunctor.Full
  kernel : HasSteinbergKernel k p n sigma
  extend : ∀ (D : FiniteSymmetricTensorCategory k) (F : TiltingFunctor k D),
    HasSteinbergKernel k p n F → ∃ H : ExactTensorFunctor W D,
      MonoidallyIsomorphic (sigma.toFunctor ⋙ H.toFunctor) F.toFunctor
  unique : ∀ (D : FiniteSymmetricTensorCategory k) (F G : ExactTensorFunctor W D),
    MonoidallyIsomorphic (sigma.toFunctor ⋙ F.toFunctor) (sigma.toFunctor ⋙ G.toFunctor) →
      MonoidallyIsomorphic F.toFunctor G.toFunctor

 

def MainTheorem : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (C : FiniteSymmetricTensorCategory k),
    ∃ s : TiltingTensorStructure k, letI := s
      ∃ n : ℕ, 1 ≤ n ∧ ∃ W : FiniteSymmetricTensorCategory k,
        Nonempty (VerlindePresentation k p n W) ∧ Nonempty (FiberFunctor C W)

end

 

open CategoryTheory
universe u
noncomputable instance elementaryRestrictionMonoidal
    (k : Type u) [Field k] (p r : ℕ) (l : (Fin r → ZMod p) →+ k) :
    (restrictElementary k p r l).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso := fun _ _ => Iso.refl _
    associativity := by
      intro X Y Z
      simp only [Iso.refl_hom]
      erw [MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id,
        Category.id_comp, Category.id_comp]
    left_unitality := by
      intro X
      simp only [Iso.refl_hom]
      erw [MonoidalCategory.id_whiskerRight, Category.id_comp, Category.id_comp]
      rfl
    right_unitality := by
      intro X
      simp only [Iso.refl_hom]
      erw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.id_comp]
      rfl }

 

def HigherThetaConstruction : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ), 1 ≤ r →
    ∀ (l : (Fin r → ZMod p) →+ k), Function.Injective l →
    ∃ s : TiltingTensorStructure k, letI := s
      ∃ W : FiniteSymmetricTensorCategory k,
        ∃ V : VerlindePresentation k p r W,
          ∃ Θ : FDRep k (Multiplicative (Fin r → ZMod p)) ⥤ W.Obj,
            ∃ _ : Θ.Additive, ∃ _ : Θ.Linear k, ∃ hΘ : Θ.Braided,
              letI := hΘ
              MonoidallyIsomorphic
                (tiltingInclusion k ⋙ restrictElementary k p r l ⋙ Θ)
                V.sigma.toFunctor
end FiberFunctorProof.ThetaTarget

end OAI
