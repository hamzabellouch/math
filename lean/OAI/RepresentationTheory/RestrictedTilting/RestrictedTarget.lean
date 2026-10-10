import Mathlib

namespace OAI

 

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof.RestrictedTarget

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

section SL2
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

end SL2
end FiberFunctorProof.RestrictedTarget

namespace FiberFunctorProof.RestrictedTarget
open CategoryTheory CategoryTheory.MonoidalCategory
universe u
 

def RestrictedTiltingTheorem : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : ℕ), 1 ≤ r → ∀ (l : (Fin r → ZMod p) →+ k), Function.Injective l →
    ∀ (D : FDRep k (Multiplicative (Fin r → ZMod p))),
      ∃ T : FDRep k (SL2 k), IsTilting k T ∧
        Nonempty (((restrictElementary k p r l).obj (steinberg k p (r-1)) ⊗ D) ≅
          (restrictElementary k p r l).obj T)
end FiberFunctorProof.RestrictedTarget

end OAI
