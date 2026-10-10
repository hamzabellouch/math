import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.DualSplitting

namespace OAI

/-! Polynomial coordinate representations and associated sections. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
universe u
variable (k : Type u) [Field k]
open scoped Matrix Kronecker

noncomputable def leftCoordinateMatrix : SL2 k →* Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k where
  toFun g := (dualMatrix k g) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) k)
  map_one' := by rw [map_one, Matrix.one_kronecker_one]
  map_mul' g h := by rw [map_mul, ← Matrix.mul_kronecker_mul, one_mul]

noncomputable def coordinatePolynomialRepresentation :
    Representation k (SL2 k) (MvPolynomial (Fin 2 × Fin 2) k) where
  toFun g := (linearChange (leftCoordinateMatrix k g)).toLinearMap
  map_one' := by rw [map_one, linearChange_one]; rfl
  map_mul' g h := by rw [map_mul, linearChange_mul]; rfl

lemma coordinatePolynomial_rational : IsRational k (coordinatePolynomialRepresentation k) := by
  intro v l
  apply regular_linearChange_coeff k
    (fun g : SL2 k => fun ij : Fin 2 × Fin 2 => g ij.1 ij.2)
    (leftCoordinateMatrix k) _ v l
  intro a b
  refine ⟨inverseCoordinatePolynomial k (b.1,a.1) *
    MvPolynomial.C ((1 : Matrix (Fin 2) (Fin 2) k) a.2 b.2), fun g => ?_⟩
  change (g⁻¹ : SL2 k) b.1 a.1 * (1 : Matrix (Fin 2) (Fin 2) k) a.2 b.2 = _
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_inverseCoordinatePolynomial]

noncomputable def coordinateEvaluation :
    MvPolynomial (Fin 2 × Fin 2) k →ₐ[k] (SL2 k → k) :=
  MvPolynomial.aeval (fun ij => fun g : SL2 k => g ij.1 ij.2)

lemma coordinateEvaluation_apply (P : MvPolynomial (Fin 2 × Fin 2) k) (g : SL2 k) :
    coordinateEvaluation k P g = MvPolynomial.eval (fun ij => g ij.1 ij.2) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [coordinateEvaluation]
  | add P Q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | mul_X P i hp =>
    simp only [map_mul, Pi.mul_apply, hp]
    congr 1
    simp [coordinateEvaluation]

lemma coordinatePolynomial_evaluation (g h : SL2 k)
    (P : MvPolynomial (Fin 2 × Fin 2) k) :
    coordinateEvaluation k (coordinatePolynomialRepresentation k g P) h =
      coordinateEvaluation k P (g⁻¹ * h) := by
  rw [coordinateEvaluation_apply, coordinateEvaluation_apply]
  change MvPolynomial.eval _ (linearChange (leftCoordinateMatrix k g) P) = _
  rw [eval_linearChange]
  apply congrArg (fun z => MvPolynomial.eval z P)
  funext i
  change (∑ j : Fin 2 × Fin 2, (g⁻¹ : SL2 k) i.1 j.1 *
    (1 : Matrix (Fin 2) (Fin 2) k) j.2 i.2 * h j.1 j.2) = _
  simp [Fintype.sum_prod_type, Matrix.one_apply, Matrix.mul_apply]

 

noncomputable def regularSL2Functions : Subalgebra k (SL2 k → k) :=
  (coordinateEvaluation k).range

noncomputable def regularSL2Representation :
    Representation k (SL2 k) (regularSL2Functions k) where
  toFun g :=
    { toFun := fun f => ⟨fun h => f.val (g⁻¹ * h), by
        obtain ⟨P,hP⟩ := f.property
        refine ⟨coordinatePolynomialRepresentation k g P, ?_⟩
        ext h
        change coordinateEvaluation k (coordinatePolynomialRepresentation k g P) h = _
        rw [coordinatePolynomial_evaluation]
        exact congrArg (fun f : SL2 k → k => f (g⁻¹ * h)) hP⟩
      map_add' := by intro f f'; rfl
      map_smul' := by intro a f; rfl }
  map_one' := by ext f h; simp
  map_mul' := by intro g h; ext f a; simp [mul_assoc]

noncomputable def coordinateToRegular :
    MvPolynomial (Fin 2 × Fin 2) k →ₗ[k] regularSL2Functions k :=
  (coordinateEvaluation k).rangeRestrict.toLinearMap

lemma coordinateToRegular_surjective : Function.Surjective (coordinateToRegular k) := by
  intro f
  obtain ⟨P,hP⟩ := f.property
  exact ⟨P, Subtype.ext hP⟩

lemma regularSL2_rational : IsRational k (regularSL2Representation k) := by
  apply IsRational.of_surjective k (coordinatePolynomialRepresentation k)
    (regularSL2Representation k) (coordinateToRegular k) (coordinateToRegular_surjective k)
    _ (coordinatePolynomial_rational k)
  intro g P
  apply Subtype.ext
  funext h
  exact coordinatePolynomial_evaluation k g h P

 

noncomputable def regularVectorRepresentation (ι : Type u) :
    Representation k (SL2 k) (ι → regularSL2Functions k) where
  toFun g :=
    { toFun := fun f i => regularSL2Representation k g (f i)
      map_add' := by intro f f'; funext i; exact map_add (regularSL2Representation k g) _ _
      map_smul' := by intro a f; funext i; exact map_smul (regularSL2Representation k g) _ _ }
  map_one' := by
    apply LinearMap.ext
    intro f
    funext i
    exact congrArg (fun a : Module.End k (regularSL2Functions k) => a (f i))
      (map_one (regularSL2Representation k))
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro f
    funext i
    exact congrArg (fun a : Module.End k (regularSL2Functions k) => a (f i))
      (map_mul (regularSL2Representation k) g h)

lemma regularVector_rational (ι : Type u) [Fintype ι] [DecidableEq ι] :
    IsRational k (regularVectorRepresentation k ι) := by
  intro v l
  let ei (i : ι) : regularSL2Functions k →ₗ[k] (ι → regularSL2Functions k) :=
    LinearMap.single k (fun _ : ι => regularSL2Functions k) i
  have hsum (w : ι → regularSL2Functions k) : ∑ i, ei i (w i) = w := by
    ext i
    simp [ei]
  choose P hP using fun i => regularSL2_rational k (v i) (l.comp (ei i))
  refine ⟨∑ i, P i, fun g => ?_⟩
  rw [← hsum (regularVectorRepresentation k ι g v), map_sum, MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact hP i g

end

universe u
variable (k : Type u) [Field k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]

noncomputable def regularVectorEvaluation (g : SL2 k) :
    (ι → regularSL2Functions k) →ₗ[k] (ι → k) where
  toFun f i := (f i).val g
  map_add' := by intro f h; rfl
  map_smul' := by intro a f; rfl

variable (ρ : Representation k (Multiplicative k) (ι → k))

 

noncomputable def associatedSectionsSubmodule :
    Submodule k (ι → regularSL2Functions k) where
  carrier := {f | ∀ (g : SL2 k) (t : k),
    regularVectorEvaluation k ι (g * unipotent k t) f =
      ρ (Multiplicative.ofAdd (-t)) (regularVectorEvaluation k ι g f)}
  zero_mem' := by intro g t; simp
  add_mem' := by
    intro f h hf hh g t
    rw [map_add, hf, hh, map_add, map_add]
  smul_mem' := by
    intro a f hf g t
    rw [map_smul, hf, map_smul, map_smul]

noncomputable def associatedSectionsSubrepresentation :
    Subrepresentation (regularVectorRepresentation k ι) where
  toSubmodule := associatedSectionsSubmodule k ι ρ
  apply_mem_toSubmodule g f hf := by
    intro h t
    change regularVectorEvaluation k ι (g⁻¹ * (h * unipotent k t)) f =
      ρ (Multiplicative.ofAdd (-t)) (regularVectorEvaluation k ι (g⁻¹ * h) f)
    rw [← mul_assoc]
    exact hf (g⁻¹ * h) t

noncomputable def associatedSectionsRepresentation :
    Representation k (SL2 k) (associatedSectionsSubmodule k ι ρ) :=
  (associatedSectionsSubrepresentation k ι ρ).toRepresentation

lemma associatedSections_rational : IsRational k
    (M := associatedSectionsSubmodule k ι ρ) (associatedSectionsRepresentation k ι ρ) := by
  exact IsRational.of_injective k (M := associatedSectionsSubmodule k ι ρ)
    (N := ι → regularSL2Functions k) (associatedSectionsRepresentation k ι ρ)
    (regularVectorRepresentation k ι) (associatedSectionsSubmodule k ι ρ).subtype
    (associatedSectionsSubmodule k ι ρ).injective_subtype (fun _ _ => rfl)
    (regularVector_rational k ι)

noncomputable def regularFirstColumn (i : Fin 2) : regularSL2Functions k :=
  coordinateToRegular k (MvPolynomial.X (i,0))

lemma regularFirstColumn_apply (i : Fin 2) (g : SL2 k) :
    (regularFirstColumn k i).val g = g i 0 := by
  change coordinateEvaluation k (MvPolynomial.X (i,0)) g = _
  rw [coordinateEvaluation_apply, MvPolynomial.eval_X]

lemma firstColumn_unipotent_mul (g : SL2 k) (t : k) (i : Fin 2) :
    (g * unipotent k t) i 0 = g i 0 := by
  change (((g : Matrix (Fin 2) (Fin 2) k) *
    (unipotent k t : Matrix (Fin 2) (Fin 2) k)) i 0) = _
  simp [Matrix.mul_apply, Fin.sum_univ_two, unipotent]

noncomputable def regularVectorCoordinateMul (i : Fin 2) :
    (ι → regularSL2Functions k) →ₗ[k] (ι → regularSL2Functions k) where
  toFun f j := regularFirstColumn k i * f j
  map_add' := by intro f h; funext j; exact mul_add _ _ _
  map_smul' := by intro a f; funext j; exact mul_smul_comm a (regularFirstColumn k i) (f j)

omit [Fintype ι] [DecidableEq ι] in
lemma regularVectorCoordinateMul_evaluation (i : Fin 2)
    (f : ι → regularSL2Functions k) (g : SL2 k) :
    regularVectorEvaluation k ι g (regularVectorCoordinateMul k ι i f) =
      g i 0 • regularVectorEvaluation k ι g f := by
  funext j
  change (regularFirstColumn k i).val g * (f j).val g = _
  rw [regularFirstColumn_apply]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma associatedSections_coordinate_mul_mem (i : Fin 2)
    (f : ι → regularSL2Functions k) (hf : f ∈ associatedSectionsSubmodule k ι ρ) :
    regularVectorCoordinateMul k ι i f ∈ associatedSectionsSubmodule k ι ρ := by
  intro g t
  rw [regularVectorCoordinateMul_evaluation, regularVectorCoordinateMul_evaluation,
    firstColumn_unipotent_mul, hf, map_smul]

noncomputable def associatedCoordinateMul (i : Fin 2) :
    (associatedSectionsSubmodule k ι ρ) →ₗ[k] (associatedSectionsSubmodule k ι ρ) :=
  (regularVectorCoordinateMul k ι i).restrict
    (associatedSections_coordinate_mul_mem k ι ρ i)

omit [Fintype ι] [DecidableEq ι] in
 

lemma associatedCoordinateMul_action (g : SL2 k) (i : Fin 2)
    (f : associatedSectionsSubmodule k ι ρ) :
    associatedSectionsRepresentation k ι ρ g (associatedCoordinateMul k ι ρ i f) =
      ∑ j : Fin 2, (g⁻¹ : SL2 k) i j •
        associatedCoordinateMul k ι ρ j (associatedSectionsRepresentation k ι ρ g f) := by
  rw [Fin.sum_univ_two]
  apply Subtype.ext
  funext a
  apply Subtype.ext
  funext h
  change (regularFirstColumn k i).val (g⁻¹ * h) * (f.val a).val (g⁻¹ * h) =
    (g⁻¹ : SL2 k) i 0 * ((regularFirstColumn k 0).val h * (f.val a).val (g⁻¹ * h)) +
    (g⁻¹ : SL2 k) i 1 * ((regularFirstColumn k 1).val h * (f.val a).val (g⁻¹ * h))
  rw [regularFirstColumn_apply, regularFirstColumn_apply, regularFirstColumn_apply]
  change (((g⁻¹ : SL2 k) : Matrix (Fin 2) (Fin 2) k) *
    (h : Matrix (Fin 2) (Fin 2) k)) i 0 * _ = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  ring

 
noncomputable def associatedOriginRelations : Submodule k (associatedSectionsSubmodule k ι ρ) :=
  LinearMap.range (associatedCoordinateMul k ι ρ 0) ⊔
    LinearMap.range (associatedCoordinateMul k ι ρ 1)

omit [Fintype ι] [DecidableEq ι] in
lemma associatedOriginRelations_stable (g : SL2 k) :
    associatedOriginRelations k ι ρ ≤
      (associatedOriginRelations k ι ρ).comap (associatedSectionsRepresentation k ι ρ g) := by
  have hcoord (i : Fin 2) (f : associatedSectionsSubmodule k ι ρ) :
      associatedSectionsRepresentation k ι ρ g (associatedCoordinateMul k ι ρ i f) ∈
        associatedOriginRelations k ι ρ := by
    rw [associatedCoordinateMul_action]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    fin_cases j
    · exact Submodule.mem_sup_left ⟨_,rfl⟩
    · exact Submodule.mem_sup_right ⟨_,rfl⟩
  apply sup_le
  · rintro _ ⟨f,rfl⟩
    exact hcoord 0 f
  · rintro _ ⟨f,rfl⟩
    exact hcoord 1 f

noncomputable def quotientRationalModule {V : Type u} [AddCommGroup V] [Module k V]
    (σ : Representation k (SL2 k) V) (P : Submodule k V)
    (hP : ∀ g, P ≤ P.comap (σ g)) : Rep k (SL2 k) :=
  Rep.of (Representation.quotient σ P hP)

omit [Fintype ι] [DecidableEq ι] in
lemma quotientRationalModule_rational {V : Type u} [AddCommGroup V] [Module k V]
    (σ : Representation k (SL2 k) V) (P : Submodule k V)
    (hP : ∀ g, P ≤ P.comap (σ g)) (hσ : IsRational k σ) :
    IsRational k (quotientRationalModule k σ P hP).ρ := by
  exact IsRational.of_surjective k (M := V) (N := V ⧸ P)
    σ (Representation.quotient σ P hP) P.mkQ P.mkQ_surjective (fun _ _ => rfl) hσ

 
noncomputable def associatedOriginRep : Rep k (SL2 k) :=
  quotientRationalModule k (V := associatedSectionsSubmodule k ι ρ)
    (associatedSectionsRepresentation k ι ρ) (associatedOriginRelations k ι ρ)
    (associatedOriginRelations_stable k ι ρ)

 

lemma associatedOrigin_rational : IsRational k (associatedOriginRep k ι ρ).ρ := by
  exact quotientRationalModule_rational k _ _ _ (associatedSections_rational k ι ρ)

end FiberFunctorProof

end

end OAI
