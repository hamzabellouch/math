import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.RepresentationMaps
import OAI.RepresentationTheory.RestrictedTilting.SL2Definitions

namespace OAI

/-! Exact tensor functors and rational tensor representations. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
universe v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]

theorem tensorLeft_preservesFiniteLimits (X : C) :
    PreservesFiniteLimits (tensorLeft X) := by
  let : (tensorLeft X).IsRightAdjoint := (tensorLeftAdjunction X Xᘁ).isRightAdjoint
  infer_instance

theorem tensorLeft_preservesFiniteColimits (X : C) :
    PreservesFiniteColimits (tensorLeft X) := by
  let : (tensorLeft X).IsLeftAdjoint := (tensorLeftAdjunction (ᘁX) X).isLeftAdjoint
  infer_instance

theorem tensorRight_preservesFiniteLimits (X : C) :
    PreservesFiniteLimits (tensorRight X) := by
  let : (tensorRight X).IsRightAdjoint := (tensorRightAdjunction (ᘁX) X).isRightAdjoint
  infer_instance

theorem tensorRight_preservesFiniteColimits (X : C) :
    PreservesFiniteColimits (tensorRight X) := by
  let : (tensorRight X).IsLeftAdjoint := (tensorRightAdjunction X Xᘁ).isLeftAdjoint
  infer_instance

end

section
universe u
variable (k : Type u) [Field k]

noncomputable instance fdrepRigid : RigidCategory (FDRep k (SL2 k)) :=
  BraidedCategory.rigidCategoryOfRightRigidCategory

 
lemma HasGoodFiltration.extension {A B C : FDRep k (SL2 k)}
    (hA : HasGoodFiltration k A) (hC : HasGoodFiltration k C)
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) : HasGoodFiltration k B := by
  induction hC generalizing A B with
  | zero C hC =>
    have : IsIso f := hS.isIso_f_iff.mpr hC
    cases hA with
    | zero initial hInitial =>
      exact .zero B (hInitial.of_iso (asIso f).symm)
    | @step prior initial degree inclusion quotient relation hSequence hPrior =>
      let equiv := asIso f
      let inclusion' := inclusion ≫ equiv.hom
      let quotient' := equiv.inv ≫ quotient
      have relation' : inclusion' ≫ quotient' = 0 := by
        simpa [inclusion', quotient'] using relation
      have hSequence' : (ShortComplex.mk inclusion' quotient' relation').ShortExact :=
        ShortComplex.shortExact_of_iso
          (ShortComplex.isoMk (Iso.refl prior) equiv (Iso.refl (costandard k degree))
            (by simp [inclusion']) (by simp [quotient'])) hSequence
      exact .step degree inclusion' quotient' relation' hSequence' hPrior
  | @step D C n i j v hT hD ih =>
    obtain ⟨K, a, b, r, wab, wr, hK, hB⟩ := fdrep_splice k f g w hS i j v hT
    exact .step n r (g ≫ j) wr hB (ih hA a b wab hK)

end

section
universe u
variable (k : Type u) [Field k]
open TensorProduct

 
lemma IsRational.tensor {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [Module.Finite k M] [Module.Finite k N]
    (ρ : Representation k (SL2 k) M) (σ : Representation k (SL2 k) N)
    (hρ : IsRational k ρ) (hσ : IsRational k σ) :
    IsRational k (Representation.tprod ρ σ) := by
  classical
  let b := Module.finBasis k M
  let c := Module.finBasis k N
  intro v l
  induction v using TensorProduct.inductionOn with
  | add v w hv hw =>
    obtain ⟨P, hP⟩ := hv
    obtain ⟨Q, hQ⟩ := hw
    exact ⟨P + Q, by intro g; simp only [map_add, hP, hQ]⟩
  | tmul v w =>
    choose P hP using fun i => hρ v (b.coord i)
    choose Q hQ using fun j => hσ w (c.coord j)
    refine ⟨∑ j, ∑ i, MvPolynomial.C (l (b i ⊗ₜ[k] c j)) * P i * Q j, fun g => ?_⟩
    change l ((ρ g v) ⊗ₜ[k] (σ g w)) = _
    conv_lhs => rw [← b.sum_repr (ρ g v), ← c.sum_repr (σ g w)]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, map_sum, map_smul]
    simp only [map_mul, MvPolynomial.eval_C, ← hP, ← hQ, Module.Basis.coord_apply,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [smul_eq_mul]
    ring

end

universe u
abbrev Binary (k : Type u) [Field k] (n : ℕ) := MvPolynomial.homogeneousSubmodule (Fin 2) k n
end FiberFunctorProof
end

end OAI
