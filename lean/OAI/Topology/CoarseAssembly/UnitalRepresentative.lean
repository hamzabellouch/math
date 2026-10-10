import OAI.Topology.CoarseAssembly.BinaryCycle
import OAI.Topology.CoarseAssembly.CharacterExtension
import OAI.Topology.CoarseAssembly.ProjectionSwap
import OAI.Topology.CoarseAssembly.UniformCycleNormalization

namespace OAI

/-! # Unital representatives for compact-source analytic classes

Adjoin a degenerate character cycle and exchange the complementary
subspaces by the explicit projection-swap unitary. This proves that
completion of a representation by a character preserves its class.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H : HilbertSpace}

theorem projectionSwap_representation (P R : End H) (hP : IsStarProjection P)
    (hPR : P * R = R) (hRP : R * P = R) (z : ℂ) :
    binaryBlock H H (R + z • (1 - P)) (z • P) =
      operatorConjugation (projectionSwapUnitary H P hP).toLinearIsometry
        (binaryBlock H H R (z • 1)) := by
  rw [projectionSwapUnitary_conjugation]
  have hu := projectionSwap_sq H P hP.isIdempotentElem
  suffices hi : binaryBlock H H (R + z • (1 - P)) (z • P) * projectionSwap H P =
      projectionSwap H P * binaryBlock H H R (z • 1) by
    have hi' := congrArg (fun T => T * projectionSwap H P) hi
    simpa only [mul_assoc, hu, mul_one] using hi'
  apply ContinuousLinearMap.ext
  intro x
  change binaryBlock H H (R + z • (1 - P)) (z • P) (projectionSwap H P x) =
    projectionSwap H P (binaryBlock H H R (z • 1) x)
  rw [projectionSwap_apply H, binaryBlock_apply H H, binaryBlock_apply H H,
    projectionSwap_apply H]
  apply (WithLp.ofLp_injective 2)
  have hp (y : H) : P (P y) = P y := DFunLike.congr_fun hP.isIdempotentElem y
  have hpr (y : H) : P (R y) = R y := DFunLike.congr_fun hPR y
  have hrp (y : H) : R (P y) = R y := DFunLike.congr_fun hRP y
  change
    ((R + z • (1 - P)) (P x.fst + (1 - P) x.snd),
      (z • P) ((1 - P) x.fst + P x.snd)) =
    (P (R x.fst) + (1 - P) ((z • (1 : End H)) x.snd),
      (1 - P) (R x.fst) + P ((z • (1 : End H)) x.snd))
  simp only [add_apply, smul_apply, sub_apply, one_apply_eq_self, map_add, map_sub,
    map_smul, hp, hpr, hrp]
  ext <;> module

theorem projectionSwap_operator (P F : End H) (hP : IsStarProjection P)
    (hF : IsSelfAdjoint F) (hQ : F * (1 - P) = 1 - P) :
    binaryBlock H H F 1 =
      operatorConjugation (projectionSwapUnitary H P hP).toLinearIsometry
        (binaryBlock H H F 1) := by
  rw [projectionSwapUnitary_conjugation]
  have hu := projectionSwap_sq H P hP.isIdempotentElem
  have hc := (commute_of_complement F P hF hP.isSelfAdjoint hQ).eq
  have hQ' : (1 - P) * F = 1 - P := by
    have h := congrArg star hQ
    simpa only [star_mul, star_sub, star_one, hP.isSelfAdjoint.star_eq, hF.star_eq] using h
  suffices hi : binaryBlock H H F 1 * projectionSwap H P =
      projectionSwap H P * binaryBlock H H F 1 by
    have hi' := congrArg (fun T => T * projectionSwap H P) hi
    simpa only [mul_assoc, hu, mul_one] using hi'
  apply ContinuousLinearMap.ext
  intro x
  change binaryBlock H H F 1 (projectionSwap H P x) =
    projectionSwap H P (binaryBlock H H F 1 x)
  rw [projectionSwap_apply H, binaryBlock_apply H H, binaryBlock_apply H H,
    projectionSwap_apply H]
  apply (WithLp.ofLp_injective 2)
  have hfp (y : H) : F (P y) = P (F y) := DFunLike.congr_fun hc y
  have hfq (y : H) : F ((1 - P) y) = (1 - P) y := DFunLike.congr_fun hQ y
  have hqf (y : H) : (1 - P) (F y) = (1 - P) y := DFunLike.congr_fun hQ' y
  change (F (P x.fst + (1 - P) x.snd), (1 - P) x.fst + P x.snd) =
    (P (F x.fst) + (1 - P) x.snd, (1 - P) (F x.fst) + P x.snd)
  rw [map_add, hfp, hfq, hqf]

variable {A : Type} [CStarAlgebra A]

theorem characterExtension_class (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ)
    (hF : IsSelfAdjoint c.operator)
    (hQ : c.operator * (1 - c.representation 1) = 1 - c.representation 1)
    (hsq : IsCompactOperator (c.operator * c.operator - 1 : End c.space)) :
    cycleClass A (c.characterExtension χ hF hQ hsq) = cycleClass A c := by
  let d := identityOperatorCycle
    (characterProjectionRepresentation χ (1 : End c.space) (IsStarProjection.one _))
  let e := identityOperatorCycle
    (characterProjectionRepresentation χ (c.representation 1) (representation_unit_projection c))
  have he : (c.binarySum d).UnitaryEquivalent
      ((c.characterExtension χ hF hQ hsq).binarySum e) := by
    refine ⟨projectionSwapUnitary c.space (c.representation 1) (representation_unit_projection c),
      ?_, ?_⟩
    · intro a
      change binaryBlock c.space c.space
        (c.representation a + χ a • (1 - c.representation 1)) (χ a • c.representation 1) = _
      exact projectionSwap_representation _ _ (representation_unit_projection c)
        (by rw [← map_mul, one_mul]) (by rw [← map_mul, mul_one]) (χ a)
    · exact projectionSwap_operator _ _ (representation_unit_projection c) hF hQ
  have h := unitary_eq _ _ he
  rw [binarySum_class, binarySum_class,
    degenerate_zero d (identityOperatorCycle_degenerate _),
    degenerate_zero e (identityOperatorCycle_degenerate _), add_zero, add_zero] at h
  exact h.symm

/-- Every analytic cycle over an algebra with a character has a unital
representative. The assertion includes equality in the actual cycle quotient. -/
theorem exists_unital_representative (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    ∃ d : OddCycle A, cycleClass A d = cycleClass A c ∧ d.representation 1 = 1 := by
  let d := c.cutDown
  let e := d.characterExtension χ (cutDown_selfAdjoint c) (cutDown_complement c)
    (cutDown_square_compact c)
  refine ⟨e, ?_, characterExtension_unital d χ _ _ _⟩
  exact (characterExtension_class d χ _ _ _).trans (cutDown_class c)

/-- The representatives needed by whole-family Rips localization can be
chosen unital, self-adjoint, involutive, and uniformly bounded by one. -/
theorem exists_unital_involutive_representative (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    ∃ d : OddCycle A, cycleClass A d = cycleClass A c ∧ d.representation 1 = 1 ∧
      IsSelfAdjoint d.operator ∧ d.operator * d.operator = 1 ∧ ‖d.operator‖ ≤ 1 := by
  obtain ⟨d, hdc, hdu⟩ := exists_unital_representative c χ
  obtain ⟨e, hed, heu, hes, heq⟩ := exists_involutive_representative d hdu
  exact ⟨e, hed.trans hdc, heu, hes, heq, involution_norm_le_one _ hes heq⟩

end CoarseAssembly.Analytic

end

end OAI
