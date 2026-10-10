import OAI.Topology.CoarseAssembly.RawCycleIndex

namespace OAI

/-! # Degenerate cycles have zero explicit Toeplitz index -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem representedCorrection_annihilates (c : OddCycle A) (hd : c.Degenerate) :
    (∀ a, representedCorrection c * c.representation a = 0) ∧
    (∀ a, c.representation a * representedCorrection c = 0) ∧
    (∀ a, star (representedCorrection c) * c.representation a = 0) := by
  let P := c.representation 1
  let K := representedCorrection c
  have hr : K * P = 0 := by
    change (symmetricCutDown P c.operator - c.operator) * P = 0
    rw [symmetricCutDown_sub_mul P c.operator (representation_unit_selfAdjoint c)
      (representation_unit_sq c), hd.1 1, hd.2.2 1]
    simp
  have hl : P * K = 0 := by
    change P * (symmetricCutDown P c.operator - c.operator) = 0
    rw [mul_symmetricCutDown_sub P c.operator (representation_unit_selfAdjoint c)
      (representation_unit_sq c), hd.1 1, hd.2.2 1]
    simp
  have hs : star K * P = 0 := by
    have he : star K * P = K * P - (star c.operator - c.operator) * P := by
      dsimp only [K, representedCorrection]
      rw [star_sub, (symmetricCutDown_selfAdjoint P c.operator (representation_unit_selfAdjoint c)).star_eq]
      noncomm_ring
    rw [he, hr, hd.2.2 1, sub_self]
  have hp (a : A) : P * c.representation a = c.representation a := by
    change c.representation 1 * c.representation a = c.representation a
    rw [← map_mul, one_mul]
  have hpr (a : A) : c.representation a * P = c.representation a := by
    change c.representation a * c.representation 1 = c.representation a
    rw [← map_mul, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [← hp a, ← mul_assoc, hr, zero_mul]
  · intro a
    rw [← hpr a, mul_assoc, hl, mul_zero]
  · intro a
    rw [← hp a, ← mul_assoc, hs, zero_mul]

theorem cutDown_degenerate (c : OddCycle A) (hd : c.Degenerate) : c.cutDown.Degenerate := by
  obtain ⟨hr, hl, hs⟩ := representedCorrection_annihilates c hd
  let K := representedCorrection c
  change (∀ a, (c.operator + K) * c.representation a - c.representation a * (c.operator + K) = 0) ∧
    (∀ a, ((c.operator + K) * (c.operator + K) - 1) * c.representation a = 0) ∧
    (∀ a, (star (c.operator + K) - (c.operator + K)) * c.representation a = 0)
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [add_mul, mul_add, hr a, hl a, add_zero, add_zero, hd.1 a]
  · intro a
    have he : ((c.operator + K) * (c.operator + K) - 1) * c.representation a =
        (c.operator * c.operator - 1) * c.representation a +
        c.operator * (K * c.representation a) +
        K * (c.operator * c.representation a - c.representation a * c.operator) +
        (K * c.representation a) * c.operator + K * (K * c.representation a) := by noncomm_ring
    rw [he, hd.2.1 a, hr a, hd.1 a, mul_zero, mul_zero, zero_mul]
    simp
  · intro a
    have he : (star (c.operator + K) - (c.operator + K)) * c.representation a =
        (star c.operator - c.operator) * c.representation a +
          star K * c.representation a - K * c.representation a := by
      rw [star_add]
      noncomm_ring
    rw [he, hd.2.2 a, hs a, hr a, add_zero, sub_self]

theorem cutDown_degenerate_sq (c : OddCycle A) (hd : c.Degenerate) :
    c.cutDown.operator * c.cutDown.operator = 1 := by
  let d := c.cutDown
  have hd' := cutDown_degenerate c hd
  have hp := hd'.2.1 (1 : A)
  have hQ := cutDown_complement c
  have hq : (d.operator * d.operator - 1) * (1 - d.representation 1) = 0 := by
    calc
      _ = d.operator * (d.operator * (1 - d.representation 1)) - (1 - d.representation 1) := by noncomm_ring
      _ = 0 := by rw [hQ, hQ, sub_self]
  apply sub_eq_zero.mp
  calc
    d.operator * d.operator - 1 = (d.operator * d.operator - 1) * d.representation 1 +
        (d.operator * d.operator - 1) * (1 - d.representation 1) := by noncomm_ring
    _ = 0 := by rw [hp, hq, add_zero]

theorem rawCycleToeplitz_eq_cutDown (c : OddCycle A) (u : A) :
    rawCycleToeplitz c u = representedToeplitz c.cutDown u := by
  change toeplitzCompression (positiveProjection (symmetricCutDown (c.representation 1) c.operator))
    (unitaryExtension c u) = toeplitzCompression
      (positiveProjection (c.operator + representedCorrection c)) (unitaryExtension c u)
  have he : c.operator + representedCorrection c = symmetricCutDown (c.representation 1) c.operator := by
    unfold representedCorrection
    abel
  rw [he]

theorem rawCycleIndex_degenerate (c : OddCycle A) (u : A) (hd : c.Degenerate)
    (hul : star u * u = 1) (hur : u * star u = 1) : rawCycleIndex c u = 0 := by
  have hi := representedIndex_degenerate c.cutDown u (cutDown_degenerate c hd)
    (cutDown_selfAdjoint c) (cutDown_degenerate_sq c hd) hul hur
  have he : rawCycleIndex c u = representedIndex c.cutDown u :=
    congrArg (fun T : End c.space => T.toLinearMap.index) (rawCycleToeplitz_eq_cutDown c u)
  exact he.trans hi

end CoarseAssembly.Analytic

end

end OAI
