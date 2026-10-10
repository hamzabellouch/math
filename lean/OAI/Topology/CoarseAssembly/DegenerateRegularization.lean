import OAI.Topology.CoarseAssembly.RegularizedCycle

namespace OAI

/-! # The explicit cut-down of a degenerate cycle remains degenerate -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A] {c : OddCycle A}

theorem OddCycle.Degenerate.cutDown_operator (hc : c.Degenerate) :
    (show End c.space from c.cutDown.operator) = c.operator * c.representation 1 + (1 - c.representation 1) := by
  let P := c.representation 1
  let F := c.operator
  have hP : star P = P := (representation_unit_selfAdjoint c).star_eq
  have hPP : P * P = P := representation_unit_sq c
  have hFP : F * P = P * F := sub_eq_zero.mp (hc.1 1)
  have hstar : star F * P = F * P := by
    have hs := hc.2.2 1
    rw [sub_mul] at hs
    exact sub_eq_zero.mp hs
  have hcut : P * F * P = F * P := by rw [← hFP, mul_assoc, hPP]
  have hcuts : star (P * F * P) = F * P := by
    rw [star_mul, star_mul, hP, hstar, ← mul_assoc, hcut]
  rw [c.cutDown_operator]
  change (1 / 2 : ℝ) • (P * F * P + star (P * F * P)) + (1 - P) = F * P + (1 - P)
  rw [hcuts, hcut]
  module

theorem OddCycle.Degenerate.cutDown_square (hc : c.Degenerate) :
    c.cutDown.operator * c.cutDown.operator = 1 := by
  let P := c.representation 1
  let F := c.operator
  have hPP : P * P = P := representation_unit_sq c
  have hFP : F * P = P * F := sub_eq_zero.mp (hc.1 1)
  have hF2P : F * F * P = P := by
    have hh := hc.2.1 1
    rw [sub_mul, one_mul] at hh
    exact sub_eq_zero.mp hh
  have hcut : P * F * P = F * P := by rw [← hFP, mul_assoc, hPP]
  have hsq : (F * P) * (F * P) = P := by
    calc
      _ = F * (P * F) * P := by noncomm_ring
      _ = F * (F * P) * P := by rw [← hFP]
      _ = (F * F) * (P * P) := by noncomm_ring
      _ = P := by rw [hPP, hF2P]
  have hright : F * P * (1 - P) = 0 := by rw [mul_sub, mul_one, mul_assoc, hPP, sub_self]
  have hleft : (1 - P) * (F * P) = 0 := by rw [sub_mul, one_mul, ← mul_assoc, hcut, sub_self]
  let G : End c.space := c.cutDown.operator
  have hG : G = F * P + (1 - P) := hc.cutDown_operator
  change G * G = 1
  rw [hG]
  rw [add_mul, mul_add, mul_add, hsq, hright, hleft]
  noncomm_ring [hPP]

theorem OddCycle.Degenerate.cutDown_commutator (hc : c.Degenerate) (a : A) :
    (show End c.space from c.cutDown.operator) * c.representation a -
      c.representation a * (show End c.space from c.cutDown.operator) = 0 := by
  let P := c.representation 1
  let F := c.operator
  let R := c.representation a
  let G : End c.space := c.cutDown.operator
  have hG : G = F * P + (1 - P) := hc.cutDown_operator
  have hPR : P * R = R := by dsimp [P, R]; rw [← map_mul, one_mul]
  have hRP : R * P = R := by dsimp [P, R]; rw [← map_mul, mul_one]
  have hFR : F * R = R * F := sub_eq_zero.mp (hc.1 a)
  have hleft : (F * P + (1 - P)) * R = F * R := by
    rw [add_mul, mul_assoc, hPR, sub_mul, one_mul, hPR, sub_self, add_zero]
  have hright : R * (F * P + (1 - P)) = F * R := by
    rw [mul_add, ← mul_assoc, ← hFR, mul_assoc, hRP, mul_sub, mul_one, hRP,
      sub_self, add_zero]
  change G * R - R * G = 0
  rw [hG, hleft, hright, sub_self]

theorem OddCycle.Degenerate.unitalSelfAdjoint (hc : c.Degenerate) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.unitalSelfAdjoint χ).Degenerate := by
  let G : End c.space := c.cutDown.operator
  let ρ : A →⋆ₙₐ[ℂ] End c.space := (c.unitalSelfAdjoint χ).representation
  have hG : IsSelfAdjoint G := cutDown_selfAdjoint c
  have hQ : G * (1 - c.representation 1) = 1 - c.representation 1 := cutDown_complement c
  have hQ' : (1 - c.representation 1) * G = 1 - c.representation 1 := by
    have hh := congrArg star hQ
    simpa only [star_mul, star_sub, star_one, hG.star_eq,
      (representation_unit_selfAdjoint c).star_eq] using hh
  change (∀ a, G * ρ a - ρ a * G = 0) ∧
    (∀ a, (G * G - 1) * ρ a = 0) ∧ (∀ a, (star G - G) * ρ a = 0)
  refine ⟨?_, ?_, ?_⟩
  · intro a
    change G * (c.representation a + χ a • (1 - c.representation 1)) -
      (c.representation a + χ a • (1 - c.representation 1)) * G = 0
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hQ, hQ', add_sub_add_right_eq_sub]
    exact hc.cutDown_commutator a
  · intro a
    have hsq : G * G = 1 := hc.cutDown_square
    rw [hsq, sub_self, zero_mul]
  · intro a
    rw [hG.star_eq, sub_self, zero_mul]

theorem OddCycle.Degenerate.bounded (hc : c.Degenerate)
    (hπ : c.representation 1 = 1) (hs : IsSelfAdjoint c.operator) :
    (c.bounded hπ hs).Degenerate := by
  have hsq : c.operator * c.operator = 1 := by
    have hh := hc.2.1 1
    rw [hπ, mul_one] at hh
    exact sub_eq_zero.mp hh
  change (∀ a, boundedTransform c.operator hs * c.representation a -
      c.representation a * boundedTransform c.operator hs = 0) ∧
    (∀ a, (boundedTransform c.operator hs * boundedTransform c.operator hs - 1) * c.representation a = 0) ∧
    (∀ a, (star (boundedTransform c.operator hs) - boundedTransform c.operator hs) * c.representation a = 0)
  rw [boundedTransform_eq_of_involution c.operator hs hsq]
  exact hc

theorem OddCycle.Degenerate.regularize (hc : c.Degenerate) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.regularize χ).Degenerate :=
  (hc.unitalSelfAdjoint χ).bounded (c.unitalSelfAdjoint_unital χ)
    (c.unitalSelfAdjoint_selfAdjoint χ)

end CoarseAssembly.Analytic

end

end OAI
