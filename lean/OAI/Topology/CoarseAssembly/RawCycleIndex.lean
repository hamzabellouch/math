import OAI.Topology.CoarseAssembly.ExplicitCutDown
import OAI.Topology.CoarseAssembly.EssentialToeplitz
import OAI.Topology.CoarseAssembly.RepresentedIndex

namespace OAI

/-! # A Fredholm index defined on every odd cycle

The operator uses the explicit self-adjoint cut-down and varies continuously
along any Fredholm-module homotopy. Its definition makes no spectral choices.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def rawCycleToeplitz (c : OddCycle A) (u : A) : End c.space :=
  toeplitzCompression (H := c.space)
    (positiveProjection (H := c.space)
      (symmetricCutDown (H := c.space) (c.representation 1) c.operator)) (unitaryExtension c u)

def rawCycleIndex (c : OddCycle A) (u : A) : ℤ := (rawCycleToeplitz c u).toLinearMap.index

theorem rawCycleToeplitz_compact_defects (c : OddCycle A) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    IsCompactOperator (star (rawCycleToeplitz c u) * rawCycleToeplitz c u - 1 : End c.space) ∧
      IsCompactOperator (rawCycleToeplitz c u * star (rawCycleToeplitz c u) - 1 : End c.space) := by
  generalize hT : rawCycleToeplitz c u = T
  let F : End c.space := symmetricCutDown (c.representation 1) c.operator
  have hF : IsSelfAdjoint F := symmetricCutDown_selfAdjoint _ _ (representation_unit_selfAdjoint c)
  have hFP : Commute F (c.representation 1) :=
    commute_of_complement F _ hF (representation_unit_selfAdjoint c)
      (symmetricCutDown_complement _ _ (representation_unit_selfAdjoint c) (representation_unit_sq c))
  have hc : IsCompactOperator (F * c.representation u - c.representation u * F : End c.space) := by
    have h := c.cutDown.commutator_compact u
    change IsCompactOperator ((c.operator + representedCorrection c) * c.representation u -
      c.representation u * (c.operator + representedCorrection c) : End c.space) at h
    have he : c.operator + representedCorrection c = F := by unfold representedCorrection; dsimp [F]; abel
    rwa [he] at h
  have hU : IsCompactOperator (F * unitaryExtension c u - unitaryExtension c u * F : End c.space) := by
    have he : F * unitaryExtension c u - unitaryExtension c u * F =
        F * c.representation u - c.representation u * F := by
      simp only [unitaryExtension, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul]
      rw [hFP.eq]
      abel
    rw [he]
    exact hc
  obtain ⟨hUl, hUr⟩ := unitaryExtension_unitary c u hul hur
  have hFF : IsCompactOperator (F * F - 1 : End c.space) := symmetricCutDown_square_compact c
  have result := essentialToeplitz_compact_defects (H := c.space) F (unitaryExtension c u)
    hF hFF hUl hUr hU
  change toeplitzCompression (positiveProjection F) (unitaryExtension c u) = T at hT
  rw [hT] at result
  exact result


theorem rawCycleToeplitz_fredholm (c : OddCycle A) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) : (rawCycleToeplitz c u).IsFredholm := by
  obtain ⟨hl, hr⟩ := rawCycleToeplitz_compact_defects c u hul hur
  exact isFredholm_of_compact_essential_unitary _ hl hr

theorem rawCycleIndex_homotopy (h : OddHomotopy A) (u : A)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    rawCycleIndex (h.eval start) u = rawCycleIndex (h.eval finish) u := by
  apply fredholmIndex_homotopy (fun t => rawCycleToeplitz (h.eval t) u)
  · have hP := h.continuous_representation (1 : A)
    have hB := (hP.mul h.continuous_operator).mul hP
    have hF : Continuous (fun t => symmetricCutDown (h.representation t 1) (h.operator t)) :=
      ((hB.add hB.star).const_smul (1 / 2 : ℝ)).add (continuous_const.sub hP)
    have hpos : Continuous (fun t => positiveProjection
        (symmetricCutDown (h.representation t 1) (h.operator t))) :=
      (hF.add continuous_const).const_smul (1 / 2 : ℝ)
    have hU : Continuous (fun t => h.representation t u + (1 - h.representation t 1)) :=
      (h.continuous_representation u).add (continuous_const.sub hP)
    change Continuous (fun t => positiveProjection
      (symmetricCutDown (h.representation t 1) (h.operator t)) *
      (h.representation t u + (1 - h.representation t 1)) *
      positiveProjection (symmetricCutDown (h.representation t 1) (h.operator t)) +
      (1 - positiveProjection (symmetricCutDown (h.representation t 1) (h.operator t))))
    exact ((hpos.mul hU).mul hpos).add (continuous_const.sub hpos)
  · intro t
    exact rawCycleToeplitz_fredholm (h.eval t) u hul hur

variable {B : Type} [CStarAlgebra B]

theorem rawCycleIndex_precomp (c : OddCycle A) (φ : B →⋆ₙₐ[ℂ] A)
    (hφ : φ 1 = 1) (u : B) : rawCycleIndex (c.precomp φ) u = rawCycleIndex c (φ u) := by
  have he : rawCycleToeplitz (c.precomp φ) u = rawCycleToeplitz c (φ u) := by
    change toeplitzCompression (positiveProjection (symmetricCutDown
      (c.representation (φ 1)) c.operator))
      (c.representation (φ u) + (1 - c.representation (φ 1))) = _
    rw [hφ]
    rfl
  exact congrArg (fun T : End c.space => T.toLinearMap.index) he

end CoarseAssembly.Analytic

end

end OAI
