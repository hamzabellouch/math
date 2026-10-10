import OAI.Topology.CoarseAssembly.RipsUnitaryLocalization

namespace OAI

/-! # Whole-union boundary invariance under unitary equivalence of cycles -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X] [DecidableEq X] (r : ℝ)
  {c d : OddCycle C(Point X r, ℂ)}

theorem ripsExtension_aligned (e : c.UnitaryEquivalent d)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1)
    (V : c.space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    coefficientExtension (V.comp e.unitary.symm.toLinearIsometry) (ripsSpatialOperator r d hd) =
      coefficientExtension V (ripsSpatialOperator r c hc) := by
  rw [ripsSpatialOperator_unitary r e hc hd]
  change isometricExtension (coefficientIsometry (V.comp e.unitary.symm.toLinearIsometry))
    (isometricExtension (coefficientIsometry e.unitary.toLinearIsometry) _) = _
  rw [isometricExtension_comp, coefficientIsometry_comp]
  have he : (V.comp e.unitary.symm.toLinearIsometry).comp e.unitary.toLinearIsometry = V := by
    ext x
    simp
  rw [he]
  rfl

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

theorem ripsFamilyBoundaryWithEmbeddings_congr (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c d : ∀ i, OddCycle C(Point (Q i) r, ℂ))
    (hc : ∀ i, (c i).representation 1 = 1) (hd : ∀ i, (d i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator) (hG : ∀ i, IsSelfAdjoint (d i).operator)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hnc : ∀ i, ‖(c i).operator‖ ≤ C) (hnd : ∀ i, ‖(d i).operator‖ ≤ D)
    (V : ∀ i, (c i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (W : ∀ i, (d i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (hVW : ∀ i, coefficientExtension (V i) (ripsSpatialOperator r (c i) (hc i)) =
      coefficientExtension (W i) (ripsSpatialOperator r (d i) (hd i))) :
    letI := separatedMetric o
    ripsFamilyBoundaryWithEmbeddings o r hr c hc hF C hC hnc V =
      ripsFamilyBoundaryWithEmbeddings o r hr d hd hG D hD hnd W := by
  let := separatedMetric o
  unfold ripsFamilyBoundaryWithEmbeddings coefficientFamilyBoundary
  apply separatedFamilyBoundary_congr
  exact funext hVW

theorem ampleRipsFamilyBoundary_unitary (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c d : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (e : ∀ i, (c i).UnitaryEquivalent (d i))
    (hc : ∀ i, (c i).representation 1 = 1) (hd : ∀ i, (d i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator) (hG : ∀ i, IsSelfAdjoint (d i).operator)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hnc : ∀ i, ‖(c i).operator‖ ≤ C) (hnd : ∀ i, ‖(d i).operator‖ ≤ D) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr c hc hF C hC hnc =
      ampleRipsFamilyBoundary o r hr d hd hG D hD hnd := by
  let := separatedMetric o
  let V : ∀ i, (c i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
    fun i => ampleIsometry (c i).space
  let W : ∀ i, (d i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
    fun i => (V i).comp (e i).unitary.symm.toLinearIsometry
  calc
    _ = ripsFamilyBoundaryWithEmbeddings o r hr c hc hF C hC hnc V :=
      ampleRipsFamilyBoundary_embeddings o r hr c hc hF C hC hnc V
    _ = ripsFamilyBoundaryWithEmbeddings o r hr d hd hG D hD hnd W :=
      ripsFamilyBoundaryWithEmbeddings_congr o r hr c d hc hd hF hG C D hC hD hnc hnd V W
        (fun i => (ripsExtension_aligned r (e i) (hc i) (hd i) (V i)).symm)
    _ = _ := (ampleRipsFamilyBoundary_embeddings o r hr d hd hG D hD hnd W).symm

end CoarseAssembly.Rips

end

end OAI
