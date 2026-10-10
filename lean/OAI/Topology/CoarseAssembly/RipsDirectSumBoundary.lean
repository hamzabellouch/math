import OAI.Topology.CoarseAssembly.FamilyBoundaryAddition

namespace OAI

/-! # Direct sums of Fredholm cycles add their whole-union Rips boundaries -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

theorem ripsFamilyBoundaryWithEmbeddings_directSum
    (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c d e : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (h : ∀ i, (c i).IsDirectSum (d i) (e i))
    (hc : ∀ i, (c i).representation 1 = 1) (hd : ∀ i, (d i).representation 1 = 1)
    (he : ∀ i, (e i).representation 1 = 1)
    (hsC : ∀ i, IsSelfAdjoint (c i).operator) (hsD : ∀ i, IsSelfAdjoint (d i).operator)
    (hsE : ∀ i, IsSelfAdjoint (e i).operator)
    (C D K : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hnC : ∀ i, ‖(c i).operator‖ ≤ C) (hnD : ∀ i, ‖(d i).operator‖ ≤ D)
    (hnE : ∀ i, ‖(e i).operator‖ ≤ K)
    (U : ∀ i, (e i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2) :
    letI := separatedMetric o
    ripsFamilyBoundaryWithEmbeddings o r hr e he hsE K hK hnE U =
      ripsFamilyBoundaryWithEmbeddings o r hr c hc hsC C hC hnC
        (fun i => (U i).comp (h i).left) +
      ripsFamilyBoundaryWithEmbeddings o r hr d hd hsD D hD hnD
        (fun i => (U i).comp (h i).right) := by
  let := separatedMetric o
  exact coefficientFamilyBoundary_add o
    (fun i => ripsSpatialOperator r (c i) (hc i))
    (fun i => ripsSpatialOperator r (d i) (hd i))
    (fun i => ripsSpatialOperator r (e i) (he i))
    (C + 2) (D + 2) (K + 2) (by linarith) (by linarith) (by linarith)
    (fun i => (ripsSpatialOperator_norm_le r (c i) (hc i)).trans (by linarith [hnC i]))
    (fun i => (ripsSpatialOperator_norm_le r (d i) (hd i)).trans (by linarith [hnD i]))
    (fun i => (ripsSpatialOperator_norm_le r (e i) (he i)).trans (by linarith [hnE i]))
    (r + r) (add_nonneg hr hr)
    (fun i => ripsSpatialOperator_propagation r hr (c i) (hc i))
    (fun i => ripsSpatialOperator_propagation r hr (d i) (hd i))
    (fun i => ripsSpatialOperator_propagation r hr (e i) (he i))
    (fun i => ripsSpatialOperator_selfAdjoint r (c i) (hc i) (hsC i))
    (fun i => ripsSpatialOperator_selfAdjoint r (d i) (hd i) (hsD i))
    (fun i => ripsSpatialOperator_selfAdjoint r (e i) (he i) (hsE i))
    (fun i => ripsSpatialOperator_square_compact r (c i) (hc i) (hsC i))
    (fun i => ripsSpatialOperator_square_compact r (d i) (hd i) (hsD i))
    (fun i => ripsSpatialOperator_square_compact r (e i) (he i) (hsE i))
    (fun i => (h i).left) (fun i => (h i).right)
    (fun i => (h i).orthogonal) (fun i => (h i).exhaustive)
    (fun i => ripsSpatialOperator_directSum_left r (h i) (hc i) (he i))
    (fun i => ripsSpatialOperator_directSum_right r (h i) (hd i) (he i)) U

theorem ampleRipsFamilyBoundary_directSum
    (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c d e : ∀ i, OddCycle C(Point (Q i) r, ℂ)) (h : ∀ i, (c i).IsDirectSum (d i) (e i))
    (hc : ∀ i, (c i).representation 1 = 1) (hd : ∀ i, (d i).representation 1 = 1)
    (he : ∀ i, (e i).representation 1 = 1)
    (hsC : ∀ i, IsSelfAdjoint (c i).operator) (hsD : ∀ i, IsSelfAdjoint (d i).operator)
    (hsE : ∀ i, IsSelfAdjoint (e i).operator)
    (C D K : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hnC : ∀ i, ‖(c i).operator‖ ≤ C) (hnD : ∀ i, ‖(d i).operator‖ ≤ D)
    (hnE : ∀ i, ‖(e i).operator‖ ≤ K) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr e he hsE K hK hnE =
      ampleRipsFamilyBoundary o r hr c hc hsC C hC hnC +
      ampleRipsFamilyBoundary o r hr d hd hsD D hD hnD := by
  let := separatedMetric o
  let U : ∀ i, (e i).space →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 := fun i => ampleIsometry (e i).space
  calc
    _ = ripsFamilyBoundaryWithEmbeddings o r hr e he hsE K hK hnE U :=
      ampleRipsFamilyBoundary_embeddings o r hr e he hsE K hK hnE U
    _ = ripsFamilyBoundaryWithEmbeddings o r hr c hc hsC C hC hnC
          (fun i => (U i).comp (h i).left) +
        ripsFamilyBoundaryWithEmbeddings o r hr d hd hsD D hD hnD
          (fun i => (U i).comp (h i).right) :=
      ripsFamilyBoundaryWithEmbeddings_directSum o r hr c d e h hc hd he hsC hsD hsE
        C D K hC hD hK hnC hnD hnE U
    _ = _ := congrArg₂ (fun x y => x + y)
      (ampleRipsFamilyBoundary_embeddings o r hr c hc hsC C hC hnC _).symm
      (ampleRipsFamilyBoundary_embeddings o r hr d hd hsD D hD hnD _).symm

end CoarseAssembly.Rips

end

end OAI
