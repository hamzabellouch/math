import OAI.Topology.CoarseAssembly.PartitionCompactPerturbation
import OAI.Topology.CoarseAssembly.SeparatedFamilyPerturbation

namespace OAI

/-! # Compact cycle perturbations preserve the whole-union Rips boundary -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

theorem ampleRipsFamilyBoundary_eq_of_compact (o : ∀ i, V i) (r : ℝ) (hr : 0 ≤ r)
    (c d : ∀ i, OddCycle C(Point (V i) r, ℂ))
    (hπ : ∀ i, (c i).representation 1 = 1) (hρ : ∀ i, (d i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator) (hG : ∀ i, IsSelfAdjoint (d i).operator)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : ∀ i, ‖(c i).operator‖ ≤ C) (hd : ∀ i, ‖(d i).operator‖ ≤ D)
    (hcd : ∀ i, IsCompactOperator (ampleRipsOperator r (c i) (hπ i) -
      ampleRipsOperator r (d i) (hρ i))) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr c hπ hF C hC hc =
      ampleRipsFamilyBoundary o r hr d hρ hG D hD hd := by
  let := separatedMetric o
  exact separatedFamilyBoundary_eq_of_component_compact o
    (fun i => ampleRipsOperator r (c i) (hπ i))
    (fun i => ampleRipsOperator r (d i) (hρ i))
    (C + 4) (D + 4) (by linarith) (by linarith)
    (fun i => (ampleRipsOperator_norm_le r (c i) (hπ i)).trans (by linarith [hc i]))
    (fun i => (ampleRipsOperator_norm_le r (d i) (hρ i)).trans (by linarith [hd i]))
    (r + r) (r + r) (add_nonneg hr hr) (add_nonneg hr hr)
    (fun i => ampleRipsOperator_propagation r hr (c i) (hπ i))
    (fun i => ampleRipsOperator_propagation r hr (d i) (hρ i))
    (fun i => ampleRipsOperator_selfAdjoint r (c i) (hπ i) (hF i))
    (fun i => ampleRipsOperator_selfAdjoint r (d i) (hρ i) (hG i))
    (fun i => ampleRipsOperator_square_compact r (c i) (hπ i) (hF i))
    (fun i => ampleRipsOperator_square_compact r (d i) (hρ i) (hG i)) hcd

theorem ampleRipsFamilyBoundary_compactPerturb (o : ∀ i, V i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (V i) r, ℂ)) (K : ∀ i, End (c i).space)
    (hK : ∀ i, IsCompactOperator (K i))
    (hKs : ∀ i, IsCompactOperator (star (K i) : End (c i).space))
    (hπ : ∀ i, (c i).representation 1 = 1)
    (hF : ∀ i, IsSelfAdjoint (c i).operator)
    (hG : ∀ i, IsSelfAdjoint ((c i).operator + K i))
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hc : ∀ i, ‖(c i).operator‖ ≤ C) (hd : ∀ i, ‖(c i).operator + K i‖ ≤ D) :
    letI := separatedMetric o
    ampleRipsFamilyBoundary o r hr (fun i => (c i).compactPerturb (K i) (hK i) (hKs i))
      hπ hG D hD hd = ampleRipsFamilyBoundary o r hr c hπ hF C hC hc := by
  let := separatedMetric o
  apply ampleRipsFamilyBoundary_eq_of_compact
  exact fun i => ampleRipsOperator_compactPerturb r (c i) (hπ i) (K i) (hK i) (hKs i)

end CoarseAssembly.Rips

end

end OAI
