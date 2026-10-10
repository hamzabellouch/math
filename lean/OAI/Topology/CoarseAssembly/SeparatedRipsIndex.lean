import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.AnalyticFamilyIndex
import OAI.Topology.CoarseAssembly.RipsFamilyRestriction
import OAI.Topology.CoarseAssembly.CompactHomotopy

namespace OAI

/-! # A scale index on the actual locally finite analytic domain

Late Rips components are compact and open in the full realization. Their
extension-by-zero homomorphisms give the restriction family used by the
constructed index. Finitely many early components are omitted; compatibility
of this omission across scales is proved separately.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe
open scoped ZeroAtInfty

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

@[simp] theorem separatedRipsIndex_class (o : ∀ i, Q i) (r : ℝ) (hr : 0 ≤ r)
    (c : letI := separatedMetric o; OddCycle C₀(Point (Sigma Q) r, ℂ)) :
    separatedRipsIndex o r hr (cycleClass _ c) =
      (regularizedFamily (fun i => c.precomp (lateRipsFunctionHom o r i))
        (ripsPointCharacter o r hr)).boundary o hr :=
  analyticFamilyIndex_class _ _ _ _ _

end CoarseAssembly.Rips

end

end OAI
