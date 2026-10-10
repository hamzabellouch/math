import OAI.Topology.CoarseAssembly.UnitalRepresentative
import OAI.Topology.CoarseAssembly.AmpleRipsFamily

namespace OAI

/-! # Whole-union representatives from arbitrary finite-Rips cycles

Each root gives an evaluation character. The proved unital normalization
removes the unitality and uniform operator-bound premises from the raw
family construction. Descent through all analytic cycle relations remains
a separate obligation.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X : Type} [PseudoMetricSpace X] [Fintype X]

def rootCharacter (r : ℝ) (hr : 0 ≤ r) (o : X) : C(Point X r, ℂ) →⋆ₐ[ℂ] ℂ where
  toFun f := f (vertex o hr)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def normalizedRipsCycle (r : ℝ) (hr : 0 ≤ r) (o : X) (c : OddCycle C(Point X r, ℂ)) :
    OddCycle C(Point X r, ℂ) :=
  (exists_unital_involutive_representative c (rootCharacter r hr o)).choose

theorem normalizedRipsCycle_properties (r : ℝ) (hr : 0 ≤ r) (o : X)
    (c : OddCycle C(Point X r, ℂ)) :
    let d := normalizedRipsCycle r hr o c
    cycleClass _ d = cycleClass _ c ∧ d.representation 1 = 1 ∧
      IsSelfAdjoint d.operator ∧ d.operator * d.operator = 1 ∧ ‖d.operator‖ ≤ 1 :=
  (exists_unital_involutive_representative c (rootCharacter r hr o)).choose_spec

variable {V : ℕ → Type} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-- An actual whole-union Roe class for every family of compact-source
cycles, with all normalization premises discharged. -/
def normalizedRipsFamilyBoundary (o : ∀ i, V i) (r : ℝ) (hr : 0 ≤ r)
    (c : ∀ i, OddCycle C(Point (V i) r, ℂ)) :
    letI := separatedMetric o
    OperatorKTheory.K1 (algebra (X := Sigma V) (H := lp (fun _ : ℕ => ℂ) 2)) :=
  ampleRipsFamilyBoundary o r hr (fun i => normalizedRipsCycle r hr (o i) (c i))
    (fun i => (normalizedRipsCycle_properties r hr (o i) (c i)).2.1)
    (fun i => (normalizedRipsCycle_properties r hr (o i) (c i)).2.2.1)
    1 (by norm_num) (fun i => (normalizedRipsCycle_properties r hr (o i) (c i)).2.2.2.2)

end CoarseAssembly.Rips

end

end OAI
