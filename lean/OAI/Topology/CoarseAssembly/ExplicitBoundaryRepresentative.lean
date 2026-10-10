import OAI.Topology.CoarseAssembly.AmpleRipsFamily
import OAI.Topology.CoarseAssembly.ExplicitBoundaryConclusion

namespace OAI

/-! # The actual Roe representative of the counterexample's boundary cycle

This constructs the index representative from the explicit circle Fredholm
operator and the paper's hexagonal loops. Identification with the descended
canonical coarse assembly map remains a separate theorem.
-/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

variable {X : Type} [PseudoMetricSpace X] [Fintype X]

def circleRipsCycle (r : ℝ) (γ : C(WindingCircle, Point X r)) : OddCycle C(Point X r, ℂ) :=
  windingCircleCycle.precomp (ContinuousMap.compStarAlgHom' ℂ ℂ γ).toNonUnitalStarAlgHom

theorem circleRipsCycle_unital (r : ℝ) (γ : C(WindingCircle, Point X r)) :
    (circleRipsCycle r γ).representation 1 = 1 := by
  change circleRepresentation 1 = 1
  exact map_one _

theorem circleRipsCycle_selfAdjoint (r : ℝ) (γ : C(WindingCircle, Point X r)) :
    IsSelfAdjoint (circleRipsCycle r γ).operator := negativeCircleOperator_selfAdjoint

theorem circleRipsCycle_norm (r : ℝ) (γ : C(WindingCircle, Point X r)) :
    ‖(circleRipsCycle r γ).operator‖ ≤ 1 := windingCircleCycle_norm

local instance explicitRepComponentDecidableEq (j : ℕ) : DecidableEq (BoundaryComponent j) :=
  Classical.decEq _

local instance explicitRepComponentMetric (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit j
local instance explicitRepComponentPseudoMetric (j : ℕ) : PseudoMetricSpace (BoundaryComponent j) :=
  (boundaryComponentMetric elementaryMoves chosenHolonomyUnit j).toPseudoMetricSpace
local instance explicitRepUnionMetric : MetricSpace (Sigma BoundaryComponent) :=
  boundaryComponentsMetric elementaryMoves chosenHolonomyUnit
local instance explicitRepBoundaryMetric : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
local instance explicitRepBoundaryPseudoMetric : PseudoMetricSpace BoundaryVertex :=
  (boundaryMetric elementaryMoves chosenHolonomyUnit).toPseudoMetricSpace

def explicitBoundaryCycle (j : ℕ) : OddCycle C(Point (BoundaryComponent j) 1, ℂ) :=
  circleRipsCycle 1 (boundaryLoops j)

def explicitBoundaryFamilyRepresentative :
    OperatorKTheory.K1 (algebra (X := Sigma BoundaryComponent) (H := AmpleSpace)) :=
  ampleRipsFamilyBoundary boundaryRoot 1 (by norm_num) explicitBoundaryCycle
    (fun j => circleRipsCycle_unital 1 (boundaryLoops j))
    (fun j => circleRipsCycle_selfAdjoint 1 (boundaryLoops j))
    1 (by norm_num) (fun j => circleRipsCycle_norm 1 (boundaryLoops j))

def boundaryReindexRoeHom :
    algebra (X := Sigma BoundaryComponent) (H := AmpleSpace) →⋆ₙₐ[ℂ] BoundaryRoe :=
  inclusionHom boundaryReindex.toEmbedding
    (fun x y => (boundaryReindex_dist elementaryMoves chosenHolonomyUnit x y).le)

/-- A concrete class in the same reduced Roe algebra used by the conditional
assembly diagram. Canonical assembly identification is not presumed here. -/
def explicitBoundaryRoeRepresentative : OperatorKTheory.K1 BoundaryRoe :=
  OperatorKTheory.map boundaryReindexRoeHom explicitBoundaryFamilyRepresentative

def explicitBaseRoeRepresentative : OperatorKTheory.K1 BaseRoe :=
  OperatorKTheory.map boundaryBaseRoeHom explicitBoundaryRoeRepresentative

def explicitTotalRoeRepresentative : OperatorKTheory.K1 TotalRoe :=
  OperatorKTheory.map boundaryTotalRoeHom explicitBoundaryRoeRepresentative

/-- The constructed representative satisfies the previously proved spatial
transfer identity. Its base vanishing still requires the assembly descent. -/
theorem explicitRoeRepresentative_transfer (hgap : PublishedKazhdanInput) :
    OperatorKTheory.map (transferRoeHom hgap) explicitBaseRoeRepresentative =
      explicitTotalRoeRepresentative :=
  DFunLike.congr_fun (transferK1_boundary hgap) explicitBoundaryRoeRepresentative

end CoarseAssembly

end

end OAI
