import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.FiniteWindingIndex
import OAI.Topology.CoarseAssembly.RipsFamilyRestriction
import OAI.Topology.CoarseAssembly.RipsPathCoarsening
import OAI.Topology.CoarseAssembly.ConcreteSpaces
import OAI.Topology.CoarseAssembly.Persistence

namespace OAI

/-! # Persistence in the actual congruence-fiber graph family

The arithmetic small-loop theorem, finite-component circle index and exact
family restriction are combined here. Boundary walks remain explicit
geometric arguments; they are not labeled as published inputs. The only
published inputs in the resulting detector are the stated circle pairing
and countable first-variable additivity.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

abbrev CircleFamily := fun _ : ℕ => WindingCircle

def boundaryCircleFamily (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) : LocallyFiniteK1 (Sigma CircleFamily) :=
  familyClass CircleFamily hadd (fun _ => input.fundamental)

variable (S : Finset ArithmeticGroup)
  (boundary : ∀ j, (fiberedGraph S chosenHolonomyUnit j).Walk
    (fiberBoundaryBase j) (fiberBoundaryBase j))

def fiberedBoundaryLoops (r : ℕ) (hr : 1 ≤ r) :
    letI := componentMetric S chosenHolonomyUnit
    ∀ j, C(WindingCircle, Point (FiberVertex j) (r : ℝ)) := by
  let := componentMetric S chosenHolonomyUnit
  intro j
  exact loopCircle (walkPath (by positivity)
    (graphEdgeBound (fiberedGraph_connected S chosenHolonomyUnit j) r hr) (boundary j))

def fiberedBoundaryStage (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) (r : ℕ) (hr : 1 ≤ r) :
    letI := componentUnionMetric S chosenHolonomyUnit
    LocallyFiniteK1 (Point FiberedUnion (r : ℝ)) := by
  let := componentMetric S chosenHolonomyUnit
  let := componentUnionMetric S chosenHolonomyUnit
  exact pushforward (ripsFamilyMap fiberBoundaryBase r (fiberedBoundaryLoops S boundary r hr))
    (boundaryCircleFamily input hadd)

theorem fiberedBoundaryLoops_coarsen {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : r ≤ s) :
    letI := componentMetric S chosenHolonomyUnit
    ∀ j z, coarsen (by exact_mod_cast hrs) (fiberedBoundaryLoops S boundary r hr j z) =
      fiberedBoundaryLoops S boundary s hs j z := by
  let := componentMetric S chosenHolonomyUnit
  intro j z
  have hrs' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  have h := coarsen_loopCircle hrs' (by positivity : (0 : ℝ) ≤ r)
    (graphEdgeBound (fiberedGraph_connected S chosenHolonomyUnit j) r hr) (boundary j)
  exact DFunLike.congr_fun h z

theorem fiberedBoundaryStage_coarsen (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) {r s : ℕ}
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : r ≤ s) :
    letI := componentUnionMetric S chosenHolonomyUnit
    pushforward (inclusion (by exact_mod_cast hrs))
      (fiberedBoundaryStage S boundary input hadd r hr) =
        fiberedBoundaryStage S boundary input hadd s hs := by
  let := componentMetric S chosenHolonomyUnit
  let := componentUnionMetric S chosenHolonomyUnit
  change (pushforward (inclusion _))
    ((pushforward (ripsFamilyMap fiberBoundaryBase r (fiberedBoundaryLoops S boundary r hr)))
      (boundaryCircleFamily input hadd)) = _
  rw [← AddMonoidHom.comp_apply, ← pushforward_comp,
    ripsFamilyMap_coarsen fiberBoundaryBase _ _ _
      (fiberedBoundaryLoops_coarsen S boundary hr hs hrs)]
  rfl

/-- Every integer scale has a detector of the same boundary family, using
the proved eventual small-loop theorem for the actual finite graphs. -/
theorem fiberedBoundaryStage_detected (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily)
    (hboundary : ∀ j, 2 ≤ j → walkCharge fiberCharge (boundary j) = 1)
    (r : ℕ) (hr : 1 ≤ r) :
    letI := componentUnionMetric S chosenHolonomyUnit
    ∃ test : LocallyFiniteK1 (Point FiberedUnion (r : ℝ)) →+ ℤ,
      test (fiberedBoundaryStage S boundary input hadd r hr) = 1 := by
  let := componentMetric S chosenHolonomyUnit
  let := componentUnionMetric S chosenHolonomyUnit
  obtain ⟨J, hJ⟩ := fiberedGraph_short_loops S (3 * r)
  let j := max J (r + 2)
  have hj : (r : ℝ) < j := by
    have h : r < j := by dsimp [j]; omega
    exact_mod_cast h
  have hj₂ : 2 ≤ j := by dsimp [j]; omega
  have hloop := hJ j (by dsimp [j]; omega)
  let c := graphRipsCocycle (fiberedGraph_connected S chosenHolonomyUnit j) fiberCharge
    (fun x y _ => latticeCharge_reverse _ _) r hloop
  let d := separatedRipsEmbedding fiberBoundaryBase (r : ℝ) j
  have hd := separatedRipsEmbedding_open fiberBoundaryBase (r : ℝ) j hj
  refine ⟨(input.pairing c.toContinuousMap).comp (restrictComponent d hd), ?_⟩
  change input.pairing c.toContinuousMap
    (restrictComponent d hd (fiberedBoundaryStage S boundary input hadd r hr)) = 1
  have hc := ripsFamily_restriction fiberBoundaryBase (r : ℝ)
    (fiberedBoundaryLoops S boundary r hr) j hj hadd (fun _ => input.fundamental)
  rw [show restrictComponent d hd (fiberedBoundaryStage S boundary input hadd r hr) =
      pushforward (compactMap (fiberedBoundaryLoops S boundary r hr j)) input.fundamental
      from hc]
  change input.pairing c.toContinuousMap
    (graphLoopClass input (fiberedGraph_connected S chosenHolonomyUnit j) r hr (boundary j)) = 1
  rw [graph_loop_index input _ fiberCharge (fun x y _ => latticeCharge_reverse _ _) r hr hloop,
    hboundary j hj₂]

def fiberedBoundaryClass (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) :
    letI := componentUnionMetric S chosenHolonomyUnit
    KX1 FiberedUnion := by
  let := componentUnionMetric S chosenHolonomyUnit
  exact (coarsening FiberedUnion).of 1 (fiberedBoundaryStage S boundary input hadd 1 le_rfl)

/-- The same global class has no nonzero integer annihilator. The boundary
walks and their charge-one proofs are geometric arguments still to be
instantiated; the small-loop and analytic restriction bridges are proved. -/
theorem fiberedBoundaryClass_infinite_order (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily)
    (hboundary : ∀ j, 2 ≤ j → walkCharge fiberCharge (boundary j) = 1)
    (n : ℤ) (hn : n ≠ 0) :
    letI := componentUnionMetric S chosenHolonomyUnit
    n • fiberedBoundaryClass S boundary input hadd ≠ 0 := by
  let := componentUnionMetric S chosenHolonomyUnit
  let C := coarsening FiberedUnion
  let test := fun r hr => (fiberedBoundaryStage_detected S boundary input hadd hboundary r hr).choose
  have hdetect : ∀ r (hr : 1 ≤ r),
      test r hr (C.map 1 r hr (fiberedBoundaryStage S boundary input hadd 1 le_rfl)) = 1 := by
    intro r hr
    change test r hr (pushforward (inclusion (by exact_mod_cast hr))
      (fiberedBoundaryStage S boundary input hadd 1 le_rfl)) = 1
    rw [fiberedBoundaryStage_coarsen S boundary input hadd le_rfl hr hr]
    exact (fiberedBoundaryStage_detected S boundary input hadd hboundary r hr).choose_spec
  exact persistent_multiples_ne_zero C.map 1
    (fiberedBoundaryStage S boundary input hadd 1 le_rfl) test hdetect n hn

theorem fiberedBoundaryClass_rational_ne_zero (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily)
    (hboundary : ∀ j, 2 ≤ j → walkCharge fiberCharge (boundary j) = 1) :
    letI := componentUnionMetric S chosenHolonomyUnit
    (1 : ℚ) ⊗ₜ[ℤ] fiberedBoundaryClass S boundary input hadd ≠ 0 := by
  let := componentUnionMetric S chosenHolonomyUnit
  exact rationalization_ne_zero _
    (fiberedBoundaryClass_infinite_order S boundary input hadd hboundary)

end CoarseAssembly

end

end OAI
