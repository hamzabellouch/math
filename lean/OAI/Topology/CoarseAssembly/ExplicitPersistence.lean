import OAI.Topology.CoarseAssembly.ExplicitCircleFamily
import OAI.Topology.CoarseAssembly.ConcretePersistence

namespace OAI

/-! # Persistence of the explicit circle cycle in the actual graph union -/

noncomputable section

namespace CoarseAssembly

open Topology Congruence Rips Analytic

theorem ripsFamily_restriction_class {V Z : ℕ → Type}
    [∀ j, MetricSpace (V j)] [∀ j, Fintype (V j)]
    [∀ j, TopologicalSpace (Z j)] [∀ j, CompactSpace (Z j)] [∀ j, T2Space (Z j)]
    (o : ∀ j, V j) (r : ℝ) (γ : ∀ j, C(Z j, Point (V j) r))
    (j : ℕ) (hj : r < j) (a : LocallyFiniteK1 (Sigma Z)) :
    letI := separatedMetric o
    restrictComponent (separatedRipsEmbedding o r j) (separatedRipsEmbedding_open o r j hj)
      (pushforward (ripsFamilyMap o r γ) a) =
        pushforward (compactMap (γ j))
          (restrictComponent (sigmaComponent Z j) (sigmaComponent_open Z j) a) := by
  let := separatedMetric o
  exact DFunLike.congr_fun (restrictComponent_natural
    (sigmaComponent Z j) (sigmaComponent_open Z j)
    (separatedRipsEmbedding o r j) (separatedRipsEmbedding_open o r j hj)
    (ripsFamilyMap o r γ) (compactMap (γ j)) (fun _ => rfl)
    (ripsFamily_component_preimage o r γ j)) a

local instance explicitPersistenceComponent (j : ℕ) : MetricSpace (FiberVertex j) :=
  componentMetric elementaryMoves chosenHolonomyUnit j
local instance explicitPersistenceMetric : MetricSpace FiberedUnion :=
  componentUnionMetric elementaryMoves chosenHolonomyUnit

def explicitFiberLoops (r : ℕ) (hr : 1 ≤ r) :=
  fiberedBoundaryLoops elementaryMoves
    (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit) r hr

def explicitFiberStage (r : ℕ) (hr : 1 ≤ r) :
    LocallyFiniteK1 (Point FiberedUnion (r : ℝ)) :=
  pushforward (ripsFamilyMap fiberBoundaryBase r (explicitFiberLoops r hr)) explicitCircleFamily

theorem explicitFiberStage_coarsen {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : r ≤ s) :
    pushforward (inclusion (by exact_mod_cast hrs)) (explicitFiberStage r hr) =
      explicitFiberStage s hs := by
  change pushforward _ (pushforward _ explicitCircleFamily) = _
  dsimp only [explicitFiberLoops]
  rw [← AddMonoidHom.comp_apply, ← pushforward_comp,
    ripsFamilyMap_coarsen fiberBoundaryBase _ _ _
      (fiberedBoundaryLoops_coarsen elementaryMoves
        (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit) hr hs hrs)]
  rfl

theorem explicitFiberStage_detected (r : ℕ) (hr : 1 ≤ r) :
    ∃ test : LocallyFiniteK1 (Point FiberedUnion (r : ℝ)) →+ ℤ,
      test (explicitFiberStage r hr) = 1 := by
  obtain ⟨J, hJ⟩ := fiberedGraph_short_loops elementaryMoves (3 * r)
  let j := max J (r + 2)
  have hj : (r : ℝ) < j := by
    have h : r < j := by dsimp [j]; omega
    exact_mod_cast h
  have hj₂ : 2 ≤ j := by dsimp [j]; omega
  have hloop := hJ j (by dsimp [j]; omega)
  let c := graphRipsCocycle (fiberedGraph_connected elementaryMoves chosenHolonomyUnit j)
    fiberCharge (fun x y _ => latticeCharge_reverse _ _) r hloop
  let d := separatedRipsEmbedding fiberBoundaryBase (r : ℝ) j
  have hd := separatedRipsEmbedding_open fiberBoundaryBase (r : ℝ) j hj
  refine ⟨(provedCircleInput.pairing c.toContinuousMap).comp (restrictComponent d hd), ?_⟩
  change provedCircleInput.pairing c.toContinuousMap
    (restrictComponent d hd (explicitFiberStage r hr)) = 1
  rw [explicitFiberStage, ripsFamily_restriction_class fiberBoundaryBase (r : ℝ)
    (explicitFiberLoops r hr) j hj, explicitCircleFamily_coordinate]
  change provedCircleInput.pairing c.toContinuousMap
    (graphLoopClass provedCircleInput
      (fiberedGraph_connected elementaryMoves chosenHolonomyUnit j) r hr
      (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit j)) = 1
  rw [graph_loop_index provedCircleInput _ fiberCharge
    (fun x y _ => latticeCharge_reverse _ _) r hr hloop,
    hexagonalBoundaryWalks.fiber_charge_one elementaryMoves chosenHolonomyUnit j hj₂]

def explicitFiberClass : KX1 FiberedUnion :=
  (coarsening FiberedUnion).of 1 (explicitFiberStage 1 le_rfl)

theorem explicitFiberClass_infinite_order (n : ℤ) (hn : n ≠ 0) :
    n • explicitFiberClass ≠ 0 := by
  let C := coarsening FiberedUnion
  let test := fun r hr => (explicitFiberStage_detected r hr).choose
  have hdetect : ∀ r (hr : 1 ≤ r),
      test r hr (C.map 1 r hr (explicitFiberStage 1 le_rfl)) = 1 := by
    intro r hr
    change test r hr (pushforward (inclusion (by exact_mod_cast hr))
      (explicitFiberStage 1 le_rfl)) = 1
    rw [explicitFiberStage_coarsen le_rfl hr hr]
    exact (explicitFiberStage_detected r hr).choose_spec
  exact persistent_multiples_ne_zero C.map 1 (explicitFiberStage 1 le_rfl) test hdetect n hn

end CoarseAssembly

end

end OAI
