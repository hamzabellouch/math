import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.BoundaryComponents
import OAI.Topology.CoarseAssembly.HexagonSides
import OAI.Topology.CoarseAssembly.RipsMapCalculus
import OAI.Topology.CoarseAssembly.FamilyFilling
import OAI.Topology.CoarseAssembly.FiberedPersistence
import OAI.Topology.CoarseAssembly.KazhdanInput
import OAI.Topology.CoarseAssembly.ConcretePersistence
import OAI.Topology.CoarseAssembly.RipsRealClass

namespace OAI

/-! # The same boundary family maps to the filled base and detected total space

The source class is defined on the actual boundary Rips complex. Its base
image is identified with the previously constructed filled loop family.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

local instance boundaryLoopMetric1 (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit j
local instance boundaryLoopMetric2 (j : ℕ) : PseudoMetricSpace (BoundaryComponent j) :=
  (boundaryComponentMetric elementaryMoves chosenHolonomyUnit j).toPseudoMetricSpace
local instance boundaryLoopMetric3 : MetricSpace (Sigma BoundaryComponent) :=
  boundaryComponentsMetric elementaryMoves chosenHolonomyUnit
local instance boundaryLoopMetric4 : MetricSpace BoundaryVertex := boundaryMetric elementaryMoves chosenHolonomyUnit
local instance boundaryLoopMetric5 : PseudoMetricSpace BoundaryVertex :=
  (boundaryMetric elementaryMoves chosenHolonomyUnit).toPseudoMetricSpace
local instance boundaryLoopMetric6 (j : ℕ) : MetricSpace (FiberVertex j) :=
  componentMetric elementaryMoves chosenHolonomyUnit j
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric7

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric8

theorem totalToFiber_dist (x y : VertexUnion) : dist (totalToFiber x) (totalToFiber y) = dist x y := rfl

def boundaryLoops (j : ℕ) : C(WindingCircle, Point (BoundaryComponent j) 1) :=
  loopCircle (walkPath (by norm_num) (boundaryEdgeBound elementaryMoves chosenHolonomyUnit)
    (hexagonalWalk j))

def boundaryLoopStage (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) : LocallyFiniteK1 (Point BoundaryVertex 1) :=
  pushforward (boundaryFamilyMap elementaryMoves chosenHolonomyUnit 1 boundaryLoops)
    (boundaryCircleFamily input hadd)

def boundaryLoopClass (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) : KX1 BoundaryVertex :=
  classAt 1 1 (by norm_num) (boundaryLoopStage input hadd)

def boundaryComponentToBase (j : ℕ) : BoundaryComponent j ↪ Disc j :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem boundaryComponentToBase_nonexpanding (j : ℕ) (x y : BoundaryComponent j) :
    dist (boundaryComponentToBase j x) (boundaryComponentToBase j y) ≤ dist x y :=
  fiberProjection_nonexpanding elementaryMoves chosenHolonomyUnit j
    (boundaryFiberEmbedding j x) (boundaryFiberEmbedding j y)

def concreteBaseWalk (j : ℕ) :
    (discGraph j).Walk (discBoundaryBase j) (discBoundaryBase j) :=
  (hexagonalWalk j).map (boundaryBaseHom j)

theorem boundaryLoop_base (j : ℕ) (z : WindingCircle) :
    mapPoint (boundaryComponentToBase j) (boundaryComponentToBase_nonexpanding j)
      (boundaryLoops j z) = baseBoundaryLoops discBoundaryBase concreteBaseWalk j z := by
  exact mapPoint_loopCircle (boundaryComponentToBase j) (boundaryComponentToBase_nonexpanding j)
    (fun _ _ h => h) (by norm_num) (boundaryEdgeBound elementaryMoves chosenHolonomyUnit)
    discEdgeBound (hexagonalWalk j) z

theorem boundaryFamily_toBase :
    (embeddingMap boundaryToBase
      (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit) 1).comp
        (boundaryFamilyMap elementaryMoves chosenHolonomyUnit 1 boundaryLoops) =
      ripsFamilyMap discBoundaryBase 1 (baseBoundaryLoops discBoundaryBase concreteBaseWalk) := by
  apply CocompactMap.ext
  rintro ⟨j, z⟩
  change mapPoint boundaryToBase (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)
    (mapPoint boundaryReindex.toEmbedding
      (fun x y => (boundaryReindex_dist elementaryMoves chosenHolonomyUnit x y).le)
      (mapPoint (separatedComponent j)
        (fun x y => ((separatedComponent_isometry boundaryRoot j).dist_eq x y).le)
        (boundaryLoops j z))) =
    mapPoint (separatedComponent j)
      (fun x y => ((separatedComponent_isometry discBoundaryBase j).dist_eq x y).le)
      (baseBoundaryLoops discBoundaryBase concreteBaseWalk j z)
  rw [← boundaryLoop_base j z]
  apply Point.ext
  simp only [mapPoint_weight]
  simp only [← Finsupp.embDomain_trans_apply]
  have he : ((separatedComponent j).trans boundaryReindex.toEmbedding).trans boundaryToBase =
      (boundaryComponentToBase j).trans (separatedComponent j) := by
    apply Function.Embedding.ext
    intro x
    rfl
  rw [he]

theorem boundaryLoopStage_base_zero (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily)
    (homotopy : PublishedCompactHomotopyInput) (hfill : CountableAdditivityInput FilledDisc) :
    pushforward (embeddingMap boundaryToBase
      (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit) 1)
      (boundaryLoopStage input hadd) = 0 := by
  change pushforward _ (pushforward _ (boundaryCircleFamily input hadd)) = 0
  rw [← AddMonoidHom.comp_apply, ← pushforward_comp, boundaryFamily_toBase]
  exact baseBoundaryFamily_zero discBoundaryBase concreteBaseWalk homotopy hfill _

def realFiberLoops (r : ℝ) (hr : 1 ≤ r) (j : ℕ) :
    C(WindingCircle, Point (FiberVertex j) r) := by
  exact loopCircle (walkPath (le_trans (by norm_num) hr)
    (fun x y h => by
      have he := graphEdgeBound (fiberedGraph_connected elementaryMoves chosenHolonomyUnit j)
        1 le_rfl x y h
      have he' : dist x y ≤ 1 := by simpa only [Nat.cast_one] using he
      exact he'.trans hr)
    (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit j))

def fiberLoopsOne := realFiberLoops 1 le_rfl

def realFiberStage (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) (r : ℝ) (hr : 1 ≤ r) :
    LocallyFiniteK1 (Point FiberedUnion r) :=
  pushforward (ripsFamilyMap fiberBoundaryBase r (realFiberLoops r hr))
    (boundaryCircleFamily input hadd)

theorem realFiberStage_cast (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) (n : ℕ) (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) (h : r = (n : ℝ)) :
    (h ▸ realFiberStage input hadd r hr) =
      fiberedBoundaryStage elementaryMoves
        (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit) input hadd n hn := by
  subst r
  rfl

theorem boundaryLoop_fiber (j : ℕ) (z : WindingCircle) :
    mapPoint (boundaryFiberEmbedding j) (fun _ _ => le_rfl) (boundaryLoops j z) =
      fiberLoopsOne j z := by
  have h := mapPoint_loopCircle (boundaryFiberEmbedding j) (fun _ _ => le_rfl)
    (fun _ _ h => boundaryFiber_adj elementaryMoves chosenHolonomyUnit h) (by norm_num)
    (boundaryEdgeBound elementaryMoves chosenHolonomyUnit)
    (fun x y h => by
      have he := graphEdgeBound (fiberedGraph_connected elementaryMoves chosenHolonomyUnit j)
        1 le_rfl x y h
      simpa only [Nat.cast_one] using he)
    (hexagonalWalk j) z
  exact h

theorem boundaryFamily_toFiber :
    (embeddingMap totalToFiber.toEmbedding (fun x y => (totalToFiber_dist x y).le) 1).comp
      ((embeddingMap boundaryToVertex
        (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit) 1).comp
        (boundaryFamilyMap elementaryMoves chosenHolonomyUnit 1 boundaryLoops)) =
      ripsFamilyMap fiberBoundaryBase 1 fiberLoopsOne := by
  apply CocompactMap.ext
  rintro ⟨j, z⟩
  change mapPoint totalToFiber.toEmbedding (fun x y => (totalToFiber_dist x y).le)
    (mapPoint boundaryToVertex (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)
      (mapPoint boundaryReindex.toEmbedding
        (fun x y => (boundaryReindex_dist elementaryMoves chosenHolonomyUnit x y).le)
        (mapPoint (separatedComponent j)
          (fun x y => ((separatedComponent_isometry boundaryRoot j).dist_eq x y).le)
          (boundaryLoops j z)))) =
    mapPoint (separatedComponent j)
      (fun x y => ((separatedComponent_isometry fiberBoundaryBase j).dist_eq x y).le)
      (fiberLoopsOne j z)
  rw [← boundaryLoop_fiber j z]
  apply Point.ext
  simp only [mapPoint_weight]
  simp only [← Finsupp.embDomain_trans_apply]
  have he : (((separatedComponent j).trans boundaryReindex.toEmbedding).trans boundaryToVertex).trans
      totalToFiber.toEmbedding = (boundaryFiberEmbedding j).trans (separatedComponent j) := by
    apply Function.Embedding.ext
    intro x
    rfl
  rw [he]

end CoarseAssembly

end

end OAI
