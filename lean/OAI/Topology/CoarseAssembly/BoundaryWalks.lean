import OAI.Topology.CoarseAssembly.BoundaryGeometry
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

namespace OAI

/-! # Boundary walks and their canonical lifts

Depth-zero fibers are singletons, so every edge of the actual boundary
subgraph has its unique lift. The walk construction and charge comparison
here leave only the explicit hexagonal boundary walk to be supplied.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

def BoundaryComponent (j : ℕ) := {u : Disc j // discDepth j u = 0}

noncomputable instance (j : ℕ) : Fintype (BoundaryComponent j) :=
  inferInstanceAs (Fintype {u : Disc j // discDepth j u = 0})

def boundaryGraph (j : ℕ) : SimpleGraph (BoundaryComponent j) :=
  (discGraph j).induce {u | discDepth j u = 0}

def boundaryRoot (j : ℕ) : BoundaryComponent j := ⟨discBoundaryBase j, discBoundaryBase_depth j⟩

def boundaryFiberEmbedding (j : ℕ) : BoundaryComponent j ↪ FiberVertex j where
  toFun u := ⟨u.val, 1⟩
  inj' _ _ h := Subtype.ext (congrArg Sigma.fst h)

theorem boundaryFiber_adj (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) {j : ℕ}
    {u v : BoundaryComponent j} (h : (boundaryGraph j).Adj u v) :
    (fiberedGraph S t j).Adj (boundaryFiberEmbedding j u) (boundaryFiberEmbedding j v) := by
  refine ⟨?_, 1, one_mem_symmetricMoves S, Or.inr ⟨h, rfl⟩, ?_⟩
  · intro he
    have huv := (boundaryFiberEmbedding j).injective he
    exact h.2.2.2 (congrArg (fun w : BoundaryComponent j => w.val.val) huv)
  · intro l hl _
    have hl0 : l = 0 := by
      change l ≤ discDepth j u.val at hl
      rw [u.property] at hl
      omega
    subst l
    exact Subsingleton.elim _ _

def boundaryFiberHom (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (j : ℕ) :
    boundaryGraph j →g fiberedGraph S t j where
  toFun := boundaryFiberEmbedding j
  map_rel' := boundaryFiber_adj S t

def boundaryBaseHom (j : ℕ) : boundaryGraph j →g discGraph j :=
  (SimpleGraph.Embedding.induce _).toHom

theorem walkCharge_map {X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    (f : G →g H) (a : Y → Y → ℤ) {u v : X} (p : G.Walk u v) :
    walkCharge a (p.map f) = walkCharge (fun x y => a (f x) (f y)) p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [SimpleGraph.Walk.map_cons, walkCharge_cons, ih]

theorem walkCharge_copy {X : Type*} {G : SimpleGraph X} (a : X → X → ℤ)
    {u v u' v' : X} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    walkCharge a (p.copy hu hv) = walkCharge a p := by
  subst u' v'
  rfl

theorem boundary_walk_charge (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) {j : ℕ}
    {u v : BoundaryComponent j} (p : (boundaryGraph j).Walk u v) :
    walkCharge fiberCharge (p.map (boundaryFiberHom S t j)) =
      walkCharge (fun x y : Disc j => latticeCharge x.val y.val) (p.map (boundaryBaseHom j)) := by
  rw [walkCharge_map, walkCharge_map]
  rfl

/-- Geometric data still to be constructed from the six sides of the
hexagon. These are own-paper obligations, not a published-input interface. -/
structure HexagonalBoundaryWalks where
  walk : ∀ j, (boundaryGraph j).Walk (boundaryRoot j) (boundaryRoot j)
  charge_one : ∀ j, 2 ≤ j →
    walkCharge (fun x y : Disc j => latticeCharge x.val y.val)
      ((walk j).map (boundaryBaseHom j)) = 1

def HexagonalBoundaryWalks.fiberWalk (w : HexagonalBoundaryWalks)
    (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (j : ℕ) :
    (fiberedGraph S t j).Walk (fiberBoundaryBase j) (fiberBoundaryBase j) :=
  (w.walk j).map (boundaryFiberHom S t j)

theorem HexagonalBoundaryWalks.fiber_charge_one (w : HexagonalBoundaryWalks)
    (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (j : ℕ) (hj : 2 ≤ j) :
    walkCharge fiberCharge (w.fiberWalk S t j) = 1 := by
  exact (boundary_walk_charge S t (w.walk j)).trans (w.charge_one j hj)

end CoarseAssembly

end

end OAI
