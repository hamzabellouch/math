import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Short loops and the Rips edge cocycle

The combinatorial step in §4 of the coarse Novikov manuscript. The only
hypothesis on the charge is vanishing on short closed graph walks, exactly
the output required from the manuscript's small-loop lemma. This is a
conditional combinatorial result, not an assumption about analytic K-homology.
-/

namespace CoarseAssembly

variable {V : Type*} {G : SimpleGraph V}

/-- Sum an integer edge charge along an actual graph walk. -/
def walkCharge (a : V → V → ℤ) : {u v : V} → G.Walk u v → ℤ
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => a u v + walkCharge a p

@[simp] theorem walkCharge_nil (a : V → V → ℤ) (u : V) :
    walkCharge a (.nil : G.Walk u u) = 0 := rfl

@[simp] theorem walkCharge_cons (a : V → V → ℤ) {u v w : V}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkCharge a (.cons h p) = a u v + walkCharge a p := rfl

@[simp] theorem walkCharge_append (a : V → V → ℤ) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkCharge a (p.append q) = walkCharge a p + walkCharge a q := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, add_assoc]

@[simp] theorem walkCharge_reverse (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) {u v : V} (p : G.Walk u v) :
    walkCharge a p.reverse = -walkCharge a p := by
  induction p with
  | nil => simp
  | cons h p ih => simp [SimpleGraph.Walk.reverse_cons, ih, ha _ _ h]

/-- Pointwise unit charges give the elementary length bound used to control
both the winding number and the word length in the small-loop argument. -/
theorem walkCharge_abs_le_length (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → |a u v| ≤ 1) {u v : V} (p : G.Walk u v) :
    |walkCharge a p| ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    calc
      |walkCharge a (.cons h p)| ≤ |a _ _| + |walkCharge a p| := abs_add_le _ _
      _ ≤ 1 + (p.length : ℤ) := add_le_add (ha _ _ h) ih
      _ = ((SimpleGraph.Walk.cons h p).length : ℤ) := by simp [add_comm]

/-- Vanishing short loops makes the charge independent of the chosen short
path. The two paths are compared by concatenating one with the reverse of
the other, exactly as in Proposition 4.1. -/
theorem walkCharge_eq_of_short_loops (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 2 * r → walkCharge a p = 0)
    {u v : V} (p q : G.Walk u v) (hp : p.length ≤ r) (hq : q.length ≤ r) :
    walkCharge a p = walkCharge a q := by
  have hlen : (p.append q.reverse).length ≤ 2 * r := by
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    omega
  have hz := hloop u (p.append q.reverse) hlen
  rw [walkCharge_append, walkCharge_reverse a ha] at hz
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hz)

/-- The graph of the edges of the Rips complex of a connected graph at scale
`r`. Connectedness is supplied to results, because graph distance is zero
between disconnected vertices in Mathlib's natural-valued convention. -/
def ripsGraph (G : SimpleGraph V) (r : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.dist u v ≤ r
  symm := ⟨fun u v h => ⟨h.1.symm, (G.dist_comm (u := u) (v := v)) ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def shortestWalk (hG : G.Connected) (u v : V) : G.Walk u v :=
  (hG.exists_walk_length_eq_dist u v).choose

@[simp] theorem shortestWalk_length (hG : G.Connected) (u v : V) :
    (shortestWalk hG u v).length = G.dist u v :=
  (hG.exists_walk_length_eq_dist u v).choose_spec

/-- The charge assigned to an oriented Rips edge, extended to all vertex
pairs by choosing shortest graph walks. -/
noncomputable def ripsCharge (hG : G.Connected) (a : V → V → ℤ) (u v : V) : ℤ :=
  walkCharge a (shortestWalk hG u v)

theorem ripsCharge_eq_walkCharge (hG : G.Connected) (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 2 * r → walkCharge a p = 0)
    {u v : V} (p : G.Walk u v) (hp : p.length ≤ r) :
    ripsCharge hG a u v = walkCharge a p := by
  apply walkCharge_eq_of_short_loops a ha r hloop
  · simpa only [shortestWalk_length] using (G.dist_le p).trans hp
  · exact hp

/-- The Rips charge is antisymmetric whenever loops of length at most `2r`
have zero charge. -/
theorem ripsCharge_antisymm (hG : G.Connected) (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 2 * r → walkCharge a p = 0)
    {u v : V} (huv : G.dist u v ≤ r) :
    ripsCharge hG a v u = -ripsCharge hG a u v := by
  rw [ripsCharge_eq_walkCharge hG a ha r hloop (shortestWalk hG u v).reverse
    (by simpa using huv), walkCharge_reverse a ha]
  rfl

/-- Every triangle in the Rips complex has zero total charge, assuming
vanishing of graph loops of length at most `3r`. This is the cocycle identity
needed for the circle-valued winding test. -/
theorem ripsCharge_triangle (hG : G.Connected) (a : V → V → ℤ) (r : ℕ)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 3 * r → walkCharge a p = 0)
    {u v w : V} (huv : G.dist u v ≤ r) (hvw : G.dist v w ≤ r)
    (hwu : G.dist w u ≤ r) :
    ripsCharge hG a u v + ripsCharge hG a v w + ripsCharge hG a w u = 0 := by
  have hlen : (((shortestWalk hG u v).append (shortestWalk hG v w)).append
      (shortestWalk hG w u)).length ≤ 3 * r := by
    simp only [SimpleGraph.Walk.length_append, shortestWalk_length]
    omega
  have hz := hloop u (((shortestWalk hG u v).append (shortestWalk hG v w)).append
    (shortestWalk hG w u)) hlen
  simpa only [walkCharge_append, ripsCharge] using hz

/-- Unit graph edges retain their original charges in the Rips cocycle. -/
theorem ripsCharge_on_edge (hG : G.Connected) (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 2 * r → walkCharge a p = 0)
    {u v : V} (h : G.Adj u v) : ripsCharge hG a u v = a u v := by
  rw [ripsCharge_eq_walkCharge hG a ha r hloop h.toWalk (by simpa using hr)]
  simp [SimpleGraph.Adj.toWalk]

/-- In particular, the same boundary walk has the same winding charge after
passing to a Rips scale. -/
theorem ripsCharge_on_walk (hG : G.Connected) (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 2 * r → walkCharge a p = 0)
    {u v : V} (p : G.Walk u v) :
    walkCharge (ripsCharge hG a) p = walkCharge a p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [walkCharge_cons, ripsCharge_on_edge hG a ha r hr hloop h, ih]

/-- The finite-scale combinatorial conclusion used in the paper: a charge-one
boundary and vanishing of loops through length `3r` give an antisymmetric
integer Rips cocycle that still evaluates to one on that boundary. -/
theorem exists_rips_cocycle (hG : G.Connected) (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 3 * r → walkCharge a p = 0)
    {u : V} (boundary : G.Walk u u) (hboundary : walkCharge a boundary = 1) :
    ∃ b : V → V → ℤ,
      (∀ x y, G.dist x y ≤ r → b y x = -b x y) ∧
      (∀ x y z, G.dist x y ≤ r → G.dist y z ≤ r → G.dist z x ≤ r →
        b x y + b y z + b z x = 0) ∧ walkCharge b boundary = 1 := by
  have hloop₂ : ∀ x (p : G.Walk x x), p.length ≤ 2 * r → walkCharge a p = 0 := by
    intro x p hp
    apply hloop x p
    omega
  refine ⟨ripsCharge hG a, ?_, ?_, ?_⟩
  · intro x y hxy
    exact ripsCharge_antisymm hG a ha r hloop₂ hxy
  · intro x y z hxy hyz hzx
    exact ripsCharge_triangle hG a r hloop hxy hyz hzx
  · rw [ripsCharge_on_walk hG a ha r hr hloop₂, hboundary]

end CoarseAssembly

end OAI
