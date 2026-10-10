import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.CocycleCircleMap
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

/-! # Paths in a finite Rips realization

Straight barycentric interpolation in a simplex, including its endpoint
and cocycle-lift formulas. These are paths in the actual realization.+-/

noncomputable section

namespace CoarseAssembly.Rips

open scoped BigOperators
open unitInterval

variable {X : Type*} [PseudoMetricSpace X] {r : ℝ}

@[simp] theorem vertex_weight (x : X) (hr : 0 ≤ r) :
    (vertex x hr).weight = Finsupp.single x 1 := rfl

def interpolate (p q : Point X r)
    (hpq : ∀ x ∈ p.weight.support, ∀ y ∈ q.weight.support, dist x y ≤ r)
    (t : unitInterval) : Point X r where
  weight := (1 - (t : ℝ)) • p.weight + (t : ℝ) • q.weight
  nonneg x := add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (p.nonneg x))
    (mul_nonneg t.2.1 (q.nonneg x))
  total := by
    rw [Finsupp.sum_add_index' (by simp) (by simp),
      Finsupp.sum_smul_index' (by simp), Finsupp.sum_smul_index' (by simp)]
    simp only [smul_eq_mul]
    rw [← Finsupp.mul_sum, ← Finsupp.mul_sum, p.total, q.total]
    ring
  diameter x hx y hy := by
    have support : ∀ z, z ∈ ((1 - (t : ℝ)) • p.weight + (t : ℝ) • q.weight).support →
        z ∈ p.weight.support ∨ z ∈ q.weight.support := by
      intro z hz
      by_contra! h
      have hpz := Finsupp.notMem_support_iff.mp h.1
      have hqz := Finsupp.notMem_support_iff.mp h.2
      simp [Finsupp.mem_support_iff, hpz, hqz] at hz
    rcases support x hx with hx | hx <;> rcases support y hy with hy | hy
    · exact p.diameter x hx y hy
    · exact hpq x hx y hy
    · simpa only [dist_comm] using hpq y hy x hx
    · exact q.diameter x hx y hy

theorem interpolate_continuous (p q : Point X r) (hpq) :
    Continuous (interpolate p q hpq) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  change Continuous (fun t : unitInterval => (1 - (t : ℝ)) * p.weight x + (t : ℝ) * q.weight x)
  fun_prop

@[simp] theorem interpolate_zero (p q : Point X r) (hpq) :
    interpolate p q hpq 0 = p := by
  apply Point.ext
  simp [interpolate]

@[simp] theorem interpolate_one (p q : Point X r) (hpq) :
    interpolate p q hpq 1 = q := by
  apply Point.ext
  simp [interpolate]

def simplexPath (p q : Point X r)
    (hpq : ∀ x ∈ p.weight.support, ∀ y ∈ q.weight.support, dist x y ≤ r) : Path p q where
  toFun := interpolate p q hpq
  continuous_toFun := interpolate_continuous p q hpq
  source' := interpolate_zero p q hpq
  target' := interpolate_one p q hpq

def edgePath {x y : X} (hxy : dist x y ≤ r) :
    Path (vertex x (dist_nonneg.trans hxy)) (vertex y (dist_nonneg.trans hxy)) :=
  simplexPath _ _ (by
    intro u hu v hv
    have hu' : u = x := by simpa using hu
    have hv' : v = y := by simpa using hv
    simpa [hu', hv'] using hxy)

variable [Fintype X]

omit [Fintype X] in
theorem IntegralCocycle.charge_self (c : IntegralCocycle X r) (hr : 0 ≤ r) (x : X) :
    c.charge x x = 0 := by
  have h := c.antisymm x x (by simpa using hr)
  omega

theorem IntegralCocycle.localAngle_vertex (c : IntegralCocycle X r)
    (hr : 0 ≤ r) (x y : X) : c.localAngle x (vertex y hr) = (c.charge x y : ℝ) := by
  classical
  simp [localAngle, Finsupp.single_apply]

@[simp] theorem IntegralCocycle.circleMap_vertex (c : IntegralCocycle X r)
    (hr : 0 ≤ r) (x : X) : c.circleMap (vertex x hr) = 0 := by
  rw [c.circleMap_eq _ (x := x) (by simp)]
  simp [c.localAngle_vertex, c.charge_self hr]

theorem IntegralCocycle.localAngle_interpolate (c : IntegralCocycle X r)
    (x : X) (p q : Point X r) (hpq) (t : unitInterval) :
    c.localAngle x (interpolate p q hpq t) =
      (1 - (t : ℝ)) * c.localAngle x p + (t : ℝ) * c.localAngle x q := by
  simp only [localAngle, interpolate, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- The edge has the real lift `t ↦ t * charge x y`. -/
theorem IntegralCocycle.circleMap_edgePath (c : IntegralCocycle X r)
    {x y : X} (hxy : dist x y ≤ r) (t : unitInterval) :
    c.circleMap (edgePath hxy t) = ((t : ℝ) * (c.charge x y : ℝ) : ℝ) := by
  have hr : 0 ≤ r := dist_nonneg.trans hxy
  by_cases ht : (t : ℝ) = 1
  · have ht' : t = 1 := Subtype.ext ht
    subst t
    simp only [Path.target, c.circleMap_vertex]
    exact ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨c.charge x y, by simp⟩).symm
  · have hx : x ∈ (edgePath hxy t).weight.support := by
      apply Finsupp.mem_support_iff.mpr
      change (1 - (t : ℝ)) * (Finsupp.single x 1 x) +
        (t : ℝ) * (Finsupp.single y 1 x) ≠ 0
      have hpos : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.2.2 ht)
      have hnn : 0 ≤ (Finsupp.single y (1 : ℝ) x) := (vertex y hr).nonneg x
      simpa only [Finsupp.single_eq_same, mul_one] using
        ne_of_gt (add_pos_of_pos_of_nonneg hpos (mul_nonneg t.2.1 hnn))
    rw [c.circleMap_eq _ hx]
    dsimp only [edgePath, simplexPath]
    simp only [Path.coe_mk_mk]
    rw [c.localAngle_interpolate, c.localAngle_vertex, c.localAngle_vertex,
      c.charge_self hr]
    simp

end CoarseAssembly.Rips

end

end OAI
