import OAI.Topology.CoarseAssembly.RipsRealization
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# The circle map of an integral Rips cocycle

On each finite component, barycentric interpolation of an integral edge
cocycle defines a genuine continuous map to `ℝ / ℤ`. The local real lifts
differ by the integral edge charge. This constructs the winding test in
the manuscript, rather than assuming its topological extension.
-/

noncomputable section

namespace CoarseAssembly.Rips

open scoped BigOperators
open Topology

variable {X : Type*} [PseudoMetricSpace X] {r : ℝ}

/-- Integral charges with the two identities required on a Rips simplex. -/
structure IntegralCocycle (X : Type*) [PseudoMetricSpace X] (r : ℝ) where
  charge : X → X → ℤ
  antisymm : ∀ x y, dist x y ≤ r → charge y x = -charge x y
  triangle : ∀ x y z, dist x y ≤ r → dist y z ≤ r → dist z x ≤ r →
    charge x y + charge y z + charge z x = 0

theorem IntegralCocycle.difference (c : IntegralCocycle X r) {x y z : X}
    (hxy : dist x y ≤ r) (hyz : dist y z ≤ r) (hzx : dist z x ≤ r) :
    c.charge x z - c.charge y z = c.charge x y := by
  have h := c.triangle x y z hxy hyz hzx
  rw [c.antisymm x z (by simpa only [dist_comm] using hzx)] at h
  omega

theorem Point.exists_positive (p : Point X r) : ∃ x, 0 < p.weight x := by
  classical
  by_contra! h
  have hz : p.weight = 0 := by
    ext x
    exact le_antisymm (h x) (p.nonneg x)
  have ht := p.total
  simp [hz] at ht

def Point.supportVertex (p : Point X r) : X := p.exists_positive.choose

theorem Point.supportVertex_positive (p : Point X r) :
    0 < p.weight p.supportVertex := p.exists_positive.choose_spec

theorem Point.supportVertex_mem (p : Point X r) :
    p.supportVertex ∈ p.weight.support :=
  Finsupp.mem_support_iff.mpr (ne_of_gt p.supportVertex_positive)

variable [Fintype X]

/-- Local real lift based at a vertex of the supporting simplex. -/
def IntegralCocycle.localAngle (c : IntegralCocycle X r) (x : X) (p : Point X r) : ℝ :=
  ∑ z : X, p.weight z * (c.charge x z : ℝ)

theorem IntegralCocycle.localAngle_continuous (c : IntegralCocycle X r) (x : X) :
    Continuous (c.localAngle x) := by
  unfold localAngle
  exact continuous_finsetSum _ (fun z _ => (coordinate_continuous z).mul continuous_const)

theorem Point.sum_weight (p : Point X r) : ∑ x : X, p.weight x = 1 := by
  rw [← p.total]
  exact (p.weight.sum_fintype (fun _ t => t) (by simp)).symm

/-- Changes of local lift are exactly the prescribed integral charges. -/
theorem IntegralCocycle.localAngle_sub (c : IntegralCocycle X r) (p : Point X r)
    {x y : X} (hx : x ∈ p.weight.support) (hy : y ∈ p.weight.support) :
    c.localAngle x p - c.localAngle y p = (c.charge x y : ℝ) := by
  classical
  unfold localAngle
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ z : X, (p.weight z * (c.charge x z : ℝ) -
        p.weight z * (c.charge y z : ℝ))) =
        ∑ z : X, p.weight z * (c.charge x y : ℝ) := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ p.weight.support
      · rw [← mul_sub]
        congr 1
        exact_mod_cast c.difference (p.diameter x hx y hy)
          (p.diameter y hy z hz) (p.diameter z hz x hx)
      · have hz' : p.weight z = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hz
        simp only [hz', zero_mul, sub_self]
    _ = (c.charge x y : ℝ) := by rw [← Finset.sum_mul, p.sum_weight, one_mul]

theorem IntegralCocycle.localAngle_coe_eq (c : IntegralCocycle X r) (p : Point X r)
    {x y : X} (hx : x ∈ p.weight.support) (hy : y ∈ p.weight.support) :
    (c.localAngle x p : AddCircle (1 : ℝ)) = c.localAngle y p := by
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub, c.localAngle_sub p hx hy]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨c.charge x y, by simp⟩

/-- Barycentric interpolation of the cocycle, with values in the unit circle. -/
def IntegralCocycle.circleMap (c : IntegralCocycle X r) (p : Point X r) :
    AddCircle (1 : ℝ) := c.localAngle p.supportVertex p

theorem IntegralCocycle.circleMap_eq (c : IntegralCocycle X r) (p : Point X r)
    {x : X} (hx : x ∈ p.weight.support) :
    c.circleMap p = (c.localAngle x p : AddCircle (1 : ℝ)) :=
  c.localAngle_coe_eq p p.supportVertex_mem hx

theorem IntegralCocycle.circleMap_continuous (c : IntegralCocycle X r) :
    Continuous c.circleMap := by
  rw [continuous_iff_continuousAt]
  intro p
  let x := p.supportVertex
  have hx : {q : Point X r | 0 < q.weight x} ∈ 𝓝 p :=
    (isOpen_lt continuous_const (coordinate_continuous x)).mem_nhds
      p.supportVertex_positive
  have hc := ((AddCircle.continuous_mk' (1 : ℝ)).comp
    (c.localAngle_continuous x)).continuousAt (x := p)
  apply hc.congr_of_eventuallyEq
  filter_upwards [hx] with q hq
  exact c.circleMap_eq q (Finsupp.mem_support_iff.mpr (ne_of_gt hq))

def IntegralCocycle.toContinuousMap (c : IntegralCocycle X r) :
    C(Point X r, AddCircle (1 : ℝ)) := ⟨c.circleMap, c.circleMap_continuous⟩

end CoarseAssembly.Rips

end

end OAI
