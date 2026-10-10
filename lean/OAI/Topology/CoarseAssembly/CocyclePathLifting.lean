import OAI.Topology.CoarseAssembly.RipsPaths
import OAI.Topology.CoarseAssembly.ShortLoops

namespace OAI

/-! # Integer lifts and winding along graph walks

The real lift of the constructed circle map along an actual graph walk
ends at the sum of its edge charges. This is the topological degree
calculation used before applying the published circle index formula.
-/

noncomputable section

namespace CoarseAssembly

open unitInterval

section Lifts

variable {Y : Type*} [TopologicalSpace Y] (f : Y → AddCircle (1 : ℝ))
  {x y z : Y}

/-- A real path lift normalized to start at zero, with integral endpoint. -/
structure IntegerPathLift (p : Path x y) (n : ℤ) where
  path : Path (0 : ℝ) (n : ℝ)
  commutes : ∀ t, f (p t) = (path t : AddCircle (1 : ℝ))

def shiftedRealPath (a b : ℤ) (p : Path (0 : ℝ) (b : ℝ)) :
    Path (a : ℝ) ((a + b : ℤ) : ℝ) where
  toFun t := (a : ℝ) + p t
  continuous_toFun := continuous_const.add p.continuous
  source' := by simp
  target' := by simp

def IntegerPathLift.refl (hfx : f x = 0) :
    IntegerPathLift f (Path.refl x) 0 where
  path := (Path.refl (0 : ℝ)).cast rfl (by simp)
  commutes t := by simpa [Path.cast] using hfx

def IntegerPathLift.trans {p : Path x y} {q : Path y z} {a b : ℤ}
    (hp : IntegerPathLift f p a) (hq : IntegerPathLift f q b) :
    IntegerPathLift f (p.trans q) (a + b) where
  path := hp.path.trans (shiftedRealPath a b hq.path)
  commutes t := by
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with ht
    · exact hp.commutes _
    · change f (q _) = ((a : ℝ) + hq.path _ : ℝ)
      rw [hq.commutes, AddCircle.coe_add]
      have ha : ((a : ℝ) : AddCircle (1 : ℝ)) = 0 :=
        (AddCircle.coe_eq_zero_iff _).mpr ⟨a, by simp⟩
      rw [ha, zero_add]

end Lifts

namespace Rips

variable {X : Type*} [PseudoMetricSpace X] {r : ℝ}

/-- Follow the barycentric unit edges of a graph walk. -/
def walkPath {G : SimpleGraph X} (hr : 0 ≤ r)
    (hE : ∀ x y, G.Adj x y → dist x y ≤ r) :
    {x y : X} → G.Walk x y → Path (vertex x hr) (vertex y hr)
  | _, _, .nil => Path.refl _
  | _, _, .cons h p => (edgePath (hE _ _ h)).trans (walkPath hr hE p)

variable [Fintype X]

def IntegralCocycle.edgeLift (c : IntegralCocycle X r)
    {x y : X} (hxy : dist x y ≤ r) :
    IntegerPathLift c.circleMap (edgePath hxy) (c.charge x y) where
  path := Path.segment 0 (c.charge x y : ℝ)
  commutes t := by
    rw [c.circleMap_edgePath]
    simp only [Path.segment_apply, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      sub_zero, smul_eq_mul, add_zero]

def IntegralCocycle.walkLift (c : IntegralCocycle X r) {G : SimpleGraph X}
    (hr : 0 ≤ r) (hE : ∀ x y, G.Adj x y → dist x y ≤ r)
    {x y : X} (p : G.Walk x y) :
    IntegerPathLift c.circleMap (walkPath hr hE p) (walkCharge c.charge p) := by
  induction p with
  | nil => exact IntegerPathLift.refl _ (c.circleMap_vertex hr _)
  | cons h p ih => exact (c.edgeLift (hE _ _ h)).trans _ ih

/-- A closed graph walk yields a circle-valued loop with a real lift whose
endpoint is exactly its integral cocycle evaluation. -/
theorem IntegralCocycle.closed_walk_lift (c : IntegralCocycle X r) {G : SimpleGraph X}
    (hr : 0 ≤ r) (hE : ∀ x y, G.Adj x y → dist x y ≤ r)
    {x : X} (p : G.Walk x x) :
    ∃ L : Path (0 : ℝ) (walkCharge c.charge p : ℝ),
      ∀ t, c.circleMap (walkPath hr hE p t) = (L t : AddCircle (1 : ℝ)) :=
  ⟨(c.walkLift hr hE p).path, (c.walkLift hr hE p).commutes⟩

end Rips

end CoarseAssembly

end

end OAI
