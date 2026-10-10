import OAI.SetTheory.PartitionPrinciple.Geometry.DirectSystem

namespace OAI

namespace PartitionPilot.Compression.RecursiveMaps
universe u

structure MeetSystem (I : Type u) [LinearOrder I] where
  system : DirectSystem I
  order : ∀ i, MeetOrder (system.Point i)
  map_le : ∀ {i j} (h : i ≤ j) x y,
    (order j).le (system.map h x) (system.map h y) ↔ (order i).le x y
  map_meet : ∀ {i j} (h : i ≤ j) x y,
    system.map h ((order i).meet x y) = (order j).meet (system.map h x) (system.map h y)

namespace MeetSystem
variable {I : Type u} [LinearOrder I] (c : MeetSystem I)

def transition {i j : I} (h : i ≤ j) : MeetEmbedding (c.order i) (c.order j) where
  toFun := c.system.map h
  le_iff := c.map_le h
  map_meet := c.map_meet h

def Le (x y : c.system.Union) : Prop :=
  ∃ i a b, c.system.point i a = x ∧ c.system.point i b = y ∧ (c.order i).le a b

theorem le_stage (i : I) (a b : c.system.Point i) :
    c.Le (c.system.point i a) (c.system.point i b) ↔ (c.order i).le a b := by
  constructor
  · rintro ⟨j, x, y, hx, hy, lower⟩
    have ex : c.system.map (le_max_right i j) x = c.system.map (le_max_left i j) a := by
      apply c.system.point_injective (max i j)
      rw [c.system.point_map, c.system.point_map]
      exact hx
    have ey : c.system.map (le_max_right i j) y = c.system.map (le_max_left i j) b := by
      apply c.system.point_injective (max i j)
      rw [c.system.point_map, c.system.point_map]
      exact hy
    have raised := (c.map_le (le_max_right i j) x y).mpr lower
    rw [ex, ey] at raised
    exact (c.map_le (le_max_left i j) a b).mp raised
  · intro lower
    exact ⟨i, a, b, rfl, rfl, lower⟩

def meet : c.system.Union → c.system.Union → c.system.Union :=
  c.system.binary c.system c.system (fun i => (c.order i).meet) c.map_meet

theorem meet_stage (i : I) (a b : c.system.Point i) :
    c.meet (c.system.point i a) (c.system.point i b) = c.system.point i ((c.order i).meet a b) :=
  c.system.binary_point c.system c.system (fun i => (c.order i).meet) c.map_meet i a b

def unionOrder : MeetOrder c.system.Union where
  le := c.Le
  meet := c.meet
  refl x := by
    rcases c.system.cover x with ⟨i, a, rfl⟩
    exact (c.le_stage i a a).mpr ((c.order i).refl a)
  trans {x y z} hxy hyz := by
    rcases c.system.triple_cover c.system c.system x y z with ⟨i, a, b, t, rfl, rfl, rfl⟩
    exact (c.le_stage i a t).mpr ((c.order i).trans
      ((c.le_stage i a b).mp hxy) ((c.le_stage i b t).mp hyz))
  antisymm {x y} hxy hyx := by
    rcases c.system.pair_cover c.system x y with ⟨i, a, b, rfl, rfl⟩
    exact congrArg (c.system.point i) ((c.order i).antisymm
      ((c.le_stage i a b).mp hxy) ((c.le_stage i b a).mp hyx))
  meet_le_left x y := by
    rcases c.system.pair_cover c.system x y with ⟨i, a, b, rfl, rfl⟩
    rw [c.meet_stage]
    exact (c.le_stage i _ a).mpr ((c.order i).meet_le_left a b)
  meet_le_right x y := by
    rcases c.system.pair_cover c.system x y with ⟨i, a, b, rfl, rfl⟩
    rw [c.meet_stage]
    exact (c.le_stage i _ b).mpr ((c.order i).meet_le_right a b)
  le_meet {z x y} hzx hzy := by
    rcases c.system.triple_cover c.system c.system z x y with ⟨i, a, b, t, rfl, rfl, rfl⟩
    rw [c.meet_stage]
    exact (c.le_stage i a _).mpr ((c.order i).le_meet
      ((c.le_stage i a b).mp hzx) ((c.le_stage i a t).mp hzy))

def inclusion (i : I) : MeetEmbedding (c.order i) c.unionOrder where
  toFun := c.system.point i
  le_iff := c.le_stage i
  map_meet x y := (c.meet_stage i x y).symm

def boundedOrder : MeetOrder (Option c.system.Union) := FixedTop.order c.unionOrder

def boundedInclusion (i : I) : MeetEmbedding (c.order i) c.boundedOrder :=
  compose (c.inclusion i) (FixedTop.embedding c.unionOrder).toMeetEmbedding

theorem bounded_strict_top (i : I) (x : c.system.Point i) :
    c.boundedOrder.le ((c.boundedInclusion i).toFun x) none ∧
      ¬ c.boundedOrder.le none ((c.boundedInclusion i).toFun x) :=
  FixedTop.strict_top c.unionOrder (c.system.point i x)

end MeetSystem

structure GroupSystem (I : Type u) [LinearOrder I] where
  system : DirectSystem I
  [group : ∀ i, Group (system.Point i)]
  map_one : ∀ {i j} (h : i ≤ j), system.map h 1 = 1
  map_mul : ∀ {i j} (h : i ≤ j) x y, system.map h (x * y) = system.map h x * system.map h y

attribute [instance] GroupSystem.group

namespace GroupSystem
variable {I : Type u} [LinearOrder I] (g : GroupSystem I)

def transition {i j : I} (h : i ≤ j) : g.system.Point i →* g.system.Point j where
  toFun := g.system.map h
  map_one' := g.map_one h
  map_mul' := g.map_mul h

theorem map_inv {i j : I} (h : i ≤ j) (x : g.system.Point i) :
    g.system.map h x⁻¹ = (g.system.map h x)⁻¹ := (g.transition h).map_inv x

def mul : g.system.Union → g.system.Union → g.system.Union :=
  g.system.binary g.system g.system (fun _ x y => x * y) g.map_mul

theorem mul_point (i : I) (x y : g.system.Point i) :
    g.mul (g.system.point i x) (g.system.point i y) = g.system.point i (x * y) :=
  g.system.binary_point g.system g.system (fun _ x y => x * y) g.map_mul i x y

def inv : g.system.Union → g.system.Union :=
  g.system.descend (fun i x => g.system.point i x⁻¹) (by
    intro i j h x
    rw [← g.map_inv h, g.system.point_map])

theorem inv_point (i : I) (x : g.system.Point i) :
    g.inv (g.system.point i x) = g.system.point i x⁻¹ := rfl

variable [Nonempty I]

noncomputable def one : g.system.Union := g.system.point (Classical.arbitrary I) 1

theorem one_point (i : I) : g.one = g.system.point i 1 := by
  apply Quotient.sound
  exact ⟨max (Classical.arbitrary I) i, le_max_left _ _, le_max_right _ _,
    (g.map_one _).trans (g.map_one _).symm⟩

noncomputable instance unionGroup : Group g.system.Union where
  one := g.one
  mul := g.mul
  inv := g.inv
  mul_assoc x y z := by
    change g.mul (g.mul x y) z = g.mul x (g.mul y z)
    rcases g.system.triple_cover g.system g.system x y z with ⟨i, a, b, c, rfl, rfl, rfl⟩
    rw [g.mul_point, g.mul_point, g.mul_point, g.mul_point, mul_assoc]
  one_mul x := by
    change g.mul g.one x = x
    rcases g.system.cover x with ⟨i, a, rfl⟩
    rw [g.one_point i, g.mul_point, one_mul]
  mul_one x := by
    change g.mul x g.one = x
    rcases g.system.cover x with ⟨i, a, rfl⟩
    rw [g.one_point i, g.mul_point, mul_one]
  inv_mul_cancel x := by
    change g.mul (g.inv x) x = g.one
    rcases g.system.cover x with ⟨i, a, rfl⟩
    rw [g.inv_point, g.mul_point, inv_mul_cancel, g.one_point i]

noncomputable def inclusion (i : I) : g.system.Point i →* g.system.Union where
  toFun := g.system.point i
  map_one' := (g.one_point i).symm
  map_mul' x y := (g.mul_point i x y).symm

theorem inclusion_injective (i : I) : Function.Injective (g.inclusion i) :=
  g.system.point_injective i

end GroupSystem
end PartitionPilot.Compression.RecursiveMaps

end OAI
