import OAI.SetTheory.PartitionPrinciple.Transfinite.LimitGroup

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps
open CosetGeometry
universe u

structure ActionSystem {I : Type u} [LinearOrder I] (g : GroupSystem I) (p : MeetSystem I) where
  action : ∀ i, OrderAction (g.system.Point i) (p.order i)
  compatible : ∀ {i j} (h : i ≤ j) s x,
    p.system.map h (((action i).iso s).toFun x) =
      ((action j).iso (g.system.map h s)).toFun (p.system.map h x)

namespace ActionSystem
variable {I : Type u} [LinearOrder I] {g : GroupSystem I} {p : MeetSystem I}
    (a : ActionSystem g p)

def act : g.system.Union → p.system.Union → p.system.Union :=
  g.system.binary p.system p.system (fun i s x => ((a.action i).iso s).toFun x) a.compatible

theorem act_point (i : I) (s : g.system.Point i) (x : p.system.Point i) :
    a.act (g.system.point i s) (p.system.point i x) =
      p.system.point i (((a.action i).iso s).toFun x) :=
  g.system.binary_point p.system p.system (fun i s x => ((a.action i).iso s).toFun x)
    a.compatible i s x

variable [Nonempty I]

theorem act_one (x : p.system.Union) : a.act 1 x = x := by
  rcases p.system.cover x with ⟨i, x, rfl⟩
  change a.act g.one _ = _
  rw [g.one_point i, a.act_point, (a.action i).one]

theorem act_mul (s t : g.system.Union) (x : p.system.Union) :
    a.act (s * t) x = a.act s (a.act t x) := by
  rcases g.system.triple_cover g.system p.system s t x with ⟨i, s, t, x, rfl, rfl, rfl⟩
  change a.act (g.mul _ _) _ = _
  rw [g.mul_point, a.act_point, a.act_point, a.act_point, (a.action i).mul]

theorem act_left_inverse (s : g.system.Union) (x : p.system.Union) :
    a.act s⁻¹ (a.act s x) = x := by
  rw [← a.act_mul, inv_mul_cancel, a.act_one]

theorem act_right_inverse (s : g.system.Union) (x : p.system.Union) :
    a.act s (a.act s⁻¹ x) = x := by
  rw [← a.act_mul, mul_inv_cancel, a.act_one]

omit [Nonempty I] in
theorem act_le_iff (s : g.system.Union) (x y : p.system.Union) :
    p.unionOrder.le (a.act s x) (a.act s y) ↔ p.unionOrder.le x y := by
  rcases g.system.triple_cover p.system p.system s x y with ⟨i, s, x, y, rfl, rfl, rfl⟩
  change p.Le _ _ ↔ p.Le _ _
  rw [a.act_point, a.act_point, p.le_stage, p.le_stage, (a.action i).iso s |>.le_iff]

noncomputable def unionIso (s : g.system.Union) : MeetIso p.unionOrder p.unionOrder :=
  isoOfOrder (a.act s) (a.act s⁻¹) (a.act_left_inverse s) (a.act_right_inverse s) (a.act_le_iff s)

noncomputable def unionAction : OrderAction g.system.Union p.unionOrder where
  iso := a.unionIso
  one := a.act_one
  mul := a.act_mul

theorem unionAction_stage (i : I) (s : g.system.Point i) (x : p.system.Point i) :
    (a.unionAction.iso ((g.inclusion i) s)).toFun ((p.inclusion i).toFun x) =
      (p.inclusion i).toFun (((a.action i).iso s).toFun x) := a.act_point i s x

noncomputable def topAction : OrderAction g.system.Union p.boundedOrder :=
  FixedTop.action p.unionOrder a.unionAction

theorem topAction_stage (i : I) (s : g.system.Point i) (x : p.system.Point i) :
    (a.topAction.iso ((g.inclusion i) s)).toFun ((p.boundedInclusion i).toFun x) =
      (p.boundedInclusion i).toFun (((a.action i).iso s).toFun x) :=
  congrArg some (a.act_point i s x)

theorem top_fixed (s : g.system.Union) : (a.topAction.iso s).toFun none = none := rfl

end ActionSystem
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
