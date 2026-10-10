import OAI.SetTheory.PartitionPrinciple.Geometry.MainInitial

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.ActionSystem

open CosetGeometry
universe u
variable {I : Type u} [LinearOrder I] [Nonempty I]
    {g : GroupSystem I} {p : MeetSystem I} (a : ActionSystem g p)

def PreservesAgreements : Prop := ∀ {i j} (lower : i ≤ j) (s t : g.system.Point i) (v : p.system.Point i),
  (∀ x, (p.order i).le x v → ((a.action i).iso s).toFun x = ((a.action i).iso t).toFun x) →
  ∀ x, (p.order j).le x (p.system.map lower v) →
    ((a.action j).iso (g.system.map lower s)).toFun x =
      ((a.action j).iso (g.system.map lower t)).toFun x

theorem union_agreement (preserves : a.PreservesAgreements)
    (i : I) (s t : g.system.Point i) (v : p.system.Point i)
    (agree : ∀ x, (p.order i).le x v → ((a.action i).iso s).toFun x = ((a.action i).iso t).toFun x)
    (x : p.system.Union) (lower : p.unionOrder.le x ((p.inclusion i).toFun v)) :
    (a.unionAction.iso ((g.inclusion i) s)).toFun x =
      (a.unionAction.iso ((g.inclusion i) t)).toFun x := by
  rcases p.system.cover x with ⟨j, x, rfl⟩
  let hi := le_max_left i j
  let hj := le_max_right i j
  have lowerAt : p.unionOrder.le (p.system.point (max i j) (p.system.map hj x))
      (p.system.point (max i j) (p.system.map hi v)) := by
    rw [p.system.point_map, p.system.point_map]
    exact lower
  have eq := preserves hi s t v agree (p.system.map hj x) ((p.le_stage _ _ _).mp lowerAt)
  change a.act (g.system.point i s) (p.system.point j x) =
    a.act (g.system.point i t) (p.system.point j x)
  rw [← g.system.point_map hi s, ← g.system.point_map hi t, ← p.system.point_map hj x,
    a.act_point, a.act_point]
  exact congrArg (p.system.point (max i j)) eq

theorem top_agreement (preserves : a.PreservesAgreements)
    (i : I) (s t : g.system.Point i) (v : p.system.Point i)
    (agree : ∀ x, (p.order i).le x v → ((a.action i).iso s).toFun x = ((a.action i).iso t).toFun x)
    (x : Option p.system.Union) (lower : p.boundedOrder.le x ((p.boundedInclusion i).toFun v)) :
    (a.topAction.iso ((g.inclusion i) s)).toFun x =
      (a.topAction.iso ((g.inclusion i) t)).toFun x := by
  cases x with
  | none => exact False.elim lower
  | some x => exact congrArg some (a.union_agreement preserves i s t v agree x lower)

end PartitionPilot.Compression.RecursiveMaps.ActionSystem

end

end OAI
