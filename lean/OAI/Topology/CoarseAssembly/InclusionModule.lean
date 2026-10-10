import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.HilbertSum
import OAI.Topology.CoarseAssembly.FiberEmbedding
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace OAI

/-! # Spatial module maps for inclusions

Extension by zero along an injection is an actual Hilbert-space isometry,
with the exact basis formula used for the boundary inclusions.
-/

noncomputable section

namespace CoarseAssembly

variable {X Y H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

omit [NormedSpace ℂ H] in
theorem extendedFunction_apply (e : X ↪ Y) (x : lp (fun _ : X => H) 2) (a : X) :
    extendedFunction e x (e a) = x a := e.injective.extend_apply _ _ _

omit [NormedSpace ℂ H] in
theorem extendedFunction_zero (e : X ↪ Y) (x : lp (fun _ : X => H) 2)
    (y : Y) (hy : y ∉ Set.range e) : extendedFunction e x y = 0 :=
  Function.extend_apply' _ _ _ hy

omit [NormedSpace ℂ H] in
theorem extendedFunction_hasSum (e : X ↪ Y) (x : lp (fun _ : X => H) 2) :
    HasSum (fun y => ‖extendedFunction e x y‖ ^ 2) (‖x‖ ^ 2) := by
  have hf : HasSum (fun a : X => ‖x a‖ ^ 2) (‖x‖ ^ 2) := by
    rw [l2_norm_sq]
    exact (l2_summable_sq x).hasSum
  apply (e.injective.hasSum_iff (fun y hy => by
    rw [extendedFunction_zero e x y hy, norm_zero, zero_pow (by decide : 2 ≠ 0)])).mp
  convert hf using 1
  funext a
  exact congrArg (fun h : H => ‖h‖ ^ 2) (extendedFunction_apply e x a)

omit [NormedSpace ℂ H] in
@[simp] theorem inclusionVector_apply (e : X ↪ Y) (x : lp (fun _ : X => H) 2) (a : X) :
    inclusionVector e x (e a) = x a := extendedFunction_apply e x a

omit [NormedSpace ℂ H] in
theorem inclusionVector_zero (e : X ↪ Y) (x : lp (fun _ : X => H) 2) (y : Y)
    (hy : y ∉ Set.range e) : inclusionVector e x y = 0 := extendedFunction_zero e x y hy

theorem inclusionIsometry_single [DecidableEq X] [DecidableEq Y]
    (e : X ↪ Y) (a : X) (h : H) :
    inclusionIsometry e (lp.single 2 a h) = lp.single 2 (e a) h := by
  apply lp.ext
  funext y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨b, rfl⟩ := hy
    change inclusionVector e (lp.single 2 a h) (e b) = _
    rw [inclusionVector_apply]
    simp only [lp.single_apply, Pi.single_apply, e.injective.eq_iff]
  · have hne : y ≠ e a := fun h => hy ⟨a, h.symm⟩
    change inclusionVector e (lp.single 2 a h) y = _
    rw [inclusionVector_zero e _ y hy, lp.single_apply_ne (E := fun _ : Y => H) 2 (e a) h hne]

end CoarseAssembly

end

end OAI
