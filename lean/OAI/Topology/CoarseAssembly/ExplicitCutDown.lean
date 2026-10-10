import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RepresentedCutDown

namespace OAI

/-! # The explicit represented-subspace cut-down cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem representedCorrection_right (c : OddCycle A) (a : A) :
    IsCompactOperator (representedCorrection c * c.representation a : End c.space) := by
  have hp : c.representation 1 * c.representation a = c.representation a := by
    rw [← map_mul, one_mul]
  rw [← hp, ← mul_assoc]
  exact compact_mul_right (representedCutDown_compact c).1 _

theorem representedCorrection_left (c : OddCycle A) (a : A) :
    IsCompactOperator (c.representation a * representedCorrection c : End c.space) := by
  have hp : c.representation a * c.representation 1 = c.representation a := by
    rw [← map_mul, mul_one]
  rw [← hp, mul_assoc]
  exact compact_mul_left (representedCutDown_compact c).2.1 _

theorem representedCorrection_star (c : OddCycle A) (a : A) :
    IsCompactOperator (star (representedCorrection c) * c.representation a : End c.space) := by
  have hp : c.representation 1 * c.representation a = c.representation a := by
    rw [← map_mul, one_mul]
  rw [← hp, ← mul_assoc]
  exact compact_mul_right (representedCutDown_compact c).2.2 _

theorem OddCycle.cutDown_operator (c : OddCycle A) :
    c.cutDown.operator = symmetricCutDown (c.representation 1) c.operator := by
  change c.operator + (symmetricCutDown (c.representation 1) c.operator - c.operator) = _
  abel

@[simp] theorem OddCycle.cutDown_representation (c : OddCycle A) :
    c.cutDown.representation = c.representation := rfl

theorem cutDown_class (c : OddCycle A) : cycleClass A c.cutDown = cycleClass A c :=
  localCompactPerturb_class c (representedCorrection c) (representedCorrection_right c)
    (representedCorrection_left c) (representedCorrection_star c)

theorem cutDown_selfAdjoint (c : OddCycle A) : IsSelfAdjoint c.cutDown.operator := by
  rw [c.cutDown_operator]
  exact symmetricCutDown_selfAdjoint _ _ (representation_unit_selfAdjoint c)

theorem cutDown_complement (c : OddCycle A) :
    c.cutDown.operator * (1 - c.cutDown.representation 1) = 1 - c.cutDown.representation 1 := by
  change (c.operator + representedCorrection c) * (1 - c.representation 1) = 1 - c.representation 1
  have he : c.operator + representedCorrection c =
      symmetricCutDown (c.representation 1) c.operator := by unfold representedCorrection; abel
  rw [he]
  exact symmetricCutDown_complement _ _ (representation_unit_selfAdjoint c) (representation_unit_sq c)

theorem cutDown_square_compact (c : OddCycle A) :
    IsCompactOperator (c.cutDown.operator * c.cutDown.operator - 1 : End c.cutDown.space) :=
  represented_square_compact c.cutDown (cutDown_complement c)

theorem symmetricCutDown_square_compact (c : OddCycle A) :
    IsCompactOperator ((symmetricCutDown (c.representation 1) c.operator) *
      symmetricCutDown (c.representation 1) c.operator - 1 : End c.space) := by
  have h := cutDown_square_compact c
  change IsCompactOperator ((c.operator + representedCorrection c) *
    (c.operator + representedCorrection c) - 1 : End c.space) at h
  have he : c.operator + representedCorrection c =
      symmetricCutDown (c.representation 1) c.operator := by unfold representedCorrection; abel
  rwa [he] at h

end CoarseAssembly.Analytic

end

end OAI
