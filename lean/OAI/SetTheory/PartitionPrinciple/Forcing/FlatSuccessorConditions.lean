import OAI.SetTheory.PartitionPrinciple.Transfinite.StageOneDataBoundLaws

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R P : Type u}
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)

structure FlatSuccessorCondition where
  row : R
  assignments : ZFSet.{u}
  assignments_mem : assignments ∈
    M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega
  lower : P
  lower_code : s.encode lower = ZFSet.pair (c.encode row)
    (assignmentCut levels alpha assignments)
  tests : tests assignments lower

namespace FlatSuccessorCondition
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests

@[ext] theorem ext {p q : Condition}
    (rows : p.row = q.row) (data : p.assignments = q.assignments) : p = q := by
  cases p with
  | mk rp Ap smallp lp codep testp =>
    cases q with
    | mk rq Aq smallq lq codeq testq =>
      dsimp only at rows data
      subst rq
      subst Aq
      have equal : lp = lq := s.injective (codep.trans codeq.symm)
      subst lq
      rfl

noncomputable def code (p : Condition) : ZFSet.{u} := ZFSet.pair (c.encode p.row) p.assignments

theorem code_eq_iff (p q : Condition) :
    code M c s I T levels alpha tests p =
    code M c s I T levels alpha tests q ↔ p.row = q.row ∧ p.assignments = q.assignments := by
  rw [code, code, ZFSet.pair_inj]
  exact and_congr c.injective.eq_iff Iff.rfl

theorem code_injective : Function.Injective (code M c s I T levels alpha tests) := by
  intro p q equal
  obtain ⟨rows, data⟩ := (code_eq_iff M c s I T levels alpha tests p q).1 equal
  exact ext M c s I T levels alpha tests rows data

theorem code_mem_candidateBound (p : Condition) :
    code M c s I T levels alpha tests p ∈ M.stageOneCandidateBound c.carrier I T :=
  ZFSet.pair_mem_prod.2 ⟨c.encode_mem p.row, p.assignments_mem⟩

instance small : Small.{u} Condition := by
  let bound := M.stageOneCandidateBound c.carrier I T
  let f : Condition → bound := fun p =>
    ⟨code M c s I T levels alpha tests p,
      code_mem_candidateBound M c s I T levels alpha tests p⟩
  apply small_of_injective (f := f)
  intro p q equal
  exact code_injective M c s I T levels alpha tests (congrArg Subtype.val equal)

end FlatSuccessorCondition

end PartitionPilot.Forcing

end

end OAI
