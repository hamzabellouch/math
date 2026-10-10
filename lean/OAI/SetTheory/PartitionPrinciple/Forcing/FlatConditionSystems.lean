import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageOneOrder

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {R Q : Type u} [PartialOrder R] [PartialOrder Q]

structure FlatConditionSystem (M : TransitiveGround.{u})
    (c : Presentation R) (s : Presentation Q) (J : ZFSet.{u}) where
  row : Q → R
  assignments : Q → ZFSet.{u}
  encode : ∀ q, s.encode q = ZFSet.pair (c.encode (row q)) (assignments q)
  le_iff : ∀ q p, q ≤ p ↔ row q ≤ row p ∧ assignments p ⊆ assignments q
  assignments_mem : ∀ q, assignments q ∈ M.groundSmallSubsets J ZFSet.omega

namespace FlatConditionSystem
variable {M : TransitiveGround.{u}} {c : Presentation R} {s : Presentation Q} {J : ZFSet.{u}}
variable (F : FlatConditionSystem M c s J)
include F

theorem conditionOrder_eq : s.conditionOrder =
    rowAssignmentOrder s.carrier c.carrier (M.groundSmallSubsets J ZFSet.omega) c.conditionOrder := by
  apply ZFSet.ext
  intro z
  rw [Presentation.conditionOrder, Presentation.mem_subset]
  constructor
  · rintro ⟨⟨q, p⟩, below, rfl⟩
    change ZFSet.pair (s.encode q) (s.encode p) ∈ _
    rw [F.encode q, F.encode p]
    exact (pair_mem_rowAssignmentOrder _ _ _ _ _ _ _ _).2
      ⟨F.encode q ▸ s.encode_mem q, F.encode p ▸ s.encode_mem p,
        c.encode_mem (F.row q), F.assignments_mem q,
        c.encode_mem (F.row p), F.assignments_mem p,
        (c.pair_mem_conditionOrder _ _).2 ((F.le_iff q p).1 below).1,
        ((F.le_iff q p).1 below).2⟩
  · intro member
    obtain ⟨rawQ, hq, rawP, hp, equal⟩ := ZFSet.mem_prod.1
      ((mem_rowAssignmentOrder _ _ _ _ z).1 member).1
    obtain ⟨q, eqQ⟩ := (s.mem_carrier rawQ).1 hq
    obtain ⟨p, eqP⟩ := (s.mem_carrier rawP).1 hp
    have entries : ZFSet.pair (s.encode q) (s.encode p) ∈
        rowAssignmentOrder s.carrier c.carrier (M.groundSmallSubsets J ZFSet.omega) c.conditionOrder := by
      rw [eqQ, eqP, ← equal]
      exact member
    rw [F.encode q, F.encode p] at entries
    obtain ⟨_, _, _, _, _, _, rows, data⟩ :=
      (pair_mem_rowAssignmentOrder _ _ _ _ _ _ _ _).1 entries
    refine ⟨(q, p), (F.le_iff q p).2 ⟨(c.pair_mem_conditionOrder _ _).1 rows, data⟩, ?_⟩
    change ZFSet.pair (s.encode q) (s.encode p) = z
    rw [eqQ, eqP]
    exact equal.symm

theorem conditionOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (rows : c.carrier ∈ M.sets) (conditions : s.carrier ∈ M.sets)
    (assignments : J ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (order : c.conditionOrder ∈ M.sets) : s.conditionOrder ∈ M.sets := by
  rw [F.conditionOrder_eq]
  exact M.rowAssignmentOrder_mem pairing unions powers separation conditions rows
    (M.groundSmallSubsets_mem powers separation assignments omega) order

end FlatConditionSystem

end PartitionPilot.Forcing

end

end OAI
