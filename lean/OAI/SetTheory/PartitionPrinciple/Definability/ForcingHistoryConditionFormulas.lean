import OAI.SetTheory.PartitionPrinciple.Forcing.ForcingHistoryTestDecomposition

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def forcingHistoryEntryFormula {n : Nat} (alpha history levels z : Fin n) : SetFormula n :=
  .ex (.conj (BoundedFormula.pairMembershipFormula alpha.succ 0 history.succ).toFormula
    (packedSuccessorConditionFormula levels.succ alpha.succ 0 z.succ))

def forcingHistoryConditionFormula {n : Nat} (stages history levels z : Fin n) : SetFormula n :=
  .all (.imp (.mem 0 stages.succ)
    (forcingHistoryEntryFormula 0 history.succ levels.succ z.succ))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_forcingHistoryEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n : Nat} (alpha history levels z : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (forcingHistoryEntryFormula alpha history levels z) env ↔
      ∃ data, ZFSet.pair (env alpha) data ∈ env history ∧
        PackedSuccessorConditionCode M (env levels) (env alpha) data (env z) := by
  rw [forcingHistoryEntryFormula, realize_ex]
  have actual (data : ZFSet.{u}) (ground : data ∈ M.sets) :
      Realize M.sets
        (.conj (BoundedFormula.pairMembershipFormula alpha.succ 0 history.succ).toFormula
          (packedSuccessorConditionFormula levels.succ alpha.succ 0 z.succ)) (extend data env) ↔
        ZFSet.pair (env alpha) data ∈ env history ∧
          PackedSuccessorConditionCode M (env levels) (env alpha) data (env z) := by
    apply and_congr
    · rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases ground members),
        BoundedFormula.truth_pairMembershipFormula]
      rfl
    · exact M.realize_packedSuccessorConditionFormula pairing separation _ _ _ _ _ (Fin.cases ground members)
  constructor
  · rintro ⟨data, ground, checked⟩
    exact ⟨data, (actual data ground).1 checked⟩
  · rintro ⟨data, entry, checked⟩
    have ground := M.pair_right (M.transitive (members history) entry)
    exact ⟨data, ground, (actual data ground).2 ⟨entry, checked⟩⟩

theorem realize_forcingHistoryConditionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n : Nat} (stages history levels z : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (forcingHistoryConditionFormula stages history levels z) env ↔
      ForcingHistoryConditionCode M (env stages) (env history) (env levels) (env z) := by
  change (∀ alpha ∈ M.sets, Realize M.sets
    (.imp (.mem 0 stages.succ) (forcingHistoryEntryFormula 0 history.succ levels.succ z.succ))
      (extend alpha env)) ↔ _
  constructor
  · intro checked alpha member
    have ground := M.transitive (members stages) member
    exact (M.realize_forcingHistoryEntryFormula pairing separation 0 history.succ levels.succ z.succ
      (extend alpha env) (Fin.cases ground members)).1
      ((realize_imp M.sets _ _ _).1 (checked alpha ground) member)
  · intro valid alpha ground
    apply (realize_imp M.sets _ _ _).2
    intro member
    exact (M.realize_forcingHistoryEntryFormula pairing separation 0 history.succ levels.succ z.succ
      (extend alpha env) (Fin.cases ground members)).2 (valid alpha member)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
