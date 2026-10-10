import OAI.SetTheory.PartitionPrinciple.Geometry.GroundAssignmentIndexLevels

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace BoundedFormula

def assignmentCutFormula {n : Nat} (cut levels alpha A : Fin n) : BoundedFormula n :=
  .conj
    (.allMem cut (.conj (.mem 0 A.succ)
      (exMem alpha.succ (pairMembershipFormula 1 0 levels.succ.succ))))
    (.allMem A (imp (exMem alpha.succ (pairMembershipFormula 1 0 levels.succ.succ))
      (.mem 0 cut.succ)))

theorem truth_assignmentCutFormula {n : Nat} (cut levels alpha A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (assignmentCutFormula cut levels alpha A) env ↔
      env cut = assignmentCut (env levels) (env alpha) (env A) := by
  simp only [assignmentCutFormula, Truth, truth_exMem, truth_pairMembershipFormula,
    truth_imp, extend]
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro z
    rw [mem_assignmentCut]
    exact ⟨forward z, fun h => backward z h.1 h.2⟩
  · intro equal
    constructor
    · intro z hz
      exact (mem_assignmentCut _ _ _ z).1 (equal ▸ hz)
    · intro z hz lower
      change z ∈ env cut
      rw [equal]
      exact (mem_assignmentCut _ _ _ z).2 ⟨hz, lower⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_assignmentCutFormula {n : Nat} (cut levels alpha A : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (BoundedFormula.assignmentCutFormula cut levels alpha A).toFormula env ↔
      env cut = assignmentCut (env levels) (env alpha) (env A) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_assignmentCutFormula cut levels alpha A env)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula
private def historyCutEntryBody {n : Nat} (beta history levels row A : Fin n) : BoundedFormula (n + 3) :=
  let old := suffixIndex n 3
  let v := prefixIndex n 3
  .conj (BoundedFormula.pairMembershipFormula (old beta) (v 0) (old history))
    (.conj (BoundedFormula.assignmentCutFormula (v 1) (old levels) (old beta) (old A))
      (.conj (BoundedFormula.orderedPairFormula (v 2) (old row) (v 1)) (.mem (v 2) (v 0))))

def historyCutEntryFormula {n : Nat} (beta history levels row A : Fin n) : SetFormula n :=
  exBlock 3 (historyCutEntryBody beta history levels row A).toFormula

def flatHistoryCutsFormula {n : Nat} (stages history levels row A : Fin n) : SetFormula n :=
  .all (.imp (.mem 0 stages.succ)
    (historyCutEntryFormula 0 history.succ levels.succ row.succ A.succ))

def flatLimitConditionFormula {n : Nat} (stages history levels z : Fin n) : SetFormula n :=
  let old := suffixIndex n 2
  let v := prefixIndex n 2
  exBlock 2 (.conj (BoundedFormula.orderedPairFormula (old z) (v 0) (v 1)).toFormula
    (flatHistoryCutsFormula (old stages) (old history) (old levels) (v 0) (v 1)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_historyCutEntryFormula {n : Nat} (beta history levels row A : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (historyCutEntryFormula beta history levels row A) env ↔
      ∃ Q, ZFSet.pair (env beta) Q ∈ env history ∧
        ZFSet.pair (env row) (assignmentCut (env levels) (env beta) (env A)) ∈ Q := by
  rw [historyCutEntryFormula, realize_exBlock]
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (SetFormula.historyCutEntryBody beta history levels row A).toFormula
        (extendMany 3 f env) ↔
      ZFSet.pair (env beta) (f 0) ∈ env history ∧
        f 1 = assignmentCut (env levels) (env beta) (env A) ∧
        f 2 = ZFSet.pair (env row) (f 1) ∧ f 2 ∈ f 0 := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 3 f env ground members)]
    simp only [SetFormula.historyCutEntryBody, BoundedFormula.Truth,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_assignmentCutFormula,
      BoundedFormula.truth_orderedPairFormula, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨entry, cut, pair, member⟩ := (actual f ground).1 body
    rw [pair, cut] at member
    exact ⟨f 0, entry, member⟩
  · rintro ⟨Q, entry, member⟩
    have hQ := M.pair_right (M.transitive (members history) entry)
    have hPair := M.transitive hQ member
    have hCut := M.pair_right hPair
    let f : Fin 3 → ZFSet.{u} :=
      ![Q, assignmentCut (env levels) (env beta) (env A),
        ZFSet.pair (env row) (assignmentCut (env levels) (env beta) (env A))]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases hQ (Fin.cases hCut (Fin.cases hPair (fun j => Fin.elim0 j)))
    exact ⟨f, ground, (actual f ground).2 ⟨entry, rfl, rfl, member⟩⟩

theorem realize_flatHistoryCutsFormula {n : Nat} (stages history levels row A : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (flatHistoryCutsFormula stages history levels row A) env ↔
      FlatHistoryCuts (env stages) (env history) (env levels) (env row) (env A) := by
  change (∀ beta ∈ M.sets, Realize M.sets
    (.imp (.mem 0 stages.succ)
      (historyCutEntryFormula 0 history.succ levels.succ row.succ A.succ))
      (extend beta env)) ↔ _
  constructor
  · intro allCuts beta hbeta
    exact (M.realize_historyCutEntryFormula 0 history.succ levels.succ row.succ A.succ
      (extend beta env) (Fin.cases (M.transitive (members stages) hbeta) members)).1
      ((realize_imp M.sets _ _ _).1
        (allCuts beta (M.transitive (members stages) hbeta)) hbeta)
  · intro valid beta hbeta
    apply (realize_imp M.sets _ _ _).2
    intro member
    exact (M.realize_historyCutEntryFormula 0 history.succ levels.succ row.succ A.succ
      (extend beta env) (Fin.cases hbeta members)).2 (valid beta member)

theorem realize_flatLimitConditionFormula {n : Nat} (stages history levels z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (flatLimitConditionFormula stages history levels z) env ↔
      FlatLimitConditionCode (env stages) (env history) (env levels) (env z) := by
  rw [flatLimitConditionFormula, realize_exBlock]
  have actual (f : Fin 2 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj
        (BoundedFormula.orderedPairFormula (suffixIndex n 2 z) (prefixIndex n 2 0) (prefixIndex n 2 1)).toFormula
        (flatHistoryCutsFormula (suffixIndex n 2 stages) (suffixIndex n 2 history)
          (suffixIndex n 2 levels) (prefixIndex n 2 0) (prefixIndex n 2 1)))
        (extendMany 2 f env) ↔
      env z = ZFSet.pair (f 0) (f 1) ∧
        FlatHistoryCuts (env stages) (env history) (env levels) (f 0) (f 1) := by
    have allground := extendMany_members 2 f env ground members
    apply and_congr
    · rw [BoundedFormula.realize_toFormula M _ _ allground, BoundedFormula.truth_orderedPairFormula]
      simp only [extendMany_prefix, extendMany_suffix]
    · rw [M.realize_flatHistoryCutsFormula _ _ _ _ _ _ allground]
      simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    exact ⟨f 0, f 1, (actual f ground).1 body⟩
  · rintro ⟨row, A, equal, valid⟩
    have pairGround := equal ▸ members z
    let f : Fin 2 → ZFSet.{u} := ![row, A]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases (M.pair_left pairGround) (Fin.cases (M.pair_right pairGround) (fun j => Fin.elim0 j))
    exact ⟨f, ground, (actual f ground).2 ⟨equal, valid⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
