import OAI.SetTheory.PartitionPrinciple.Forcing.GroundForcingHistorySuccessors

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace BoundedFormula

def stageOneAssignmentsMemberFormula {n : Nat} (z I T : Fin n) : BoundedFormula n :=
  exMem I (exMem T.succ (exMem T.succ.succ
    (stageOneAssignmentFormula z.succ.succ.succ 2 1 0)))

theorem truth_stageOneAssignmentsMemberFormula {n : Nat} (z I T : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (stageOneAssignmentsMemberFormula z I T) env ↔
      env z ∈ stageOneAssignments (env I) (env T) := by
  simp only [stageOneAssignmentsMemberFormula, truth_exMem, truth_stageOneAssignmentFormula]
  exact (mem_stageOneAssignments _ _ _).symm

def stageOneAssignmentsSubsetFormula {n : Nat} (A I T : Fin n) : BoundedFormula n :=
  .allMem A (stageOneAssignmentsMemberFormula 0 I.succ T.succ)

theorem truth_stageOneAssignmentsSubsetFormula {n : Nat} (A I T : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (stageOneAssignmentsSubsetFormula A I T) env ↔
      env A ⊆ stageOneAssignments (env I) (env T) := by
  simp only [stageOneAssignmentsSubsetFormula, Truth, truth_stageOneAssignmentsMemberFormula]
  rfl

end BoundedFormula

namespace SetFormula

def stageOneCandidateFormula {n : Nat} (rows I T N z : Fin n) : SetFormula n :=
  let old := suffixIndex n 2
  let v := prefixIndex n 2
  exBlock 2 (.conj (BoundedFormula.orderedPairFormula (old z) (v 0) (v 1)).toFormula
    (.conj (.mem (v 0) (old rows))
      (.conj (BoundedFormula.stageOneAssignmentsSubsetFormula (v 1) (old I) (old T)).toFormula
        (hasInjectionFormula (v 1) (old N)))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneCandidateFormula {n : Nat} (rows I T N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneCandidateFormula rows I T N z) env ↔
      env z ∈ ZFSet.prod (env rows)
        (M.groundSmallSubsets (stageOneAssignments (env I) (env T)) (env N)) := by
  rw [stageOneCandidateFormula, realize_exBlock]
  have actual (fields : Fin 2 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets (.conj
        (BoundedFormula.orderedPairFormula (suffixIndex n 2 z) (prefixIndex n 2 0)
          (prefixIndex n 2 1)).toFormula
        (.conj (.mem (prefixIndex n 2 0) (suffixIndex n 2 rows))
          (.conj (BoundedFormula.stageOneAssignmentsSubsetFormula (prefixIndex n 2 1)
            (suffixIndex n 2 I) (suffixIndex n 2 T)).toFormula
            (hasInjectionFormula (prefixIndex n 2 1) (suffixIndex n 2 N)))))
        (extendMany 2 fields env) ↔
      env z = ZFSet.pair (fields 0) (fields 1) ∧ fields 0 ∈ env rows ∧
        fields 1 ⊆ stageOneAssignments (env I) (env T) ∧
        M.groundEmbeddable (fields 1) (env N) := by
    have bounds := extendMany_members 2 fields env ground members
    rw [Realize, BoundedFormula.realize_toFormula M _ _ bounds,
      BoundedFormula.truth_orderedPairFormula]
    apply and_congr Iff.rfl
    change (_ ∧ Realize M.sets _ _) ↔ _
    apply and_congr Iff.rfl
    rw [Realize, BoundedFormula.realize_toFormula M _ _ bounds,
      BoundedFormula.truth_stageOneAssignmentsSubsetFormula, M.realize_hasInjectionFormula _ _ _ bounds]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨fields, ground, body⟩
    obtain ⟨equal, row, subset, small⟩ := (actual fields ground).1 body
    rw [equal, ZFSet.pair_mem_prod, M.mem_groundSmallSubsets]
    exact ⟨row, ground 1, subset, small⟩
  · intro member
    obtain ⟨row, hrow, A, hA, equal⟩ := ZFSet.mem_prod.1 member
    obtain ⟨hA, subset, small⟩ := (M.mem_groundSmallSubsets _ _ _).1 hA
    have ground : ∀ j : Fin 2, (![row, A] : Fin 2 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.transitive (members rows) hrow) (Fin.cases hA (fun j => Fin.elim0 j))
    exact ⟨![row, A], ground, (actual ![row, A] ground).2 ⟨equal, hrow, subset, small⟩⟩

theorem realize_stageOneCandidateFormula_omega {n : Nat} (rows I T N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (naturals : env N = ZFSet.omega) :
    Realize M.sets (stageOneCandidateFormula rows I T N z) env ↔
      env z ∈ M.stageOneCandidateBound (env rows) (env I) (env T) := by
  rw [M.realize_stageOneCandidateFormula rows I T N z env members, naturals]
  rfl

end TransitiveGround

namespace SetFormula

def forcingHistoryConditionsOutputFormula {n : Nat}
    (output rows I T stages history levels N : Fin n) : SetFormula n :=
  exactSetFormula output (.conj
    (stageOneCandidateFormula rows.succ I.succ T.succ N.succ 0)
    (forcingHistoryConditionFormula stages.succ history.succ levels.succ 0))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_forcingHistoryConditionsOutputFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n : Nat} (output rows I T stages history levels N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (naturals : env N = ZFSet.omega) :
    Realize M.sets (forcingHistoryConditionsOutputFormula output rows I T stages history levels N) env ↔
      env output = M.forcingHistoryConditions (env rows) (env I) (env T)
        (env stages) (env history) (env levels) := by
  apply M.realize_exactSetFormula output _ env (members output)
  · intro z member
    have candidate := ((M.mem_forcingHistoryConditions _ _ _ _ _ _ _).1 member).1
    obtain ⟨row, hrow, A, ground, _, _, equal⟩ :=
      (M.mem_stageOneCandidateBound _ _ _ _).1 candidate
    exact equal ▸ M.orderedPair_mem pairing (M.transitive (members rows) hrow) ground
  · intro z ground
    rw [Realize, M.mem_forcingHistoryConditions]
    exact and_congr
      (M.realize_stageOneCandidateFormula_omega rows.succ I.succ T.succ N.succ 0
        (extend z env) (Fin.cases ground members) naturals)
      (M.realize_forcingHistoryConditionFormula pairing separation stages.succ history.succ levels.succ 0
        (extend z env) (Fin.cases ground members))

theorem exists_unique_forcingHistoryConditionsOutput
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rows I T stages history levels : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hLevels : levels ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    ∃ output ∈ M.sets,
      Realize M.sets (forcingHistoryConditionsOutputFormula 0 1 2 3 4 5 6 7)
        ![output, rows, I, T, stages, history, levels, ZFSet.omega] ∧
      ∀ other ∈ M.sets,
        Realize M.sets (forcingHistoryConditionsOutputFormula 0 1 2 3 4 5 6 7)
          ![other, rows, I, T, stages, history, levels, ZFSet.omega] → other = output := by
  have ground := M.forcingHistoryConditions_mem pairing unions powers separation
    hRows hI hT hStages hHistory hLevels omega
  have meaning (output : ZFSet.{u}) (hOutput : output ∈ M.sets) :
      Realize M.sets (forcingHistoryConditionsOutputFormula 0 1 2 3 4 5 6 7)
        ![output, rows, I, T, stages, history, levels, ZFSet.omega] ↔
      output = M.forcingHistoryConditions rows I T stages history levels :=
    M.realize_forcingHistoryConditionsOutputFormula pairing separation 0 1 2 3 4 5 6 7 _
      (Fin.cases hOutput (Fin.cases hRows (Fin.cases hI (Fin.cases hT
        (Fin.cases hStages (Fin.cases hHistory (Fin.cases hLevels (Fin.cases omega
          (fun j => Fin.elim0 j))))))))) rfl
  exact ⟨_, ground, (meaning _ ground).2 rfl, fun other member valid => (meaning other member).1 valid⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
