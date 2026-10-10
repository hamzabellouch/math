import OAI.SetTheory.PartitionPrinciple.Definability.PreservedMainPrefixHistoryFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def mainPrefixAtIndexFormula {n} (T q : Fin n) : SetFormula n :=
  exBlock 2 (BoundedFormula.mainPrefixTupleFormula (suffixIndex n 2 q)
    (suffixIndex n 2 T) (prefixIndex n 2 0) (prefixIndex n 2 1)).toFormula

def mainPrefixAtSuccessorFormula {n} (α q : Fin n) : SetFormula n :=
  ex (.conj (BoundedFormula.successorFormula 0 α.succ).toFormula
    (mainPrefixAtIndexFormula 0 q.succ))

def mainPrefixHistoryExtendsFormula {n} (p q : Fin n) : SetFormula n :=
  .all (.all (imp (BoundedFormula.pairMembershipFormula 1 0 p.succ.succ).toFormula
    (mainPrefixExtensionFormula 0 q.succ.succ)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixAtIndexFormula {n} (T q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixAtIndexFormula T q) env ↔ MainPrefixAtIndex (env T) (env q) := by
  rw [mainPrefixAtIndexFormula, realize_exBlock]
  have actual (f : Fin 2 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :=
    BoundedFormula.realize_mainPrefixTupleFormula M (suffixIndex n 2 q)
      (suffixIndex n 2 T) (prefixIndex n 2 0) (prefixIndex n 2 1)
      (extendMany 2 f env) (extendMany_members 2 f env ground members)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨f, ground, recognized⟩
    exact ⟨f 0, f 1, (actual f ground).1 recognized⟩
  · rintro ⟨S, E, encoded⟩
    have fields := M.mainPrefixCode_fields_mem (encoded ▸ members q)
    let f : Fin 2 → ZFSet.{u} := Fin.cases S (fun _ => E)
    have ground : ∀ j, f j ∈ M.sets := Fin.cases fields.2.1 (fun _ => fields.2.2)
    exact ⟨f, ground, (actual f ground).2 encoded⟩

theorem realize_mainPrefixAtSuccessorFormula {n} (α q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixAtSuccessorFormula α q) env ↔
      MainPrefixAtIndex (insert (env α) (env α)) (env q) := by
  rw [mainPrefixAtSuccessorFormula, realize_ex]
  have actual T (ground : T ∈ M.sets) :
      Realize M.sets (.conj (BoundedFormula.successorFormula 0 α.succ).toFormula
        (mainPrefixAtIndexFormula 0 q.succ)) (extend T env) ↔
      T = insert (env α) (env α) ∧ MainPrefixAtIndex T (env q) := by
    change (_ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases ground members),
      BoundedFormula.truth_successorFormula,
      M.realize_mainPrefixAtIndexFormula _ _ _ (Fin.cases ground members)]
    rfl
  constructor
  · rintro ⟨T, ground, recognized⟩
    obtain ⟨rfl, code⟩ := (actual T ground).1 recognized
    exact code
  · intro code
    obtain ⟨S, E, equal⟩ := code
    have ground := (M.mainPrefixCode_fields_mem (equal ▸ members q)).1
    exact ⟨_, ground, (actual _ ground).2 ⟨rfl, S, E, equal⟩⟩

theorem realize_mainPrefixHistoryExtendsFormula {n} (p q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixHistoryExtendsFormula p q) env ↔
      MainPrefixHistoryExtends (env p) (env q) := by
  change (∀ i ∈ M.sets, ∀ old ∈ M.sets, Realize M.sets
    (imp (BoundedFormula.pairMembershipFormula 1 0 p.succ.succ).toFormula
      (mainPrefixExtensionFormula 0 q.succ.succ)) (extend old (extend i env))) ↔ _
  have actual i old (hi : i ∈ M.sets) (ho : old ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.pairMembershipFormula 1 0 p.succ.succ).toFormula
          (mainPrefixExtensionFormula 0 q.succ.succ)) (extend old (extend i env)) ↔
      (ZFSet.pair i old ∈ env p → MainPrefixExtends old (env q)) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _ (Fin.cases ho (Fin.cases hi members)),
      BoundedFormula.truth_pairMembershipFormula,
      M.realize_mainPrefixExtensionFormula _ _ _ (Fin.cases ho (Fin.cases hi members))]
    rfl
  constructor
  · intro recognized i old entry
    have pairGround := M.transitive (members p) entry
    exact (actual i old (M.pair_left pairGround) (M.pair_right pairGround)).1
      (recognized i (M.pair_left pairGround) old (M.pair_right pairGround)) entry
  · intro history i hi old ho
    exact (actual i old hi ho).2 (history i old)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def mainPrefixTraceBranchFormula {n} (seed g α p y : Fin n) : SetFormula n :=
  disj (.conj (BoundedFormula.emptyFormula α).toFormula (.equal y seed))
    (.conj (.neg (BoundedFormula.emptyFormula α).toFormula)
      (ex (.conj (mainPrefixHistoryUnionFormula p.succ 0)
        (BoundedFormula.pairMembershipFormula 0 y.succ g.succ).toFormula)))

def mainPrefixTraceStepFormula {n} (B seed g α p y : Fin n) : SetFormula n :=
  .conj (.mem y B) (.conj (mainPrefixAtSuccessorFormula α y)
    (.conj (mainPrefixHistoryExtendsFormula p y) (mainPrefixTraceBranchFormula seed g α p y)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixTraceBranchFormula {n} (seed g α p y : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixTraceBranchFormula seed g α p y) env ↔
      ((env α = ∅ ∧ env y = env seed) ∨ (env α ≠ ∅ ∧
        ∃ input, MainPrefixHistoryUnionCode (env p) input ∧ ZFSet.pair input (env y) ∈ env g)) := by
  have empty := (BoundedFormula.realize_toFormula M (BoundedFormula.emptyFormula α) env members).trans
    (BoundedFormula.truth_emptyFormula α env)
  rw [mainPrefixTraceBranchFormula, realize_disj]
  change ((_ ∧ _) ∨ ((¬ _) ∧ _)) ↔ _
  rw [empty]
  apply or_congr Iff.rfl
  apply and_congr Iff.rfl
  rw [realize_ex]
  have actual input (ground : input ∈ M.sets) :
      Realize M.sets (.conj (mainPrefixHistoryUnionFormula p.succ 0)
        (BoundedFormula.pairMembershipFormula 0 y.succ g.succ).toFormula) (extend input env) ↔
      MainPrefixHistoryUnionCode (env p) input ∧ ZFSet.pair input (env y) ∈ env g := by
    change (_ ∧ _) ↔ _
    rw [M.realize_mainPrefixHistoryUnionFormula _ _ _ (Fin.cases ground members),
      BoundedFormula.realize_toFormula M _ _ (Fin.cases ground members),
      BoundedFormula.truth_pairMembershipFormula]
    rfl
  constructor
  · rintro ⟨input, ground, recognized⟩
    exact ⟨input, (actual input ground).1 recognized⟩
  · rintro ⟨input, union, entry⟩
    have ground := M.pair_left (M.transitive (members g) entry)
    exact ⟨input, ground, (actual input ground).2 ⟨union, entry⟩⟩

theorem realize_mainPrefixTraceStepFormula {n} (B seed g α p y : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixTraceStepFormula B seed g α p y) env ↔
      MainPrefixTraceStepCode (env B) (env seed) (env g) (env α) (env p) (env y) := by
  unfold mainPrefixTraceStepFormula MainPrefixTraceStepCode
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  rw [M.realize_mainPrefixAtSuccessorFormula _ _ _ members,
    M.realize_mainPrefixHistoryExtendsFormula _ _ _ members,
    M.realize_mainPrefixTraceBranchFormula _ _ _ _ _ _ members]
  rfl

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
