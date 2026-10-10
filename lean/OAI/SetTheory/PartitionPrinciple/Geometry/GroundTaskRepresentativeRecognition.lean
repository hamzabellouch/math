import OAI.SetTheory.PartitionPrinciple.Definability.GroundEligibleTaskSetRecognition
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRecursiveActions

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def groundRelationsFormula {n} (output P Q : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.relationBetweenFormula P.succ Q.succ 0).toFormula

def groundMeetFiltersFormula {n} (output P r μ : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.meetFilterFormula P.succ r.succ μ.succ 0).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundRelationsFormula {n} (output P Q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (groundRelationsFormula output P Q) env ↔
      env output = M.groundRelations (env P) (env Q) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => ((M.mem_groundRelations _ _ z).1 hz).1)
  intro z hz
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
    BoundedFormula.truth_relationBetweenFormula, M.mem_groundRelations]
  exact ⟨fun subset => ⟨hz, subset⟩, And.right⟩

theorem realize_groundMeetFiltersFormula {n} (output P r μ : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundMeetFiltersFormula output P r μ) env ↔
      env output = M.groundMeetFilters (env P) (env r) (env μ) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => ((M.mem_groundMeetFilters _ _ _ z).1 hz).1)
  intro z hz
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
    BoundedFormula.truth_meetFilterFormula P.succ r.succ μ.succ 0 (extend z env) meet, M.mem_groundMeetFilters]
  exact ⟨fun filter => ⟨hz, filter⟩, And.right⟩

end TransitiveGround

namespace SetFormula

def groundLiteralTaskFieldFormula {n} (j : Fin 6) (output I P r μ Labels : Fin n) : SetFormula n :=
  ex (ex (.conj (groundRelationsFormula 1 P.succ.succ P.succ.succ)
    (.conj (groundMeetFiltersFormula 0 P.succ.succ r.succ.succ μ.succ.succ)
      (literalTaskFieldSetFormula j output.succ.succ I.succ.succ P.succ.succ 1 0 Labels.succ.succ))))

def taskTransportSetFormula {n} (output G I P R U Labels A : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.taskTransportEntryFormula 0 G.succ I.succ P.succ R.succ U.succ Labels.succ A.succ).toFormula

def groundTaskTransportFormula {n} (output P G r μ A Labels : Fin n) : SetFormula n :=
  let old (i : Fin n) := i.succ.succ.succ
  ex (ex (ex (.conj (groundEligibleTasksFormula 2 (old P) (old G) (old r) (old μ) (old A) (old Labels))
    (.conj (groundRelationsFormula 1 (old P) (old P))
      (.conj (groundMeetFiltersFormula 0 (old P) (old r) (old μ))
        (taskTransportSetFormula (old output) (old G) 2 (old P) 1 0 (old Labels) (old A)))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_groundLiteralTaskFieldFormula {n} (j : Fin 6) (output I P r μ Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundLiteralTaskFieldFormula j output I P r μ Labels) env ↔
      env output = literalTaskFieldGraph (env I) (env P)
        (M.groundRelations (env P) (env P)) (M.groundMeetFilters (env P) (env r) (env μ)) (env Labels) j := by
  simp only [groundLiteralTaskFieldFormula, realize_ex, Realize]
  constructor
  · rintro ⟨R, hR, U, hU, relations, filters, result⟩
    have bounds : ∀ i, (extend U (extend R env)) i ∈ M.sets := Fin.cases hU (Fin.cases hR members)
    have eqR := (M.realize_groundRelationsFormula 1 P.succ.succ P.succ.succ _ bounds).1 relations
    have eqU := (M.realize_groundMeetFiltersFormula 0 P.succ.succ r.succ.succ μ.succ.succ _ bounds meet).1 filters
    have outputEq := (M.realize_literalTaskFieldSetFormula pairing unions powers separation
      j output.succ.succ I.succ.succ P.succ.succ 1 0 Labels.succ.succ _ bounds).1 result
    change R = M.groundRelations (env P) (env P) at eqR
    change U = M.groundMeetFilters (env P) (env r) (env μ) at eqU
    change env output = literalTaskFieldGraph (env I) (env P) R U (env Labels) j at outputEq
    rwa [eqR, eqU] at outputEq
  · intro equal
    let R := M.groundRelations (env P) (env P)
    let U := M.groundMeetFilters (env P) (env r) (env μ)
    have hR : R ∈ M.sets := M.groundRelations_mem pairing unions powers separation (members P) (members P)
    have hU : U ∈ M.sets := M.groundMeetFilters_mem powers separation (members P) (members r) (members μ) meet
    have bounds : ∀ i, (extend U (extend R env)) i ∈ M.sets := Fin.cases hU (Fin.cases hR members)
    exact ⟨R, hR, U, hU,
      (M.realize_groundRelationsFormula 1 P.succ.succ P.succ.succ _ bounds).2 rfl,
      (M.realize_groundMeetFiltersFormula 0 P.succ.succ r.succ.succ μ.succ.succ _ bounds meet).2 rfl,
      (M.realize_literalTaskFieldSetFormula pairing unions powers separation
        j output.succ.succ I.succ.succ P.succ.succ 1 0 Labels.succ.succ _ bounds).2 equal⟩

theorem realize_taskTransportSetFormula {n} (output G I P R U Labels A : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (taskTransportSetFormula output G I P R U Labels A) env ↔
      env output = taskTransportGraph (env G) (env I) (env P) (env R) (env U) (env Labels) (env A) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => M.transitive (M.taskTransportGraph_mem pairing unions powers separation
      (members G) (members I) (members P) (members R) (members U) (members Labels) (members A)) hz)
  intro z hz
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
    BoundedFormula.truth_taskTransportEntryFormula]
  rw [taskTransportGraph, ZFSet.mem_sep]
  refine ⟨fun entry => ⟨?_, entry⟩, And.right⟩
  obtain ⟨g, hg, t, ht, t', ht', equal, _⟩ := entry
  change z = ZFSet.pair (ZFSet.pair g t) t' at equal
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, ht⟩, ht'⟩

theorem realize_groundTaskTransportFormula {n} (output P G r μ A Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundTaskTransportFormula output P G r μ A Labels) env ↔
      env output = M.groundTaskTransport (env P) (env G) (env r) (env μ) (env A) (env Labels) := by
  simp only [groundTaskTransportFormula, realize_ex, Realize]
  constructor
  · rintro ⟨tasks, hTasks, R, hR, U, hU, eligible, relations, filters, result⟩
    have bounds : ∀ i, (extend U (extend R (extend tasks env))) i ∈ M.sets :=
      Fin.cases hU (Fin.cases hR (Fin.cases hTasks members))
    have eqI := (M.realize_groundEligibleTasksFormula pairing unions powers separation
      2 P.succ.succ.succ G.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ
      A.succ.succ.succ Labels.succ.succ.succ _ bounds meet).1 eligible
    have eqR := (M.realize_groundRelationsFormula 1 P.succ.succ.succ P.succ.succ.succ _ bounds).1 relations
    have eqU := (M.realize_groundMeetFiltersFormula 0 P.succ.succ.succ r.succ.succ.succ
      μ.succ.succ.succ _ bounds meet).1 filters
    have outputEq := (M.realize_taskTransportSetFormula pairing unions powers separation
      output.succ.succ.succ G.succ.succ.succ 2 P.succ.succ.succ 1 0
      Labels.succ.succ.succ A.succ.succ.succ _ bounds).1 result
    change tasks = M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels) at eqI
    change R = M.groundRelations (env P) (env P) at eqR
    change U = M.groundMeetFilters (env P) (env r) (env μ) at eqU
    change env output = taskTransportGraph (env G) tasks (env P) R U (env Labels) (env A) at outputEq
    rw [eqI, eqR, eqU] at outputEq
    exact outputEq
  · intro equal
    let tasks := M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels)
    let R := M.groundRelations (env P) (env P)
    let U := M.groundMeetFilters (env P) (env r) (env μ)
    have hTasks : tasks ∈ M.sets := M.groundEligibleTasks_mem pairing unions powers separation
      (members P) (members G) (members r) (members μ) (members A) (members Labels) meet
    have hR : R ∈ M.sets := M.groundRelations_mem pairing unions powers separation (members P) (members P)
    have hU : U ∈ M.sets := M.groundMeetFilters_mem powers separation (members P) (members r) (members μ) meet
    have bounds : ∀ i, (extend U (extend R (extend tasks env))) i ∈ M.sets :=
      Fin.cases hU (Fin.cases hR (Fin.cases hTasks members))
    exact ⟨tasks, hTasks, R, hR, U, hU,
      (M.realize_groundEligibleTasksFormula pairing unions powers separation
        2 P.succ.succ.succ G.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ
        A.succ.succ.succ Labels.succ.succ.succ _ bounds meet).2 rfl,
      (M.realize_groundRelationsFormula 1 P.succ.succ.succ P.succ.succ.succ _ bounds).2 rfl,
      (M.realize_groundMeetFiltersFormula 0 P.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ _ bounds meet).2 rfl,
      (M.realize_taskTransportSetFormula pairing unions powers separation
        output.succ.succ.succ G.succ.succ.succ 2 P.succ.succ.succ 1 0
        Labels.succ.succ.succ A.succ.succ.succ _ bounds).2 equal⟩

end TransitiveGround

def TaskRepresentativesCode (Reps I P G r A R U Labels : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc I G Reps ∧ ∀ i g, ZFSet.pair i g ∈ Reps →
    TaskRepresentative P r A R U Labels i g

namespace BoundedFormula

def taskRepresentativesFormula {n} (Reps I P G r A R U Labels : Fin n) : BoundedFormula n :=
  .conj (functionFormula I G Reps)
    (.allMem I (.allMem G.succ (imp (pairMembershipFormula 1 0 Reps.succ.succ)
      (taskRepresentativeFormula 1 0 P.succ.succ r.succ.succ A.succ.succ
        R.succ.succ U.succ.succ Labels.succ.succ))))

theorem truth_taskRepresentativesFormula {n} (Reps I P G r A R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskRepresentativesFormula Reps I P G r A R U Labels) env ↔
      TaskRepresentativesCode (env Reps) (env I) (env P) (env G) (env r)
        (env A) (env R) (env U) (env Labels) := by
  simp only [taskRepresentativesFormula, Truth, truth_functionFormula,
    truth_imp, truth_pairMembershipFormula, truth_taskRepresentativeFormula]
  change (_ ∧ ∀ i ∈ env I, ∀ g ∈ env G, ZFSet.pair i g ∈ env Reps →
    TaskRepresentative (env P) (env r) (env A) (env R) (env U) (env Labels) i g) ↔ _
  constructor
  · rintro ⟨function, valid⟩
    refine ⟨function, ?_⟩
    intro i g entry
    obtain ⟨hi, hg⟩ := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact valid i hi g hg entry
  · rintro ⟨function, valid⟩
    exact ⟨function, fun i _ g _ entry => valid i g entry⟩

end BoundedFormula

namespace SetFormula

def groundTaskRepresentativesFormula {n} (Reps P G r μ A Labels : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (.conj (groundEligibleTasksFormula (field 0) (old P) (old G)
    (old r) (old μ) (old A) (old Labels))
    (.conj (groundRelationsFormula (field 1) (old P) (old P))
      (.conj (groundMeetFiltersFormula (field 2) (old P) (old r) (old μ))
        (BoundedFormula.taskRepresentativesFormula (old Reps) (field 0) (old P) (old G)
          (old r) (old A) (field 1) (field 2) (old Labels)).toFormula)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundTaskRepresentativesFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (Reps P G r μ A Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundTaskRepresentativesFormula Reps P G r μ A Labels) env ↔
      TaskRepresentativesCode (env Reps)
        (M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels))
        (env P) (env G) (env r) (env A) (M.groundRelations (env P) (env P))
        (M.groundMeetFilters (env P) (env r) (env μ)) (env Labels) := by
  rw [groundTaskRepresentativesFormula, realize_exBlock]
  constructor
  · rintro ⟨fields, fieldMembers, tasks, relations, filters, selected⟩
    have bounds := extendMany_members 3 fields env fieldMembers members
    have tasksEq := (M.realize_groundEligibleTasksFormula pairing unions powers separation
      (prefixIndex n 3 0) (suffixIndex n 3 P) (suffixIndex n 3 G) (suffixIndex n 3 r)
      (suffixIndex n 3 μ) (suffixIndex n 3 A) (suffixIndex n 3 Labels) _ bounds
      (by simpa only [extendMany_suffix] using meet)).1 tasks
    have relationsEq := (M.realize_groundRelationsFormula (prefixIndex n 3 1)
      (suffixIndex n 3 P) (suffixIndex n 3 P) _ bounds).1 relations
    have filtersEq := (M.realize_groundMeetFiltersFormula (prefixIndex n 3 2)
      (suffixIndex n 3 P) (suffixIndex n 3 r) (suffixIndex n 3 μ) _ bounds
      (by simpa only [extendMany_suffix] using meet)).1 filters
    have represented := (BoundedFormula.truth_taskRepresentativesFormula
      (suffixIndex n 3 Reps) (prefixIndex n 3 0) (suffixIndex n 3 P) (suffixIndex n 3 G)
      (suffixIndex n 3 r) (suffixIndex n 3 A) (prefixIndex n 3 1) (prefixIndex n 3 2)
      (suffixIndex n 3 Labels) _).1 ((BoundedFormula.realize_toFormula M _ _ bounds).1 selected)
    simp only [extendMany_prefix, extendMany_suffix] at tasksEq relationsEq filtersEq represented
    rwa [tasksEq, relationsEq, filtersEq] at represented
  · intro selected
    let I := M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels)
    let R := M.groundRelations (env P) (env P)
    let U := M.groundMeetFilters (env P) (env r) (env μ)
    let fields : Fin 3 → ZFSet.{u} := Fin.cases I (Fin.cases R (fun _ => U))
    have fieldMembers : ∀ j, fields j ∈ M.sets :=
      Fin.cases (M.groundEligibleTasks_mem pairing unions powers separation
        (members P) (members G) (members r) (members μ) (members A) (members Labels) meet)
        (Fin.cases (M.groundRelations_mem pairing unions powers separation (members P) (members P))
          (fun _ => M.groundMeetFilters_mem powers separation (members P) (members r) (members μ) meet))
    have bounds := extendMany_members 3 fields env fieldMembers members
    refine ⟨fields, fieldMembers, ?_, ?_, ?_, ?_⟩
    · apply (M.realize_groundEligibleTasksFormula pairing unions powers separation
        (prefixIndex n 3 0) (suffixIndex n 3 P) (suffixIndex n 3 G) (suffixIndex n 3 r)
        (suffixIndex n 3 μ) (suffixIndex n 3 A) (suffixIndex n 3 Labels) _ bounds
        (by simpa only [extendMany_suffix] using meet)).2
      simp only [extendMany_prefix, extendMany_suffix]
      rfl
    · apply (M.realize_groundRelationsFormula (prefixIndex n 3 1)
        (suffixIndex n 3 P) (suffixIndex n 3 P) _ bounds).2
      simp only [extendMany_prefix, extendMany_suffix]
      rfl
    · apply (M.realize_groundMeetFiltersFormula (prefixIndex n 3 2)
        (suffixIndex n 3 P) (suffixIndex n 3 r) (suffixIndex n 3 μ) _ bounds
        (by simpa only [extendMany_suffix] using meet)).2
      simp only [extendMany_prefix, extendMany_suffix]
      rfl
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      apply (BoundedFormula.truth_taskRepresentativesFormula
        (suffixIndex n 3 Reps) (prefixIndex n 3 0) (suffixIndex n 3 P) (suffixIndex n 3 G)
        (suffixIndex n 3 r) (suffixIndex n 3 A) (prefixIndex n 3 1) (prefixIndex n 3 2)
        (suffixIndex n 3 Labels) _).2
      simp only [extendMany_prefix, extendMany_suffix]
      exact selected

end TransitiveGround

end PartitionPilot.Forcing

end OAI
