import OAI.SetTheory.PartitionPrinciple.Geometry.GroundEligibleCaps

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

noncomputable def identityIdealGraph (P r C : ZFSet.{u}) : ZFSet.{u} :=
  identityFunctionGraph (attachmentIdeal P r C)

theorem pair_mem_identityIdealGraph (P r C x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ identityIdealGraph P r C ↔
      x = y ∧ x ∈ P ∧ ZFSet.pair x C ∈ r := by
  rw [identityIdealGraph, pair_mem_identityFunctionGraph, mem_attachmentIdeal]

theorem identityIdealGraph_restrictedAction {P G r A m one C : ZFSet.{u}}
    (action : PosetActionCode G P m one r A) (hC : C ∈ P) :
    RestrictedActionCode P r A one C C (identityIdealGraph P r C) where
  shape := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_identityFunctionGraph (attachmentIdeal P r C) z).1 hz
    have member := ((mem_attachmentIdeal P r C x).1 hx).1
    exact ZFSet.pair_mem_prod.2 ⟨member, member⟩
  target_entry := action.one C hC
  entries x hx y hy := by
    rw [pair_mem_identityIdealGraph]
    constructor
    · rintro ⟨rfl, _, lower⟩
      exact ⟨lower, action.one x hx⟩
    · rintro ⟨lower, entry⟩
      have equal := (show FunctionGraphOn (ZFSet.prod G P) A from ⟨P, action.function⟩).unique
        entry (action.one x hx)
      exact ⟨equal.symm, hx, lower⟩

theorem identityInsertion_eligible {P G r μ A m one C E F : ZFSet.{u}}
    (action : PosetActionCode G P m one r A) (hOne : one ∈ G)
    (hC : C ∈ P) (hE : E ∈ P) (filter : MeetFilterCode P r μ F)
    (lower : ZFSet.pair C E ∈ r) (strict : ZFSet.pair E C ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair E x ∈ r) :
    EligibleTaskCode P G r μ A C C (identityIdealGraph P r C) E F :=
  ⟨hC, hC, hE, filter, lower, strict, above,
    one, hOne, identityIdealGraph_restrictedAction action hC⟩

noncomputable def identityInsertionTask (P r C E F label : ZFSet.{u}) : ZFSet.{u} :=
  literalTaskCode C C (identityIdealGraph P r C) E F label

theorem identityInsertionTask_injective (P r C E F : ZFSet.{u}) :
    Function.Injective (identityInsertionTask P r C E F) := by
  intro first second equal
  exact (literalTaskCode_inj.1 equal).2.2.2.2.2

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def identityInsertionTaskGraph (Labels I P r C E F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ label ∈ Labels, ∃ task ∈ I,
    z = ZFSet.pair label task ∧ task = identityInsertionTask P r C E F label)
    (ZFSet.prod Labels I)

theorem pair_mem_identityInsertionTaskGraph (Labels I P r C E F label task : ZFSet.{u}) :
    ZFSet.pair label task ∈ identityInsertionTaskGraph Labels I P r C E F ↔
      label ∈ Labels ∧ task ∈ I ∧ task = identityInsertionTask P r C E F label := by
  rw [identityInsertionTaskGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, equal, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, code⟩
  · rintro ⟨ha, hb, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, label, ha, task, hb, rfl, code⟩

namespace BoundedFormula

def identityInsertionGraphEntryFormula {n} (z Labels I C base E F : Fin n) : BoundedFormula n :=
  .exMem Labels (.exMem I.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (literalTaskFormula 0 C.succ.succ C.succ.succ base.succ.succ E.succ.succ F.succ.succ 1)))

theorem truth_identityInsertionGraphEntryFormula {n} (z Labels I C base E F : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (identityInsertionGraphEntryFormula z Labels I C base E F) env ↔
      ∃ label ∈ env Labels, ∃ task ∈ env I, env z = ZFSet.pair label task ∧
        task = literalTaskCode (env C) (env C) (env base) (env E) (env F) label := by
  simp only [identityInsertionGraphEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_literalTaskFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem identityIdealGraph_mem {P r C : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hC : C ∈ P) : identityIdealGraph P r C ∈ M.sets :=
  M.identityFunctionGraph_mem pairing unions powers separation
    (M.attachmentIdeal_mem separation hP hr (M.transitive hP hC))

theorem identityInsertionTask_mem {P G r μ A m one Labels C E F label : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hF : F ∈ M.sets)
    (action : PosetActionCode G P m one r A) (hOne : one ∈ G)
    (hC : C ∈ P) (hE : E ∈ P) (filter : MeetFilterCode P r μ F)
    (lower : ZFSet.pair C E ∈ r) (strict : ZFSet.pair E C ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair E x ∈ r) (hlabel : label ∈ Labels) :
    identityInsertionTask P r C E F label ∈ M.groundEligibleTasks P G r μ A Labels :=
  (M.literalTaskCode_mem_groundEligibleTasks P G r μ A Labels C C (identityIdealGraph P r C)
    E F label).2 ⟨hlabel, M.identityIdealGraph_mem pairing unions powers separation hP hr hC,
      hF, identityInsertion_eligible action hOne hC hE filter lower strict above⟩

theorem identityInsertionTaskGraph_mem {Labels I P r C E F : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hC : C ∈ P) (hE : E ∈ P) (hF : F ∈ M.sets) :
    identityInsertionTaskGraph Labels I P r C E F ∈ M.sets := by
  let params := extend Labels (extend I (extend C (extend (identityIdealGraph P r C)
    (extend E (extend F Fin.elim0)))))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hLabels (Fin.cases hI
    (Fin.cases (M.transitive hP hC) (Fin.cases (M.identityIdealGraph_mem pairing unions powers separation hP hr hC)
      (Fin.cases (M.transitive hP hE) (Fin.cases hF (fun j => Fin.elim0 j))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.identityInsertionGraphEntryFormula 0 1 2 3 4 5 6) params members
    (M.prod_mem pairing unions powers separation hLabels hI)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.identityInsertionGraphEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod Labels I) = identityInsertionTaskGraph Labels I P r C E F := by
    apply ZFSet.ext
    intro z
    rw [identityInsertionTaskGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_identityInsertionGraphEntryFormula 0 1 2 3 4 5 6 _)
  exact equal ▸ selected

theorem identityInsertionTaskGraph_injection {P G r μ A m one Labels C E F : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hF : F ∈ M.sets)
    (action : PosetActionCode G P m one r A) (hOne : one ∈ G)
    (hC : C ∈ P) (hE : E ∈ P) (filter : MeetFilterCode P r μ F)
    (lower : ZFSet.pair C E ∈ r) (strict : ZFSet.pair E C ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair E x ∈ r) :
    InjectionCode Labels (M.groundEligibleTasks P G r μ A Labels)
      (identityInsertionTaskGraph Labels (M.groundEligibleTasks P G r μ A Labels) P r C E F) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  have every (label : ZFSet.{u}) (hlabel : label ∈ Labels) : identityInsertionTask P r C E F label ∈ I :=
    M.identityInsertionTask_mem pairing unions powers separation hP hr hF action hOne hC hE
      filter lower strict above hlabel
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
  · intro label hlabel
    refine ⟨identityInsertionTask P r C E F label,
      (pair_mem_identityInsertionTaskGraph Labels I P r C E F _ _).2 ⟨hlabel, every label hlabel, rfl⟩, ?_⟩
    intro task entry
    exact ((pair_mem_identityInsertionTaskGraph Labels I P r C E F _ _).1 entry).2.2
  · intro first second task oneEntry twoEntry
    have firstEq := ((pair_mem_identityInsertionTaskGraph Labels I P r C E F _ _).1 oneEntry).2.2
    have secondEq := ((pair_mem_identityInsertionTaskGraph Labels I P r C E F _ _).1 twoEntry).2.2
    exact identityInsertionTask_injective P r C E F (firstEq.symm.trans secondEq)

theorem identityInsertionTask_fields {P G r μ A m one Labels C E F label : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hF : F ∈ M.sets)
    (action : PosetActionCode G P m one r A) (hOne : one ∈ G)
    (hC : C ∈ P) (hE : E ∈ P) (filter : MeetFilterCode P r μ F)
    (lower : ZFSet.pair C E ∈ r) (strict : ZFSet.pair E C ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair E x ∈ r) (hlabel : label ∈ Labels) (j : Fin 6) :
    ZFSet.pair (identityInsertionTask P r C E F label)
      (literalTaskField C C (identityIdealGraph P r C) E F label j) ∈
      literalTaskFieldGraph (M.groundEligibleTasks P G r μ A Labels) P
        (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels j := by
  have base := identityIdealGraph_restrictedAction action hC
  have hBase := (M.mem_groundRelations P P _).2
    ⟨M.identityIdealGraph_mem pairing unions powers separation hP hr hC, base.shape⟩
  exact (literalTaskFieldGraph_entry_iff hC hC hBase hE
    ((M.mem_groundMeetFilters P r μ F).2 ⟨hF, filter⟩) hlabel j).2
    ⟨M.identityInsertionTask_mem pairing unions powers separation hP hr hF action hOne hC hE
      filter lower strict above hlabel, rfl⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
