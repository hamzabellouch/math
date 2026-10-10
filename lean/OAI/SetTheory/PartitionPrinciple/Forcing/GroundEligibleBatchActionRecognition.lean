import OAI.SetTheory.PartitionPrinciple.Definability.GroundDefinableRelationProducts
import OAI.SetTheory.PartitionPrinciple.Definability.GroundRecursiveActionFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundTaskRepresentativeRecognition

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def definable_indexedTaskAction : GroundDefinableFunction M
    (fun env : Fin 5 → ZFSet.{u} => indexedTaskActionGraph (env 0) (env 1) (env 2) (env 3) (env 4)) where
  formula := indexedTaskActionGraphFormula 0 1 2 3 4 5
  closed := fun _ members => M.indexedTaskActionGraph_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4)
  correct := fun env members z hz => M.realize_indexedTaskActionGraphFormula pairing
    0 1 2 3 4 5 (extend z env) (Fin.cases hz members)

noncomputable def definable_taggedAction : GroundDefinableFunction M
    (fun env : Fin 5 → ZFSet.{u} => taggedActionGraph (env 0) (env 1) (env 2) (env 3) (env 4)) where
  formula := taggedActionGraphFormula 0 1 2 3 4 5
  closed := fun _ members => M.taggedActionGraph_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4)
  correct := fun env members z hz => M.realize_taggedActionGraphFormula pairing
    0 1 2 3 4 5 (extend z env) (Fin.cases hz members)

noncomputable def definable_constantBatchAction : GroundDefinableFunction M
    (fun env : Fin 7 → ZFSet.{u} =>
      let N := indexedAttachmentFresh (env 1) (constantFamilyGraph (env 1) (env 2))
        (constantFamilyGraph (env 1) (env 3)) (env 5)
      taggedActionGraph (env 0) (env 2) N (env 4)
        (indexedTaskActionGraph (env 0) (env 1) (env 2) N (env 6))) := by
  let v : Fin 7 → GroundSetTerm M 7 := GroundSetTerm.var M
  let pointFamily := GroundSetTerm.app (M.definable_constantFamily pairing unions powers separation)
    (Fin.cases (v 1) (Fin.cases (v 2) Fin.elim0))
  let orderFamily := GroundSetTerm.app (M.definable_constantFamily pairing unions powers separation)
    (Fin.cases (v 1) (Fin.cases (v 3) Fin.elim0))
  let fresh := GroundSetTerm.app (M.definable_indexedFresh pairing unions powers separation)
    (Fin.cases (v 1) (Fin.cases pointFamily (Fin.cases orderFamily (Fin.cases (v 5) Fin.elim0))))
  let action := GroundSetTerm.app (M.definable_indexedTaskAction pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 2) (Fin.cases fresh (Fin.cases (v 6) Fin.elim0)))))
  let tagged := GroundSetTerm.app (M.definable_taggedAction pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (v 2) (Fin.cases fresh (Fin.cases (v 4) (Fin.cases action Fin.elim0)))))
  exact tagged.definition.congr (fun _ => rfl)

noncomputable def constantBatchActionFormula {n} (output G I P r A Sources T : Fin n) : SetFormula n :=
  SetFormula.reindex
    (Fin.cases output (Fin.cases G (Fin.cases I (Fin.cases P
      (Fin.cases r (Fin.cases A (Fin.cases Sources (fun _ => T))))))))
    (M.definable_constantBatchAction pairing unions powers separation).formula

theorem realize_constantBatchActionFormula {n} (output G I P r A Sources T : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.constantBatchActionFormula pairing unions powers separation output G I P r A Sources T) env ↔
      env output =
        let N := indexedAttachmentFresh (env I) (constantFamilyGraph (env I) (env P))
          (constantFamilyGraph (env I) (env r)) (env Sources)
        taggedActionGraph (env G) (env P) N (env A)
          (indexedTaskActionGraph (env G) (env I) (env P) N (env T)) := by
  unfold constantBatchActionFormula
  rw [realize_reindex]
  let args : Fin 7 → ZFSet.{u} := Fin.cases (env G) (Fin.cases (env I) (Fin.cases (env P)
    (Fin.cases (env r) (Fin.cases (env A) (Fin.cases (env Sources) (fun _ => env T))))))
  have ground : ∀ j, args j ∈ M.sets := Fin.cases (members G) (Fin.cases (members I)
    (Fin.cases (members P) (Fin.cases (members r) (Fin.cases (members A)
      (Fin.cases (members Sources) (fun _ => members T))))))
  have equal : (fun j => env (Fin.cases output (Fin.cases G (Fin.cases I (Fin.cases P
      (Fin.cases r (Fin.cases A (Fin.cases Sources (fun _ => T))))))) j)) = extend (env output) args := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))))) j
  rw [equal]
  exact (M.definable_constantBatchAction pairing unions powers separation).correct args ground
    (env output) (members output)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def groundEligibleBatchActionFormula {n} (output P G r μ A Labels : Fin n) : SetFormula n :=
  let old (i : Fin n) := i.succ.succ.succ
  ex (ex (ex
    (.conj (groundEligibleTasksFormula 2 (old P) (old G) (old r) (old μ) (old A) (old Labels))
      (.conj (groundLiteralTaskFieldFormula 0 1 2 (old P) (old r) (old μ) (old Labels))
        (.conj (groundTaskTransportFormula 0 (old P) (old G) (old r) (old μ) (old A) (old Labels))
          (M.constantBatchActionFormula pairing unions powers separation
            (old output) (old G) 2 (old P) (old r) (old A) 1 0))))))

theorem realize_groundEligibleBatchActionFormula {n} (output P G r μ A Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (M.groundEligibleBatchActionFormula pairing unions powers separation
      output P G r μ A Labels) env ↔
      env output = M.groundEligibleBatchAction (env P) (env G) (env r) (env μ) (env A) (env Labels) := by
  simp only [groundEligibleBatchActionFormula, realize_ex, Realize]
  constructor
  · rintro ⟨tasks, hTasks, sources, hSources, transport, hTransport, taskCode, sourceCode, transportCode, actionCode⟩
    have bounds : ∀ j, (extend transport (extend sources (extend tasks env))) j ∈ M.sets :=
      Fin.cases hTransport (Fin.cases hSources (Fin.cases hTasks members))
    have eqTasks := (M.realize_groundEligibleTasksFormula pairing unions powers separation
      2 P.succ.succ.succ G.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ
      A.succ.succ.succ Labels.succ.succ.succ _ bounds meet).1 taskCode
    have eqSources := (M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
      0 1 2 P.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ Labels.succ.succ.succ _ bounds meet).1 sourceCode
    have eqTransport := (M.realize_groundTaskTransportFormula pairing unions powers separation
      0 P.succ.succ.succ G.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ
      A.succ.succ.succ Labels.succ.succ.succ _ bounds meet).1 transportCode
    have outputEq := (M.realize_constantBatchActionFormula pairing unions powers separation
      output.succ.succ.succ G.succ.succ.succ 2 P.succ.succ.succ r.succ.succ.succ
      A.succ.succ.succ 1 0 _ bounds).1 actionCode
    change tasks = M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels) at eqTasks
    change sources = literalTaskFieldGraph tasks (env P) (M.groundRelations (env P) (env P))
      (M.groundMeetFilters (env P) (env r) (env μ)) (env Labels) 0 at eqSources
    change transport = M.groundTaskTransport (env P) (env G) (env r) (env μ) (env A) (env Labels) at eqTransport
    change env output = taggedActionGraph (env G) (env P)
      (indexedAttachmentFresh tasks (constantFamilyGraph tasks (env P)) (constantFamilyGraph tasks (env r)) sources)
      (env A) (indexedTaskActionGraph (env G) tasks (env P)
        (indexedAttachmentFresh tasks (constantFamilyGraph tasks (env P)) (constantFamilyGraph tasks (env r)) sources)
        transport) at outputEq
    rw [eqSources, eqTasks, eqTransport] at outputEq
    exact outputEq
  · intro equal
    let tasks := M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels)
    let sources := literalTaskSourceGraph tasks (env P) (M.groundRelations (env P) (env P))
      (M.groundMeetFilters (env P) (env r) (env μ)) (env Labels)
    let transport := M.groundTaskTransport (env P) (env G) (env r) (env μ) (env A) (env Labels)
    obtain ⟨hTasks, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
      (members P) (members G) (members r) (members μ) (members A) (members Labels) meet
    have hSources : sources ∈ M.sets := (fields 0).1
    have hTransport : transport ∈ M.sets := M.groundTaskTransport_mem pairing unions powers separation
      (members P) (members G) (members r) (members μ) (members A) (members Labels) meet
    have bounds : ∀ j, (extend transport (extend sources (extend tasks env))) j ∈ M.sets :=
      Fin.cases hTransport (Fin.cases hSources (Fin.cases hTasks members))
    exact ⟨tasks, hTasks, sources, hSources, transport, hTransport,
      (M.realize_groundEligibleTasksFormula pairing unions powers separation
        2 P.succ.succ.succ G.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ
        A.succ.succ.succ Labels.succ.succ.succ _ bounds meet).2 rfl,
      (M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
        0 1 2 P.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ Labels.succ.succ.succ _ bounds meet).2 rfl,
      (M.realize_groundTaskTransportFormula pairing unions powers separation
        0 P.succ.succ.succ G.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ
        A.succ.succ.succ Labels.succ.succ.succ _ bounds meet).2 rfl,
      (M.realize_constantBatchActionFormula pairing unions powers separation
        output.succ.succ.succ G.succ.succ.succ 2 P.succ.succ.succ r.succ.succ.succ
        A.succ.succ.succ 1 0 _ bounds).2 equal⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
