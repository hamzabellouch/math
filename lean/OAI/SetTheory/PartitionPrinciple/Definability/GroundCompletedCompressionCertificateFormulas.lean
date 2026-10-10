import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompletedMapRecognition
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionMarkingRecognition
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialCompletedCompressionCertificates

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem initialCompressionData_ground {P G r μ A Labels : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets) (meet : MeetOrderCode P r μ) :
    (M.initialCompressionData P G r μ A Labels).code ∈ M.sets := by
  obtain ⟨hI, hQs, hrs, hμs, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hMaps := (M.batchEmbeddingFamily_spec pairing unions powers separation
    hI hP hQs hrs (fields 0).1 (fields 2).1).1
  have hAction := M.groundEligibleBatchAction_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  apply M.nonemptyTupleCode_mem pairing 12
  exact Fin.cases hP (Fin.cases hr (Fin.cases hμ (Fin.cases hI (Fin.cases hQs
    (Fin.cases hrs (Fin.cases hμs (Fin.cases (fields 0).1 (Fin.cases (fields 2).1
      (Fin.cases (fields 4).1 (Fin.cases (fields 3).1 (Fin.cases hMaps
        (Fin.cases hAction (fun j => Fin.elim0 j)))))))))))))

noncomputable def initialCompressionCertificateFormula {n}
    (output N P G r μ A Labels : Fin n) : SetFormula n :=
  let old := suffixIndex n 7
  let f := prefixIndex n 7
  exBlock 7 (.conj
    (BoundedFormula.nonemptyTupleFormula 2 (old output) (Fin.cases (f 0) (Fin.cases (f 1) (fun _ => f 2)))).toFormula
    (.conj (groundTaskRepresentativesFormula (f 0) (old P) (old G) (old r) (old μ) (old A) (old Labels))
      (.conj (M.initialCompressionDataFormula pairing unions powers separation
        (f 3) (old P) (old G) (old r) (old μ) (old A) (old Labels))
        (.conj (groundEligibleTasksFormula (f 4) (old P) (old G) (old r) (old μ) (old A) (old Labels))
          (.conj (groundLiteralTaskFieldFormula 0 (f 5) (f 4) (old P) (old r) (old μ) (old Labels))
            (.conj (groundTaskTransportFormula (f 6) (old P) (old G) (old r) (old μ) (old A) (old Labels))
              (.conj (reindex (extend (old N) (extend (f 1) (extend (f 3) (extend (f 4)
                (extend (f 5) (extend (f 0) (extend (old G) (extend (f 6) Fin.elim0))))))))
                (M.compressionHistoryFormula pairing unions powers separation))
                (reindex (extend (f 2) (extend (old N) (extend (f 1) Fin.elim0)))
                  (historyFieldUnionTupleFormula 0 1 2)))))))))

def InitialCompressionCertificateCode (output N P G r μ A Labels : ZFSet.{u}) : Prop :=
  let I := M.groundEligibleTasks P G r μ A Labels
  let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
  let T := M.groundTaskTransport P G r μ A Labels
  ∃ Reps ∈ M.sets, ∃ history ∈ M.sets, ∃ unionCode ∈ M.sets,
    output = nonemptyTupleCode 2 (Fin.cases Reps (Fin.cases history (fun _ => unionCode))) ∧
      TaskRepresentativesCode Reps I P G r A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels ∧
      Realize M.sets (M.compressionHistoryFormula pairing unions powers separation)
        (extend N (extend history (extend (M.initialCompressionData P G r μ A Labels).code
          (extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0)))))))) ∧
      Realize M.sets (historyFieldUnionTupleFormula 0 1 2)
        (extend unionCode (extend N (extend history Fin.elim0)))

theorem realize_initialCompressionCertificateFormula {n}
    (output N P G r μ A Labels : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (M.initialCompressionCertificateFormula pairing unions powers separation
      output N P G r μ A Labels) env ↔
      M.InitialCompressionCertificateCode pairing unions powers separation
        (env output) (env N) (env P) (env G) (env r) (env μ) (env A) (env Labels) := by
  let I := M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels)
  let Sources := literalTaskSourceGraph I (env P) (M.groundRelations (env P) (env P))
    (M.groundMeetFilters (env P) (env r) (env μ)) (env Labels)
  let T := M.groundTaskTransport (env P) (env G) (env r) (env μ) (env A) (env Labels)
  let initial := M.initialCompressionData (env P) (env G) (env r) (env μ) (env A) (env Labels)
  let old := suffixIndex n 7
  let f := prefixIndex n 7
  have historyEnv (fields : Fin 7 → ZFSet.{u}) :
      (fun j => extendMany 7 fields env
        (extend (old N) (extend (f 1) (extend (f 3) (extend (f 4) (extend (f 5)
          (extend (f 0) (extend (old G) (extend (f 6) Fin.elim0))))))) j)) =
        extend (env N) (extend (fields 1) (extend (fields 3) (extend (fields 4)
          (extend (fields 5) (extend (fields 0) (extend (env G) (extend (fields 6) Fin.elim0))))))) := by
    apply funext
    exact Fin.cases (extendMany_suffix 7 fields env N)
      (Fin.cases (extendMany_prefix 7 fields env 1) (Fin.cases (extendMany_prefix 7 fields env 3)
        (Fin.cases (extendMany_prefix 7 fields env 4) (Fin.cases (extendMany_prefix 7 fields env 5)
          (Fin.cases (extendMany_prefix 7 fields env 0) (Fin.cases (extendMany_suffix 7 fields env G)
            (Fin.cases (extendMany_prefix 7 fields env 6) (fun j => Fin.elim0 j))))))))
  have unionEnv (fields : Fin 7 → ZFSet.{u}) :
      (fun j => extendMany 7 fields env (extend (f 2) (extend (old N) (extend (f 1) Fin.elim0)) j)) =
        extend (fields 2) (extend (env N) (extend (fields 1) Fin.elim0)) := by
    apply funext
    exact Fin.cases (extendMany_prefix 7 fields env 2) (Fin.cases (extendMany_suffix 7 fields env N)
      (Fin.cases (extendMany_prefix 7 fields env 1) (fun j => Fin.elim0 j)))
  unfold initialCompressionCertificateFormula
  rw [realize_exBlock]
  constructor
  · rintro ⟨fields, fieldMembers, tuple, reps, start, tasks, sources, transport, history, unionCode⟩
    have bounds := extendMany_members 7 fields env fieldMembers members
    have stored := (BoundedFormula.truth_nonemptyTupleFormula 2 (old output)
      (Fin.cases (f 0) (Fin.cases (f 1) (fun _ => f 2))) _).1
      ((BoundedFormula.realize_toFormula M _ _ bounds).1 tuple)
    have represented := (M.realize_groundTaskRepresentativesFormula pairing unions powers separation
      (f 0) (old P) (old G) (old r) (old μ) (old A) (old Labels) _ bounds
      (by simpa only [old, extendMany_suffix] using meet)).1 reps
    have startEq := (M.realize_initialCompressionDataFormula pairing unions powers separation
      (f 3) (old P) (old G) (old r) (old μ) (old A) (old Labels) _ bounds
      (by simpa only [old, extendMany_suffix] using meet)).1 start
    have taskEq := (M.realize_groundEligibleTasksFormula pairing unions powers separation
      (f 4) (old P) (old G) (old r) (old μ) (old A) (old Labels) _ bounds
      (by simpa only [old, extendMany_suffix] using meet)).1 tasks
    have sourceEq := (M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
      0 (f 5) (f 4) (old P) (old r) (old μ) (old Labels) _ bounds
      (by simpa only [old, extendMany_suffix] using meet)).1 sources
    have transportEq := (M.realize_groundTaskTransportFormula pairing unions powers separation
      (f 6) (old P) (old G) (old r) (old μ) (old A) (old Labels) _ bounds
      (by simpa only [old, extendMany_suffix] using meet)).1 transport
    simp only [f, old, extendMany_prefix, extendMany_suffix] at stored represented startEq taskEq sourceEq transportEq
    rw [taskEq] at sourceEq
    rw [realize_reindex, historyEnv fields, startEq, taskEq, sourceEq, transportEq] at history
    rw [realize_reindex, unionEnv fields] at unionCode
    exact ⟨fields 0, fieldMembers 0, fields 1, fieldMembers 1, fields 2, fieldMembers 2,
      stored, represented, history, unionCode⟩
  · rintro ⟨Reps, hReps, history, hHistory, unionCode, hUnion, stored, represented, trace, united⟩
    obtain ⟨hI, _, _, _, taskFields⟩ := M.groundEligibleTaskFields pairing unions powers separation
      (members P) (members G) (members r) (members μ) (members A) (members Labels) meet
    have hSources : Sources ∈ M.sets := (taskFields 0).1
    have hT : T ∈ M.sets := M.groundTaskTransport_mem pairing unions powers separation
      (members P) (members G) (members r) (members μ) (members A) (members Labels) meet
    have hInitial : initial.code ∈ M.sets := M.initialCompressionData_ground pairing unions powers separation
      (members P) (members G) (members r) (members μ) (members A) (members Labels) meet
    let fields : Fin 7 → ZFSet.{u} := Fin.cases Reps (Fin.cases history (Fin.cases unionCode
      (Fin.cases initial.code (Fin.cases I (Fin.cases Sources (Fin.cases T Fin.elim0))))))
    have fieldMembers : ∀ j, fields j ∈ M.sets := Fin.cases hReps (Fin.cases hHistory (Fin.cases hUnion
      (Fin.cases hInitial (Fin.cases hI (Fin.cases hSources (Fin.cases hT (fun j => Fin.elim0 j)))))))
    have bounds := extendMany_members 7 fields env fieldMembers members
    refine ⟨fields, fieldMembers, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 2 (old output)
        (Fin.cases (f 0) (Fin.cases (f 1) (fun _ => f 2))) _).2
      simp only [old, extendMany_suffix]
      exact stored.trans (congrArg (nonemptyTupleCode 2) (by
        funext index
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun index => Fin.elim0 index))) index))
    · apply (M.realize_groundTaskRepresentativesFormula pairing unions powers separation
        (f 0) (old P) (old G) (old r) (old μ) (old A) (old Labels) _ bounds
        (by simpa only [old, extendMany_suffix] using meet)).2
      simp only [old, f, extendMany_prefix, extendMany_suffix]
      exact represented
    · apply (M.realize_initialCompressionDataFormula pairing unions powers separation
        (f 3) (old P) (old G) (old r) (old μ) (old A) (old Labels) _ bounds
        (by simpa only [old, extendMany_suffix] using meet)).2
      simp only [old, f, extendMany_prefix, extendMany_suffix]
      rfl
    · apply (M.realize_groundEligibleTasksFormula pairing unions powers separation
        (f 4) (old P) (old G) (old r) (old μ) (old A) (old Labels) _ bounds
        (by simpa only [old, extendMany_suffix] using meet)).2
      simp only [old, f, extendMany_prefix, extendMany_suffix]
      rfl
    · apply (M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
        0 (f 5) (f 4) (old P) (old r) (old μ) (old Labels) _ bounds
        (by simpa only [old, extendMany_suffix] using meet)).2
      simp only [old, f, extendMany_prefix, extendMany_suffix]
      rfl
    · apply (M.realize_groundTaskTransportFormula pairing unions powers separation
        (f 6) (old P) (old G) (old r) (old μ) (old A) (old Labels) _ bounds
        (by simpa only [old, extendMany_suffix] using meet)).2
      simp only [old, f, extendMany_prefix, extendMany_suffix]
      rfl
    · rw [realize_reindex, historyEnv fields]
      exact trace
    · rw [realize_reindex, unionEnv fields]
      exact united

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def completedCompressionCertificateFormula {n}
    (output N P G r μ A Labels top : Fin n) : SetFormula n :=
  let old := suffixIndex n 22
  let f := prefixIndex n 22
  exBlock 22 (.conj
    (BoundedFormula.nonemptyTupleFormula 3 (old output)
      (Fin.cases (f 0) (Fin.cases (f 1) (Fin.cases (f 2) (fun _ => f 3))))).toFormula
    (.conj (M.initialCompressionCertificateFormula pairing unions powers separation
      (f 0) (old N) (old P) (old G) (old r) (old μ) (old A) (old Labels))
      (.conj (BoundedFormula.nonemptyTupleFormula 2 (f 0)
        (Fin.cases (f 4) (Fin.cases (f 5) (fun _ => f 6)))).toFormula
        (.conj (BoundedFormula.nonemptyTupleFormula 12 (f 6) (fun j => f (Fin.natAdd 9 j))).toFormula
          (.conj (groundEligibleTasksFormula (f 7) (old P) (old G) (old r) (old μ) (old A) (old Labels))
            (.conj (groundLiteralTaskFieldFormula 0 (f 8) (f 7) (old P) (old r) (old μ) (old Labels))
              (.conj (M.completedMapFamilyFormula pairing unions powers separation (f 1) (f 7) (f 9) (f 20))
                (.conj (M.compressionBasesFormula pairing unions powers separation (f 2) (f 7) (f 9) (f 1) (f 8))
                  (M.compressionCapsFormula pairing unions powers separation (f 3) (f 7) (f 9) (f 1) (old top))))))))))

def CompletedCompressionCertificateCode (output N P G r μ A Labels top : ZFSet.{u}) : Prop :=
  let I := M.groundEligibleTasks P G r μ A Labels
  let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
  ∃ stored : Fin 4 → ZFSet.{u}, (∀ j, stored j ∈ M.sets) ∧
    output = nonemptyTupleCode 3 stored ∧
    M.InitialCompressionCertificateCode pairing unions powers separation (stored 0) N P G r μ A Labels ∧
    ∃ core : Fin 3 → ZFSet.{u}, ∃ fields : Fin 13 → ZFSet.{u},
      stored 0 = nonemptyTupleCode 2 core ∧ core 2 = nonemptyTupleCode 12 fields ∧
      stored 1 = M.indexedRelationSections I (fields 0) (fields 0)
        (mapFamilyApplicationGraph I (fields 0) (fields 0) (fields 11)) ∧
      stored 2 = familyEvaluationGraph I (fields 0) (fields 0) (⋃₀ ⋃₀ stored 1) (stored 1) Sources ∧
      stored 3 = familyEvaluationGraph I (fields 0) (fields 0) (⋃₀ ⋃₀ stored 1) (stored 1)
        (constantFamilyGraph I top)

theorem realize_completedCompressionCertificateFormula {n}
    (output N P G r μ A Labels top : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (M.completedCompressionCertificateFormula pairing unions powers separation
      output N P G r μ A Labels top) env ↔
    M.CompletedCompressionCertificateCode pairing unions powers separation
      (env output) (env N) (env P) (env G) (env r) (env μ) (env A) (env Labels) (env top) := by
  let I := M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels)
  let Sources := literalTaskSourceGraph I (env P) (M.groundRelations (env P) (env P))
    (M.groundMeetFilters (env P) (env r) (env μ)) (env Labels)
  unfold completedCompressionCertificateFormula
  rw [realize_exBlock]
  constructor
  · rintro ⟨values, ground, outer, recognized, inner, unionTuple, tasks, sources, maps, bases, caps⟩
    have bounds := extendMany_members 22 values env ground members
    rw [BoundedFormula.realize_toFormula M _ _ bounds, BoundedFormula.truth_nonemptyTupleFormula] at outer
    have outerEq := outer
    have recognizedCode := (M.realize_initialCompressionCertificateFormula pairing unions powers separation
      (prefixIndex n 22 0) (suffixIndex n 22 N) (suffixIndex n 22 P) (suffixIndex n 22 G) (suffixIndex n 22 r) (suffixIndex n 22 μ) (suffixIndex n 22 A) (suffixIndex n 22 Labels) (extendMany 22 values env) bounds
      (by simpa only [extendMany_suffix] using meet)).1 recognized
    rw [BoundedFormula.realize_toFormula M _ _ bounds, BoundedFormula.truth_nonemptyTupleFormula] at inner unionTuple
    have innerEq := inner
    have unionEq := unionTuple
    have taskEq := (M.realize_groundEligibleTasksFormula pairing unions powers separation
      (prefixIndex n 22 7) (suffixIndex n 22 P) (suffixIndex n 22 G) (suffixIndex n 22 r) (suffixIndex n 22 μ) (suffixIndex n 22 A) (suffixIndex n 22 Labels) (extendMany 22 values env) bounds
      (by simpa only [extendMany_suffix] using meet)).1 tasks
    have sourceEq := (M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
      0 (prefixIndex n 22 8) (prefixIndex n 22 7) (suffixIndex n 22 P) (suffixIndex n 22 r) (suffixIndex n 22 μ) (suffixIndex n 22 Labels) (extendMany 22 values env) bounds
      (by simpa only [extendMany_suffix] using meet)).1 sources
    have mapEq := (M.realize_completedMapFamilyFormula pairing unions powers separation
      (prefixIndex n 22 1) (prefixIndex n 22 7) (prefixIndex n 22 9) (prefixIndex n 22 20) (extendMany 22 values env) bounds).1 maps
    have baseEq := (M.realize_compressionBasesFormula pairing unions powers separation
      (prefixIndex n 22 2) (prefixIndex n 22 7) (prefixIndex n 22 9) (prefixIndex n 22 1) (prefixIndex n 22 8) (extendMany 22 values env) bounds).1 bases
    have capEq := (M.realize_compressionCapsFormula pairing unions powers separation
      (prefixIndex n 22 3) (prefixIndex n 22 7) (prefixIndex n 22 9) (prefixIndex n 22 1) (suffixIndex n 22 top) (extendMany 22 values env) bounds).1 caps
    simp only [extendMany_prefix, extendMany_suffix] at outerEq recognizedCode innerEq unionEq taskEq sourceEq mapEq baseEq capEq
    rw [taskEq] at sourceEq mapEq baseEq capEq
    rw [sourceEq] at baseEq
    let stored : Fin 4 → ZFSet.{u} := Fin.cases (values 0)
      (Fin.cases (values 1) (Fin.cases (values 2) (fun _ => values 3)))
    let core : Fin 3 → ZFSet.{u} := Fin.cases (values 4) (Fin.cases (values 5) (fun _ => values 6))
    refine ⟨stored, Fin.cases (ground 0) (Fin.cases (ground 1) (Fin.cases (ground 2) (fun _ => ground 3))),
      ?_, recognizedCode, core, (fun j => values (Fin.natAdd 9 j)), ?_, unionEq, mapEq, baseEq, capEq⟩
    · exact outerEq.trans (congrArg (nonemptyTupleCode 3) (by
        funext j
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j))
    · exact innerEq.trans (congrArg (nonemptyTupleCode 2) (by
        funext j
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j))
  · rintro ⟨stored, storedGround, outerEq, recognized, core, fields, innerEq, unionEq, mapEq, baseEq, capEq⟩
    have coreGround := M.nonemptyTupleCode_field_mem 2 core (innerEq ▸ storedGround 0)
    have fieldGround := M.nonemptyTupleCode_field_mem 12 fields (unionEq ▸ coreGround 2)
    obtain ⟨hI, _, _, _, taskFields⟩ := M.groundEligibleTaskFields pairing unions powers separation
      (members P) (members G) (members r) (members μ) (members A) (members Labels) meet
    have hSources : Sources ∈ M.sets := (taskFields 0).1
    let head : Fin 9 → ZFSet.{u} := Fin.cases (stored 0) (Fin.cases (stored 1)
      (Fin.cases (stored 2) (Fin.cases (stored 3) (Fin.cases (core 0)
        (Fin.cases (core 1) (Fin.cases (core 2) (Fin.cases I (fun _ => Sources))))))))
    let values : Fin 22 → ZFSet.{u} := Fin.addCases (m := 9) (n := 13) head fields
    have headGround : ∀ j, head j ∈ M.sets := Fin.cases (storedGround 0) (Fin.cases (storedGround 1)
      (Fin.cases (storedGround 2) (Fin.cases (storedGround 3) (Fin.cases (coreGround 0)
        (Fin.cases (coreGround 1) (Fin.cases (coreGround 2) (Fin.cases hI (fun _ => hSources))))))))
    have ground : ∀ j, values j ∈ M.sets := by
      intro j
      refine Fin.addCases (m := 9) (n := 13) ?_ ?_ j
      · intro i
        simpa only [values, Fin.addCases_left] using headGround i
      · intro i
        simpa only [values, Fin.addCases_right] using fieldGround i
    have bounds := extendMany_members 22 values env ground members
    refine ⟨values, ground, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ (extendMany 22 values env) bounds).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 3 (suffixIndex n 22 output)
        (Fin.cases (prefixIndex n 22 0) (Fin.cases (prefixIndex n 22 1) (Fin.cases (prefixIndex n 22 2) (fun _ => prefixIndex n 22 3)))) (extendMany 22 values env)).2
      simp only [extendMany_suffix]
      exact outerEq.trans (congrArg (nonemptyTupleCode 3) (by
        funext j
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j))
    · apply (M.realize_initialCompressionCertificateFormula pairing unions powers separation
        (prefixIndex n 22 0) (suffixIndex n 22 N) (suffixIndex n 22 P) (suffixIndex n 22 G) (suffixIndex n 22 r) (suffixIndex n 22 μ) (suffixIndex n 22 A) (suffixIndex n 22 Labels) (extendMany 22 values env) bounds
        (by simpa only [extendMany_suffix] using meet)).2
      simp only [extendMany_prefix, extendMany_suffix]
      exact recognized
    · apply (BoundedFormula.realize_toFormula M _ (extendMany 22 values env) bounds).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 2 (prefixIndex n 22 0)
        (Fin.cases (prefixIndex n 22 4) (Fin.cases (prefixIndex n 22 5) (fun _ => prefixIndex n 22 6))) (extendMany 22 values env)).2
      simp only [extendMany_prefix]
      exact innerEq.trans (congrArg (nonemptyTupleCode 2) (by
        funext j
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j))
    · apply (BoundedFormula.realize_toFormula M _ (extendMany 22 values env) bounds).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 12 (prefixIndex n 22 6) (fun j => prefixIndex n 22 (Fin.natAdd 9 j)) (extendMany 22 values env)).2
      simp only [extendMany_prefix, values, Fin.addCases_right]
      exact unionEq
    · apply (M.realize_groundEligibleTasksFormula pairing unions powers separation
        (prefixIndex n 22 7) (suffixIndex n 22 P) (suffixIndex n 22 G) (suffixIndex n 22 r) (suffixIndex n 22 μ) (suffixIndex n 22 A) (suffixIndex n 22 Labels) (extendMany 22 values env) bounds
        (by simpa only [extendMany_suffix] using meet)).2
      simp only [extendMany_prefix, extendMany_suffix]
      rfl
    · apply (M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
        0 (prefixIndex n 22 8) (prefixIndex n 22 7) (suffixIndex n 22 P) (suffixIndex n 22 r) (suffixIndex n 22 μ) (suffixIndex n 22 Labels) (extendMany 22 values env) bounds
        (by simpa only [extendMany_suffix] using meet)).2
      simp only [extendMany_prefix, extendMany_suffix]
      rfl
    · apply (M.realize_completedMapFamilyFormula pairing unions powers separation
        (prefixIndex n 22 1) (prefixIndex n 22 7) (prefixIndex n 22 9) (prefixIndex n 22 20) (extendMany 22 values env) bounds).2
      simp only [extendMany_prefix]
      exact mapEq
    · apply (M.realize_compressionBasesFormula pairing unions powers separation
        (prefixIndex n 22 2) (prefixIndex n 22 7) (prefixIndex n 22 9) (prefixIndex n 22 1) (prefixIndex n 22 8) (extendMany 22 values env) bounds).2
      simp only [extendMany_prefix]
      exact baseEq
    · apply (M.realize_compressionCapsFormula pairing unions powers separation
        (prefixIndex n 22 3) (prefixIndex n 22 7) (prefixIndex n 22 9) (prefixIndex n 22 1) (suffixIndex n 22 top) (extendMany 22 values env) bounds).2
      simp only [extendMany_prefix, extendMany_suffix]
      exact capEq

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
