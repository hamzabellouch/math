import OAI.SetTheory.PartitionPrinciple.Definability.ForcingHistoryOutputFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.GreedyAntichainTraces
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitCoverageGraph

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def orderAntichainFormula {n} (Q order A : Fin n) : BoundedFormula n :=
  .conj (.allMem A (.mem 0 Q.succ))
    (.allMem A (.allMem A.succ (.allMem Q.succ.succ
      (imp (.conj (pairMembershipFormula 0 2 order.succ.succ.succ)
        (pairMembershipFormula 0 1 order.succ.succ.succ)) (.equal 2 1)))))

theorem truth_orderAntichainFormula {n} (Q order A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (orderAntichainFormula Q order A) env ↔ OrderAntichainCode (env Q) (env order) (env A) := by
  simp only [orderAntichainFormula, Truth, truth_imp, truth_pairMembershipFormula]
  constructor
  · rintro ⟨subset, law⟩
    exact ⟨subset, fun p hp q hq r hr first second => law p hp q hq r hr ⟨first, second⟩⟩
  · rintro ⟨subset, law⟩
    exact ⟨subset, fun p hp q hq r hr both => law p hp q hq r hr both.1 both.2⟩

def relativeMaximalAntichainFormula {n} (Q order D A : Fin n) : BoundedFormula n :=
  .conj (.allMem A (.mem 0 D.succ)) (.conj (orderAntichainFormula Q order A)
    (.allMem D (exMem A.succ (exMem Q.succ.succ
      (.conj (pairMembershipFormula 0 2 order.succ.succ.succ)
        (pairMembershipFormula 0 1 order.succ.succ.succ))))))

theorem truth_relativeMaximalAntichainFormula {n} (Q order D A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relativeMaximalAntichainFormula Q order D A) env ↔
      RelativeMaximalAntichainCode (env Q) (env order) (env D) (env A) := by
  simp only [relativeMaximalAntichainFormula, Truth, truth_orderAntichainFormula,
    truth_exMem, truth_pairMembershipFormula]
  rfl





def exGraphFields {n} (f : Fin n) (body : BoundedFormula (n + 2)) : BoundedFormula n :=
  exMem f (exPairFields 0
    (reindex (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ))) body))

theorem truth_exGraphFields {n} (f : Fin n) (body : BoundedFormula (n + 2))
    (env : Fin n → ZFSet.{u}) :
    Truth (exGraphFields f body) env ↔
      ∃ x y, ZFSet.pair x y ∈ env f ∧ Truth body (extend y (extend x env)) := by
  simp only [exGraphFields, truth_exMem, truth_exPairFields, truth_reindex]
  have rearrange (z x y : ZFSet.{u}) :
      (fun i => extend y (extend x (extend z env))
        (Fin.cases 0 (Fin.cases 1 (fun j => j.succ.succ.succ)) i)) =
        extend y (extend x env) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  simp only [rearrange]
  change (∃ z ∈ env f, ∃ x y, z = ZFSet.pair x y ∧
    Truth body (extend y (extend x env))) ↔ _
  constructor
  · rintro ⟨z, member, x, y, rfl, holds⟩
    exact ⟨x, y, member, holds⟩
  · rintro ⟨x, y, member, holds⟩
    exact ⟨ZFSet.pair x y, member, x, y, rfl, holds⟩

def exLinkedCoverageFields {n} (z : Fin n) (body : BoundedFormula (n + 3)) : BoundedFormula n :=
  exPairFields z (exPairFields 0 (exPairFields 3
    (exPairFields 0 (exPairFields 0 (exPairFields 0
      (.conj (tupleShapeFormula 6 0)
        (reindex (Fin.cases 9 (Fin.cases 1 (Fin.cases 7
          (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)))) body)))))))

theorem truth_exLinkedCoverageFields {n} (z : Fin n) (body : BoundedFormula (n + 3))
    (env : Fin n → ZFSet.{u}) :
    Truth (exLinkedCoverageFields z body) env ↔
      ∃ P G cutoff, LinkedCoverageFieldsCode (env z) P G cutoff ∧
        Truth body (extend cutoff (extend G (extend P env))) := by
  simp only [exLinkedCoverageFields, truth_exPairFields, Truth, truth_tupleShapeFormula,
    truth_reindex]
  have rearrange (s outer cutoff serial P tail r tail' μ tail'' G rest : ZFSet.{u}) :
      (fun i => extend rest (extend G (extend tail'' (extend μ (extend tail' (extend r
        (extend tail (extend P (extend serial (extend cutoff (extend outer (extend s env)))))))))))
        (Fin.cases 9 (Fin.cases 1 (Fin.cases 7
          (fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))) i)) =
        extend cutoff (extend G (extend P env)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j) i <;> rfl
  simp only [rearrange]
  change (∃ s outer, env z = ZFSet.pair s outer ∧ ∃ cutoff serial,
    outer = ZFSet.pair cutoff serial ∧ ∃ P tail, s = ZFSet.pair P tail ∧
    ∃ r tail', tail = ZFSet.pair r tail' ∧ ∃ μ tail'', tail' = ZFSet.pair μ tail'' ∧
    ∃ G rest, tail'' = ZFSet.pair G rest ∧
      (∃ fields, rest = nonemptyTupleCode 6 fields) ∧
      Truth body (extend cutoff (extend G (extend P env)))) ↔ _
  constructor
  · rintro ⟨s, outer, equal, cutoff, serial, rfl, P, tail, rfl, r, tail', rfl,
      μ, tail'', rfl, G, rest, rfl, ⟨fields, rfl⟩, holds⟩
    exact ⟨P, G, cutoff, ⟨r, μ, fields 0, fields 1, fields 2, fields 3, fields 4,
      fields 5, fields 6, serial, equal⟩, holds⟩
  · rintro ⟨P, G, cutoff, ⟨r, μ, m, inv, one, action, bottom, top, height, serial, equal⟩, holds⟩
    let fields : Fin 7 → ZFSet.{u} := Fin.cases m (Fin.cases inv (Fin.cases one
      (Fin.cases action (Fin.cases bottom (Fin.cases top (fun _ => height))))))
    refine ⟨_, _, equal, cutoff, serial, rfl, P, _, rfl, r, _, rfl, μ, _, rfl,
      G, nonemptyTupleCode 6 fields, rfl, ⟨fields, rfl⟩, holds⟩





def exMainLimitStageFields {n} (T S : Fin n) (body : BoundedFormula (n + 4)) : BoundedFormula n :=
  exGraphFields S (.conj (.mem 1 T.succ.succ)
    (exLinkedCoverageFields 0 (reindex
      (Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (Fin.cases 4
        (fun i => i.succ.succ.succ.succ.succ))))) body)))

theorem truth_exMainLimitStageFields {n} (T S : Fin n) (body : BoundedFormula (n + 4))
    (env : Fin n → ZFSet.{u}) :
    Truth (exMainLimitStageFields T S body) env ↔
      ∃ i z P G t, i ∈ env T ∧ ZFSet.pair i z ∈ env S ∧
        LinkedCoverageFieldsCode z P G t ∧ Truth body (extend t (extend G (extend P (extend i env)))) := by
  simp only [exMainLimitStageFields, truth_exGraphFields, Truth, truth_exLinkedCoverageFields,
    truth_reindex]
  have rearrange (i z P G t : ZFSet.{u}) :
      (fun j => extend t (extend G (extend P (extend z (extend i env))))
        (Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (Fin.cases 4
          (fun k => k.succ.succ.succ.succ.succ)))) j)) =
        extend t (extend G (extend P (extend i env))) := by
    funext j
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_
      (fun m => Fin.cases ?_ (fun a => ?_) m) l) k) j <;> rfl
  simp only [rearrange]
  change (∃ i z, ZFSet.pair i z ∈ env S ∧ i ∈ env T ∧ ∃ P G t,
    LinkedCoverageFieldsCode z P G t ∧ Truth body (extend t (extend G (extend P (extend i env))))) ↔ _
  constructor
  · rintro ⟨i,z,entry,member,P,G,t,shape,holds⟩
    exact ⟨i,z,P,G,t,member,entry,shape,holds⟩
  · rintro ⟨i,z,P,G,t,member,entry,shape,holds⟩
    exact ⟨i,z,entry,member,P,G,t,shape,holds⟩

def exMainLimitConeFields {n} (T S row : Fin n) (body : BoundedFormula (n + 6)) : BoundedFormula n :=
  exMainLimitStageFields T S (exGraphFields row.succ.succ.succ.succ
    (.conj (orderedPairFormula 1 T.succ.succ.succ.succ.succ.succ 5)
      (exPairFields 0 (reindex (Fin.cases 0 (Fin.cases 1 (Fin.cases 4 (Fin.cases 5
        (Fin.cases 6 (Fin.cases 7 (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ))))))) body))))

theorem truth_exMainLimitConeFields {n} (T S row : Fin n) (body : BoundedFormula (n + 6))
    (env : Fin n → ZFSet.{u}) :
    Truth (exMainLimitConeFields T S row body) env ↔
      ∃ i P G t points actors, MainLimitConeEntryCode (env T) (env S) (env row) i P G t points actors ∧
        Truth body (extend actors (extend points (extend t (extend G (extend P (extend i env)))))) := by
  simp only [exMainLimitConeFields, truth_exMainLimitStageFields, truth_exGraphFields, Truth,
    truth_orderedPairFormula, truth_exPairFields, truth_reindex]
  have rearrange (i P G t key value points actors : ZFSet.{u}) :
      (fun j => extend actors (extend points (extend value (extend key (extend t
        (extend G (extend P (extend i env)))))))
        (Fin.cases 0 (Fin.cases 1 (Fin.cases 4 (Fin.cases 5 (Fin.cases 6
          (Fin.cases 7 (fun k => k.succ.succ.succ.succ.succ.succ.succ.succ)))))) j)) =
      extend actors (extend points (extend t (extend G (extend P (extend i env))))) := by
    funext j
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
      Fin.cases ?_ (fun d => Fin.cases ?_ (fun e => Fin.cases ?_ (fun f => ?_) e) d) c) b) a) j <;> rfl
  simp only [rearrange]
  change (∃ i z P G t, i ∈ env T ∧ ZFSet.pair i z ∈ env S ∧ LinkedCoverageFieldsCode z P G t ∧
    ∃ key value, ZFSet.pair key value ∈ env row ∧ key = ZFSet.pair (env T) i ∧
    ∃ points actors, value = ZFSet.pair points actors ∧
    Truth body (extend actors (extend points (extend t (extend G (extend P (extend i env))))))) ↔ _
  constructor
  · rintro ⟨i,z,P,G,t,member,entry,shape,key,value,rowEntry,rfl,points,actors,rfl,holds⟩
    exact ⟨i,P,G,t,points,actors,⟨member,z,entry,shape,rowEntry⟩,holds⟩
  · rintro ⟨i,P,G,t,points,actors,⟨member,z,entry,shape,rowEntry⟩,holds⟩
    exact ⟨i,z,P,G,t,member,entry,shape,_,_,rowEntry,rfl,points,actors,rfl,holds⟩





def certificateGraphEntryAt {n} (j F B f k : Fin n) : BoundedFormula n :=
  exGraphFields k (.conj (.equal 1 j.succ.succ)
    (exPairFields 0 (.conj (.equal 1 F.succ.succ.succ.succ)
      (orderedPairFormula 0 B.succ.succ.succ.succ f.succ.succ.succ.succ))))

theorem truth_certificateGraphEntryAt {n} (j F B f k : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (certificateGraphEntryAt j F B f k) env ↔
      ZFSet.pair (env j) (ZFSet.pair (env F) (ZFSet.pair (env B) (env f))) ∈ env k := by
  simp only [certificateGraphEntryAt, truth_exGraphFields, Truth,
    truth_exPairFields, truth_orderedPairFormula]
  change (∃ key certificate, ZFSet.pair key certificate ∈ env k ∧ key = env j ∧
    ∃ profile tail, certificate = ZFSet.pair profile tail ∧ profile = env F ∧
      tail = ZFSet.pair (env B) (env f)) ↔ _
  constructor
  · rintro ⟨key, certificate, entry, rfl, profile, tail, rfl, rfl, rfl⟩
    exact entry
  · intro entry
    exact ⟨env j, _, entry, rfl, env F, _, rfl, rfl, rfl⟩

def enumerationGraphEntryAt {n} (j e names g : Fin n) : BoundedFormula n :=
  exGraphFields g (.conj (.equal 1 j.succ.succ)
    (orderedPairFormula 0 e.succ.succ names.succ.succ))

theorem truth_enumerationGraphEntryAt {n} (j e names g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (enumerationGraphEntryAt j e names g) env ↔
      ZFSet.pair (env j) (ZFSet.pair (env e) (env names)) ∈ env g := by
  simp only [enumerationGraphEntryAt, truth_exGraphFields, Truth, truth_orderedPairFormula]
  change (∃ key pair, ZFSet.pair key pair ∈ env g ∧ key = env j ∧
    pair = ZFSet.pair (env e) (env names)) ↔ _
  constructor
  · rintro ⟨key, pair, entry, rfl, rfl⟩
    exact entry
  · intro entry
    exact ⟨env j, _, entry, rfl, rfl⟩





def relativeAntichainFamilyFormula {n} (j A Q order domains : Fin n) : BoundedFormula n :=
  exGraphFields domains (.conj (.equal 1 j.succ.succ)
    (relativeMaximalAntichainFormula Q.succ.succ order.succ.succ 0 A.succ.succ))

theorem truth_relativeAntichainFamilyFormula {n} (j A Q order domains : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relativeAntichainFamilyFormula j A Q order domains) env ↔
      ∃ D, ZFSet.pair (env j) D ∈ env domains ∧
        RelativeMaximalAntichainCode (env Q) (env order) D (env A) := by
  simp only [relativeAntichainFamilyFormula, truth_exGraphFields, Truth,
    truth_relativeMaximalAntichainFormula]
  change (∃ key D, ZFSet.pair key D ∈ env domains ∧ key = env j ∧
    RelativeMaximalAntichainCode (env Q) (env order) D (env A)) ↔ _
  constructor
  · rintro ⟨key, D, entry, rfl, code⟩
    exact ⟨D, entry, code⟩
  · rintro ⟨D, entry, code⟩
    exact ⟨env j, D, entry, rfl, code⟩





def assignmentQueryWithinFormula {n} (X T q : Fin n) : BoundedFormula n :=
  exPairFields q (stageOneAssignmentsSubsetFormula 0 X.succ.succ T.succ.succ)

theorem truth_assignmentQueryWithinFormula {n} (X T q : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (assignmentQueryWithinFormula X T q) env ↔
      AssignmentQueryWithin (env X) (env T) (env q) := by
  simp only [assignmentQueryWithinFormula, truth_exPairFields,
    truth_stageOneAssignmentsSubsetFormula]
  rfl

def representativeIndexAdditionsMemberFormula {n} (i I T Q c X : Fin n) : BoundedFormula n :=
  .conj (.mem i I) (exMem Q
    (.conj (assignmentQueryWithinFormula X.succ T.succ 0)
      (exGraphFields c.succ (.conj (.equal 1 2)
        (exPairFields 0
          (exMem T.succ.succ.succ.succ.succ
            (exMem T.succ.succ.succ.succ.succ.succ
              (exMem 2 (stageOneAssignmentFormula 0
                i.succ.succ.succ.succ.succ.succ.succ.succ 2 1)))))))))

theorem truth_representativeIndexAdditionsMemberFormula {n} (i I T Q c X : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (representativeIndexAdditionsMemberFormula i I T Q c X) env ↔
      env i ∈ representativeIndexAdditions (env I) (env T) (env Q) (env c) (env X) := by
  simp only [representativeIndexAdditionsMemberFormula, Truth, truth_exMem,
    truth_assignmentQueryWithinFormula, truth_exGraphFields, truth_exPairFields,
    truth_stageOneAssignmentFormula]
  rw [mem_representativeIndexAdditions]
  change (env i ∈ env I ∧ ∃ q ∈ env Q, AssignmentQueryWithin (env X) (env T) q ∧
    ∃ key value, ZFSet.pair key value ∈ env c ∧ key = q ∧
      ∃ row A, value = ZFSet.pair row A ∧ ∃ v ∈ env T, ∃ w ∈ env T,
        ∃ z ∈ A, z = stageOneAssignment (env i) v w) ↔ _
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨q, hq, localQuery, key, value, entry, rfl, row, A, rfl, v, hv, w, hw, z, hz, rfl⟩
    exact ⟨key, hq, localQuery, row, A, entry, v, hv, w, hw, hz⟩
  · rintro ⟨q, hq, localQuery, row, A, entry, v, hv, w, hw, hz⟩
    exact ⟨q, hq, localQuery, q, ZFSet.pair row A, entry, rfl, row, A, rfl,
      v, hv, w, hw, stageOneAssignment (env i) v w, hz, rfl⟩





def supportedCertificateFormula {n}
    (nodes N order R niceEval visibilityEval value F B f : Fin n) : BoundedFormula n :=
  .conj (.allMem F (.mem 0 nodes.succ))
    (.conj (.allMem B (.mem 0 F.succ))
      (.conj (.allMem F (exMem B.succ (pairMembershipFormula 0 1 order.succ.succ)))
        (.conj (functionFormula B N f)
          (.conj
            (.neg (exGraphFields visibilityEval
              (.conj (.mem 1 nodes.succ.succ)
                (.neg (.conj (imp (.mem value.succ.succ 0) (.mem 1 F.succ.succ))
                  (imp (.mem 1 F.succ.succ) (.mem value.succ.succ 0)))))))
            (.allMem B (.allMem N.succ
              (imp (pairMembershipFormula 1 0 f.succ.succ)
                (.conj (pairMembershipFormula 1 0 R.succ.succ)
                  (pairMembershipFormula 0 value.succ.succ niceEval.succ.succ)))))))))

theorem truth_supportedCertificateFormula {n}
    (nodes N order R niceEval visibilityEval value F B f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (supportedCertificateFormula nodes N order R niceEval visibilityEval value F B f) env ↔
      SupportedEqualityCertificate (env nodes) (env N) (env order) (env R)
        (env niceEval) (env visibilityEval) (env value) (env F) (env B) (env f) := by
  classical
  simp only [supportedCertificateFormula, Truth, truth_exMem, truth_pairMembershipFormula,
    truth_functionFormula, truth_exGraphFields, truth_imp, not_exists, not_and, not_not,
    ← iff_def]
  rfl

def supportedCertificateEntryFormula {n}
    (entry J PF PB WF nodes N order R inputEval niceEval visibilityEval : Fin n) :
    BoundedFormula n :=
  exPairFields entry (exPairFields 0 (exPairFields 0
    (.conj (.mem 5 J.succ.succ.succ.succ.succ.succ)
      (.conj (.mem 3 PF.succ.succ.succ.succ.succ.succ)
        (.conj (.mem 1 PB.succ.succ.succ.succ.succ.succ)
          (.conj (.mem 0 WF.succ.succ.succ.succ.succ.succ)
            (exGraphFields inputEval.succ.succ.succ.succ.succ.succ
              (.conj (.equal 1 7)
                (supportedCertificateFormula
                  nodes.succ.succ.succ.succ.succ.succ.succ.succ
                  N.succ.succ.succ.succ.succ.succ.succ.succ
                  order.succ.succ.succ.succ.succ.succ.succ.succ
                  R.succ.succ.succ.succ.succ.succ.succ.succ
                  niceEval.succ.succ.succ.succ.succ.succ.succ.succ
                  visibilityEval.succ.succ.succ.succ.succ.succ.succ.succ
                  0 5 3 2)))))))))

theorem truth_supportedCertificateEntryFormula {n}
    (entry J PF PB WF nodes N order R inputEval niceEval visibilityEval : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (supportedCertificateEntryFormula entry J PF PB WF nodes N order R
      inputEval niceEval visibilityEval) env ↔
      ∃ j ∈ env J, ∃ F ∈ env PF, ∃ B ∈ env PB, ∃ f ∈ env WF,
        env entry = ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∧
        ∃ value, ZFSet.pair j value ∈ env inputEval ∧
          SupportedEqualityCertificate (env nodes) (env N) (env order) (env R)
            (env niceEval) (env visibilityEval) value F B f := by
  simp only [supportedCertificateEntryFormula, truth_exPairFields, Truth,
    truth_exGraphFields, truth_supportedCertificateFormula]
  change (∃ j tail, env entry = ZFSet.pair j tail ∧
    ∃ F rest, tail = ZFSet.pair F rest ∧
    ∃ B f, rest = ZFSet.pair B f ∧
      j ∈ env J ∧ F ∈ env PF ∧ B ∈ env PB ∧ f ∈ env WF ∧
      ∃ j' value, ZFSet.pair j' value ∈ env inputEval ∧ j' = j ∧
        SupportedEqualityCertificate (env nodes) (env N) (env order) (env R)
          (env niceEval) (env visibilityEval) value F B f) ↔ _
  constructor
  · rintro ⟨j, tail, equal, F, rest, rfl, B, f, rfl, hj, hF, hB, hf,
      j', value, evaluated, rfl, certificate⟩
    exact ⟨j', hj, F, hF, B, hB, f, hf, equal, value, evaluated, certificate⟩
  · rintro ⟨j, hj, F, hF, B, hB, f, hf, equal, value, evaluated, certificate⟩
    exact ⟨j, _, equal, F, _, rfl, B, f, rfl, hj, hF, hB, hf,
      j, value, evaluated, rfl, certificate⟩





def exMainLimitImageFields {n} (actor : Bool) (T S row : Fin n)
    (body : BoundedFormula (n + 1)) : BoundedFormula n :=
  exMainLimitConeFields T S row (exGraphFields (if actor then 0 else 1)
    (.conj (.mem 1 (if actor then 5 else 6))
      (reindex (Fin.cases 0 (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ)) body)))

theorem truth_exMainLimitImageFields {n} (actor : Bool) (T S row : Fin n)
    (body : BoundedFormula (n + 1)) (env : Fin n → ZFSet.{u}) :
    Truth (exMainLimitImageFields actor T S row body) env ↔
      ∃ x, (if actor then MainLimitOldActorImageCode (env T) (env S) (env row) x
        else MainLimitOldPointImageCode (env T) (env S) (env row) x) ∧ Truth body (extend x env) := by
  simp only [exMainLimitImageFields, truth_exMainLimitConeFields, truth_exGraphFields, Truth, truth_reindex]
  have rearrange (i P G t points actors y x : ZFSet.{u}) :
      (fun j => extend x (extend y (extend actors (extend points (extend t
        (extend G (extend P (extend i env)))))))
        (Fin.cases 0 (fun k => k.succ.succ.succ.succ.succ.succ.succ.succ) j)) = extend x env := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  simp only [rearrange]
  cases actor <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · change (∃ i P G t points actors, MainLimitConeEntryCode (env T) (env S) (env row) i P G t points actors ∧
      ∃ y x, ZFSet.pair y x ∈ points ∧ y ∈ P ∧ Truth body (extend x env)) ↔ _
    constructor
    · rintro ⟨i,P,G,t,points,actors,entry,y,x,image,member,holds⟩
      exact ⟨x,⟨i,P,G,t,points,actors,y,entry,member,image⟩,holds⟩
    · rintro ⟨x,⟨i,P,G,t,points,actors,y,entry,member,image⟩,holds⟩
      exact ⟨i,P,G,t,points,actors,entry,y,x,image,member,holds⟩
  · change (∃ i P G t points actors, MainLimitConeEntryCode (env T) (env S) (env row) i P G t points actors ∧
      ∃ y x, ZFSet.pair y x ∈ actors ∧ y ∈ G ∧ Truth body (extend x env)) ↔ _
    constructor
    · rintro ⟨i,P,G,t,points,actors,entry,y,x,image,member,holds⟩
      exact ⟨x,⟨i,P,G,t,points,actors,y,entry,member,image⟩,holds⟩
    · rintro ⟨x,⟨i,P,G,t,points,actors,y,entry,member,image⟩,holds⟩
      exact ⟨i,P,G,t,points,actors,entry,y,x,image,member,holds⟩

def mainLimitImageFormula {n} (actor : Bool) (T S row x : Fin n) : BoundedFormula n :=
  exMainLimitImageFields actor T S row (.equal 0 x.succ)

theorem truth_mainLimitImageFormula {n} (actor : Bool) (T S row x : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitImageFormula actor T S row x) env ↔
      (if actor then MainLimitOldActorImageCode (env T) (env S) (env row) (env x)
        else MainLimitOldPointImageCode (env T) (env S) (env row) (env x)) := by
  rw [mainLimitImageFormula, truth_exMainLimitImageFields]
  change (∃ y, _ ∧ y = env x) ↔ _
  constructor
  · rintro ⟨y, member, rfl⟩
    exact member
  · exact fun member => ⟨env x, member, rfl⟩

def mainLimitOldCutoffFormula {n} (T S t : Fin n) : BoundedFormula n :=
  exMainLimitStageFields T S (disj (.equal t.succ.succ.succ.succ 0)
    (.mem t.succ.succ.succ.succ 0))

theorem truth_mainLimitOldCutoffFormula {n} (T S t : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainLimitOldCutoffFormula T S t) env ↔ MainLimitOldCutoffCode (env T) (env S) (env t) := by
  simp only [mainLimitOldCutoffFormula, truth_exMainLimitStageFields, truth_disj, Truth]
  change (∃ i z P G cutoff, i ∈ env T ∧ ZFSet.pair i z ∈ env S ∧
    LinkedCoverageFieldsCode z P G cutoff ∧ (env t = cutoff ∨ env t ∈ cutoff)) ↔ _
  constructor
  · rintro ⟨i,z,P,G,cutoff,member,entry,shape,bound⟩
    exact ⟨i,member,z,entry,P,G,cutoff,shape,bound⟩
  · rintro ⟨i,member,z,entry,P,G,cutoff,shape,bound⟩
    exact ⟨i,z,P,G,cutoff,member,entry,shape,bound⟩





def mainLimitPointCoverageFormula {n} (T S row Q top : Fin n) : BoundedFormula n :=
  .conj (.allMem Q (imp (.neg (.equal 0 top.succ))
    (mainLimitImageFormula false T.succ S.succ row.succ 0)))
    (.neg (exMainLimitImageFields false T S row
      (.neg (.conj (.mem 0 Q.succ) (.neg (.equal 0 top.succ))))))

theorem truth_mainLimitPointCoverageFormula {n} (T S row Q top : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitPointCoverageFormula T S row Q top) env ↔
      ∀ x, (x ∈ env Q ∧ x ≠ env top) ↔ MainLimitOldPointImageCode (env T) (env S) (env row) x := by
  classical
  simp only [mainLimitPointCoverageFormula, Truth, truth_imp, truth_mainLimitImageFormula,
    truth_exMainLimitImageFields, Bool.false_eq_true, ite_false, not_exists, not_and, not_not, Classical.not_imp]
  change ((∀ x ∈ env Q, x ≠ env top → MainLimitOldPointImageCode (env T) (env S) (env row) x) ∧
    ∀ x, MainLimitOldPointImageCode (env T) (env S) (env row) x → x ∈ env Q ∧ x ≠ env top) ↔ _
  constructor
  · rintro ⟨forward, reverse⟩ x
    exact ⟨fun h => forward x h.1 h.2, reverse x⟩
  · intro laws
    exact ⟨fun x member different => (laws x).1 ⟨member,different⟩, fun x => (laws x).2⟩

def mainLimitActorCoverageFormula {n} (T S row H : Fin n) : BoundedFormula n :=
  .conj (.allMem H (mainLimitImageFormula true T.succ S.succ row.succ 0))
    (.neg (exMainLimitImageFields true T S row (.neg (.mem 0 H.succ))))

theorem truth_mainLimitActorCoverageFormula {n} (T S row H : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitActorCoverageFormula T S row H) env ↔
      ∀ g, g ∈ env H ↔ MainLimitOldActorImageCode (env T) (env S) (env row) g := by
  classical
  simp only [mainLimitActorCoverageFormula, Truth, truth_mainLimitImageFormula,
    truth_exMainLimitImageFields, ite_true, not_exists, not_and, not_not]
  change ((∀ g ∈ env H, MainLimitOldActorImageCode (env T) (env S) (env row) g) ∧
    ∀ g, MainLimitOldActorImageCode (env T) (env S) (env row) g → g ∈ env H) ↔ _
  exact ⟨fun h g => ⟨h.1 g,h.2 g⟩, fun h => ⟨fun g => (h g).1,fun g => (h g).2⟩⟩

def mainLimitStrictTopFormula {n} (T S row R top : Fin n) : BoundedFormula n :=
  .neg (exMainLimitConeFields T S row (exGraphFields 1 (.neg
    (.conj (pairMembershipFormula 0 top.succ.succ.succ.succ.succ.succ.succ.succ
      R.succ.succ.succ.succ.succ.succ.succ.succ)
      (.neg (pairMembershipFormula top.succ.succ.succ.succ.succ.succ.succ.succ 0
        R.succ.succ.succ.succ.succ.succ.succ.succ))))))

theorem truth_mainLimitStrictTopFormula {n} (T S row R top : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitStrictTopFormula T S row R top) env ↔
      ∀ i P G t points actors, MainLimitConeEntryCode (env T) (env S) (env row) i P G t points actors →
        ∀ x y, ZFSet.pair x y ∈ points → ZFSet.pair y (env top) ∈ env R ∧
          ZFSet.pair (env top) y ∉ env R := by
  classical
  simp only [mainLimitStrictTopFormula, Truth, truth_exMainLimitConeFields,
    truth_exGraphFields, truth_pairMembershipFormula, not_exists, not_and, not_not, Classical.not_imp]
  rfl

def mainLimitCutoffFormula {n} (T S cutoff : Fin n) : BoundedFormula n :=
  .conj (.allMem cutoff (mainLimitOldCutoffFormula T.succ S.succ 0))
    (.neg (exMainLimitStageFields T S (.neg
      (.conj (.mem 0 cutoff.succ.succ.succ.succ)
        (.allMem 0 (.mem 0 cutoff.succ.succ.succ.succ.succ))))))

theorem truth_mainLimitCutoffFormula {n} (T S cutoff : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainLimitCutoffFormula T S cutoff) env ↔
      ∀ t, t ∈ env cutoff ↔ MainLimitOldCutoffCode (env T) (env S) t := by
  classical
  simp only [mainLimitCutoffFormula, Truth, truth_mainLimitOldCutoffFormula,
    truth_exMainLimitStageFields, not_exists, not_and, not_not, Classical.not_imp]
  change ((∀ t ∈ env cutoff, MainLimitOldCutoffCode (env T) (env S) t) ∧
    ∀ i z P G t, i ∈ env T → ZFSet.pair i z ∈ env S → LinkedCoverageFieldsCode z P G t →
      t ∈ env cutoff ∧ ∀ s ∈ t, s ∈ env cutoff) ↔ _
  constructor
  · rintro ⟨forward,bound⟩ t
    refine ⟨forward t, ?_⟩
    rintro ⟨i,member,z,entry,P,G,s,shape,equal | lower⟩
    · exact equal.symm ▸ (bound i z P G s member entry shape).1
    · exact (bound i z P G s member entry shape).2 t lower
  · intro laws
    refine ⟨fun t => (laws t).1, ?_⟩
    intro i z P G t member entry shape
    exact ⟨(laws t).2 ⟨i,member,z,entry,P,G,t,shape,Or.inl rfl⟩,
      fun s lower => (laws s).2 ⟨i,member,z,entry,P,G,t,shape,Or.inr lower⟩⟩

def mainLimitTopBirthFormula {n} (top cutoff birth : Fin n) : BoundedFormula n :=
  .conj (pairMembershipFormula top cutoff birth)
    (.neg (exGraphFields birth (.conj (.equal 0 cutoff.succ.succ)
      (.neg (.equal 1 top.succ.succ)))))

theorem truth_mainLimitTopBirthFormula {n} (top cutoff birth : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitTopBirthFormula top cutoff birth) env ↔
      ∀ x, ZFSet.pair x (env cutoff) ∈ env birth ↔ x = env top := by
  classical
  simp only [mainLimitTopBirthFormula, Truth, truth_pairMembershipFormula,
    truth_exGraphFields, not_exists, not_and, not_not]
  change (ZFSet.pair (env top) (env cutoff) ∈ env birth ∧
    ∀ x t, ZFSet.pair x t ∈ env birth → t = env cutoff → x = env top) ↔ _
  constructor
  · rintro ⟨entry,unique⟩ x
    exact ⟨fun image => unique x (env cutoff) image rfl, fun equal => equal.symm ▸ entry⟩
  · intro laws
    exact ⟨(laws (env top)).2 rfl, fun x t image equal => (laws x).1 (equal ▸ image)⟩

def mainLimitCoverageFormula {n} (T S row Q H R top cutoff birth : Fin n) : BoundedFormula n :=
  .conj (mainLimitPointCoverageFormula T S row Q top)
    (.conj (mainLimitActorCoverageFormula T S row H)
      (.conj (mainLimitStrictTopFormula T S row R top)
        (.conj (mainLimitCutoffFormula T S cutoff) (mainLimitTopBirthFormula top cutoff birth))))

theorem truth_mainLimitCoverageFormula {n} (T S row Q H R top cutoff birth : Fin n)
    (env : Fin n → ZFSet.{u}) : Truth (mainLimitCoverageFormula T S row Q H R top cutoff birth) env ↔
      MainLimitCoverageGraphCode (env T) (env S) (env row) (env Q) (env H) (env R)
        (env top) (env cutoff) (env birth) := by
  simp only [mainLimitCoverageFormula, Truth, truth_mainLimitPointCoverageFormula,
    truth_mainLimitActorCoverageFormula, truth_mainLimitStrictTopFormula,
    truth_mainLimitCutoffFormula, truth_mainLimitTopBirthFormula]
  exact ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,
    fun h => ⟨h.points,h.actors,h.strict_top,h.cutoff_mem,h.top_birth⟩⟩

theorem realize_mainLimitCoverageFormula (M : TransitiveGround.{u}) {n}
    (T S row Q H R top cutoff birth : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (mainLimitCoverageFormula T S row Q H R top cutoff birth).toFormula env ↔
      MainLimitCoverageGraphCode (env T) (env S) (env row) (env Q) (env H) (env R)
        (env top) (env cutoff) (env birth) :=
  (realize_toFormula M _ env members).trans (truth_mainLimitCoverageFormula T S row Q H R top cutoff birth env)

end PartitionPilot.Forcing.BoundedFormula

end OAI
