import OAI.SetTheory.PartitionPrinciple.Definability.GroundCompletedCompressionCertificateFormulas

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions powers separation collection infinite

theorem realize_compressionCertificate_iff {Labels z : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets (M.initialCompressionCertificateFormula pairing unions powers separation
      0 1 2 3 4 5 6 7)
      (extend z (extend ZFSet.omega (extend stage.carrier (extend stage.actors
        (extend stage.order (extend stage.meetGraph (extend stage.action (extend Labels Fin.elim0)))))))) ↔
      ∃ certificate : GroundInitialCompressionCertificate stage Labels, certificate.code = z := by
  let env := extend z (extend ZFSet.omega (extend stage.carrier (extend stage.actors
    (extend stage.order (extend stage.meetGraph (extend stage.action (extend Labels Fin.elim0)))))))
  have members : ∀ i, env i ∈ M.sets :=
    Fin.cases hz (Fin.cases (M.omega_mem separation infinite) (Fin.cases stage.carrier_ground
      (Fin.cases stage.actors_ground (Fin.cases stage.order_ground (Fin.cases stage.meet_ground
        (Fin.cases stage.action_ground (Fin.cases hLabels (fun i => Fin.elim0 i))))))))
  rw [M.realize_initialCompressionCertificateFormula pairing unions powers separation
    0 1 2 3 4 5 6 7 env members stage.meet]
  change M.InitialCompressionCertificateCode pairing unions powers separation z ZFSet.omega
    stage.carrier stage.actors stage.order stage.meetGraph stage.action Labels ↔ _
  unfold TransitiveGround.InitialCompressionCertificateCode
  constructor
  · rintro ⟨Reps, hReps, H, hH, U, hU, stored, represented, trace, unionCode⟩
    obtain ⟨certificate, sameReps⟩ := stage.compressionCertificate_of_representatives
      pairing unions powers separation collection infinite hLabels hReps represented
    have historyCode := (certificate.realize_history_iff pairing unions powers separation
      collection infinite hLabels hH)
    rw [sameReps] at historyCode
    have historyEq := historyCode.1 trace
    have unionEq := (certificate.realize_union_iff separation infinite hU hH historyEq).1 unionCode
    refine ⟨certificate, ?_⟩
    simpa only [GroundInitialCompressionCertificate.code, sameReps, historyEq, unionEq] using stored.symm
  · rintro ⟨certificate, coded⟩
    have hH := certificate.history_ground pairing unions powers separation collection infinite hLabels
    have hU := certificate.unionData.code_ground pairing
    exact ⟨certificate.Reps, certificate.representatives_ground, certificate.history, hH,
      certificate.unionData.code, hU, coded.symm, certificate.representatives,
      (certificate.realize_history_iff pairing unions powers separation collection infinite hLabels hH).2 rfl,
      (certificate.realize_union_iff separation infinite hU hH rfl).2 rfl⟩

theorem exists_groundRecognizedCompressionCertificate
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Labels : ZFSet.{u}} (hLabels : Labels ∈ M.sets) :
    ∃ z ∈ M.sets, Realize M.sets
      (M.initialCompressionCertificateFormula pairing unions powers separation 0 1 2 3 4 5 6 7)
      (extend z (extend ZFSet.omega (extend stage.carrier (extend stage.actors
        (extend stage.order (extend stage.meetGraph (extend stage.action (extend Labels Fin.elim0)))))))) := by
  obtain ⟨certificate⟩ := stage.exists_compressionCertificate
    pairing unions powers separation collection infinite choice hLabels
  have ground := certificate.code_ground pairing unions powers separation collection infinite hLabels
  exact ⟨certificate.code, ground, (stage.realize_compressionCertificate_iff
    pairing unions powers separation collection infinite hLabels ground).2 ⟨certificate, rfl⟩⟩

end PartitionPilot.Forcing.GroundMainStage



namespace PartitionPilot.Forcing.GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions powers separation collection infinite

theorem realize_completedCompressionCertificate_iff {Labels z : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets (M.completedCompressionCertificateFormula pairing unions powers separation
      0 1 2 3 4 5 6 7 8)
      (extend z (extend ZFSet.omega (extend stage.carrier (extend stage.actors
        (extend stage.order (extend stage.meetGraph (extend stage.action
          (extend Labels (extend stage.top Fin.elim0))))))))) ↔
      ∃ completed : GroundInitialCompletedCompressionCertificate stage Labels,
        completed.code = z := by
  let env := extend z (extend ZFSet.omega (extend stage.carrier (extend stage.actors
    (extend stage.order (extend stage.meetGraph (extend stage.action
      (extend Labels (extend stage.top Fin.elim0))))))))
  have members : ∀ j, env j ∈ M.sets :=
    Fin.cases hz (Fin.cases (M.omega_mem separation infinite) (Fin.cases stage.carrier_ground
      (Fin.cases stage.actors_ground (Fin.cases stage.order_ground (Fin.cases stage.meet_ground
        (Fin.cases stage.action_ground (Fin.cases hLabels
          (Fin.cases stage.top_ground (fun j => Fin.elim0 j)))))))))
  rw [M.realize_completedCompressionCertificateFormula pairing unions powers separation
    0 1 2 3 4 5 6 7 8 env members stage.meet]
  change M.CompletedCompressionCertificateCode pairing unions powers separation z ZFSet.omega
    stage.carrier stage.actors stage.order stage.meetGraph stage.action Labels stage.top ↔ _
  have initial_iff (c : ZFSet.{u}) (hc : c ∈ M.sets) :
      M.InitialCompressionCertificateCode pairing unions powers separation c ZFSet.omega
        stage.carrier stage.actors stage.order stage.meetGraph stage.action Labels ↔
      ∃ certificate : GroundInitialCompressionCertificate stage Labels, certificate.code = c := by
    have recognized := stage.realize_compressionCertificate_iff
      pairing unions powers separation collection infinite hLabels hc
    have coreMembers : ∀ j : Fin 8,
        (extend c (extend ZFSet.omega (extend stage.carrier (extend stage.actors
          (extend stage.order (extend stage.meetGraph (extend stage.action
            (extend Labels Fin.elim0)))))))) j ∈ M.sets :=
      Fin.cases hc (Fin.cases (M.omega_mem separation infinite)
      (Fin.cases stage.carrier_ground (Fin.cases stage.actors_ground
        (Fin.cases stage.order_ground (Fin.cases stage.meet_ground
          (Fin.cases stage.action_ground (Fin.cases hLabels (fun j => Fin.elim0 j))))))))
    exact (M.realize_initialCompressionCertificateFormula pairing unions powers separation
      0 1 2 3 4 5 6 7 _ coreMembers stage.meet).symm.trans recognized
  unfold TransitiveGround.CompletedCompressionCertificateCode
  constructor
  · rintro ⟨stored, storedGround, outer, initialCode, core, fields, inner, unionTuple, maps, bases, caps⟩
    obtain ⟨certificate, certificateEq⟩ := (initial_iff (stored 0) (storedGround 0)).1 initialCode
    obtain ⟨completion⟩ := certificate.exists_completion
      pairing unions powers separation collection infinite hLabels
    have sameCore := nonemptyTupleCode_injective 2 (certificateEq.trans inner)
    have sameUnionCode : certificate.unionData.code = core 2 := congrFun sameCore 2
    have sameFields : certificate.unionData.fields = fields :=
      nonemptyTupleCode_injective 12 (sameUnionCode.trans unionTuple)
    have fieldsEq : completion.algebra.union.fields = fields :=
      (congrArg GroundCompressionUnionData.fields (certificate.completion_union completion)).trans sameFields
    have mapsEq : completion.algebra.maps = stored 1 := by
      rw [completion.algebra.maps_eq_sections, fieldsEq]
      exact maps.symm
    have basesEq : completion.algebra.bases = stored 2 := by
      unfold GroundCompressionAlgebra.bases
      rw [fieldsEq, mapsEq]
      exact bases.symm
    have capsEq : completion.algebra.caps stage.top = stored 3 := by
      unfold GroundCompressionAlgebra.caps
      rw [fieldsEq, mapsEq]
      exact caps.symm
    refine ⟨⟨certificate, completion⟩, ?_⟩
    change nonemptyTupleCode 3 (Fin.cases certificate.code
      (Fin.cases completion.algebra.maps (Fin.cases completion.algebra.bases
        (fun _ => completion.algebra.caps stage.top)))) = z
    rw [certificateEq, mapsEq, basesEq, capsEq]
    exact (congrArg (nonemptyTupleCode 3) (by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun k => Fin.elim0 k)))) j)).trans outer.symm
  · rintro ⟨completed, coded⟩
    let stored : Fin 4 → ZFSet.{u} := Fin.cases completed.certificate.code
      (Fin.cases completed.completion.algebra.maps (Fin.cases completed.completion.algebra.bases
        (fun _ => completed.completion.algebra.caps stage.top)))
    let core : Fin 3 → ZFSet.{u} := Fin.cases completed.certificate.Reps
      (Fin.cases completed.certificate.history (fun _ => completed.certificate.unionData.code))
    have hCore := completed.certificate.code_ground
      pairing unions powers separation collection infinite hLabels
    have ground : ∀ j, stored j ∈ M.sets := Fin.cases hCore
      (Fin.cases completed.completion.algebra.ground
        (Fin.cases completed.completion.bases_ground (fun _ => completed.completion.caps_ground)))
    refine ⟨stored, ground, coded.symm, (initial_iff _ hCore).2 ⟨completed.certificate, rfl⟩,
      core, completed.certificate.unionData.fields, rfl, rfl, ?_, ?_, ?_⟩
    · change completed.completion.algebra.maps = _
      rw [completed.completion.algebra.maps_eq_sections,
        completed.certificate.completion_union completed.completion]
      rfl
    · change completed.completion.algebra.bases = _
      unfold GroundCompressionAlgebra.bases
      rw [completed.certificate.completion_union completed.completion]
      rfl
    · change completed.completion.algebra.caps stage.top = _
      unfold GroundCompressionAlgebra.caps
      rw [completed.certificate.completion_union completed.completion]
      rfl

theorem exists_groundRecognizedCompletedCompressionCertificate
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Labels : ZFSet.{u}} (hLabels : Labels ∈ M.sets) :
    ∃ z ∈ M.sets, Realize M.sets
      (M.completedCompressionCertificateFormula pairing unions powers separation 0 1 2 3 4 5 6 7 8)
      (extend z (extend ZFSet.omega (extend stage.carrier (extend stage.actors
        (extend stage.order (extend stage.meetGraph (extend stage.action
          (extend Labels (extend stage.top Fin.elim0))))))))) := by
  obtain ⟨certificate⟩ := stage.exists_compressionCertificate
    pairing unions powers separation collection infinite choice hLabels
  obtain ⟨completed, _⟩ := certificate.exists_completedCertificate
    pairing unions powers separation collection infinite hLabels
  have ground := completed.code_ground pairing unions powers separation collection infinite hLabels
  exact ⟨completed.code, ground, (stage.realize_completedCompressionCertificate_iff
    pairing unions powers separation collection infinite hLabels ground).2 ⟨completed, rfl⟩⟩

end PartitionPilot.Forcing.GroundMainStage

end

end OAI
