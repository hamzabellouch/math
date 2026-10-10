import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialCompressionCompletion
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRecognizedInitialOrigin
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCanonicalCompressionHistory
import OAI.SetTheory.PartitionPrinciple.Transfinite.MainStageTaskCodes

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def historyFieldUnionElementFormula {n} (x N history : Fin n) (j : Fin 13) : SetFormula n :=
  ex (.conj (.mem 0 N.succ)
    (ex (.conj (historyFieldValueFormula 1 0 history.succ.succ j)
      (.mem x.succ.succ 0))))

def historyFieldUnionFormula {n} (output N history : Fin n) (j : Fin 13) : SetFormula n :=
  exactSetFormula output (historyFieldUnionElementFormula 0 N.succ history.succ j)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_historyFieldUnionElementFormula {k} (x N history : Fin k) (j : Fin 13)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (states : Nat → RecursiveStateData.{u}) (naturals : env N = ZFSet.omega)
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ env history ↔ y = (states n).code) :
    Realize M.sets (historyFieldUnionElementFormula x N history j) env ↔
      ∃ n, env x ∈ (states n).field j := by
  rw [historyFieldUnionElementFormula, realize_ex]
  simp only [Realize, realize_ex]
  constructor
  · rintro ⟨index, hIndex, indexMember, value, hValue, specified, member⟩
    change index ∈ env N at indexMember
    rw [naturals] at indexMember
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode index).1 indexMember
    have bounds : ∀ i, extend value (extend (natSetCode n) env) i ∈ M.sets :=
      Fin.cases hValue (Fin.cases hIndex members)
    have equal := (M.realize_historyFieldValueFormula 1 0 history.succ.succ j
      (extend value (extend (natSetCode n) env)) bounds states entries n rfl).1 specified
    change env x ∈ value at member
    exact ⟨n, equal ▸ member⟩
  · rintro ⟨n, member⟩
    have hIndex : natSetCode n ∈ M.sets :=
      M.transitive (naturals ▸ members N) (natSetCode_mem_omega n)
    have hCode := M.pair_right (M.transitive (members history) ((entries n _).2 rfl))
    have hValue := M.recursiveStateData_field_mem (states n) hCode j
    have bounds : ∀ i, extend ((states n).field j) (extend (natSetCode n) env) i ∈ M.sets :=
      Fin.cases hValue (Fin.cases hIndex members)
    refine ⟨natSetCode n, hIndex, ?_, (states n).field j, hValue, ?_, member⟩
    · change natSetCode n ∈ env N
      exact naturals.symm ▸ natSetCode_mem_omega n
    · exact (M.realize_historyFieldValueFormula 1 0 history.succ.succ j
        (extend ((states n).field j) (extend (natSetCode n) env)) bounds
        states entries n rfl).2 rfl

theorem realize_historyFieldUnionFormula {k} (output N history : Fin k) (j : Fin 13)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (states : Nat → RecursiveStateData.{u}) (naturals : env N = ZFSet.omega)
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ env history ↔ y = (states n).code)
    {target : ZFSet.{u}} (unionCode : NatUnionCode (fun n => (states n).field j) target) :
    Realize M.sets (historyFieldUnionFormula output N history j) env ↔ env output = target := by
  apply M.realize_exactSetFormula output _ env (members output)
  · intro z hz
    obtain ⟨n, member⟩ := (unionCode z).1 hz
    have hCode := M.pair_right (M.transitive (members history) ((entries n _).2 rfl))
    exact M.transitive (M.recursiveStateData_field_mem (states n) hCode j) member
  · intro z hz
    exact (M.realize_historyFieldUnionElementFormula 0 N.succ history.succ j
      (extend z env) (Fin.cases hz members) states naturals entries).trans (unionCode z).symm

end TransitiveGround

namespace GroundCompressionUnionData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}
variable (data : GroundCompressionUnionData M initial I Sources Reps G m one T)

theorem realize_canonicalFieldUnionFormula {k} (output N history : Fin k) (j : Fin 13)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (naturals : env N = ZFSet.omega)
    (canonical : env history = initial.canonicalHistory M I Sources Reps G T) :
    Realize M.sets (historyFieldUnionFormula output N history j) env ↔
      env output = data.fields j := by
  apply M.realize_historyFieldUnionFormula output N history j env members
    (initial.iterate M I Sources Reps G T) naturals _ (data.fieldUnion j)
  intro n y
  rw [canonical]
  exact initial.pair_mem_canonicalHistory M I Sources Reps G T n y

end GroundCompressionUnionData




namespace SetFormula

def historyFieldUnionTupleFormula {n} (output N history : Fin n) : SetFormula n :=
  exBlock 13 (.conj
    (BoundedFormula.nonemptyTupleFormula 12 (suffixIndex n 13 output) (prefixIndex n 13)).toFormula
    (conjBlock 13 (fun j => historyFieldUnionFormula (prefixIndex n 13 j)
      (suffixIndex n 13 N) (suffixIndex n 13 history) j)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_historyFieldUnionTupleFormula {k} (output N history : Fin k)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (states : Nat → RecursiveStateData.{u}) (naturals : env N = ZFSet.omega)
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ env history ↔ y = (states n).code)
    (fields : Fin 13 → ZFSet.{u})
    (unions : ∀ j, NatUnionCode (fun n => (states n).field j) (fields j)) :
    Realize M.sets (historyFieldUnionTupleFormula output N history) env ↔
      env output = nonemptyTupleCode 12 fields := by
  rw [historyFieldUnionTupleFormula, realize_exBlock]
  constructor
  · rintro ⟨stored, storedMembers, tuple, clauses⟩
    have bounds := extendMany_members 13 stored env storedMembers members
    have tupleEq := (BoundedFormula.truth_nonemptyTupleFormula 12
      (suffixIndex k 13 output) (prefixIndex k 13) _).1
        ((BoundedFormula.realize_toFormula M _ _ bounds).1 tuple)
    have each := (realize_conjBlock M.sets 13 _ _).1 clauses
    have fieldsEq : stored = fields := by
      funext j
      have equal := (M.realize_historyFieldUnionFormula
        (prefixIndex k 13 j) (suffixIndex k 13 N) (suffixIndex k 13 history) j
        _ bounds states (by simpa only [extendMany_suffix] using naturals)
        (by simpa only [extendMany_suffix] using entries) (unions j)).1 (each j)
      simpa only [extendMany_prefix] using equal
    simp only [extendMany_prefix, extendMany_suffix] at tupleEq
    exact tupleEq.trans (congrArg (nonemptyTupleCode 12) fieldsEq)
  · intro equal
    have fieldMembers := M.nonemptyTupleCode_field_mem 12 fields (equal ▸ members output)
    have bounds := extendMany_members 13 fields env fieldMembers members
    refine ⟨fields, fieldMembers, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 12
        (suffixIndex k 13 output) (prefixIndex k 13) _).2
      simpa only [extendMany_prefix, extendMany_suffix] using equal
    · apply (realize_conjBlock M.sets 13 _ _).2
      intro j
      apply (M.realize_historyFieldUnionFormula
        (prefixIndex k 13 j) (suffixIndex k 13 N) (suffixIndex k 13 history) j
        _ bounds states (by simpa only [extendMany_suffix] using naturals)
        (by simpa only [extendMany_suffix] using entries) (unions j)).2
      exact extendMany_prefix 13 fields env j

end TransitiveGround

namespace GroundCompressionUnionData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}
variable (data : GroundCompressionUnionData M initial I Sources Reps G m one T)

noncomputable def code : ZFSet.{u} := nonemptyTupleCode 12 data.fields

theorem code_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    data.code ∈ M.sets := M.nonemptyTupleCode_mem pairing 12 data.fields data.ground

theorem realize_canonicalUnionTupleFormula {k} (output N history : Fin k)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (naturals : env N = ZFSet.omega)
    (canonical : env history = initial.canonicalHistory M I Sources Reps G T) :
    Realize M.sets (historyFieldUnionTupleFormula output N history) env ↔
      env output = data.code := by
  apply M.realize_historyFieldUnionTupleFormula output N history env members
    (initial.iterate M I Sources Reps G T) naturals _ data.fields data.fieldUnion
  intro n y
  rw [canonical]
  exact initial.pair_mem_canonicalHistory M I Sources Reps G T n y

end GroundCompressionUnionData




structure GroundInitialCompressionCertificate {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
    (stage : GroundMainStage M C D rD) (Labels : ZFSet.{u}) where
  Reps : ZFSet.{u}
  representatives_ground : Reps ∈ M.sets
  representatives : TaskRepresentativesCode Reps (stage.compressionTasks Labels)
    stage.carrier stage.actors stage.order stage.action
    (M.groundRelations stage.carrier stage.carrier)
    (M.groundMeetFilters stage.carrier stage.order stage.meetGraph) Labels
  origin : GroundCompressionOrigin M (stage.compressionInitial Labels)
    stage.carrier stage.order stage.meetGraph stage.action stage.top
    (stage.compressionTasks Labels) (stage.compressionSources Labels) Reps
    stage.actors stage.multiplication stage.inverse stage.identity
    (stage.compressionTaskAction Labels) (stage.compressionFilters Labels)
  unionData : GroundCompressionUnionData M (stage.compressionInitial Labels)
    (stage.compressionTasks Labels) (stage.compressionSources Labels) Reps
    stage.actors stage.multiplication stage.identity (stage.compressionTaskAction Labels)

namespace GroundInitialCompressionCertificate
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {stage : GroundMainStage M C D rD}
variable (certificate : GroundInitialCompressionCertificate stage Labels)

noncomputable def history : ZFSet.{u} :=
  (stage.compressionInitial Labels).canonicalHistory M (stage.compressionTasks Labels)
    (stage.compressionSources Labels) certificate.Reps stage.actors (stage.compressionTaskAction Labels)

noncomputable def code : ZFSet.{u} :=
  nonemptyTupleCode 2 (Fin.cases certificate.Reps
    (Fin.cases certificate.history (fun _ => certificate.unionData.code)))

theorem history_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hLabels : Labels ∈ M.sets) : certificate.history ∈ M.sets := by
  obtain ⟨hI, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  have hT := M.groundTaskTransport_mem pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  have ground := certificate.origin.state.canonicalHistory_mem pairing unions powers separation
    collection infinite hI (fields 0).1 certificate.representatives_ground stage.actors_ground hT
  simpa only [certificate.origin.initial_data, history] using ground

theorem code_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hLabels : Labels ∈ M.sets) : certificate.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 _ (Fin.cases certificate.representatives_ground
    (Fin.cases (certificate.history_ground pairing unions powers separation collection infinite hLabels)
      (fun _ => certificate.unionData.code_ground pairing)))

end GroundInitialCompressionCertificate

namespace GroundMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions powers separation collection infinite

theorem compressionCertificate_of_representatives {Labels Reps : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hReps : Reps ∈ M.sets)
    (represented : TaskRepresentativesCode Reps (stage.compressionTasks Labels)
      stage.carrier stage.actors stage.order stage.action
      (M.groundRelations stage.carrier stage.carrier)
      (M.groundMeetFilters stage.carrier stage.order stage.meetGraph) Labels) :
    ∃ certificate : GroundInitialCompressionCertificate stage Labels, certificate.Reps = Reps := by
  obtain ⟨origin⟩ := M.initialCompressionOrigin_of_representatives pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground stage.action_ground
    hLabels stage.group_code stage.action_code stage.meet stage.top_mem stage.greatest
    represented.1 represented.2
  obtain ⟨hI, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  have hT := M.groundTaskTransport_mem pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  obtain ⟨data⟩ := origin.state.exists_groundUnion pairing unions powers separation collection infinite
    hI (fields 0).1 hReps stage.actors_ground hT
  have data' : GroundCompressionUnionData M (stage.compressionInitial Labels)
      (stage.compressionTasks Labels) (stage.compressionSources Labels) Reps
      stage.actors stage.multiplication stage.identity (stage.compressionTaskAction Labels) := by
    rw [origin.initial_data] at data
    exact data
  exact ⟨⟨Reps, hReps, represented, origin, data'⟩, rfl⟩

theorem exists_compressionCertificate
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Labels : ZFSet.{u}} (hLabels : Labels ∈ M.sets) :
    Nonempty (GroundInitialCompressionCertificate stage Labels) := by
  obtain ⟨Reps, hReps, function, represented, _⟩ := M.exists_groundTaskRepresentatives
    pairing unions powers separation choice stage.carrier_ground stage.actors_ground
      stage.order_ground stage.meet_ground stage.action_ground hLabels stage.meet
  obtain ⟨certificate, _⟩ := stage.compressionCertificate_of_representatives
    pairing unions powers separation collection infinite hLabels hReps ⟨function, represented⟩
  exact ⟨certificate⟩

end GroundMainStage

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundInitialCompressionCertificate
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {stage : GroundMainStage M C D rD}
variable (certificate : GroundInitialCompressionCertificate stage Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hLabels : Labels ∈ M.sets)
include pairing unions powers separation collection infinite hLabels

theorem realize_history_iff {H : ZFSet.{u}} (hH : H ∈ M.sets) :
    Realize M.sets (M.compressionHistoryFormula pairing unions powers separation)
      (extend ZFSet.omega (extend H (extend (stage.compressionInitial Labels).code
        (extend (stage.compressionTasks Labels) (extend (stage.compressionSources Labels)
          (extend certificate.Reps (extend stage.actors
            (extend (stage.compressionTaskAction Labels) Fin.elim0)))))))) ↔
      H = certificate.history := by
  obtain ⟨hI, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  have hT := M.groundTaskTransport_mem pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  have recognized := certificate.origin.state.realize_compressionHistory_iff
    pairing unions powers separation collection infinite hI (fields 0).1
    certificate.representatives_ground stage.actors_ground hT hH
  simpa only [certificate.origin.initial_data, history] using recognized

omit pairing unions powers collection hLabels in
theorem realize_union_iff {U H : ZFSet.{u}} (hU : U ∈ M.sets) (hH : H ∈ M.sets)
    (canonical : H = certificate.history) :
    Realize M.sets (historyFieldUnionTupleFormula 0 1 2)
      (extend U (extend ZFSet.omega (extend H Fin.elim0))) ↔ U = certificate.unionData.code := by
  exact certificate.unionData.realize_canonicalUnionTupleFormula 0 1 2
    (extend U (extend ZFSet.omega (extend H Fin.elim0)))
    (Fin.cases hU (Fin.cases (M.omega_mem separation infinite)
      (Fin.cases hH (fun i => Fin.elim0 i)))) rfl canonical

end PartitionPilot.Forcing.GroundInitialCompressionCertificate



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P r μ A τ I Sources Reps G m inv one T Filters Labels : ZFSet.{u}}
variable {seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)

theorem initial_union_range_accounting
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets)
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    (initialIndices : I = M.groundEligibleTasks P G r μ A Labels)
    (initialSources : Sources = literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :
    CompressionRangeAccounting P I (algebra.union.fields 0)
      (algebra.union.fields 1) (algebra.union.fields 2) algebra.maps algebra.bases (algebra.caps τ) := by
  have sourceLiteral {i a : ZFSet.{u}} (source : ZFSet.pair i a ∈ Sources) :
      ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels := initialSources ▸ source
  refine {
    original_subset := state.union_original_subset algebra.union
    base_filled := ?_
    old_shadow := ?_
    cap_separation := ?_
    fresh_accounting := ?_
  }
  · intro i hi f b indexed based x hx below
    obtain ⟨a, source, _⟩ := seed.sources.2 i hi
    obtain ⟨g, representative, _⟩ := state.inputs.representatives.2 i hi
    exact state.union_map_base_filling algebra pairing unions powers separation hI hSources hReps hG hT
      indexed source representative ((state.union_base_entry_iff algebra indexed source).1 based) hx below
  · intro i hi b k based capped x hx below
    obtain ⟨f, indexed⟩ := algebra.function.total hi
    obtain ⟨a, source, _⟩ := seed.sources.2 i hi
    exact state.union_initial_old_shadow algebra pairing unions powers separation
      hP hG hr hμ hA hLabels hI hSources hReps hT initialData indexed (sourceLiteral source)
      ((state.union_cap_entry_iff algebra indexed).1 capped)
      ((state.union_base_entry_iff algebra indexed source).1 based) hx below
  · intro i hi j hj different b c k l basedI basedJ cappedI cappedJ
    obtain ⟨f, indexedI⟩ := algebra.function.total hi
    obtain ⟨g, indexedJ⟩ := algebra.function.total hj
    obtain ⟨a, sourceI, _⟩ := seed.sources.2 i hi
    obtain ⟨d, sourceJ, _⟩ := seed.sources.2 j hj
    exact state.union_initial_cap_separation algebra pairing unions powers separation
      hP hG hr hμ hA hLabels initialData indexedI indexedJ (sourceLiteral sourceI) (sourceLiteral sourceJ)
      ((state.union_cap_entry_iff algebra indexedI).1 cappedI)
      ((state.union_cap_entry_iff algebra indexedJ).1 cappedJ)
      ((state.union_base_entry_iff algebra indexedI sourceI).1 basedI)
      ((state.union_base_entry_iff algebra indexedJ sourceJ).1 basedJ) different
  · have top : ∀ x ∈ P, ZFSet.pair x τ ∈ r := by
      simpa only [initialData, TransitiveGround.initialCompressionData] using state.invariant.top
    have initialAccounting : FiniteCompressionAccounting P I Sources τ state.data := by
      simpa only [initialData, initialIndices, initialSources] using
        (M.initialCompressionData_accounting pairing unions powers separation
          hP hG hr hμ hA hLabels state.inputs.group seed.originalAction seed.originalOrder seed.top_mem top)
    intro x hx
    rcases state.union_fresh_accounting algebra pairing unions powers separation
      hI hSources hReps hG hT initialAccounting x hx with original | fresh
    · exact Or.inl original
    · obtain ⟨i, hi, f, a, k, b, y, hy, indexed, source, cap, base, image, below, outside⟩ := fresh
      exact Or.inr ⟨i, hi, f, k, b, y, hy, indexed,
        (state.union_cap_entry_iff algebra indexed).2 cap,
        (state.union_base_entry_iff algebra indexed source).2 base, image, below, outside⟩

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundInitialCompressionCertificate
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {stage : GroundMainStage M C D rD}
variable (certificate : GroundInitialCompressionCertificate stage Labels)

abbrev Completion := GroundCompressionCompletion M (stage.compressionInitial Labels)
  (stage.compressionTasks Labels) (stage.compressionSources Labels) certificate.Reps
  stage.actors stage.multiplication stage.identity (stage.compressionTaskAction Labels) stage.top

theorem completion_union (completion : certificate.Completion) :
    completion.algebra.union = certificate.unionData :=
  completion.algebra.union.unique certificate.unionData

theorem exists_completion
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hLabels : Labels ∈ M.sets) :
    Nonempty certificate.Completion := by
  obtain ⟨hI, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  have hT := M.groundTaskTransport_mem pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  obtain ⟨algebra⟩ := certificate.origin.state.exists_groundAlgebra
    pairing unions powers separation collection infinite hI (fields 0).1
    certificate.representatives_ground stage.actors_ground hT
  have accounting := certificate.origin.state.initial_union_range_accounting algebra
    pairing unions powers separation stage.carrier_ground stage.actors_ground
    stage.order_ground stage.meet_ground stage.action_ground hLabels hI (fields 0).1
    certificate.representatives_ground hT certificate.origin.initial_data rfl rfl
  obtain ⟨completion⟩ := certificate.origin.state.completion_of_accounting algebra
    pairing unions powers separation hI (fields 0).1 certificate.representatives_ground
    stage.actors_ground hT accounting
  exact ⟨by simpa only [certificate.origin.initial_data] using completion⟩

theorem completion_profiles (completion : certificate.Completion)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hLabels : Labels ∈ M.sets) :
    CodedCompressionProfiles (completion.algebra.union.fields 0)
      (completion.algebra.union.fields 1) (completion.algebra.union.fields 2)
      (completion.algebra.caps stage.top) (stage.compressionTargets Labels)
      (stage.compressionSeparators Labels) (stage.compressionFilters Labels) := by
  obtain ⟨hI, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  have hT := M.groundTaskTransport_mem pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  have transfer (initial : RecursiveStateData.{u})
      (origin : GroundCompressionOrigin M initial stage.carrier stage.order stage.meetGraph
        stage.action stage.top (stage.compressionTasks Labels) (stage.compressionSources Labels)
        certificate.Reps stage.actors stage.multiplication stage.inverse stage.identity
        (stage.compressionTaskAction Labels) (stage.compressionFilters Labels))
      (algebra : GroundCompressionAlgebra M initial (stage.compressionTasks Labels)
        (stage.compressionSources Labels) certificate.Reps stage.actors stage.multiplication
        stage.identity (stage.compressionTaskAction Labels))
      (initialData : initial = stage.compressionInitial Labels) :
      CodedCompressionProfiles (algebra.union.fields 0) (algebra.union.fields 1)
        (algebra.union.fields 2) (algebra.caps stage.top) (stage.compressionTargets Labels)
        (stage.compressionSeparators Labels) (stage.compressionFilters Labels) := by
    obtain ⟨seed, state, equal⟩ := origin
    cases equal
    exact state.initial_union_profiles algebra pairing unions powers separation
      stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
      stage.action_ground hLabels hI (fields 0).1 certificate.representatives_ground hT initialData rfl
  exact transfer _ certificate.origin completion.algebra rfl

theorem completion_original_data (completion : certificate.Completion)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hLabels : Labels ∈ M.sets) :
    CompressionOriginalData stage.carrier stage.order stage.meetGraph stage.action stage.actors
      (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 2) (completion.algebra.union.fields 12) := by
  obtain ⟨hI, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  have hT := M.groundTaskTransport_mem pairing unions powers separation
    stage.carrier_ground stage.actors_ground stage.order_ground stage.meet_ground
    stage.action_ground hLabels stage.meet
  exact certificate.origin.union_original_data completion.algebra.union
    pairing unions powers separation hI (fields 0).1 certificate.representatives_ground
    stage.actors_ground hT

end PartitionPilot.Forcing.GroundInitialCompressionCertificate



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure GroundInitialCompletedCompressionCertificate
    {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
    (stage : GroundMainStage M C D rD) (Labels : ZFSet.{u}) where
  certificate : GroundInitialCompressionCertificate stage Labels
  completion : certificate.Completion

namespace GroundInitialCompletedCompressionCertificate
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {stage : GroundMainStage M C D rD}
variable (completed : GroundInitialCompletedCompressionCertificate stage Labels)

noncomputable def code : ZFSet.{u} := nonemptyTupleCode 3
  (Fin.cases completed.certificate.code
    (Fin.cases completed.completion.algebra.maps
      (Fin.cases completed.completion.algebra.bases
        (fun _ => completed.completion.algebra.caps stage.top))))

theorem code_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hLabels : Labels ∈ M.sets) : completed.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 3 _
    (Fin.cases (completed.certificate.code_ground pairing unions powers separation
      collection infinite hLabels) (Fin.cases completed.completion.algebra.ground
      (Fin.cases completed.completion.bases_ground (fun _ => completed.completion.caps_ground))))

end GroundInitialCompletedCompressionCertificate

namespace GroundInitialCompressionCertificate
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {stage : GroundMainStage M C D rD}
variable (certificate : GroundInitialCompressionCertificate stage Labels)

theorem exists_completedCertificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hLabels : Labels ∈ M.sets) :
    ∃ completed : GroundInitialCompletedCompressionCertificate stage Labels,
      completed.certificate = certificate := by
  obtain ⟨completion⟩ := certificate.exists_completion
    pairing unions powers separation collection infinite hLabels
  exact ⟨⟨certificate, completion⟩, rfl⟩

end GroundInitialCompressionCertificate

end PartitionPilot.Forcing

end OAI
