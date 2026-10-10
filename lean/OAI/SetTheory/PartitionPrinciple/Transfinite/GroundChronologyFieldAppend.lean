import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFixedTopOrders
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCompressionBirthData
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSerializedChronologyTimeEquality

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem isFunc_retarget_of_entries {A B C f : ZFSet.{u}}
    (function : ZFSet.IsFunc A B f)
    (bound : ∀ x y, ZFSet.pair x y ∈ f → y ∈ C) : ZFSet.IsFunc A C f := by
  refine ⟨?_, function.2⟩
  intro z entry
  obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 entry)
  exact ZFSet.pair_mem_prod.2 ⟨hx, bound x y entry⟩

namespace GroundCompressionBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T base old : ZFSet.{u}}
variable {data : GroundCompressionUnionData M initial I Sources Reps G m one T}
variable (births : GroundCompressionBirthData M initial I Sources Reps G m one T data base old)

theorem union_function_successor :
    ZFSet.IsFunc (data.fields 0) (insert births.limit births.limit) births.birth :=
  isFunc_retarget_of_entries births.function
    (fun _ _ entry => ZFSet.mem_insert_of_mem _ (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2)

theorem finite_function_successor (n : Nat) :
    ZFSet.IsFunc (initial.iterate M I Sources Reps G T (n + 1)).D
      (insert births.limit births.limit)
      (graphRestriction (initial.iterate M I Sources Reps G T (n + 1)).D births.birth) := by
  have restricted := (show FunctionGraphOn (data.fields 0) births.birth from
    ⟨births.limit, births.function⟩).restrict ((data.fieldUnion 0).subset (n + 1))
  apply isFunc_retarget_of_entries restricted.to_isFunc
  intro x t entry
  exact ZFSet.mem_insert_of_mem _
    (ZFSet.pair_mem_prod.1 (births.function.1 (pair_mem_graphRestriction.1 entry).1)).2

end GroundCompressionBirthData

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)

theorem finite_birth_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) (n : Nat) {x t : ZFSet.{u}}
    (entry : ZFSet.pair x t ∈
      graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth) :
    t ∈ compressionStamp base n ∨ t = compressionStamp base n := by
  have before := state.canonical_birth_before_stamp pairing unions powers separation
    hI hSources hReps hG hT births.extension births.initial_bound (n + 1) entry
  rw [compressionStamp_succ] at before
  exact (ZFSet.mem_insert_iff.1 before).symm

end GroundCompressionState

namespace GroundChronologicalHistory
variable {M : TransitiveGround.{u}} {T0 C Q qlt base stamps limit s : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T0 C Q qlt)

theorem prefix_birth_function_successor
    (times : CompressionStampCode base stamps limit)
    (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
    (prior : s ∈ base ∨ s = base) :
    ZFSet.IsFunc (history.space s) (insert limit limit) (history.birth s) := by
  have hs : s ∈ T0 := prior.elim (fun before => ordinal.1 base hBase s before)
    (fun equal => equal.symm ▸ hBase)
  have below : s ∈ limit := times.union.subset 0 (compressionStamp_old_mem prior 0)
  apply isFunc_retarget_of_entries (history.birth_function s hs)
  intro x t entry
  have hx := (ZFSet.pair_mem_prod.1 ((history.birth_function s hs).1 entry)).1
  have bounded := history.birth_bound s hs x hx t entry
  apply ZFSet.mem_insert_of_mem
  exact bounded.elim (fun equal => equal.symm ▸ below)
    (fun before => times.ordinal.1 s below t before)

end GroundChronologicalHistory

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure CompressionChronologyFields where
  space : ZFSet.{u} → ZFSet.{u}
  order : ZFSet.{u} → ZFSet.{u}
  meetGraph : ZFSet.{u} → ZFSet.{u}
  birth : ZFSet.{u} → ZFSet.{u}
  height : ZFSet.{u} → ZFSet.{u}

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)

noncomputable def prefixFields : CompressionChronologyFields.{u} where
  space := compressionPrefixValue base births.limit prior.space
    (fun n => (state.data.iterate M I Sources Reps G T (n + 1)).D) (data.fields 0)
  order := compressionPrefixValue base births.limit prior.order
    (fun n => (state.data.iterate M I Sources Reps G T (n + 1)).rD) (data.fields 1)
  meetGraph := compressionPrefixValue base births.limit prior.meetGraph
    (fun n => (state.data.iterate M I Sources Reps G T (n + 1)).μD) (data.fields 2)
  birth := compressionPrefixValue base births.limit prior.birth
    (fun n => graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth) births.birth
  height := compressionPrefixValue base births.limit prior.height
    (fun n => heights.function.natValue (n + 1)) heights.height

theorem prefixFields_old {s : ZFSet.{u}} (before : s ∈ base ∨ s = base) :
    (state.prefixFields data births heights prior).space s = prior.space s ∧
    (state.prefixFields data births heights prior).order s = prior.order s ∧
    (state.prefixFields data births heights prior).meetGraph s = prior.meetGraph s ∧
    (state.prefixFields data births heights prior).birth s = prior.birth s ∧
    (state.prefixFields data births heights prior).height s = prior.height s := by
  dsimp only [prefixFields]
  exact ⟨compressionPrefixValue_old _ _ _ before,
    compressionPrefixValue_old _ _ _ before, compressionPrefixValue_old _ _ _ before,
    compressionPrefixValue_old _ _ _ before, compressionPrefixValue_old _ _ _ before⟩

theorem prefixFields_stamp (n : Nat) :
    (state.prefixFields data births heights prior).space (compressionStamp base n) =
      (state.data.iterate M I Sources Reps G T (n + 1)).D ∧
    (state.prefixFields data births heights prior).order (compressionStamp base n) =
      (state.data.iterate M I Sources Reps G T (n + 1)).rD ∧
    (state.prefixFields data births heights prior).meetGraph (compressionStamp base n) =
      (state.data.iterate M I Sources Reps G T (n + 1)).μD ∧
    (state.prefixFields data births heights prior).birth (compressionStamp base n) =
      graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth ∧
    (state.prefixFields data births heights prior).height (compressionStamp base n) =
      heights.function.natValue (n + 1) := by
  dsimp only [prefixFields]
  exact ⟨compressionPrefixValue_stamp _ _ _ births.times n,
    compressionPrefixValue_stamp _ _ _ births.times n, compressionPrefixValue_stamp _ _ _ births.times n,
    compressionPrefixValue_stamp _ _ _ births.times n, compressionPrefixValue_stamp _ _ _ births.times n⟩

theorem prefixFields_limit :
    (state.prefixFields data births heights prior).space births.limit = data.fields 0 ∧
    (state.prefixFields data births heights prior).order births.limit = data.fields 1 ∧
    (state.prefixFields data births heights prior).meetGraph births.limit = data.fields 2 ∧
    (state.prefixFields data births heights prior).birth births.limit = births.birth ∧
    (state.prefixFields data births heights prior).height births.limit = heights.height := by
  dsimp only [prefixFields]
  exact ⟨compressionPrefixValue_limit _ _ _ births.times,
    compressionPrefixValue_limit _ _ _ births.times, compressionPrefixValue_limit _ _ _ births.times,
    compressionPrefixValue_limit _ _ _ births.times, compressionPrefixValue_limit _ _ _ births.times⟩

end GroundCompressionState

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundChronologicalHistory
universe u
variable {M : TransitiveGround.{u}} {T C D rD cutoff : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C D rD)
variable (ordinal : ordinalSetProperty T) (hc : cutoff ∈ T)

def restrictToCutoff : GroundChronologicalHistory M (insert cutoff cutoff) C D rD := by
  have included : insert cutoff cutoff ⊆ T := by
    intro s hs
    rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
    · exact hc
    · exact ordinal.1 cutoff hc s hs
  refine {
    space := history.space, order := history.order, meetGraph := history.meetGraph
    birth := history.birth, height := history.height
    space_mem := fun s hs => history.space_mem s (included hs)
    order_mem := fun s hs => history.order_mem s (included hs)
    meet_mem := fun s hs => history.meet_mem s (included hs)
    birth_mem := fun s hs => history.birth_mem s (included hs)
    height_mem := fun s hs => history.height_mem s (included hs)
    meet_order := fun s hs => history.meet_order s (included hs)
    birth_function := ?_
    birth_bound := fun s hs => history.birth_bound s (included hs)
    old_meet := fun s hs => history.old_meet s (included hs)
    strict_height := fun s hs => history.strict_height s (included hs)
    layer := fun s hs t ht bound => history.layer s (included hs) t (included ht) bound }
  intro s hs
  apply isFunc_retarget_of_entries (history.birth_function s (included hs))
  intro x t entry
  have hx := (ZFSet.pair_mem_prod.1 ((history.birth_function s (included hs)).1 entry)).1
  rcases history.birth_bound s (included hs) x hx t entry with rfl | before
  · exact hs
  · rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
    · exact ZFSet.mem_insert_of_mem _ before
    · exact ZFSet.mem_insert_of_mem _ (ordinal.2 cutoff hc s hs t before)

theorem restrictToCutoff_values (s : ZFSet.{u}) :
    (history.restrictToCutoff ordinal hc).space s = history.space s ∧
    (history.restrictToCutoff ordinal hc).order s = history.order s ∧
    (history.restrictToCutoff ordinal hc).meetGraph s = history.meetGraph s ∧
    (history.restrictToCutoff ordinal hc).birth s = history.birth s ∧
    (history.restrictToCutoff ordinal hc).height s = history.height s := ⟨rfl, rfl, rfl, rfl, rfl⟩

end PartitionPilot.Forcing.GroundChronologicalHistory



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def appendHistoryValue (time : ZFSet.{u})
    (previous : ZFSet.{u} → ZFSet.{u}) (latest t : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if t = time then latest else previous t

theorem appendHistoryValue_at (time : ZFSet.{u}) (previous : ZFSet.{u} → ZFSet.{u})
    (latest : ZFSet.{u}) : appendHistoryValue time previous latest time = latest := by
  simp [appendHistoryValue]

theorem appendHistoryValue_old {time t : ZFSet.{u}} (member : t ∈ time)
    (previous : ZFSet.{u} → ZFSet.{u}) (latest : ZFSet.{u}) :
    appendHistoryValue time previous latest t = previous t := by
  apply ite_eq_right
  intro equal
  exact ZFSet.mem_irrefl time (equal ▸ member)

namespace GroundChronologicalHistory
variable {M : TransitiveGround.{u}} {s C D rD : ZFSet.{u}}
variable (history : GroundChronologicalHistory M (insert s s) C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (ordinal : ordinalSetProperty s) (hs : s ∈ M.sets)
variable (earlier : ∀ x t, ZFSet.pair x t ∈ history.birth s → t ∈ s)
variable (newHeight : ZFSet.{u}) (hHeight : newHeight ∈ M.sets)
variable (heightCode : StrictLexHeightCode (fixedTopCarrier (history.space s)) C D
  (fixedTopOrder (history.space s) (history.order s)) newHeight rD)

local notation "time" => (insert s s)
local notation "times" => (insert (insert s s) (insert s s))
local notation "P" => history.space s
local notation "r" => history.order s
local notation "μ" => history.meetGraph s
local notation "born" => history.birth s
local notation "space'" => appendHistoryValue time history.space (fixedTopCarrier P)
local notation "order'" => appendHistoryValue time history.order (fixedTopOrder P r)
local notation "meet'" => appendHistoryValue time history.meetGraph (fixedTopMeet P r)
local notation "birth'" => appendHistoryValue time history.birth (fixedTopBirth P born s)
local notation "height'" => appendHistoryValue time history.height newHeight

noncomputable def appendFixedTop : GroundChronologicalHistory M times C D rD := by
  classical
  have terminal : s ∈ time := ZFSet.mem_insert_iff.2 (Or.inl rfl)
  have hP := history.space_mem s terminal
  have hr := history.order_mem s terminal
  have meet := history.meet_order s terminal
  have function := history.birth_function s terminal
  have oldOrdinal := ordinalSetProperty_succ ordinal
  have sourceSpace : ∀ t ∈ time, ∀ z ∈ t, history.space z = space' z :=
    fun t ht z hz => (appendHistoryValue_old (oldOrdinal.1 t ht z hz) _ _).symm
  have sourceOrder : ∀ t ∈ time, ∀ z ∈ t, history.order z = order' z :=
    fun t ht z hz => (appendHistoryValue_old (oldOrdinal.1 t ht z hz) _ _).symm
  have sourceMeet : ∀ t ∈ time, ∀ z ∈ t, history.meetGraph z = meet' z :=
    fun t ht z hz => (appendHistoryValue_old (oldOrdinal.1 t ht z hz) _ _).symm
  have newBefore : ∀ x t, ZFSet.pair x t ∈ fixedTopBirth P born s → t ∈ time := by
    intro x t entry
    exact ZFSet.mem_insert_iff.2 (fixedTopBirth_bound earlier x t entry)
  refine {
    space := space', order := order', meetGraph := meet', birth := birth', height := height'
    space_mem := ?_, order_mem := ?_, meet_mem := ?_, birth_mem := ?_, height_mem := ?_
    meet_order := ?_, birth_function := ?_, birth_bound := ?_, old_meet := ?_
    strict_height := ?_, layer := ?_ }
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using M.fixedTopCarrier_mem pairing unions hP
    · simpa only [appendHistoryValue_old ht] using history.space_mem t ht
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using M.fixedTopOrder_mem pairing unions powers separation hP hr
    · simpa only [appendHistoryValue_old ht] using history.order_mem t ht
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using M.fixedTopMeet_mem pairing unions powers separation hP hr
    · simpa only [appendHistoryValue_old ht] using history.meet_mem t ht
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using
        M.fixedTopBirth_mem pairing unions hP (history.birth_mem s terminal) hs
    · simpa only [appendHistoryValue_old ht] using history.birth_mem t ht
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using hHeight
    · simpa only [appendHistoryValue_old ht] using history.height_mem t ht
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using fixedTopMeet_code meet
    · simpa only [appendHistoryValue_old ht] using history.meet_order t ht
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simp only [appendHistoryValue_at]
      exact isFunc_retarget_of_entries (fixedTopBirth_function function terminal)
        (fun x a entry => ZFSet.mem_insert_iff.2 (Or.inr (newBefore x a entry)))
    · simp only [appendHistoryValue_old ht]
      exact isFunc_retarget_of_entries (history.birth_function t ht)
        (fun _ _ entry => ZFSet.mem_insert_iff.2
          (Or.inr (ZFSet.pair_mem_prod.1 ((history.birth_function t ht).1 entry)).2))
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simp only [appendHistoryValue_at]
      exact fun x _ a entry => Or.inr (newBefore x a entry)
    · simpa only [appendHistoryValue_old ht] using history.birth_bound t ht
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using
        fixedTopBirth_oldMeet meet function earlier (history.old_meet s terminal)
    · simpa only [appendHistoryValue_old ht] using history.old_meet t ht
  · intro t ht
    rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
    · simpa only [appendHistoryValue_at] using heightCode
    · simpa only [appendHistoryValue_old ht] using history.strict_height t ht
  · intro cutoff hc t ht bound
    by_cases equal : cutoff = time
    · subst cutoff
      simp only [appendHistoryValue_at]
      by_cases same : t = time
      · subst t
        exact CodedGrowthLayer.empty_at_birth_bound ⟨P, hP⟩ newBefore
      · have ht := (ZFSet.mem_insert_iff.1 ht).resolve_left same
        have layer := M.fixedTopBirth_layers pairing separation hP meet function earlier
          (fun a ha => history.layer s terminal a (ZFSet.mem_insert_iff.2 (Or.inr ha)) (Or.inr ha))
          t (ZFSet.mem_insert_iff.1 ht)
        exact layer.congr_sources_below (sourceSpace t ht) (sourceOrder t ht) (sourceMeet t ht)
    · have hc := (ZFSet.mem_insert_iff.1 hc).resolve_left equal
      have htOld : t ∈ time := bound.elim (fun equal => equal ▸ hc)
        (fun before => oldOrdinal.1 cutoff hc t before)
      simpa only [appendHistoryValue_old hc] using
        (history.layer cutoff hc t htOld bound).congr_sources_below
          (sourceSpace t htOld) (sourceOrder t htOld) (sourceMeet t htOld)

local notation "extended" => history.appendFixedTop pairing unions powers separation ordinal hs earlier newHeight hHeight heightCode

theorem appendFixedTop_old {t : ZFSet.{u}} (ht : t ∈ time) :
    (extended).space t = history.space t ∧ (extended).order t = history.order t ∧
      (extended).meetGraph t = history.meetGraph t ∧ (extended).birth t = history.birth t ∧
      (extended).height t = history.height t := by
  exact ⟨appendHistoryValue_old ht _ _, appendHistoryValue_old ht _ _, appendHistoryValue_old ht _ _,
    appendHistoryValue_old ht _ _, appendHistoryValue_old ht _ _⟩

theorem appendFixedTop_new :
    (extended).space time = fixedTopCarrier P ∧ (extended).order time = fixedTopOrder P r ∧
      (extended).meetGraph time = fixedTopMeet P r ∧ (extended).birth time = fixedTopBirth P born s ∧
      (extended).height time = newHeight := by
  exact ⟨appendHistoryValue_at _ _ _, appendHistoryValue_at _ _ _, appendHistoryValue_at _ _ _,
    appendHistoryValue_at _ _ _, appendHistoryValue_at _ _ _⟩

end GroundChronologicalHistory

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)

theorem prefixFields_stage_laws
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
    {s : ZFSet.{u}} (cutoff : s ∈ insert births.limit births.limit) :
    let fields := state.prefixFields data births heights prior
    MeetOrderCode (fields.space s) (fields.order s) (fields.meetGraph s) ∧
    ZFSet.IsFunc (fields.space s) (insert births.limit births.limit) (fields.birth s) ∧
    (∀ x ∈ fields.space s, ∀ t, ZFSet.pair x t ∈ fields.birth s → t = s ∨ t ∈ s) ∧
    OldMeetCode (fields.order s) (fields.meetGraph s) (fields.birth s) ∧
    StrictLexHeightCode (fields.space s) C Q (fields.order s) (fields.height s) qlt := by
  classical
  dsimp only
  by_cases before : s ∈ base ∨ s = base
  · have hs := before.elim (fun member => ordinal.1 base hBase s member)
      (fun equal => equal.symm ▸ hBase)
    obtain ⟨space, order, meet, birth, height⟩ := state.prefixFields_old data births heights prior before
    rw [space, order, meet, birth, height]
    exact ⟨prior.meet_order s hs,
      prior.prefix_birth_function_successor births.times ordinal hBase before,
      prior.birth_bound s hs, prior.old_meet s hs, prior.strict_height s hs⟩
  · rcases ZFSet.mem_insert_iff.1 cutoff with rfl | below
    · obtain ⟨space, order, meet, birth, height⟩ := state.prefixFields_limit data births heights prior
      rw [space, order, meet, birth, height]
      exact ⟨data.meet, births.union_function_successor,
        fun _ _ _ entry => Or.inr (ZFSet.pair_mem_prod.1 (births.function.1 entry)).2,
        births.old_meet, heights.code⟩
    · have stamped : ∃ n, s = compressionStamp base n := by
        rcases (births.times.mem_limit_iff s).1 below with member | equal | stamped
        · exact False.elim (before (Or.inl member))
        · exact False.elim (before (Or.inr equal))
        · exact stamped
      obtain ⟨n, rfl⟩ := stamped
      obtain ⟨space, order, meet, birth, height⟩ := state.prefixFields_stamp data births heights prior n
      rw [space, order, meet, birth, height]
      exact ⟨(state.canonical_iterate_codes pairing unions powers separation
          hI hSources hReps hG hT (n + 1)).1,
        births.finite_function_successor n,
        fun _ _ _ entry => (state.finite_birth_bound data births pairing unions powers separation
          hI hSources hReps hG hT n entry).symm,
        births.finite_old_meet (n + 1), heights.finite (n + 1)⟩





theorem prefixFields_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
    {s : ZFSet.{u}} (cutoff : s ∈ insert births.limit births.limit) :
    (state.prefixFields data births heights prior).space s ∈ M.sets ∧
    (state.prefixFields data births heights prior).order s ∈ M.sets ∧
    (state.prefixFields data births heights prior).meetGraph s ∈ M.sets ∧
    (state.prefixFields data births heights prior).birth s ∈ M.sets ∧
    (state.prefixFields data births heights prior).height s ∈ M.sets := by
  have originalIndex {t : ZFSet.{u}} (before : t ∈ base ∨ t = base) : t ∈ T0 :=
    before.elim (fun h => ordinal.1 base hBase t h) (fun h => h ▸ hBase)
  have finite (n : Nat) :
      (state.data.iterate M I Sources Reps G T (n + 1)).D ∈ M.sets ∧
      (state.data.iterate M I Sources Reps G T (n + 1)).rD ∈ M.sets ∧
      (state.data.iterate M I Sources Reps G T (n + 1)).μD ∈ M.sets := by
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT (n + 1)
    rw [← equal]
    exact ⟨current.ground.carrier, current.ground.order, current.ground.meet⟩
  have finiteBirth (n : Nat) :
      graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth ∈ M.sets :=
    M.pair_right (M.transitive births.family_ground ((births.family_entries (n + 1) _).2 rfl))
  have finiteHeight (n : Nat) : heights.function.natValue (n + 1) ∈ M.sets :=
    M.pair_right (M.transitive heights.family_ground (heights.function.natValue_entry (n + 1)))
  dsimp only [prefixFields]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact TransitiveGround.compressionPrefixValue_mem _ _ _ M births.times
      (fun t ht => prior.space_mem t (originalIndex ht)) (fun n => (finite n).1) (data.ground 0) cutoff
  · exact TransitiveGround.compressionPrefixValue_mem _ _ _ M births.times
      (fun t ht => prior.order_mem t (originalIndex ht)) (fun n => (finite n).2.1) (data.ground 1) cutoff
  · exact TransitiveGround.compressionPrefixValue_mem _ _ _ M births.times
      (fun t ht => prior.meet_mem t (originalIndex ht)) (fun n => (finite n).2.2) (data.ground 2) cutoff
  · exact TransitiveGround.compressionPrefixValue_mem _ _ _ M births.times
      (fun t ht => prior.birth_mem t (originalIndex ht)) finiteBirth births.birth_ground cutoff
  · exact TransitiveGround.compressionPrefixValue_mem _ _ _ M births.times
      (fun t ht => prior.height_mem t (originalIndex ht)) finiteHeight heights.height_ground cutoff

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def terminalChronologyGraph (s f v : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair s v) (graphRestriction s f)

theorem pair_mem_terminalChronologyGraph (s f v x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ terminalChronologyGraph s f v ↔
      (x = s ∧ y = v) ∨ (ZFSet.pair x y ∈ f ∧ x ∈ s) := by
  rw [terminalChronologyGraph, ZFSet.mem_insert_iff, ZFSet.pair_inj, pair_mem_graphRestriction]

theorem terminalChronologyGraph_function {s f v : ZFSet.{u}}
    (function : FunctionGraphOn (insert s s) f) :
    FunctionGraphOn (insert s s) (terminalChronologyGraph s f v) := by
  refine ⟨insert v (ZFSet.sUnion (ZFSet.sUnion f)), ?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | old
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert _ _, ZFSet.mem_insert _ _⟩
    · obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 old
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem _ hx,
        ZFSet.mem_insert_of_mem _ (pair_second_mem_doubleUnion entry)⟩
  · intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | hx
    · refine ⟨v, (pair_mem_terminalChronologyGraph _ _ _ _ _).2 (Or.inl ⟨rfl,rfl⟩), ?_⟩
      intro y entry
      rcases (pair_mem_terminalChronologyGraph _ _ _ _ _).1 entry with new | old
      · exact new.2
      · exact False.elim (ZFSet.mem_irrefl _ old.2)
    · obtain ⟨y, entry, unique⟩ := function.to_isFunc.2 x (ZFSet.mem_insert_of_mem _ hx)
      refine ⟨y, (pair_mem_terminalChronologyGraph _ _ _ _ _).2 (Or.inr ⟨entry,hx⟩), ?_⟩
      intro y' entry'
      rcases (pair_mem_terminalChronologyGraph _ _ _ _ _).1 entry' with new | old
      · exact False.elim (ZFSet.mem_irrefl s (new.1 ▸ hx))
      · exact unique y' old.1

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {s : ZFSet.{u}}
variable (fields : GroundChronologyFields M (insert s s))
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
variable (newValues : Fin 5 → ZFSet.{u}) (ground : ∀ j, newValues j ∈ M.sets)

noncomputable def replaceTerminal : GroundChronologyFields M (insert s s) :=
  GroundChronologyFields.ofGraphs pairing unions fields.time_ground
    (fun j => terminalChronologyGraph s (fields.graph j) (newValues j))
    (fun j => M.insert_mem pairing unions
      (M.orderedPair_mem pairing (M.transitive fields.time_ground (ZFSet.mem_insert _ _)) (ground j))
      (M.graphRestriction_mem unions separation
        (M.transitive fields.time_ground (ZFSet.mem_insert _ _)) (fields.graph_ground j)))
    (fun j => terminalChronologyGraph_function ⟨fields.bound, fields.function j⟩)

theorem replaceTerminal_graph (j : Fin 5) :
    (fields.replaceTerminal pairing unions separation newValues ground).graph j =
      terminalChronologyGraph s (fields.graph j) (newValues j) := rfl

theorem replaceTerminal_value_at (j : Fin 5) :
    (fields.replaceTerminal pairing unions separation newValues ground).value j s = newValues j := by
  apply GroundChronologyFields.value_eq_of_entry
  exact (pair_mem_terminalChronologyGraph _ _ _ _ _).2 (Or.inl ⟨rfl,rfl⟩)

theorem replaceTerminal_value_old (j : Fin 5) {t : ZFSet.{u}} (ht : t ∈ s) :
    (fields.replaceTerminal pairing unions separation newValues ground).value j t = fields.value j t := by
  apply GroundChronologyFields.value_eq_of_entry
  exact (pair_mem_terminalChronologyGraph _ _ _ _ _).2
    (Or.inr ⟨fields.value_entry j (ZFSet.mem_insert_of_mem _ ht),ht⟩)

theorem replaceTerminal_value (j : Fin 5) {t : ZFSet.{u}} (ht : t ∈ insert s s) :
    (fields.replaceTerminal pairing unions separation newValues ground).value j t =
      appendHistoryValue s (fields.value j) (newValues j) t := by
  rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
  · rw [appendHistoryValue_at]
    exact fields.replaceTerminal_value_at pairing unions separation newValues ground j
  · rw [appendHistoryValue_old ht]
    exact fields.replaceTerminal_value_old pairing unions separation newValues ground j ht

theorem replaceTerminal_old_entries (j : Fin 5) {t y : ZFSet.{u}} (ht : t ∈ s) :
    ZFSet.pair t y ∈ (fields.replaceTerminal pairing unions separation newValues ground).graph j ↔
      ZFSet.pair t y ∈ fields.graph j := by
  rw [replaceTerminal_graph, pair_mem_terminalChronologyGraph]
  exact ⟨fun h => h.elim (fun eq => False.elim (ZFSet.mem_irrefl s (eq.1 ▸ ht))) And.left,
    fun entry => Or.inr ⟨entry,ht⟩⟩

end GroundChronologyFields

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (newValues : Fin 5 → ZFSet.{u}) (ground : ∀ j, newValues j ∈ M.sets)

noncomputable def appendTime : GroundChronologyFields M (insert T T) :=
  GroundChronologyFields.ofGraphs pairing unions (M.insert_mem pairing unions fields.time_ground fields.time_ground)
    (fun j => insert (ZFSet.pair T (newValues j)) (fields.graph j))
    (fun j => M.insert_mem pairing unions (M.orderedPair_mem pairing fields.time_ground (ground j))
      (fields.graph_ground j))
    (fun j => (fields.graphFunction j).insert (ZFSet.mem_irrefl T) (newValues j))

theorem appendTime_graph (j : Fin 5) :
    (fields.appendTime pairing unions newValues ground).graph j =
      insert (ZFSet.pair T (newValues j)) (fields.graph j) := rfl

theorem appendTime_value_at (j : Fin 5) :
    (fields.appendTime pairing unions newValues ground).value j T = newValues j := by
  apply GroundChronologyFields.value_eq_of_entry
  exact ZFSet.mem_insert _ _

theorem appendTime_old_entries (j : Fin 5) {s y : ZFSet.{u}} (hs : s ∈ T) :
    ZFSet.pair s y ∈ (fields.appendTime pairing unions newValues ground).graph j ↔
      ZFSet.pair s y ∈ fields.graph j := by
  rw [appendTime_graph, ZFSet.mem_insert_iff, ZFSet.pair_inj]
  constructor
  · rintro (⟨rfl, _⟩ | entry)
    · exact False.elim (ZFSet.mem_irrefl _ hs)
    · exact entry
  · exact Or.inr

theorem appendTime_value_old (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ T) :
    (fields.appendTime pairing unions newValues ground).value j s = fields.value j s := by
  apply GroundChronologyFields.value_eq_of_entry
  exact (fields.appendTime_old_entries pairing unions newValues ground j hs).2 (fields.value_entry j hs)

theorem appendTime_graph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (time : ZFSet.rank T < o) (graphs : ∀ j, ZFSet.rank (fields.graph j) < o)
    (values : ∀ j, ZFSet.rank (newValues j) < o) (j : Fin 5) :
    ZFSet.rank ((fields.appendTime pairing unions newValues ground).graph j) < o := by
  rw [appendTime_graph, ZFSet.rank_insert]
  exact max_lt (limit.succ_lt (rank_orderedPair_lt limit time (values j))) (graphs j)

end PartitionPilot.Forcing.GroundChronologyFields

end OAI
