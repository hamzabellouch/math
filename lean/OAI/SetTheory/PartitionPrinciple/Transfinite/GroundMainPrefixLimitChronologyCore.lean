import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitBottom
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixPriorFields

namespace OAI


namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem related_birth_iff {i j : I} {x y : ZFSet.{u}}
    (related : run.pointSystem.Related i x j y) (t : ZFSet.{u}) :
    ZFSet.pair x t ∈ (run.diagram.stage i).birth ↔
      ZFSet.pair y t ∈ (run.diagram.stage j).birth := by
  obtain ⟨k, first, second, z, xz, yz⟩ := related
  exact ((run.diagram.transition first).birth x z t xz).symm.trans
    ((run.diagram.transition second).birth y z t yz)

theorem limitPoint_birth_iff {i j : I} {x y : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage j).stage.carrier)
    (equal : run.pointPresentation.limitPoint i x = run.pointPresentation.limitPoint j y)
    (t : ZFSet.{u}) :
    ZFSet.pair x t ∈ (run.diagram.stage i).birth ↔
      ZFSet.pair y t ∈ (run.diagram.stage j).birth :=
  run.related_birth_iff ((run.pointPresentation.limitPoint_eq_iff_related hx hy).1 equal) t

theorem related_height_iff {i j : I} {x y : ZFSet.{u}}
    (related : run.pointSystem.Related i x j y) (t : ZFSet.{u}) :
    ZFSet.pair x t ∈ (run.diagram.stage i).stage.height ↔
      ZFSet.pair y t ∈ (run.diagram.stage j).stage.height := by
  obtain ⟨k, first, second, z, xz, yz⟩ := related
  exact ((run.diagram.transition first).map.height x z t xz).symm.trans
    ((run.diagram.transition second).map.height y z t yz)

theorem limitPoint_height_iff {i j : I} {x y : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier)
    (hy : y ∈ (run.diagram.stage j).stage.carrier)
    (equal : run.pointPresentation.limitPoint i x = run.pointPresentation.limitPoint j y)
    (t : ZFSet.{u}) :
    ZFSet.pair x t ∈ (run.diagram.stage i).stage.height ↔
      ZFSet.pair y t ∈ (run.diagram.stage j).stage.height :=
  run.related_height_iff ((run.pointPresentation.limitPoint_eq_iff_related hx hy).1 equal) t





noncomputable def limitValueGraph (F V : ZFSet.{u}) : ZFSet.{u} :=
  indexedValueLift run.indices run.carrierUnion run.limitPoints V F run.limitPointInclusions

theorem limitValueGraph_ground {F V : ZFSet.{u}} (hF : F ∈ M.sets) (hV : V ∈ M.sets) :
    run.limitValueGraph F V ∈ M.sets :=
  M.indexedValueLift_mem pairing unions powers separation run.indices_ground run.carrierUnion_ground
    run.limitPoints_ground hV hF run.limitPointInclusions_ground

theorem limitValueGraph_entry (value : I → ZFSet.{u}) {F V : ZFSet.{u}}
    (lookup : ∀ i f, ZFSet.pair (run.key i) f ∈ F ↔ f = value i)
    (bound : ∀ i x t, ZFSet.pair x t ∈ value i → t ∈ V) (q t : ZFSet.{u}) :
    ZFSet.pair q t ∈ run.limitValueGraph F V ↔
      ∃ i x, x ∈ (run.diagram.stage i).stage.carrier ∧
        q = run.pointPresentation.limitPoint i x ∧ ZFSet.pair x t ∈ value i := by
  rw [limitValueGraph, pair_mem_indexedValueLift]
  constructor
  · rintro ⟨_, _, k, hk, f, e, x, _, family, inclusion, image, entry⟩
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hk
    obtain rfl := (lookup i f).1 family
    obtain rfl := (run.limitPointInclusions_entry i e).1 inclusion
    obtain ⟨hx, equal⟩ := (run.pointPresentation.inclusion_entry i x q).1 image
    exact ⟨i, x, hx, equal, entry⟩
  · rintro ⟨i, x, hx, rfl, entry⟩
    exact ⟨run.pointPresentation.limitPoint_mem hx, bound i x t entry,
      run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩, value i, run.limitPointMap i,
      x, run.pointPresentation.carrier_bound i hx, (lookup i _).2 rfl,
      (run.limitPointInclusions_entry i _).2 rfl,
      (run.pointPresentation.inclusion_entry i x _).2 ⟨hx, rfl⟩, entry⟩

theorem limitValueGraph_at (value : I → ZFSet.{u}) {F V : ZFSet.{u}}
    (lookup : ∀ i f, ZFSet.pair (run.key i) f ∈ F ↔ f = value i)
    (bound : ∀ i x t, ZFSet.pair x t ∈ value i → t ∈ V)
    (compatible : ∀ i j x y, x ∈ (run.diagram.stage i).stage.carrier →
      y ∈ (run.diagram.stage j).stage.carrier →
      run.pointPresentation.limitPoint i x = run.pointPresentation.limitPoint j y →
      ∀ t, ZFSet.pair x t ∈ value i ↔ ZFSet.pair y t ∈ value j)
    (i : I) {x : ZFSet.{u}} (hx : x ∈ (run.diagram.stage i).stage.carrier) (t : ZFSet.{u}) :
    ZFSet.pair (run.pointPresentation.limitPoint i x) t ∈ run.limitValueGraph F V ↔
      ZFSet.pair x t ∈ value i := by
  rw [run.limitValueGraph_entry value lookup bound]
  constructor
  · rintro ⟨j, y, hy, equal, entry⟩
    exact (compatible i j x y hx hy equal t).2 entry
  · intro entry
    exact ⟨i, x, hx, rfl, entry⟩

theorem limitValueGraph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) (F : ZFSet.{u}) {V : ZFSet.{u}}
    (values : ZFSet.rank V < o) : ZFSet.rank (run.limitValueGraph F V) < o :=
  indexedValueLift_rank_lt limit run.indices run.carrierUnion F run.limitPointInclusions
    (run.limitPoints_rank_lt limit rank) values





theorem limitPoint_old_birth_coverage (i j : I) {x t : ZFSet.{u}}
    (entry : ZFSet.pair x t ∈ (run.diagram.stage j).birth)
    (before : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff) :
    ∃ y ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair y t ∈ (run.diagram.stage i).birth ∧
      run.pointPresentation.limitPoint i y = run.pointPresentation.limitPoint j x := by
  have hx := (ZFSet.pair_mem_prod.1 ((run.diagram.stage j).birth_function.1 entry)).1
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨z, xz⟩ := run.pointSystem.map_entry_total jk hx
  have terminal := ((run.diagram.transition jk).birth x z t xz).2 entry
  obtain ⟨y, hy, yz⟩ := run.coverage ik z t terminal before
  exact ⟨y, hy, ((run.diagram.transition ik).birth y z t yz).1 terminal,
    (run.pointPresentation.limitPoint_transition ik yz).trans
      (run.pointPresentation.limitPoint_transition jk xz).symm⟩

def LimitBirthValue (q t : ZFSet.{u}) : Prop :=
  ∃ i x, x ∈ (run.diagram.stage i).stage.carrier ∧
    q = run.pointPresentation.limitPoint i x ∧ ZFSet.pair x t ∈ (run.diagram.stage i).birth

theorem limitBirthValue_at (i : I) {x : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier) (t : ZFSet.{u}) :
    run.LimitBirthValue (run.pointPresentation.limitPoint i x) t ↔
      ZFSet.pair x t ∈ (run.diagram.stage i).birth := by
  constructor
  · rintro ⟨j, y, hy, equal, entry⟩
    exact (run.limitPoint_birth_iff hx hy equal t).2 entry
  · intro entry
    exact ⟨i, x, hx, rfl, entry⟩

theorem limitBirthValue_total {q : ZFSet.{u}} (member : q ∈ run.limitPoints) :
    ∃ t, run.LimitBirthValue q t := by
  obtain ⟨i, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage member
  obtain ⟨t, entry, _⟩ := (run.diagram.stage i).birth_function.2 x hx
  exact ⟨t, i, x, hx, rfl, entry⟩

theorem limitBirthValue_unique {q t s : ZFSet.{u}}
    (first : run.LimitBirthValue q t) (second : run.LimitBirthValue q s) : t = s := by
  obtain ⟨i, x, hx, rfl, xt⟩ := first
  have xs := (run.limitBirthValue_at i hx s).1 second
  exact (show FunctionGraphOn (run.diagram.stage i).stage.carrier (run.diagram.stage i).birth from
    ⟨_, (run.diagram.stage i).birth_function⟩).unique xt xs

theorem limitBirthValue_old_fiber (i : I) (q t : ZFSet.{u})
    (before : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff) :
    run.LimitBirthValue q t ↔ ∃ x ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair x t ∈ (run.diagram.stage i).birth ∧ q = run.pointPresentation.limitPoint i x := by
  constructor
  · rintro ⟨j, y, _, rfl, entry⟩
    obtain ⟨x, hx, birth, equal⟩ := run.limitPoint_old_birth_coverage i j entry before
    exact ⟨x, hx, birth, equal.symm⟩
  · rintro ⟨x, hx, birth, rfl⟩
    exact ⟨i, x, hx, rfl, birth⟩





noncomputable def heightValueBound : ZFSet.{u} := ZFSet.sUnion (ZFSet.sUnion (run.stageFieldUnion 10))

theorem heightValueBound_ground : run.heightValueBound ∈ M.sets :=
  M.union_mem unions (M.union_mem unions (run.stageFieldUnion_ground 10))

theorem height_value_mem_bound (i : I) {x t : ZFSet.{u}}
    (entry : ZFSet.pair x t ∈ (run.diagram.stage i).stage.height) : t ∈ run.heightValueBound :=
  pair_second_mem_doubleUnion ((run.stageFieldUnion_mem 10 _).2 ⟨i, entry⟩)

theorem heightValueBound_rank_le_code : ZFSet.rank run.heightValueBound ≤ ZFSet.rank run.code :=
  (ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans (run.stageFieldUnion_rank_le_code 10))

noncomputable def limitHeight : ZFSet.{u} :=
  run.limitValueGraph (run.stageFieldFamily 10) run.heightValueBound

theorem limitHeight_ground : run.limitHeight ∈ M.sets :=
  run.limitValueGraph_ground (run.stageFieldFamily_ground 10) run.heightValueBound_ground

theorem limitHeight_entry (q t : ZFSet.{u}) :
    ZFSet.pair q t ∈ run.limitHeight ↔
      ∃ i x, x ∈ (run.diagram.stage i).stage.carrier ∧
        q = run.pointPresentation.limitPoint i x ∧ ZFSet.pair x t ∈ (run.diagram.stage i).stage.height :=
  run.limitValueGraph_entry (fun i => (run.diagram.stage i).stage.height)
    (run.stageFieldFamily_entry 10) (fun i _ _ => run.height_value_mem_bound i) q t

theorem limitHeight_at (i : I) {x : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier) (t : ZFSet.{u}) :
    ZFSet.pair (run.pointPresentation.limitPoint i x) t ∈ run.limitHeight ↔
      ZFSet.pair x t ∈ (run.diagram.stage i).stage.height :=
  run.limitValueGraph_at (fun j => (run.diagram.stage j).stage.height)
    (run.stageFieldFamily_entry 10) (fun j _ _ => run.height_value_mem_bound j)
    (fun _ _ _ _ hx hy equal t => run.limitPoint_height_iff hx hy equal t) i hx t

theorem limitHeight_function : ZFSet.IsFunc run.limitPoints (ZFSet.prod C D) run.limitHeight := by
  refine ⟨?_, ?_⟩
  · intro z hz
    have subset := indexedValueLift_subset run.indices run.carrierUnion run.limitPoints
      run.heightValueBound (run.stageFieldFamily 10) run.limitPointInclusions
    obtain ⟨q, _, t, _, rfl⟩ := ZFSet.mem_prod.1 (subset hz)
    obtain ⟨i, x, hx, rfl, entry⟩ := (run.limitHeight_entry q t).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨run.pointPresentation.limitPoint_mem hx,
      (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.height_code.function.1 entry)).2⟩
  · intro q hq
    obtain ⟨i, x, hx, rfl⟩ := run.pointPresentation.limitPoint_coverage hq
    obtain ⟨t, entry, unique⟩ := (run.diagram.stage i).stage.height_code.function.2 x hx
    refine ⟨t, (run.limitHeight_at i hx t).2 entry, ?_⟩
    intro s hs
    exact unique s ((run.limitHeight_at i hx s).1 hs)

theorem limitPointMap_height (i : I) {x q : ZFSet.{u}}
    (image : ZFSet.pair x q ∈ run.limitPointMap i) (t : ZFSet.{u}) :
    ZFSet.pair q t ∈ run.limitHeight ↔ ZFSet.pair x t ∈ (run.diagram.stage i).stage.height := by
  obtain ⟨hx, rfl⟩ := (run.pointPresentation.inclusion_entry i x q).1 image
  exact run.limitHeight_at i hx t

theorem limitHeight_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitHeight < o :=
  run.limitValueGraph_rank_lt limit rank _ (run.heightValueBound_rank_le_code.trans_lt rank)





noncomputable def limitBirth : ZFSet.{u} :=
  run.limitValueGraph run.birthFamily run.cutoffLimit

theorem limitBirth_ground : run.limitBirth ∈ M.sets :=
  run.limitValueGraph_ground run.birthFamily_ground run.cutoffLimit_ground

theorem limitBirth_entry (q t : ZFSet.{u}) :
    ZFSet.pair q t ∈ run.limitBirth ↔ run.LimitBirthValue q t :=
  run.limitValueGraph_entry (fun i => (run.diagram.stage i).birth) run.birthFamily_entry
    (fun i _ _ entry => run.birth_time_mem_cutoffLimit i entry) q t

theorem limitBirth_function : ZFSet.IsFunc run.limitPoints run.cutoffLimit run.limitBirth := by
  refine ⟨indexedValueLift_subset run.indices run.carrierUnion run.limitPoints
    run.cutoffLimit run.birthFamily run.limitPointInclusions, ?_⟩
  intro q hq
  obtain ⟨t, birth⟩ := run.limitBirthValue_total hq
  refine ⟨t, (run.limitBirth_entry q t).2 birth, ?_⟩
  intro s entry
  exact run.limitBirthValue_unique ((run.limitBirth_entry q s).1 entry) birth

theorem limitBirth_at (i : I) {x : ZFSet.{u}}
    (hx : x ∈ (run.diagram.stage i).stage.carrier) (t : ZFSet.{u}) :
    ZFSet.pair (run.pointPresentation.limitPoint i x) t ∈ run.limitBirth ↔
      ZFSet.pair x t ∈ (run.diagram.stage i).birth :=
  (run.limitBirth_entry _ t).trans (run.limitBirthValue_at i hx t)

theorem limitPointMap_birth_iff (i : I) (x q t : ZFSet.{u})
    (entry : ZFSet.pair x q ∈ run.limitPointMap i) :
    ZFSet.pair q t ∈ run.limitBirth ↔ ZFSet.pair x t ∈ (run.diagram.stage i).birth := by
  obtain ⟨hx, rfl⟩ := (run.pointPresentation.inclusion_entry i x q).1 entry
  exact run.limitBirth_at i hx t

theorem limitBirth_old_fiber (i : I) (q t : ZFSet.{u})
    (before : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff) :
    ZFSet.pair q t ∈ run.limitBirth ↔ ∃ x ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair x t ∈ (run.diagram.stage i).birth ∧ ZFSet.pair x q ∈ run.limitPointMap i := by
  rw [run.limitBirth_entry, run.limitBirthValue_old_fiber i q t before]
  constructor
  · rintro ⟨x, hx, birth, equal⟩
    exact ⟨x, hx, birth, (run.pointPresentation.inclusion_entry i x q).2 ⟨hx, equal⟩⟩
  · rintro ⟨x, hx, birth, entry⟩
    exact ⟨x, hx, birth, ((run.pointPresentation.inclusion_entry i x q).1 entry).2⟩

theorem limitBirth_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitBirth < o :=
  run.limitValueGraph_rank_lt limit rank run.birthFamily (run.cutoffLimit_rank_le_code.trans_lt rank)





theorem limitHeight_code : StrictLexHeightCode run.limitPoints C D run.limitOrder run.limitHeight rD where
  function := run.limitHeight_function
  strict p hp q hq c a d b lower different first second := by
    obtain ⟨i, x, y, hx, hy, rfl, rfl⟩ := run.pointPresentation.pair_coverage hp hq
    have sourceOrder := (run.limitLE_at i hx hy).1 ((run.limitOrder_entry _ _).1 lower)
    have sourceDifferent : x ≠ y := fun equal => different (congrArg (run.pointPresentation.limitPoint i) equal)
    exact (run.diagram.stage i).stage.height_code.strict x hx y hy c a d b sourceOrder sourceDifferent
      ((run.limitHeight_at i hx _).1 first) ((run.limitHeight_at i hy _).1 second)

noncomputable def limitHeightRange : ZFSet.{u} := functionGraphRange run.limitPoints run.limitHeight

theorem limitHeightRange_ground : run.limitHeightRange ∈ M.sets :=
  M.functionGraphRange_mem unions separation run.limitPoints_ground run.limitHeight_ground

theorem limitHeightRange_mem (t : ZFSet.{u}) :
    t ∈ run.limitHeightRange ↔
      ∃ i x, x ∈ (run.diagram.stage i).stage.carrier ∧ ZFSet.pair x t ∈ (run.diagram.stage i).stage.height := by
  rw [limitHeightRange, mem_functionGraphRange]
  constructor
  · rintro ⟨q, _, entry⟩
    obtain ⟨i, x, hx, _, value⟩ := (run.limitHeight_entry q t).1 entry
    exact ⟨i, x, hx, value⟩
  · rintro ⟨i, x, hx, entry⟩
    exact ⟨run.pointPresentation.limitPoint i x, run.pointPresentation.limitPoint_mem hx,
      (run.limitHeight_at i hx t).2 entry⟩

theorem limitHeightRange_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitHeightRange < o :=
  (functionGraphRange_rank_le _ _).trans_lt (run.limitHeight_rank_lt limit rank)





theorem limit_old_meet : OldMeetCode run.limitOrder run.limitMeetGraph run.limitBirth := by
  intro p q v a b c bornQ bornP earlier notLower meet bornV
  have bounds := run.limitMeet_bounds ((run.limitMeetGraph_entry p q v).1 meet)
  obtain ⟨i, x, y, z, hx, hy, hz, rfl, rfl, rfl⟩ :=
    run.pointPresentation.triple_coverage bounds.1 bounds.2.1 bounds.2.2
  apply (run.diagram.stage i).old_meet x y z a b c
    ((run.limitBirth_at i hy a).1 bornQ) ((run.limitBirth_at i hx b).1 bornP) earlier
  · intro lower
    exact notLower ((run.limitOrder_entry _ _).2 ((run.limitLE_at i hx hy).2 lower))
  · exact (run.limitMeet_at i hx hy hz).1 ((run.limitMeetGraph_entry _ _ _).1 meet)
  · exact (run.limitBirth_at i hz c).1 bornV





noncomputable def limitTerminalFields : Fin 5 → ZFSet.{u} :=
  Fin.cases run.limitPoints (Fin.cases run.limitOrder (Fin.cases run.limitMeetGraph
    (Fin.cases run.limitBirth (Fin.cases run.limitHeight Fin.elim0))))

theorem limitTerminalFields_ground : ∀ j, run.limitTerminalFields j ∈ M.sets :=
  Fin.cases run.limitPoints_ground (Fin.cases run.limitOrder_ground (Fin.cases run.limitMeetGraph_ground
    (Fin.cases run.limitBirth_ground (Fin.cases run.limitHeight_ground (fun i => Fin.elim0 i)))))

theorem limitTerminalPoint : ChronologyPointCode (insert run.cutoffLimit run.cutoffLimit) C D rD
    run.cutoffLimit run.limitPoints run.limitOrder run.limitMeetGraph run.limitBirth run.limitHeight where
  meet := run.limitMeet_code
  birth_function := by
    refine ⟨?_, run.limitBirth_function.2⟩
    intro z hz
    obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 (run.limitBirth_function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_insert_of_mem _ ht⟩
  birth_bound _ _ _ entry := Or.inr (ZFSet.pair_mem_prod.1 (run.limitBirth_function.1 entry)).2
  old_meet := run.limit_old_meet
  strict_height := run.limitHeight_code

theorem limitTerminalFields_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ∀ j, ZFSet.rank (run.limitTerminalFields j) < o :=
  Fin.cases (run.limitPoints_rank_lt limit rank) (Fin.cases (run.limitOrder_rank_lt limit rank)
    (Fin.cases (run.limitMeetGraph_rank_lt limit rank) (Fin.cases (run.limitBirth_rank_lt limit rank)
      (Fin.cases (run.limitHeight_rank_lt limit rank) (fun i => Fin.elim0 i)))))





noncomputable def limitChronologyFields :
    GroundChronologyFields M (insert run.cutoffLimit run.cutoffLimit) :=
  run.limitPriorFields.appendTime pairing unions run.limitTerminalFields run.limitTerminalFields_ground

theorem limitChronologyFields_graph (j : Fin 5) :
    run.limitChronologyFields.graph j =
      insert (ZFSet.pair run.cutoffLimit (run.limitTerminalFields j)) (run.serialFieldUnion j) := rfl

theorem limitChronologyFields_terminal (j : Fin 5) :
    run.limitChronologyFields.value j run.cutoffLimit = run.limitTerminalFields j :=
  run.limitPriorFields.appendTime_value_at pairing unions run.limitTerminalFields run.limitTerminalFields_ground j

theorem limitChronologyFields_values (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (before : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) :
    run.limitChronologyFields.value j s = (run.diagram.stage i).history.fieldValue j s :=
  (run.limitPriorFields.appendTime_value_old pairing unions run.limitTerminalFields run.limitTerminalFields_ground
    j ((run.cutoffLimit_mem s).2 ⟨i, before⟩)).trans (run.limitPriorFields_values i j before)

theorem limitChronologyFields_source_entries (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (before : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) (y : ZFSet.{u}) :
    ZFSet.pair s y ∈ run.limitChronologyFields.graph j ↔
      ZFSet.pair s y ∈ (run.linked i).serial.fields.graph j := by
  have old := run.limitPriorFields.appendTime_old_entries pairing unions run.limitTerminalFields
    run.limitTerminalFields_ground j ((run.cutoffLimit_mem s).2 ⟨i, before⟩) (y := y)
  exact (old.trans (run.serialFieldUnion_at i j before y)).trans
    ((run.serialFieldGraph_entry i j s y).trans (and_iff_right before)).symm

theorem limitChronologyFields_graph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) (j : Fin 5) :
    ZFSet.rank (run.limitChronologyFields.graph j) < o :=
  run.limitPriorFields.appendTime_graph_rank_lt pairing unions run.limitTerminalFields
    run.limitTerminalFields_ground limit (run.cutoffLimit_rank_le_code.trans_lt rank)
    (fun j => (run.serialFieldUnion_rank_le_code j).trans_lt rank)
    (run.limitTerminalFields_rank_lt limit rank) j





theorem limitChronologyPoint {s : ZFSet.{u}} (hs : s ∈ insert run.cutoffLimit run.cutoffLimit) :
    ChronologyPointCode (insert run.cutoffLimit run.cutoffLimit) C D rD s
      (run.limitChronologyFields.value 0 s) (run.limitChronologyFields.value 1 s)
      (run.limitChronologyFields.value 2 s) (run.limitChronologyFields.value 3 s)
      (run.limitChronologyFields.value 4 s) := by
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · simp only [run.limitChronologyFields_terminal]
    exact run.limitTerminalPoint
  · obtain ⟨i, before⟩ := (run.cutoffLimit_mem s).1 hs
    rw [run.limitChronologyFields_values i 0 before, run.limitChronologyFields_values i 1 before,
      run.limitChronologyFields_values i 2 before, run.limitChronologyFields_values i 3 before,
      run.limitChronologyFields_values i 4 before]
    change ChronologyPointCode (insert run.cutoffLimit run.cutoffLimit) C D rD s
      ((run.diagram.stage i).history.space s) ((run.diagram.stage i).history.order s)
      ((run.diagram.stage i).history.meetGraph s) ((run.diagram.stage i).history.birth s)
      ((run.diagram.stage i).history.height s)
    have sourceTime : s ∈ insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff :=
      ZFSet.mem_insert_iff.2 before
    refine ⟨(run.diagram.stage i).history.meet_order s sourceTime, ?_,
      (run.diagram.stage i).history.birth_bound s sourceTime,
      (run.diagram.stage i).history.old_meet s sourceTime,
      (run.diagram.stage i).history.strict_height s sourceTime⟩
    refine ⟨?_, ((run.diagram.stage i).history.birth_function s sourceTime).2⟩
    intro z hz
    obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1
      (((run.diagram.stage i).history.birth_function s sourceTime).1 hz)
    have member : t ∈ run.cutoffLimit := by
      rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
      · exact run.cutoff_mem_cutoffLimit i
      · exact run.cutoffLimit_ordinal.1 _ (run.cutoff_mem_cutoffLimit i) _ ht
    exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_insert_of_mem _ member⟩

theorem limitChronologyCore : ChronologyCoreCode (insert run.cutoffLimit run.cutoffLimit)
    run.limitChronologyFields.bound C D rD run.limitChronologyFields.graph where
  function := run.limitChronologyFields.function
  point s hs L r μ birth height eL er eμ eb eh := by
    have current := run.limitChronologyPoint hs
    rw [run.limitChronologyFields.value_eq_of_entry 0 eL,
      run.limitChronologyFields.value_eq_of_entry 1 er,
      run.limitChronologyFields.value_eq_of_entry 2 eμ,
      run.limitChronologyFields.value_eq_of_entry 3 eb,
      run.limitChronologyFields.value_eq_of_entry 4 eh] at current
    exact current

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
