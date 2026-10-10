import OAI.SetTheory.PartitionPrinciple.Geometry.GroundLinkedProfileTransitionRecognition

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u v

structure MainPrefixGraphFamily (M : TransitiveGround.{u})
    (K Labels C D rD : ZFSet.{u}) (I : Type v) where
  indices : I → ZFSet.{u}
  stages : I → ZFSet.{u}
  transitions : I → ZFSet.{u}
  valid : ∀ i, MainPrefixGraphCode M K Labels C D rD (indices i) (stages i) (transitions i)
  mono : ∀ i j, indices i ⊆ indices j → stages i ⊆ stages j ∧ transitions i ⊆ transitions j

namespace MainPrefixGraphFamily
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {I : Type v} [Small.{u} I]
variable (family : MainPrefixGraphFamily M K Labels C D rD I)

noncomputable def indexUnion : ZFSet.{u} := ⋃₀ ZFSet.range family.indices
noncomputable def stageUnion : ZFSet.{u} := ⋃₀ ZFSet.range family.stages
noncomputable def transitionUnion : ZFSet.{u} := ⋃₀ ZFSet.range family.transitions

noncomputable def code (i : I) : ZFSet.{u} :=
  mainPrefixCode (family.indices i) (family.stages i) (family.transitions i)

noncomputable def unionCode : ZFSet.{u} :=
  mainPrefixCode family.indexUnion family.stageUnion family.transitionUnion

theorem indexUnion_mem (x : ZFSet.{u}) : x ∈ family.indexUnion ↔ ∃ i, x ∈ family.indices i :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem stageUnion_mem (x : ZFSet.{u}) : x ∈ family.stageUnion ↔ ∃ i, x ∈ family.stages i :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem transitionUnion_mem (x : ZFSet.{u}) :
    x ∈ family.transitionUnion ↔ ∃ i, x ∈ family.transitions i :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem indexUnion_ordinal : ordinalSetProperty family.indexUnion := by
  apply ordinalSetProperty_sUnion
  intro T hT
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hT
  exact (family.valid i).ordinal

omit [Small.{u} I] in
theorem common_upper (i j : I) :
    ∃ k, family.indices i ⊆ family.indices k ∧ family.indices j ⊆ family.indices k := by
  have first := ordinalSetProperty_eq_code_rank (family.indices i) (family.valid i).ordinal
  have second := ordinalSetProperty_eq_code_rank (family.indices j) (family.valid j).ordinal
  rcases le_total (ZFSet.rank (family.indices i)) (ZFSet.rank (family.indices j)) with ij | ji
  · refine ⟨j, ?_, fun _ h => h⟩
    have subset := (SetRealization.ordinalCode_subset_iff _ _).2 ij
    simpa only [← first, ← second] using subset
  · refine ⟨i, fun _ h => h, ?_⟩
    have subset := (SetRealization.ordinalCode_subset_iff _ _).2 ji
    simpa only [← first, ← second] using subset

theorem chronologyPairs_indexUnion_mem (x : ZFSet.{u}) :
    x ∈ chronologyPairs family.indexUnion ↔ ∃ i, x ∈ chronologyPairs (family.indices i) := by
  constructor
  · intro hx
    obtain ⟨target, ht, source, _, rfl, before⟩ := (mem_chronologyPairs _ _).1 hx
    obtain ⟨i, hi⟩ := (family.indexUnion_mem target).1 ht
    have sourceMem : source ∈ family.indices i := by
      rcases before with rfl | before
      · exact hi
      · exact (family.valid i).ordinal.1 target hi source before
    exact ⟨i, (pair_mem_chronologyPairs _ _ _).2 ⟨hi, sourceMem, before⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨target, ht, source, hs, rfl, before⟩ := (mem_chronologyPairs _ _).1 hi
    exact (pair_mem_chronologyPairs _ _ _).2
      ⟨(family.indexUnion_mem target).2 ⟨i, ht⟩, (family.indexUnion_mem source).2 ⟨i, hs⟩, before⟩

theorem stageUnion_function : FunctionGraphOn family.indexUnion family.stageUnion := by
  apply functionGraphOn_sUnion
  · intro f hf
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hf
    exact ⟨family.indices i, fun x hx => (family.indexUnion_mem x).2 ⟨i, hx⟩, (family.valid i).stages⟩
  · intro x hx
    obtain ⟨i, hi⟩ := (family.indexUnion_mem x).1 hx
    obtain ⟨y, entry⟩ := (family.valid i).stages.total hi
    exact ⟨family.stages i, ZFSet.mem_range.2 ⟨i, rfl⟩, y, entry⟩
  · intro f hf g hg x y z first second
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hf
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 hg
    obtain ⟨k, ik, jk⟩ := family.common_upper i j
    exact (family.valid k).stages.unique ((family.mono i k ik).1 first) ((family.mono j k jk).1 second)

theorem transitionUnion_function :
    FunctionGraphOn (chronologyPairs family.indexUnion) family.transitionUnion := by
  apply functionGraphOn_sUnion
  · intro f hf
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hf
    exact ⟨chronologyPairs (family.indices i),
      fun x hx => (family.chronologyPairs_indexUnion_mem x).2 ⟨i, hx⟩, (family.valid i).transitions⟩
  · intro x hx
    obtain ⟨i, hi⟩ := (family.chronologyPairs_indexUnion_mem x).1 hx
    obtain ⟨y, entry⟩ := (family.valid i).transitions.total hi
    exact ⟨family.transitions i, ZFSet.mem_range.2 ⟨i, rfl⟩, y, entry⟩
  · intro f hf g hg x y z first second
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hf
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 hg
    obtain ⟨k, ik, jk⟩ := family.common_upper i j
    exact (family.valid k).transitions.unique
      ((family.mono i k ik).2 first) ((family.mono j k jk).2 second)

theorem stageUnion_restrict (i : I) :
    graphRestriction (family.indices i) family.stageUnion = family.stages i := by
  apply (family.stageUnion_function.restrict
    (fun x hx => (family.indexUnion_mem x).2 ⟨i, hx⟩)).eq_of_agree (family.valid i).stages
  intro x y z first second
  exact family.stageUnion_function.unique (pair_mem_graphRestriction.1 first).1
    ((family.stageUnion_mem _).2 ⟨i, second⟩)

theorem transitionUnion_restrict (i : I) :
    graphRestriction (chronologyPairs (family.indices i)) family.transitionUnion = family.transitions i := by
  apply (family.transitionUnion_function.restrict
    (fun x hx => (family.chronologyPairs_indexUnion_mem x).2 ⟨i, hx⟩)).eq_of_agree (family.valid i).transitions
  intro x y z first second
  exact family.transitionUnion_function.unique (pair_mem_graphRestriction.1 first).1
    ((family.transitionUnion_mem _).2 ⟨i, second⟩)

theorem union_valid :
    MainPrefixGraphCode M K Labels C D rD family.indexUnion family.stageUnion family.transitionUnion := by
  refine ⟨family.indexUnion_ordinal, family.stageUnion_function, family.transitionUnion_function,
    ?_, ?_, ?_, ?_⟩
  · intro i a entry
    obtain ⟨k, hk⟩ := (family.stageUnion_mem _).1 entry
    exact (family.valid k).stage_valid i a hk
  · intro i j a b z first second step
    obtain ⟨k, hk⟩ := (family.transitionUnion_mem _).1 step
    have indices := (pair_mem_chronologyPairs _ _ _).1 ((family.valid k).transitions.pair_source hk)
    have firstOld : ZFSet.pair i a ∈ family.stages k := by
      rw [← family.stageUnion_restrict k]
      exact pair_mem_graphRestriction.2 ⟨first, indices.2.1⟩
    have secondOld : ZFSet.pair j b ∈ family.stages k := by
      rw [← family.stageUnion_restrict k]
      exact pair_mem_graphRestriction.2 ⟨second, indices.1⟩
    exact (family.valid k).transition_valid i j a b z firstOld secondOld hk
  · intro i p a entry
    obtain ⟨k, hk⟩ := (family.transitionUnion_mem _).1 entry
    exact (family.valid k).identity i p a hk
  · intro i j k p₁ a₁ p₂ a₂ p₃ a₃ first second third
    obtain ⟨b, hb⟩ := (family.transitionUnion_mem _).1 first
    obtain ⟨c, hc⟩ := (family.transitionUnion_mem _).1 second
    obtain ⟨d, hd⟩ := (family.transitionUnion_mem _).1 third
    obtain ⟨e, be, ce⟩ := family.common_upper b c
    obtain ⟨f, ef, df⟩ := family.common_upper e d
    exact (family.valid f).composition i j k p₁ a₁ p₂ a₂ p₃ a₃
      ((family.mono e f ef).2 ((family.mono b e be).2 hb))
      ((family.mono e f ef).2 ((family.mono c e ce).2 hc)) ((family.mono d f df).2 hd)

theorem unionCode_valid : MainPrefixCode M K Labels C D rD family.unionCode :=
  ⟨family.indexUnion, family.stageUnion, family.transitionUnion, rfl, family.union_valid⟩

end MainPrefixGraphFamily

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.MainPrefixGraphFamily
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {I : Type v} [Small.{u} I]
variable (family : MainPrefixGraphFamily M K Labels C D rD I)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (key : I → ZFSet.{u}) (injective : Function.Injective key)
variable (domain : ZFSet.range key ∈ M.sets)
variable (whole : familyCodeGraph key family.code ∈ M.sets)
include pairing unions powers separation injective domain whole

theorem fieldFamilies_ground :
    familyCodeGraph key family.indices ∈ M.sets ∧ familyCodeGraph key family.stages ∈ M.sets ∧
      familyCodeGraph key family.transitions ∈ M.sets := by
  have encoded : familyCodeGraph key (fun i => ZFSet.pair (family.indices i)
      (ZFSet.pair (family.stages i) (family.transitions i))) ∈ M.sets := by
    change familyCodeGraph key family.code ∈ M.sets
    exact whole
  have first := M.familyCodeGraph_pair_projections pairing unions powers separation key family.indices
    (fun i => ZFSet.pair (family.stages i) (family.transitions i)) injective domain encoded
  have second := M.familyCodeGraph_pair_projections pairing unions powers separation key family.stages
    family.transitions injective domain first.2
  exact ⟨first.1, second.1, second.2⟩

theorem fieldRanges_ground :
    ZFSet.range family.indices ∈ M.sets ∧ ZFSet.range family.stages ∈ M.sets ∧
      ZFSet.range family.transitions ∈ M.sets := by
  have fields := family.fieldFamilies_ground pairing unions powers separation key injective domain whole
  exact ⟨M.familyCodeGraph_valueRange_mem unions separation key family.indices domain fields.1,
    M.familyCodeGraph_valueRange_mem unions separation key family.stages domain fields.2.1,
    M.familyCodeGraph_valueRange_mem unions separation key family.transitions domain fields.2.2⟩

theorem fieldUnions_ground :
    family.indexUnion ∈ M.sets ∧ family.stageUnion ∈ M.sets ∧ family.transitionUnion ∈ M.sets := by
  have ranges := family.fieldRanges_ground pairing unions powers separation key injective domain whole
  exact ⟨M.union_mem unions ranges.1, M.union_mem unions ranges.2.1, M.union_mem unions ranges.2.2⟩

theorem unionCode_ground : family.unionCode ∈ M.sets := by
  have grounds := family.fieldUnions_ground pairing unions powers separation key injective domain whole
  exact M.mainPrefixCode_mem pairing grounds.1 grounds.2.1 grounds.2.2

omit pairing unions powers separation injective domain whole in
theorem code_extends_union (i : I) : MainPrefixExtends (family.code i) family.unionCode := by
  apply mainPrefixExtends_iff.2
  exact ⟨fun x hx => (family.indexUnion_mem x).2 ⟨i, hx⟩,
    fun x hx => (family.stageUnion_mem x).2 ⟨i, hx⟩,
    fun x hx => (family.transitionUnion_mem x).2 ⟨i, hx⟩⟩

end PartitionPilot.Forcing.MainPrefixGraphFamily



namespace PartitionPilot.Forcing
open SetFormula
universe u v

def MainPrefixProfileGraphCode (M : TransitiveGround.{u})
    (K Labels C D rD S E : ZFSet.{u}) : Prop :=
  ∀ i j a b z, ZFSet.pair i a ∈ S → ZFSet.pair j b ∈ S →
    ZFSet.pair (ZFSet.pair j i) z ∈ E →
    LinkedProfilePreservingTransitionCode M K Labels C D rD a b z

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem linked_profile_code (preserved : run.PreservesOldProfiles) {i j : I} (before : i ≤ j) :
    LinkedProfilePreservingTransitionCode M K Labels C D rD
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code := by
  refine ⟨run.linked i, run.linked j, rfl, rfl, ?_⟩
  rw [run.linked_main i, run.linked_main j]
  exact ⟨run.diagram.transition before, rfl, run.coverage before, preserved i j before⟩

theorem profile_graph_code (preserved : run.PreservesOldProfiles) :
    MainPrefixProfileGraphCode M K Labels C D rD run.stageGraph run.transitionGraph := by
  intro i j a b z first second entry
  obtain ⟨s, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source first)
  obtain ⟨t, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source second)
  have order := ((pair_mem_chronologyPairs _ _ _).1
    (run.transitionGraph_function.pair_source entry)).2.2
  have before := (run.key_order s t).2 order
  rw [(run.stageGraph_entry s a).1 first, (run.stageGraph_entry t b).1 second,
    (run.transitionGraph_entry before z).1 entry]
  exact run.linked_profile_code preserved before

theorem preservesOldProfiles_of_graph_code
    (code : MainPrefixProfileGraphCode M K Labels C D rD run.stageGraph run.transitionGraph) :
    run.PreservesOldProfiles := by
  intro i j before
  have entry := code (run.key i) (run.key j) (run.linked i).code (run.linked j).code
    (run.diagram.transition before).map.code
    ((run.stageGraph_entry i _).2 rfl) ((run.stageGraph_entry j _).2 rfl)
    ((run.transitionGraph_entry before _).2 rfl)
  let step := (run.diagram.transition before).retargetEq
    (run.linked_main i).symm (run.linked_main j).symm
  have stepCode : step.map.code = (run.diagram.transition before).map.code :=
    (run.diagram.transition before).retargetEq_code (run.linked_main i).symm (run.linked_main j).symm
  have actual : LinkedProfilePreservingTransitionCode M K Labels C D rD
      (run.linked i).code (run.linked j).code step.map.code := stepCode.symm ▸ entry
  exact ((run.diagram.transition before).retargetEq_preservesOldProfiles_iff
    (run.linked_main i).symm (run.linked_main j).symm).1 (actual.preserves_at step)

theorem preservesOldProfiles_iff_graph_code : run.PreservesOldProfiles ↔
    MainPrefixProfileGraphCode M K Labels C D rD run.stageGraph run.transitionGraph :=
  ⟨run.profile_graph_code, run.preservesOldProfiles_of_graph_code⟩

end GroundMainPrefix

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.MainPrefixGraphFamily
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {I : Type v} [Small.{u} I]
variable (family : MainPrefixGraphFamily M K Labels C D rD I)

theorem union_profile_graph_code
    (preserved : ∀ k, MainPrefixProfileGraphCode M K Labels C D rD (family.stages k) (family.transitions k)) :
    MainPrefixProfileGraphCode M K Labels C D rD family.stageUnion family.transitionUnion := by
  intro i j a b z first second entry
  obtain ⟨k, hk⟩ := (family.transitionUnion_mem _).1 entry
  have indices := (pair_mem_chronologyPairs _ _ _).1 ((family.valid k).transitions.pair_source hk)
  have firstOld : ZFSet.pair i a ∈ family.stages k := by
    rw [← family.stageUnion_restrict k]
    exact pair_mem_graphRestriction.2 ⟨first, indices.2.1⟩
  have secondOld : ZFSet.pair j b ∈ family.stages k := by
    rw [← family.stageUnion_restrict k]
    exact pair_mem_graphRestriction.2 ⟨second, indices.1⟩
  exact preserved k i j a b z firstOld secondOld hk

theorem exists_preservedUnionPrefix
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (key : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets) (whole : familyCodeGraph key family.code ∈ M.sets)
    (preserved : ∀ k, MainPrefixProfileGraphCode M K Labels C D rD (family.stages k) (family.transitions k)) :
    letI := ordinalMainIndexPreorder family.indexUnion_ordinal
    ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers family.indexUnion),
      run.indices = family.indexUnion ∧ run.stageGraph = family.stageUnion ∧
      run.transitionGraph = family.transitionUnion ∧ run.code = family.unionCode ∧
      run.PreservesOldProfiles := by
  let := ordinalMainIndexPreorder family.indexUnion_ordinal
  have grounds := family.fieldUnions_ground pairing unions powers separation key injective domain whole
  let run := family.union_valid.decodedPrefix pairing unions powers separation grounds.1 grounds.2.1 grounds.2.2
  have indices : run.indices = family.indexUnion :=
    family.union_valid.decodedPrefix_indices pairing unions powers separation grounds.1 grounds.2.1 grounds.2.2
  have stages : run.stageGraph = family.stageUnion :=
    family.union_valid.decodedPrefix_stageGraph pairing unions powers separation grounds.1 grounds.2.1 grounds.2.2
  have transitions : run.transitionGraph = family.transitionUnion :=
    family.union_valid.decodedPrefix_transitionGraph pairing unions powers separation grounds.1 grounds.2.1 grounds.2.2
  have code : run.code = family.unionCode :=
    family.union_valid.decodedPrefix_code pairing unions powers separation grounds.1 grounds.2.1 grounds.2.2
  refine ⟨run, indices, stages, transitions, code, ?_⟩
  apply run.preservesOldProfiles_of_graph_code
  rw [stages, transitions]
  exact family.union_profile_graph_code preserved

end PartitionPilot.Forcing.MainPrefixGraphFamily



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v

def PreservedMainPrefixCode (M : TransitiveGround.{u}) (K Labels C D rD z : ZFSet.{u}) : Prop :=
  ∃ T S E, z = mainPrefixCode T S E ∧ MainPrefixGraphCode M K Labels C D rD T S E ∧
    MainPrefixProfileGraphCode M K Labels C D rD S E

namespace PreservedMainPrefixCode
variable {M : TransitiveGround.{u}} {K Labels C D rD z : ZFSet.{u}}

theorem valid (code : PreservedMainPrefixCode M K Labels C D rD z) :
    MainPrefixCode M K Labels C D rD z := by
  obtain ⟨T, S, E, equal, raw, _⟩ := code
  exact ⟨T, S, E, equal, raw⟩

theorem exists_decodedPrefix (code : PreservedMainPrefixCode M K Labels C D rD z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (ground : z ∈ M.sets) :
    ∃ T ∈ M.sets, ∃ ordinal : ordinalSetProperty T,
      letI := ordinalMainIndexPreorder ordinal
      ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers T),
        run.indices = T ∧ run.code = z ∧ run.PreservesOldProfiles := by
  obtain ⟨T, S, E, equal, raw, preserved⟩ := code
  obtain ⟨hT, hS, hE⟩ := M.mainPrefixCode_fields_mem (equal ▸ ground)
  let := ordinalMainIndexPreorder raw.ordinal
  let run := raw.decodedPrefix pairing unions powers separation hT hS hE
  refine ⟨T, hT, raw.ordinal, run,
    raw.decodedPrefix_indices pairing unions powers separation hT hS hE,
    (raw.decodedPrefix_code pairing unions powers separation hT hS hE).trans equal.symm, ?_⟩
  apply run.preservesOldProfiles_of_graph_code
  change MainPrefixProfileGraphCode M K Labels C D rD
    (raw.decodedPrefix pairing unions powers separation hT hS hE).stageGraph
    (raw.decodedPrefix pairing unions powers separation hT hS hE).transitionGraph
  rw [raw.decodedPrefix_stageGraph, raw.decodedPrefix_transitionGraph]
  exact preserved

end PreservedMainPrefixCode

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem preserved_code (preserved : run.PreservesOldProfiles) :
    PreservedMainPrefixCode M K Labels C D rD run.code :=
  ⟨run.indices, run.stageGraph, run.transitionGraph, rfl, run.graph_code, run.profile_graph_code preserved⟩

theorem preserved_code_iff : PreservedMainPrefixCode M K Labels C D rD run.code ↔ run.PreservesOldProfiles := by
  constructor
  · rintro ⟨T, S, E, equal, _, preserved⟩
    have fields := mainPrefixCode_inj.1 equal
    apply run.preservesOldProfiles_of_graph_code
    rw [fields.2.1, fields.2.2]
    exact preserved
  · exact run.preserved_code

end GroundMainPrefix

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def mainPrefixProfileGraphFormula {n} (K Labels C D rD N S E : Fin n) : SetFormula n :=
  let old := suffixIndex n 5
  let v := prefixIndex n 5
  allBlock 5 (imp (BoundedFormula.conj
    (BoundedFormula.pairMembershipFormula (v 0) (v 2) (old S))
    (.conj (BoundedFormula.pairMembershipFormula (v 1) (v 3) (old S))
      (BoundedFormula.tripleMembershipFormula (v 1) (v 0) (v 4) (old E)))).toFormula
    (linkedProfilePreservingTransitionFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
      (v 2) (v 3) (v 4)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_mainPrefixProfileGraphFormula {n} (K Labels C D rD N S E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixProfileGraphFormula K Labels C D rD N S E) env ↔
      MainPrefixProfileGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (env S) (env E) := by
  rw [mainPrefixProfileGraphFormula, realize_allBlock]
  have actual (fields : Fin 5 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.conj
          (BoundedFormula.pairMembershipFormula (prefixIndex n 5 0) (prefixIndex n 5 2) (suffixIndex n 5 S))
          (.conj (BoundedFormula.pairMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 3) (suffixIndex n 5 S))
            (BoundedFormula.tripleMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 0) (prefixIndex n 5 4)
              (suffixIndex n 5 E)))).toFormula
          (linkedProfilePreservingTransitionFormula (suffixIndex n 5 K) (suffixIndex n 5 Labels) (suffixIndex n 5 C)
            (suffixIndex n 5 D) (suffixIndex n 5 rD) (suffixIndex n 5 N)
            (prefixIndex n 5 2) (prefixIndex n 5 3) (prefixIndex n 5 4))) (extendMany 5 fields env) ↔
        (ZFSet.pair (fields 0) (fields 2) ∈ env S ∧ ZFSet.pair (fields 1) (fields 3) ∈ env S ∧
          ZFSet.pair (ZFSet.pair (fields 1) (fields 0)) (fields 4) ∈ env E) →
        LinkedProfilePreservingTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
          (fields 2) (fields 3) (fields 4) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 5 fields env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_pairMembershipFormula,
      BoundedFormula.truth_tripleMembershipFormula]
    rw [M.realize_linkedProfilePreservingTransitionFormula pairing unions powers separation collection _ _ _ _ _ _ _ _ _ _
      (extendMany_members 5 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · intro recognized i j a b z first second third
    have h₁ := M.transitive (members S) first
    have h₂ := M.transitive (members S) second
    have h₃ := M.transitive (members E) third
    let fields : Fin 5 → ZFSet.{u} := Fin.cases i (Fin.cases j (Fin.cases a (Fin.cases b (fun _ => z))))
    have ground : ∀ k, fields k ∈ M.sets := Fin.cases (M.pair_left h₁)
      (Fin.cases (M.pair_left h₂) (Fin.cases (M.pair_right h₁)
        (Fin.cases (M.pair_right h₂) (fun _ => M.pair_right h₃))))
    exact (actual fields ground).1 (recognized fields ground) ⟨first, second, third⟩
  · intro law fields ground
    exact (actual fields ground).2 (fun entries =>
      law (fields 0) (fields 1) (fields 2) (fields 3) (fields 4) entries.1 entries.2.1 entries.2.2)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u

structure PreservedMainPrefixHistoryCode (M : TransitiveGround.{u})
    (K Labels C D rD A p : ZFSet.{u}) : Prop where
  function : FunctionGraphOn A p
  values : ∀ i q, ZFSet.pair i q ∈ p →
    ∃ S E, q = mainPrefixCode (insert i i) S E ∧
      MainPrefixGraphCode M K Labels C D rD (insert i i) S E ∧
      MainPrefixProfileGraphCode M K Labels C D rD S E
  compatible : ∀ i j q r, ZFSet.pair i q ∈ p → ZFSet.pair j r ∈ p →
    (i = j ∨ i ∈ j) → MainPrefixExtends q r

namespace PreservedMainPrefixHistoryCode
variable {M : TransitiveGround.{u}} {K Labels C D rD A p : ZFSet.{u}}
variable (history : PreservedMainPrefixHistoryCode M K Labels C D rD A p)

private theorem exists_fields (i : SetMembers A) :
    ∃ fields : ZFSet.{u} × ZFSet.{u},
      decodedFamilyValue history.function i = mainPrefixCode (insert (SetMembers.raw i) (SetMembers.raw i))
        fields.1 fields.2 ∧
      MainPrefixGraphCode M K Labels C D rD (insert (SetMembers.raw i) (SetMembers.raw i)) fields.1 fields.2 ∧
      MainPrefixProfileGraphCode M K Labels C D rD fields.1 fields.2 := by
  obtain ⟨S, E, equal, valid, profiles⟩ := history.values _ _
    (decodedFamilyValue_entry history.function i)
  exact ⟨(S, E), equal, valid, profiles⟩

noncomputable def fields (i : SetMembers A) : ZFSet.{u} × ZFSet.{u} :=
  Classical.choose (history.exists_fields i)

theorem fields_spec (i : SetMembers A) :
    decodedFamilyValue history.function i = mainPrefixCode (insert (SetMembers.raw i) (SetMembers.raw i))
      (history.fields i).1 (history.fields i).2 ∧
    MainPrefixGraphCode M K Labels C D rD (insert (SetMembers.raw i) (SetMembers.raw i))
      (history.fields i).1 (history.fields i).2 ∧
    MainPrefixProfileGraphCode M K Labels C D rD (history.fields i).1 (history.fields i).2 :=
  Classical.choose_spec (history.exists_fields i)

noncomputable def graphFamily : MainPrefixGraphFamily M K Labels C D rD (SetMembers A) where
  indices i := insert (SetMembers.raw i) (SetMembers.raw i)
  stages i := (history.fields i).1
  transitions i := (history.fields i).2
  valid i := (history.fields_spec i).2.1
  mono i j subset := by
    have before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j :=
      ZFSet.mem_insert_iff.1 (subset (ZFSet.mem_insert_iff.2 (Or.inl rfl)))
    have extension := history.compatible _ _ _ _
      (decodedFamilyValue_entry history.function i) (decodedFamilyValue_entry history.function j) before
    rw [(history.fields_spec i).1, (history.fields_spec j).1] at extension
    exact (mainPrefixExtends_iff.1 extension).2

theorem graphFamily_code_entry (i : SetMembers A) :
    ZFSet.pair (SetMembers.raw i) (history.graphFamily.code i) ∈ p := by
  change ZFSet.pair (SetMembers.raw i)
    (mainPrefixCode (insert (SetMembers.raw i) (SetMembers.raw i))
      (history.fields i).1 (history.fields i).2) ∈ p
  rw [← (history.fields_spec i).1]
  exact decodedFamilyValue_entry history.function i

theorem graphFamily_codeGraph_eq :
    familyCodeGraph (@SetMembers.raw A) history.graphFamily.code = p :=
  familyCodeGraph_eq_of_entries history.function _ _ (ordinalMainIndex_key_range A)
    history.graphFamily_code_entry

theorem graphFamily_profiles (i : SetMembers A) :
    MainPrefixProfileGraphCode M K Labels C D rD
      (history.graphFamily.stages i) (history.graphFamily.transitions i) :=
  (history.fields_spec i).2.2

theorem graphFamily_indexUnion (ordinal : ordinalSetProperty A) :
    history.graphFamily.indexUnion = A := by
  apply ZFSet.ext
  intro x
  rw [history.graphFamily.indexUnion_mem]
  constructor
  · rintro ⟨i, hi⟩
    rcases ZFSet.mem_insert_iff.1 hi with equal | below
    · exact equal.symm ▸ SetMembers.raw_mem i
    · exact ordinal.1 _ (SetMembers.raw_mem i) x below
  · intro hx
    refine ⟨SetMembers.ofMem x hx, ?_⟩
    change x ∈ insert (SetMembers.raw (SetMembers.ofMem x hx)) (SetMembers.raw (SetMembers.ofMem x hx))
    rw [SetMembers.raw_ofMem]
    exact ZFSet.mem_insert_iff.2 (Or.inl rfl)

end PreservedMainPrefixHistoryCode





def MainPrefixHistoryFieldMem (p x : ZFSet.{u}) (j : Fin 3) : Prop :=
  ∃ i T S E, ZFSet.pair i (mainPrefixCode T S E) ∈ p ∧
    x ∈ (Fin.cases T (Fin.cases S (fun _ => E)) : Fin 3 → ZFSet.{u}) j

def MainPrefixHistoryUnionCode (p q : ZFSet.{u}) : Prop :=
  ∃ T S E, q = mainPrefixCode T S E ∧
    ∀ (j : Fin 3) x, x ∈ (Fin.cases T (Fin.cases S (fun _ => E)) : Fin 3 → ZFSet.{u}) j ↔
      MainPrefixHistoryFieldMem p x j

theorem MainPrefixHistoryUnionCode.unique {p q r : ZFSet.{u}}
    (first : MainPrefixHistoryUnionCode p q) (second : MainPrefixHistoryUnionCode p r) : q = r := by
  obtain ⟨T, S, E, rfl, fields⟩ := first
  obtain ⟨U, F, G, rfl, fields'⟩ := second
  apply mainPrefixCode_inj.2
  exact ⟨ZFSet.ext (fun x => (fields 0 x).trans (fields' 0 x).symm),
    ZFSet.ext (fun x => (fields 1 x).trans (fields' 1 x).symm),
    ZFSet.ext (fun x => (fields 2 x).trans (fields' 2 x).symm)⟩

namespace PreservedMainPrefixHistoryCode
variable {M : TransitiveGround.{u}} {K Labels C D rD A p : ZFSet.{u}}
variable (history : PreservedMainPrefixHistoryCode M K Labels C D rD A p)

theorem field_mem_iff (j : Fin 3) (x : ZFSet.{u}) :
    MainPrefixHistoryFieldMem p x j ↔
      ∃ i : SetMembers A, x ∈ (Fin.cases (history.graphFamily.indices i)
        (Fin.cases (history.graphFamily.stages i) (fun _ => history.graphFamily.transitions i)) :
          Fin 3 → ZFSet.{u}) j := by
  constructor
  · rintro ⟨i, T, S, E, entry, member⟩
    have hi := history.function.pair_source entry
    let k := SetMembers.ofMem i hi
    have actual : ZFSet.pair i (history.graphFamily.code k) ∈ p := by
      have actual := history.graphFamily_code_entry k
      simpa only [k, SetMembers.raw_ofMem] using actual
    have equal := history.function.unique entry actual
    have fields := mainPrefixCode_inj.1 equal
    refine ⟨k, ?_⟩
    rw [fields.1, fields.2.1, fields.2.2] at member
    exact member
  · rintro ⟨i, member⟩
    exact ⟨SetMembers.raw i, history.graphFamily.indices i, history.graphFamily.stages i,
      history.graphFamily.transitions i, history.graphFamily_code_entry i, member⟩

theorem union_code : MainPrefixHistoryUnionCode p history.graphFamily.unionCode := by
  refine ⟨history.graphFamily.indexUnion, history.graphFamily.stageUnion,
    history.graphFamily.transitionUnion, rfl, ?_⟩
  intro j
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) j
  · intro x
    exact (history.graphFamily.indexUnion_mem x).trans (history.field_mem_iff 0 x).symm
  · intro x
    exact (history.graphFamily.stageUnion_mem x).trans (history.field_mem_iff 1 x).symm
  · intro x
    exact (history.graphFamily.transitionUnion_mem x).trans (history.field_mem_iff 2 x).symm

end PreservedMainPrefixHistoryCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def mainPrefixHistoryFieldMemFormula {n} (p x : Fin n) (j : Fin 3) : SetFormula n :=
  let old := suffixIndex n 5
  let field := prefixIndex n 5
  let selected : Fin 3 → Fin (n + 5) := Fin.cases (field 1) (Fin.cases (field 2) (fun _ => field 3))
  exBlock 5 (BoundedFormula.conj
    (BoundedFormula.pairMembershipFormula (field 0) (field 4) (old p))
    (.conj (BoundedFormula.mainPrefixTupleFormula (field 4) (field 1) (field 2) (field 3))
      (.mem (old x) (selected j)))).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mainPrefixHistoryFieldMem_ground {p x : ZFSet.{u}} {j : Fin 3}
    (hp : p ∈ M.sets) (member : MainPrefixHistoryFieldMem p x j) : x ∈ M.sets := by
  obtain ⟨i, T, S, E, entry, member⟩ := member
  have fields := M.mainPrefixCode_fields_mem (M.pair_right (M.transitive hp entry))
  have ground : ∀ k, (Fin.cases T (Fin.cases S (fun _ => E)) : Fin 3 → ZFSet.{u}) k ∈ M.sets :=
    Fin.cases fields.1 (Fin.cases fields.2.1 (fun _ => fields.2.2))
  exact M.transitive (ground j) member

theorem realize_mainPrefixHistoryFieldMemFormula {n} (p x : Fin n) (j : Fin 3)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (mainPrefixHistoryFieldMemFormula p x j) env ↔
      MainPrefixHistoryFieldMem (env p) (env x) j := by
  rw [mainPrefixHistoryFieldMemFormula, realize_exBlock]
  let old := suffixIndex n 5
  let field := prefixIndex n 5
  let selected : Fin 3 → Fin (n + 5) := Fin.cases (field 1) (Fin.cases (field 2) (fun _ => field 3))
  have actual (f : Fin 5 → ZFSet.{u}) (ground : ∀ k, f k ∈ M.sets) :
      Realize M.sets (BoundedFormula.conj
        (BoundedFormula.pairMembershipFormula (field 0) (field 4) (old p))
        (.conj (BoundedFormula.mainPrefixTupleFormula (field 4) (field 1) (field 2) (field 3))
          (.mem (old x) (selected j)))).toFormula (extendMany 5 f env) ↔
      ZFSet.pair (f 0) (f 4) ∈ env p ∧ f 4 = mainPrefixCode (f 1) (f 2) (f 3) ∧
        env x ∈ (Fin.cases (f 1) (Fin.cases (f 2) (fun _ => f 3)) : Fin 3 → ZFSet.{u}) j := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 f env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_pairMembershipFormula,
      BoundedFormula.truth_mainPrefixTupleFormula, old, field, extendMany_prefix, extendMany_suffix]
    refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) j <;> rfl
  constructor
  · rintro ⟨f, ground, recognized⟩
    obtain ⟨entry, equal, member⟩ := (actual f ground).1 recognized
    exact ⟨f 0, f 1, f 2, f 3, equal ▸ entry, member⟩
  · rintro ⟨i, T, S, E, entry, member⟩
    have pairGround := M.transitive (members p) entry
    have fieldsGround := M.mainPrefixCode_fields_mem (M.pair_right pairGround)
    let f : Fin 5 → ZFSet.{u} := Fin.cases i (Fin.cases T (Fin.cases S
      (Fin.cases E (fun _ => mainPrefixCode T S E))))
    have ground : ∀ k, f k ∈ M.sets := Fin.cases (M.pair_left pairGround)
      (Fin.cases fieldsGround.1 (Fin.cases fieldsGround.2.1
        (Fin.cases fieldsGround.2.2 (fun _ => M.pair_right pairGround))))
    exact ⟨f, ground, (actual f ground).2 ⟨entry, rfl, member⟩⟩

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

def MainPrefixAtIndex (T q : ZFSet.{u}) : Prop :=
  ∃ S E, q = mainPrefixCode T S E

def MainPrefixHistoryExtends (p q : ZFSet.{u}) : Prop :=
  ∀ i old, ZFSet.pair i old ∈ p → MainPrefixExtends old q

def MainPrefixTraceStepCode (B seed g α p y : ZFSet.{u}) : Prop :=
  y ∈ B ∧ MainPrefixAtIndex (insert α α) y ∧ MainPrefixHistoryExtends p y ∧
    ((α = ∅ ∧ y = seed) ∨
      (α ≠ ∅ ∧ ∃ input, MainPrefixHistoryUnionCode p input ∧ ZFSet.pair input y ∈ g))

theorem MainPrefixAtIndex.unique {T U q : ZFSet.{u}}
    (first : MainPrefixAtIndex T q) (second : MainPrefixAtIndex U q) : T = U := by
  obtain ⟨S, E, a⟩ := first
  obtain ⟨F, G, b⟩ := second
  exact (mainPrefixCode_inj.1 (a.symm.trans b)).1

theorem MainPrefixAtIndex.refl {T q : ZFSet.{u}} (code : MainPrefixAtIndex T q) :
    MainPrefixExtends q q := by
  obtain ⟨S, E, rfl⟩ := code
  exact MainPrefixExtends.refl T S E

theorem MainPrefixTraceStepCode.unique {B seed g α p y z : ZFSet.{u}}
    (function : FunctionGraphOn B g)
    (first : MainPrefixTraceStepCode B seed g α p y)
    (second : MainPrefixTraceStepCode B seed g α p z) : y = z := by
  rcases first.2.2.2 with ⟨zero, hy⟩ | ⟨nonzero, a, unionA, entryA⟩
  · rcases second.2.2.2 with ⟨_, hz⟩ | ⟨nonzero, _⟩
    · exact hy.trans hz.symm
    · exact False.elim (nonzero zero)
  · rcases second.2.2.2 with ⟨zero, _⟩ | ⟨_, b, unionB, entryB⟩
    · exact False.elim (nonzero zero)
    · have equal := unionA.unique unionB
      exact function.unique entryA (equal.symm ▸ entryB)

theorem MainPrefixHistoryExtends.trans {p q r : ZFSet.{u}}
    (history : MainPrefixHistoryExtends p q) (extension : MainPrefixExtends q r) :
    MainPrefixHistoryExtends p r :=
  fun i old entry => (history i old entry).trans extension

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def mainPrefixHistoryFieldUnionFormula {n} (p output : Fin n) (j : Fin 3) : SetFormula n :=
  exactSetFormula output (mainPrefixHistoryFieldMemFormula p.succ 0 j)

def mainPrefixHistoryUnionFormula {n} (p q : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (.conj (BoundedFormula.mainPrefixTupleFormula (old q) (field 0) (field 1) (field 2)).toFormula
    (conjBlock 3 (fun j => mainPrefixHistoryFieldUnionFormula (old p) (field j) j)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixHistoryFieldUnionFormula {n} (p output : Fin n) (j : Fin 3)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (mainPrefixHistoryFieldUnionFormula p output j) env ↔
      ∀ x, x ∈ env output ↔ MainPrefixHistoryFieldMem (env p) x j := by
  change (∀ x ∈ M.sets, Realize M.sets
    (.conj (imp (.mem 0 output.succ) (mainPrefixHistoryFieldMemFormula p.succ 0 j))
      (imp (mainPrefixHistoryFieldMemFormula p.succ 0 j) (.mem 0 output.succ))) (extend x env)) ↔ _
  simp only [Realize, realize_imp]
  have meaning (x : ZFSet.{u}) (hx : x ∈ M.sets) :
      Realize M.sets (mainPrefixHistoryFieldMemFormula p.succ 0 j) (extend x env) ↔
        MainPrefixHistoryFieldMem (env p) x j :=
    M.realize_mainPrefixHistoryFieldMemFormula p.succ 0 j (extend x env) (Fin.cases hx members)
  constructor
  · intro recognized x
    constructor
    · intro member
      have hx := M.transitive (members output) member
      exact (meaning x hx).1 ((recognized x hx).1 member)
    · intro member
      have hx := M.mainPrefixHistoryFieldMem_ground (members p) member
      exact (recognized x hx).2 ((meaning x hx).2 member)
  · intro exactFields x hx
    exact ⟨fun member => (meaning x hx).2 ((exactFields x).1 member),
      fun recognized => (exactFields x).2 ((meaning x hx).1 recognized)⟩

theorem realize_mainPrefixHistoryUnionFormula {n} (p q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (mainPrefixHistoryUnionFormula p q) env ↔
      MainPrefixHistoryUnionCode (env p) (env q) := by
  rw [mainPrefixHistoryUnionFormula, realize_exBlock]
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ k, f k ∈ M.sets) :
      (Realize M.sets (BoundedFormula.mainPrefixTupleFormula (old q) (field 0) (field 1) (field 2)).toFormula
          (extendMany 3 f env) ∧
        Realize M.sets (conjBlock 3 (fun j => mainPrefixHistoryFieldUnionFormula (old p) (field j) j))
          (extendMany 3 f env)) ↔
      env q = mainPrefixCode (f 0) (f 1) (f 2) ∧
        ∀ j x, x ∈ f j ↔ MainPrefixHistoryFieldMem (env p) x j := by
    have mems := extendMany_members 3 f env ground members
    rw [BoundedFormula.realize_mainPrefixTupleFormula M _ _ _ _ _ mems, realize_conjBlock]
    apply and_congr
    · simp only [old, field, extendMany_prefix, extendMany_suffix]
    · apply forall_congr'
      intro j
      simpa only [old, field, extendMany_prefix, extendMany_suffix] using
        M.realize_mainPrefixHistoryFieldUnionFormula (old p) (field j) j (extendMany 3 f env) mems
  constructor
  · rintro ⟨f, ground, recognized⟩
    obtain ⟨encoded, fields⟩ := (actual f ground).1 recognized
    have same : (Fin.cases (f 0) (Fin.cases (f 1) (fun _ => f 2)) : Fin 3 → ZFSet.{u}) = f := by
      funext j
      refine Fin.cases rfl (Fin.cases rfl (fun k => ?_)) j
      rw [Fin.eq_zero k]
      rfl
    refine ⟨f 0, f 1, f 2, encoded, ?_⟩
    rw [same]
    exact fields
  · rintro ⟨T, S, E, encoded, fields⟩
    have grounds := M.mainPrefixCode_fields_mem (encoded ▸ members q)
    let f : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have ground : ∀ k, f k ∈ M.sets := Fin.cases grounds.1 (Fin.cases grounds.2.1 (fun _ => grounds.2.2))
    exact ⟨f, ground, (actual f ground).2 ⟨encoded, fields⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
