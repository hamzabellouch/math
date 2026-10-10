import OAI.SetTheory.PartitionPrinciple.Geometry.GroundLinkedTransitionRetarget

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

structure MainPrefixGraphCode (M : TransitiveGround.{u})
    (K Labels C D rD T S E : ZFSet.{u}) : Prop where
  ordinal : ordinalSetProperty T
  stages : FunctionGraphOn T S
  transitions : FunctionGraphOn (chronologyPairs T) E
  stage_valid : ∀ i a, ZFSet.pair i a ∈ S →
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = a
  transition_valid : ∀ i j a b z, ZFSet.pair i a ∈ S → ZFSet.pair j b ∈ S →
    ZFSet.pair (ZFSet.pair j i) z ∈ E → LinkedMainTransitionCode M K Labels C D rD a b z
  identity : ∀ i p a, ZFSet.pair (ZFSet.pair i i) (ZFSet.pair p a) ∈ E →
    GraphDiagonalCode p ∧ GraphDiagonalCode a
  composition : ∀ i j k p₁ a₁ p₂ a₂ p₃ a₃,
    ZFSet.pair (ZFSet.pair j i) (ZFSet.pair p₁ a₁) ∈ E →
    ZFSet.pair (ZFSet.pair k j) (ZFSet.pair p₂ a₂) ∈ E →
    ZFSet.pair (ZFSet.pair k i) (ZFSet.pair p₃ a₃) ∈ E →
    GraphCompositionCode p₁ p₂ p₃ ∧ GraphCompositionCode a₁ a₂ a₃

end

namespace MainPrefixGraphCode
open SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD T S E : ZFSet.{u}}
variable (raw : MainPrefixGraphCode M K Labels C D rD T S E)

noncomputable def decodedLinked (i : SetMembers T) : GroundLinkedMainStage M K Labels C D rD :=
  Classical.choose (raw.stage_valid (SetMembers.raw i) (decodedFamilyValue raw.stages i)
    (decodedFamilyValue_entry raw.stages i))

theorem decodedLinked_code (i : SetMembers T) :
    (raw.decodedLinked i).code = decodedFamilyValue raw.stages i :=
  Classical.choose_spec (raw.stage_valid (SetMembers.raw i) (decodedFamilyValue raw.stages i)
    (decodedFamilyValue_entry raw.stages i))

theorem decodedLinked_entry (i : SetMembers T) :
    ZFSet.pair (SetMembers.raw i) (raw.decodedLinked i).code ∈ S := by
  rw [raw.decodedLinked_code]
  exact decodedFamilyValue_entry raw.stages i

noncomputable def decodedTransitionIndex (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    {q : ZFSet.{u} // q ∈ chronologyPairs T} :=
  ⟨ZFSet.pair (SetMembers.raw j) (SetMembers.raw i),
    (pair_mem_chronologyPairs T _ _).2 ⟨SetMembers.raw_mem j, SetMembers.raw_mem i, before⟩⟩

noncomputable def decodedTransitionCode (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) : ZFSet.{u} :=
  raw.transitions.value (decodedTransitionIndex i j before)

theorem decodedTransitionCode_entry (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw j) (SetMembers.raw i))
      (raw.decodedTransitionCode i j before) ∈ E :=
  raw.transitions.value_entry (decodedTransitionIndex i j before)

theorem exists_decodedTransition (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    ∃ transition : GroundChronologicalMainTransition (raw.decodedLinked i).main (raw.decodedLinked j).main,
      transition.map.code = raw.decodedTransitionCode i j before ∧ transition.CoversOldBirths :=
  LinkedMainTransitionCode.exists_at (raw.decodedLinked i) (raw.decodedLinked j)
    (raw.transition_valid _ _ _ _ _ (raw.decodedLinked_entry i) (raw.decodedLinked_entry j)
      (raw.decodedTransitionCode_entry i j before))

noncomputable def decodedTransition (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    GroundChronologicalMainTransition (raw.decodedLinked i).main (raw.decodedLinked j).main :=
  Classical.choose (raw.exists_decodedTransition i j before)

theorem decodedTransition_code (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    (raw.decodedTransition i j before).map.code = raw.decodedTransitionCode i j before :=
  (Classical.choose_spec (raw.exists_decodedTransition i j before)).1

theorem decodedTransition_coverage (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    (raw.decodedTransition i j before).CoversOldBirths :=
  (Classical.choose_spec (raw.exists_decodedTransition i j before)).2

theorem decodedTransition_entry (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw j) (SetMembers.raw i))
      (raw.decodedTransition i j before).map.code ∈ E := by
  rw [raw.decodedTransition_code]
  exact raw.decodedTransitionCode_entry i j before

end MainPrefixGraphCode

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem linked_transition_code {i j : I} (before : i ≤ j) :
    LinkedMainTransitionCode M K Labels C D rD (run.linked i).code (run.linked j).code
      (run.diagram.transition before).map.code := by
  refine ⟨run.linked i, run.linked j, rfl, rfl, ?_⟩
  rw [run.linked_main i, run.linked_main j]
  exact ⟨run.diagram.transition before, rfl, run.coverage before⟩

theorem stageGraph_valid {i a : ZFSet.{u}} (entry : ZFSet.pair i a ∈ run.stageGraph) :
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = a := by
  obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source entry)
  exact ⟨run.linked j, ((run.stageGraph_entry j a).1 entry).symm⟩

theorem transitionGraph_valid {i j a b z : ZFSet.{u}}
    (first : ZFSet.pair i a ∈ run.stageGraph) (second : ZFSet.pair j b ∈ run.stageGraph)
    (entry : ZFSet.pair (ZFSet.pair j i) z ∈ run.transitionGraph) :
    LinkedMainTransitionCode M K Labels C D rD a b z := by
  obtain ⟨s, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source first)
  obtain ⟨t, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source second)
  have order := ((pair_mem_chronologyPairs _ _ _).1
    (run.transitionGraph_function.pair_source entry)).2.2
  have before := (run.key_order s t).2 order
  rw [(run.stageGraph_entry s a).1 first, (run.stageGraph_entry t b).1 second,
    (run.transitionGraph_entry before z).1 entry]
  exact run.linked_transition_code before

theorem transitionGraph_identity {i p a : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair i i) (ZFSet.pair p a) ∈ run.transitionGraph) :
    GraphDiagonalCode p ∧ GraphDiagonalCode a := by
  have domain := (pair_mem_chronologyPairs _ _ _).1 (run.transitionGraph_function.pair_source entry)
  obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 domain.1
  have equal := (run.transitionGraph_entry (le_refl j) (ZFSet.pair p a)).1 entry
  rw [run.diagram.self] at equal
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  exact ⟨graphDiagonalCode_identity _, graphDiagonalCode_identity _⟩

theorem transitionGraph_composition {i j k p₁ a₁ p₂ a₂ p₃ a₃ : ZFSet.{u}}
    (first : ZFSet.pair (ZFSet.pair j i) (ZFSet.pair p₁ a₁) ∈ run.transitionGraph)
    (second : ZFSet.pair (ZFSet.pair k j) (ZFSet.pair p₂ a₂) ∈ run.transitionGraph)
    (third : ZFSet.pair (ZFSet.pair k i) (ZFSet.pair p₃ a₃) ∈ run.transitionGraph) :
    GraphCompositionCode p₁ p₂ p₃ ∧ GraphCompositionCode a₁ a₂ a₃ := by
  have domain₁ := (pair_mem_chronologyPairs _ _ _).1 (run.transitionGraph_function.pair_source first)
  have domain₂ := (pair_mem_chronologyPairs _ _ _).1 (run.transitionGraph_function.pair_source second)
  obtain ⟨s, rfl⟩ := ZFSet.mem_range.1 domain₁.2.1
  obtain ⟨t, rfl⟩ := ZFSet.mem_range.1 domain₁.1
  obtain ⟨v, rfl⟩ := ZFSet.mem_range.1 domain₂.1
  have before₁ := (run.key_order s t).2 domain₁.2.2
  have before₂ := (run.key_order t v).2 domain₂.2.2
  have equal₁ := (run.transitionGraph_entry before₁ _).1 first
  have equal₂ := (run.transitionGraph_entry before₂ _).1 second
  have equal₃ := (run.transitionGraph_entry (le_trans before₁ before₂) _).1 third
  rw [run.diagram.comp before₁ before₂] at equal₃
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal₁
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal₂
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal₃
  exact ⟨graphCompositionCode_relationCompose
      (run.diagram.transition before₁).map.point_embedding.injection.function
      (run.diagram.transition before₂).map.point_embedding.injection.function,
    graphCompositionCode_relationCompose
      (run.diagram.transition before₁).map.group_embedding.injection.function
      (run.diagram.transition before₂).map.group_embedding.injection.function⟩

theorem graph_code : MainPrefixGraphCode M K Labels C D rD run.indices run.stageGraph run.transitionGraph where
  ordinal := run.indices_ordinal
  stages := run.stageGraph_function
  transitions := run.transitionGraph_function
  stage_valid := fun _ _ entry => run.stageGraph_valid entry
  transition_valid := fun _ _ _ _ _ first second entry => run.transitionGraph_valid first second entry
  identity := fun _ _ _ entry => run.transitionGraph_identity entry
  composition := fun _ _ _ _ _ _ _ _ _ first second third => run.transitionGraph_composition first second third

end GroundMainPrefix

section
open SetFormula
universe u

noncomputable def mainPrefixCode (T S E : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 2 (Fin.cases T (Fin.cases S (fun _ => E)))

theorem mainPrefixCode_inj {T S E T' S' E' : ZFSet.{u}} :
    mainPrefixCode T S E = mainPrefixCode T' S' E' ↔ T = T' ∧ S = S' ∧ E = E' := by
  constructor
  · intro equal
    have fields := nonemptyTupleCode_injective 2 equal
    exact ⟨congrFun fields 0, congrFun fields 1, congrFun fields 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

def MainPrefixCode (M : TransitiveGround.{u}) (K Labels C D rD z : ZFSet.{u}) : Prop :=
  ∃ T S E, z = mainPrefixCode T S E ∧ MainPrefixGraphCode M K Labels C D rD T S E

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mainPrefixCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {T S E : ZFSet.{u}} (hT : T ∈ M.sets) (hS : S ∈ M.sets) (hE : E ∈ M.sets) :
    mainPrefixCode T S E ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 _ (Fin.cases hT (Fin.cases hS (fun _ => hE)))

theorem mainPrefixCode_fields_mem {T S E : ZFSet.{u}} (ground : mainPrefixCode T S E ∈ M.sets) :
    T ∈ M.sets ∧ S ∈ M.sets ∧ E ∈ M.sets := by
  let fields : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
  have encoded : nonemptyTupleCode 2 fields ∈ M.sets := ground
  have each := M.nonemptyTupleCode_field_mem 2 fields encoded
  exact ⟨each 0, each 1, each 2⟩

end TransitiveGround

namespace BoundedFormula

def mainPrefixTupleFormula {n} (z T S E : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 2 z (Fin.cases T (Fin.cases S (fun _ => E)))

theorem truth_mainPrefixTupleFormula {n} (z T S E : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainPrefixTupleFormula z T S E) env ↔ env z = mainPrefixCode (env T) (env S) (env E) := by
  rw [mainPrefixTupleFormula, truth_nonemptyTupleFormula]
  have map : (fun j : Fin 3 => env (Fin.cases T (Fin.cases S (fun _ => E)) j)) =
      Fin.cases (env T) (Fin.cases (env S) (fun _ => env E)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) j
  rw [map]
  rfl

theorem realize_mainPrefixTupleFormula (M : TransitiveGround.{u}) {n}
    (z T S E : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixTupleFormula z T S E).toFormula env ↔
      env z = mainPrefixCode (env T) (env S) (env E) :=
  (realize_toFormula M _ env members).trans (truth_mainPrefixTupleFormula z T S E env)

end BoundedFormula

end

namespace MainPrefixGraphCode
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD T S E : ZFSet.{u}}
variable (raw : MainPrefixGraphCode M K Labels C D rD T S E)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem decodedTransition_self (i : SetMembers T) :
    raw.decodedTransition i i (Or.inl rfl) =
      GroundChronologicalMainTransition.identity pairing unions powers separation (raw.decodedLinked i).main := by
  have diagonal := raw.identity (SetMembers.raw i) _ _ (raw.decodedTransition_entry i i (Or.inl rfl))
  apply GroundChronologicalMainTransition.ext
  apply GroundMainTransition.ext
  · exact diagonal.1.eq_identityFunctionGraph
      (raw.decodedTransition i i (Or.inl rfl)).map.point_embedding.injection.function
  · exact diagonal.2.eq_identityFunctionGraph
      (raw.decodedTransition i i (Or.inl rfl)).map.group_embedding.injection.function

theorem decodedTransition_comp (i j k : SetMembers T)
    (first : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j)
    (second : SetMembers.raw j = SetMembers.raw k ∨ SetMembers.raw j ∈ SetMembers.raw k) :
    raw.decodedTransition i k ((ordinalMainIndexPreorder raw.ordinal).le_trans i j k first second) =
      (raw.decodedTransition i j first).comp pairing unions powers separation (raw.decodedTransition j k second) := by
  have direct := (ordinalMainIndexPreorder raw.ordinal).le_trans i j k first second
  have coherent := raw.composition (SetMembers.raw i) (SetMembers.raw j) (SetMembers.raw k)
    _ _ _ _ _ _ (raw.decodedTransition_entry i j first) (raw.decodedTransition_entry j k second)
      (raw.decodedTransition_entry i k direct)
  apply GroundChronologicalMainTransition.ext
  apply GroundMainTransition.ext
  · exact coherent.1.eq_relationCompose
      (raw.decodedTransition i j first).map.point_embedding.injection.function
      (raw.decodedTransition i k direct).map.point_embedding.injection.function.1
  · exact coherent.2.eq_relationCompose
      (raw.decodedTransition i j first).map.group_embedding.injection.function
      (raw.decodedTransition i k direct).map.group_embedding.injection.function.1

noncomputable def decodedDiagram :
    letI := ordinalMainIndexPreorder raw.ordinal
    GroundChronologicalMainDiagram M C D rD pairing unions powers separation (SetMembers T) := by
  let := ordinalMainIndexPreorder raw.ordinal
  exact {
    stage := fun i => (raw.decodedLinked i).main
    transition := fun {i j} before => raw.decodedTransition i j before
    self := raw.decodedTransition_self pairing unions powers separation
    comp := fun {i j k} first second => raw.decodedTransition_comp pairing unions powers separation i j k first second
  }

theorem decodedDiagram_coverage :
    letI := ordinalMainIndexPreorder raw.ordinal
    (raw.decodedDiagram pairing unions powers separation).CoversOldBirths := by
  let := ordinalMainIndexPreorder raw.ordinal
  exact fun {i j} before => raw.decodedTransition_coverage i j before

end MainPrefixGraphCode

section
universe u

def MainPrefixExtends (old next : ZFSet.{u}) : Prop :=
  ∃ T S E T' S' E', old = mainPrefixCode T S E ∧ next = mainPrefixCode T' S' E' ∧
    T ⊆ T' ∧ S ⊆ S' ∧ E ⊆ E'

theorem mainPrefixExtends_iff {T S E T' S' E' : ZFSet.{u}} :
    MainPrefixExtends (mainPrefixCode T S E) (mainPrefixCode T' S' E') ↔
      T ⊆ T' ∧ S ⊆ S' ∧ E ⊆ E' := by
  constructor
  · rintro ⟨A, B, C, A', B', C', first, second, indices, stages, transitions⟩
    obtain ⟨rfl, rfl, rfl⟩ := mainPrefixCode_inj.1 first
    obtain ⟨rfl, rfl, rfl⟩ := mainPrefixCode_inj.1 second
    exact ⟨indices, stages, transitions⟩
  · rintro ⟨indices, stages, transitions⟩
    exact ⟨T, S, E, T', S', E', rfl, rfl, indices, stages, transitions⟩

theorem MainPrefixExtends.refl (T S E : ZFSet.{u}) :
    MainPrefixExtends (mainPrefixCode T S E) (mainPrefixCode T S E) :=
  mainPrefixExtends_iff.2 ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem MainPrefixExtends.trans {a b c : ZFSet.{u}}
    (first : MainPrefixExtends a b) (second : MainPrefixExtends b c) : MainPrefixExtends a c := by
  obtain ⟨T, S, E, U, F, G, rfl, hb, indices, stages, transitions⟩ := first
  obtain ⟨U', F', G', V, H, J, hb', rfl, indices', stages', transitions'⟩ := second
  obtain ⟨rfl, rfl, rfl⟩ := mainPrefixCode_inj.1 (hb.symm.trans hb')
  exact mainPrefixExtends_iff.2 ⟨fun _ h => indices' (indices h),
    fun _ h => stages' (stages h), fun _ h => transitions' (transitions h)⟩

theorem MainPrefixExtends.antisymm {a b : ZFSet.{u}}
    (first : MainPrefixExtends a b) (second : MainPrefixExtends b a) : a = b := by
  obtain ⟨T, S, E, U, F, G, rfl, rfl, indices, stages, transitions⟩ := first
  obtain ⟨indices', stages', transitions'⟩ := mainPrefixExtends_iff.1 second
  exact mainPrefixCode_inj.2 ⟨ZFSet.ext fun _ => ⟨fun h => indices h, fun h => indices' h⟩,
    ZFSet.ext fun _ => ⟨fun h => stages h, fun h => stages' h⟩,
    ZFSet.ext fun _ => ⟨fun h => transitions h, fun h => transitions' h⟩⟩

theorem FunctionGraphOn.restriction_eq_of_subset {A B f g : ZFSet.{u}}
    (first : FunctionGraphOn A f) (second : FunctionGraphOn B g) (subset : f ⊆ g) :
    graphRestriction A g = f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨w, old⟩ := first.total hx
    have equal := second.unique entry (subset old)
    exact equal.symm ▸ old
  · intro hz
    obtain ⟨x, hx, y, rfl⟩ := first.shape _ hz
    exact pair_mem_graphRestriction.2 ⟨subset hz, hx⟩

theorem mainPrefixExtends_iff_restrictions
    {M : TransitiveGround.{u}} {K Labels C D rD T S E T' S' E' : ZFSet.{u}}
    (old : MainPrefixGraphCode M K Labels C D rD T S E)
    (next : MainPrefixGraphCode M K Labels C D rD T' S' E') :
    MainPrefixExtends (mainPrefixCode T S E) (mainPrefixCode T' S' E') ↔
      T ⊆ T' ∧ graphRestriction T S' = S ∧ graphRestriction (chronologyPairs T) E' = E := by
  rw [mainPrefixExtends_iff]
  constructor
  · rintro ⟨indices, stages, transitions⟩
    exact ⟨indices, old.stages.restriction_eq_of_subset next.stages stages,
      old.transitions.restriction_eq_of_subset next.transitions transitions⟩
  · rintro ⟨indices, stages, transitions⟩
    exact ⟨indices, stages ▸ graphRestriction_subset T S',
      transitions ▸ graphRestriction_subset (chronologyPairs T) E'⟩

end

namespace MainPrefixGraphCode
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD T S E : ZFSet.{u}}
variable (raw : MainPrefixGraphCode M K Labels C D rD T S E)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hT : T ∈ M.sets) (hS : S ∈ M.sets) (hE : E ∈ M.sets)

noncomputable def decodedPrefix :
    letI := ordinalMainIndexPreorder raw.ordinal
    GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers T) := by
  let := ordinalMainIndexPreorder raw.ordinal
  exact {
    key := SetMembers.raw
    key_injective := SetMembers.raw_injective T
    key_order := fun i j => ordinalMainIndex_le_iff raw.ordinal i j
    indices_ground := (ordinalMainIndex_key_range T).symm ▸ hT
    indices_ordinal := (ordinalMainIndex_key_range T).symm ▸ raw.ordinal
    diagram := raw.decodedDiagram pairing unions powers separation
    linked := raw.decodedLinked
    linked_main := fun _ => rfl
    coverage := raw.decodedDiagram_coverage pairing unions powers separation
    stages_ground := familyCodeGraph_ground_of_entries hS raw.stages _ _
      (ordinalMainIndex_key_range T) raw.decodedLinked_entry
    transitions_ground := familyCodeGraph_ground_of_entries hE raw.transitions _ _
      (ordinalMainTransitionIndex_range raw.ordinal)
      (fun p => raw.decodedTransition_entry p.val.1 p.val.2 p.property)
  }

theorem decodedPrefix_indices :
    letI := ordinalMainIndexPreorder raw.ordinal
    (raw.decodedPrefix pairing unions powers separation hT hS hE).indices = T :=
  ordinalMainIndex_key_range T

theorem decodedPrefix_stageGraph :
    letI := ordinalMainIndexPreorder raw.ordinal
    (raw.decodedPrefix pairing unions powers separation hT hS hE).stageGraph = S :=
  familyCodeGraph_eq_of_entries raw.stages _ _ (ordinalMainIndex_key_range T) raw.decodedLinked_entry

theorem decodedPrefix_transitionGraph :
    letI := ordinalMainIndexPreorder raw.ordinal
    (raw.decodedPrefix pairing unions powers separation hT hS hE).transitionGraph = E := by
  let := ordinalMainIndexPreorder raw.ordinal
  exact familyCodeGraph_eq_of_entries raw.transitions _ _ (ordinalMainTransitionIndex_range raw.ordinal)
    (fun p => raw.decodedTransition_entry p.val.1 p.val.2 p.property)

theorem decodedPrefix_code :
    letI := ordinalMainIndexPreorder raw.ordinal
    (raw.decodedPrefix pairing unions powers separation hT hS hE).code =
      nonemptyTupleCode 2 (Fin.cases T (Fin.cases S (fun _ => E))) := by
  let := ordinalMainIndexPreorder raw.ordinal
  unfold GroundMainPrefix.code
  rw [raw.decodedPrefix_indices, raw.decodedPrefix_stageGraph, raw.decodedPrefix_transitionGraph]

end MainPrefixGraphCode

end PartitionPilot.Forcing

end OAI
