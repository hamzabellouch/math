import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNiceAssignmentClassFamilies

namespace OAI


namespace PartitionPilot.Forcing
universe u

noncomputable def assignmentIndices (I T A : ZFSet.{u}) : ZFSet.{u} :=
  relationImage A I (productFirst I (ZFSet.prod T T))

noncomputable def assignmentOnIndices (B T A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ stageOneAssignments B T) A

theorem mem_assignmentIndices (I T A t : ZFSet.{u}) :
    t ∈ assignmentIndices I T A ↔
      t ∈ I ∧ ∃ u ∈ T, ∃ w ∈ T, stageOneAssignment t u w ∈ A := by
  rw [assignmentIndices, mem_relationImage]
  constructor
  · rintro ⟨ht, z, hz, entry⟩
    obtain ⟨i, _, rest, hr, equal⟩ := (mem_productFirst I (ZFSet.prod T T) _).1 entry
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨u, hu, w, hw, rfl⟩ := ZFSet.mem_prod.1 hr
    exact ⟨ht, u, hu, w, hw, hz⟩
  · rintro ⟨ht, u, hu, w, hw, member⟩
    exact ⟨ht, stageOneAssignment t u w, member,
      (mem_productFirst I (ZFSet.prod T T) _).2
        ⟨t, ht, ZFSet.pair u w, ZFSet.pair_mem_prod.2 ⟨hu, hw⟩, rfl⟩⟩

theorem mem_assignmentOnIndices (B T A z : ZFSet.{u}) :
    z ∈ assignmentOnIndices B T A ↔ z ∈ A ∧ z ∈ stageOneAssignments B T :=
  ZFSet.mem_sep

theorem assignmentOnIndices_entry (B T A t u w : ZFSet.{u}) :
    stageOneAssignment t u w ∈ assignmentOnIndices B T A ↔
      stageOneAssignment t u w ∈ A ∧ t ∈ B ∧ u ∈ T ∧ w ∈ T := by
  rw [mem_assignmentOnIndices, stageOneAssignment_mem_assignments]

theorem assignmentIndices_on (I T B A : ZFSet.{u}) :
    assignmentIndices I T (assignmentOnIndices B T A) = assignmentIndices I T A ∩ B := by
  apply ZFSet.ext
  intro t
  rw [mem_assignmentIndices, ZFSet.mem_inter, mem_assignmentIndices]
  constructor
  · rintro ⟨ht, u, hu, w, hw, entry⟩
    have e := (assignmentOnIndices_entry B T A t u w).1 entry
    exact ⟨⟨ht, u, hu, w, hw, e.1⟩, e.2.1⟩
  · rintro ⟨⟨ht, u, hu, w, hw, entry⟩, hb⟩
    exact ⟨ht, u, hu, w, hw, (assignmentOnIndices_entry B T A t u w).2
      ⟨entry, hb, hu, hw⟩⟩

theorem assignmentOnIndices_own {I T A : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments I T) :
    assignmentOnIndices (assignmentIndices I T A) T A = A := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentOnIndices]
  refine ⟨And.left, fun hz => ⟨hz, ?_⟩⟩
  obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 (subset hz)
  exact (stageOneAssignment_mem_assignments _ _ _ _ _).2
    ⟨(mem_assignmentIndices I T A t).2 ⟨ht, u, hu, w, hw, hz⟩, hu, hw⟩

theorem assignment_subset_iff_indices_subset {I T A X : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments I T) :
    A ⊆ stageOneAssignments X T ↔ assignmentIndices I T A ⊆ X := by
  constructor
  · intro h t ht
    obtain ⟨_, u, _, w, _, entry⟩ := (mem_assignmentIndices I T A t).1 ht
    exact ((stageOneAssignment_mem_assignments X T t u w).1 (h entry)).1
  · intro h z hz
    obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 (subset hz)
    exact (stageOneAssignment_mem_assignments X T t u w).2
      ⟨h ((mem_assignmentIndices I T A t).2 ⟨ht, u, hu, w, hw, hz⟩), hu, hw⟩





def AssignmentQueryWithin (X T q : ZFSet.{u}) : Prop :=
  ∃ row L, q = ZFSet.pair row L ∧ L ⊆ stageOneAssignments X T

noncomputable def assignmentQueriesWithin (Q X T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (AssignmentQueryWithin X T) Q

noncomputable def representativeIndexAdditions (I T Q c X : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun i => ∃ q ∈ Q, AssignmentQueryWithin X T q ∧
    ∃ row A, ZFSet.pair q (ZFSet.pair row A) ∈ c ∧
      ∃ v ∈ T, ∃ w ∈ T, stageOneAssignment i v w ∈ A) I

noncomputable def representativeIndexStep (I T Q c X : ZFSet.{u}) : ZFSet.{u} :=
  X ∪ representativeIndexAdditions I T Q c X

theorem mem_assignmentQueriesWithin (Q X T q : ZFSet.{u}) :
    q ∈ assignmentQueriesWithin Q X T ↔ q ∈ Q ∧ AssignmentQueryWithin X T q :=
  ZFSet.mem_sep

theorem mem_representativeIndexAdditions (I T Q c X i : ZFSet.{u}) :
    i ∈ representativeIndexAdditions I T Q c X ↔ i ∈ I ∧
      ∃ q ∈ Q, AssignmentQueryWithin X T q ∧
        ∃ row A, ZFSet.pair q (ZFSet.pair row A) ∈ c ∧
          ∃ v ∈ T, ∃ w ∈ T, stageOneAssignment i v w ∈ A :=
  ZFSet.mem_sep

theorem representativeIndexStep_contains (I T Q c X : ZFSet.{u}) :
    X ⊆ representativeIndexStep I T Q c X :=
  fun _ member => ZFSet.mem_union.2 (Or.inl member)

theorem representativeIndexStep_subset {I T Q c X : ZFSet.{u}} (subset : X ⊆ I) :
    representativeIndexStep I T Q c X ⊆ I := by
  intro i member
  exact (ZFSet.mem_union.1 member).elim (fun h => subset h)
    (fun h => ((mem_representativeIndexAdditions I T Q c X i).1 h).1)

theorem representativeIndexStep_covers {I T Q c X q row A : ZFSet.{u}}
    (query : q ∈ Q) (within : AssignmentQueryWithin X T q)
    (entry : ZFSet.pair q (ZFSet.pair row A) ∈ c) :
    assignmentIndices I T A ⊆ representativeIndexStep I T Q c X := by
  intro i member
  obtain ⟨hi, v, hv, w, hw, e⟩ := (mem_assignmentIndices I T A i).1 member
  exact ZFSet.mem_union.2 (Or.inr
    ((mem_representativeIndexAdditions I T Q c X i).2
      ⟨hi, q, query, within, row, A, entry, v, hv, w, hw, e⟩))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem assignmentIndices_mem {I T A : ZFSet.{u}}
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentIndices I T A ∈ M.sets :=
  M.relationImage_mem separation hA hI (M.productFirst_mem pairing unions powers separation
    hI (M.prod_mem pairing unions powers separation hT hT))

theorem assignmentOnIndices_mem {B T A : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentOnIndices B T A ∈ M.sets :=
  M.bounded_separation_mem separation (.mem 0 1)
    (extend (stageOneAssignments B T) Fin.elim0)
    (Fin.cases (M.stageOneAssignments_mem pairing unions powers separation hB hT)
      (fun i => Fin.elim0 i)) hA

theorem assignmentIndices_small
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I T A N : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hA : A ∈ M.sets) (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    M.groundEmbeddable (assignmentIndices I T A) N :=
  M.groundEmbeddable_function_image pairing unions powers separation choice hA hI hN
    (M.productFirst_mem pairing unions powers separation hI
      (M.prod_mem pairing unions powers separation hT hT)) (productFirst_function I (ZFSet.prod T T)) small

theorem assignmentOnIndices_small {B T A N : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets)
    (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    M.groundEmbeddable (assignmentOnIndices B T A) N :=
  M.groundEmbeddable_restrict separation
    (M.assignmentOnIndices_mem pairing unions powers separation hB hT hA) hN
    (fun _ hz => (mem_assignmentOnIndices B T A _).1 hz |>.1) small

theorem assignmentOnIndices_candidate {rows I T B row A : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (member : ZFSet.pair row A ∈ M.stageOneCandidateBound rows I T) :
    ZFSet.pair row (assignmentOnIndices B T A) ∈ M.stageOneCandidateBound rows B T := by
  obtain ⟨hr, hA, _, small⟩ := (M.pair_mem_stageOneCandidateBound rows I T row A).1 member
  exact (M.pair_mem_stageOneCandidateBound rows B T row _).2
    ⟨hr, M.assignmentOnIndices_mem pairing unions powers separation hB hT hA,
      fun _ hz => (mem_assignmentOnIndices B T A _).1 hz |>.2,
      M.assignmentOnIndices_small pairing unions powers separation hB hT hA omega small⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
universe u
variable (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})

theorem stageOneRawTests_transfer {A B : ZFSet.{u}} (lower : ZFSet.{u})
    (tests : stageOneRawTests M d A lower)
    (guards : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
      stageOneAssignment t u w ∈ B → stageOneAssignment t u w ∈ A) :
    stageOneRawTests M d B lower :=
  ⟨fun t ht u hu w hw entry => tests.1 t ht u hu w hw (guards t ht u hu w hw entry),
    fun t ht u hu u' hu' w hw w' hw' entry entry' =>
      tests.2 t ht u hu u' hu' w hw w' hw'
        (guards t ht u hu w hw entry) (guards t ht u' hu' w' hw' entry')⟩

theorem stageOneRawTests_congr (A B lower : ZFSet.{u})
    (guards : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
      stageOneAssignment t u w ∈ A ↔ stageOneAssignment t u w ∈ B) :
    stageOneRawTests M d A lower ↔ stageOneRawTests M d B lower :=
  ⟨fun tests => stageOneRawTests_transfer M d lower tests
      (fun t ht u hu w hw entry => (guards t ht u hu w hw).2 entry),
    fun tests => stageOneRawTests_transfer M d lower tests
      (fun t ht u hu w hw entry => (guards t ht u hu w hw).1 entry)⟩

theorem stageOneRawTests_cut_iff (levels beta A lower : ZFSet.{u})
    (covered : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
      ∃ xi ∈ beta, ZFSet.pair (stageOneAssignment t u w) xi ∈ levels) :
    stageOneRawTests M d (assignmentCut levels beta A) lower ↔ stageOneRawTests M d A lower := by
  apply stageOneRawTests_congr
  intro t ht u hu w hw
  rw [mem_assignmentCut]
  exact ⟨And.left, fun entry => ⟨entry, covered t ht u hu w hw⟩⟩

theorem stageTwoConditionCode_pair_iff (levels alpha row A : ZFSet.{u}) :
    StageTwoConditionCode M levels alpha d (ZFSet.pair row A) ↔
      ZFSet.pair row (assignmentCut levels alpha A) ∈ d 7 ∧
      stageOneRawTests M d A (ZFSet.pair row (assignmentCut levels alpha A)) := by
  constructor
  · rintro ⟨row', A', equal, member, tests⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective equal
    exact ⟨member, tests⟩
  · rintro ⟨member, tests⟩
    exact ⟨row, A, rfl, member, tests⟩

theorem stageTwoConditionCode_cut_iff (levels alpha beta row A : ZFSet.{u})
    (below : alpha ⊆ beta)
    (covered : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
      ∃ xi ∈ beta, ZFSet.pair (stageOneAssignment t u w) xi ∈ levels) :
    StageTwoConditionCode M levels alpha d (ZFSet.pair row (assignmentCut levels beta A)) ↔
      StageTwoConditionCode M levels alpha d (ZFSet.pair row A) := by
  rw [stageTwoConditionCode_pair_iff, stageTwoConditionCode_pair_iff, assignmentCut_nested below]
  exact and_congr Iff.rfl (stageOneRawTests_cut_iff M d levels beta A _ covered)

theorem packedSuccessorConditionCode_cut_iff (levels alpha beta row A : ZFSet.{u})
    (below : alpha ⊆ beta)
    (covered : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
      ∃ xi ∈ beta, ZFSet.pair (stageOneAssignment t u w) xi ∈ levels) :
    PackedSuccessorConditionCode M levels alpha (refinementFormulaDataCode d)
      (ZFSet.pair row (assignmentCut levels beta A)) ↔
    PackedSuccessorConditionCode M levels alpha (refinementFormulaDataCode d) (ZFSet.pair row A) := by
  rw [packedSuccessorConditionCode_code_iff, packedSuccessorConditionCode_code_iff]
  exact stageTwoConditionCode_cut_iff M d levels alpha beta row A below covered

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

def AssignmentIndexAgreement (A B : ZFSet.{u}) : Prop :=
  ∀ t, (∃ u w, stageOneAssignment t u w ∈ A) →
    (∃ u w, stageOneAssignment t u w ∈ B) →
    ∀ u w, stageOneAssignment t u w ∈ A ↔ stageOneAssignment t u w ∈ B

theorem stageOneRawTests_binary_union (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    {A B lower : ZFSet.{u}} (agreement : AssignmentIndexAgreement A B)
    (first : stageOneRawTests M d A lower) (second : stageOneRawTests M d B lower) :
    stageOneRawTests M d (A ∪ B) lower := by
  refine ⟨?_, ?_⟩
  · intro t ht u hu w hw entry
    rcases ZFSet.mem_union.1 entry with entry | entry
    · exact first.1 t ht u hu w hw entry
    · exact second.1 t ht u hu w hw entry
  · intro t ht u hu u' hu' w hw w' hw' entry entry'
    rcases ZFSet.mem_union.1 entry with entry | entry
    · rcases ZFSet.mem_union.1 entry' with entry' | entry'
      · exact first.2 t ht u hu u' hu' w hw w' hw' entry entry'
      · exact first.2 t ht u hu u' hu' w hw w' hw' entry
          ((agreement t ⟨u, w, entry⟩ ⟨u', w', entry'⟩ u' w').2 entry')
    · rcases ZFSet.mem_union.1 entry' with entry' | entry'
      · exact second.2 t ht u hu u' hu' w hw w' hw' entry
          ((agreement t ⟨u', w', entry'⟩ ⟨u, w, entry⟩ u' w').1 entry')
      · exact second.2 t ht u hu u' hu' w hw w' hw' entry entry'





def stageOneRawCrossCollisions (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (A B lower : ZFSet.{u}) : Prop :=
  ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ u' ∈ d 6, ∀ w ∈ d 6, ∀ w' ∈ d 6,
    stageOneAssignment t u w ∈ A → stageOneAssignment t u' w' ∈ B →
    stageOneRawCollision M d t u u' w w' lower ∧
      stageOneRawCollision M d t u' u w' w lower

theorem stageOneRawTests_mixed_union (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    {A B lower : ZFSet.{u}} (first : stageOneRawTests M d A lower)
    (second : stageOneRawTests M d B lower)
    (cross : stageOneRawCrossCollisions M d A B lower) :
    stageOneRawTests M d (A ∪ B) lower := by
  refine ⟨?_, ?_⟩
  · intro t ht u hu w hw entry
    exact (ZFSet.mem_union.1 entry).elim
      (first.1 t ht u hu w hw) (second.1 t ht u hu w hw)
  · intro t ht u hu u' hu' w hw w' hw' entry entry'
    rcases ZFSet.mem_union.1 entry with entry | entry
    · rcases ZFSet.mem_union.1 entry' with entry' | entry'
      · exact first.2 t ht u hu u' hu' w hw w' hw' entry entry'
      · exact (cross t ht u hu u' hu' w hw w' hw' entry entry').1
    · rcases ZFSet.mem_union.1 entry' with entry' | entry'
      · exact (cross t ht u' hu' u hu w' hw' w hw entry' entry).2
      · exact second.2 t ht u hu u' hu' w hw w' hw' entry entry'





theorem assignment_representative_agreement {I T X A C : ZFSet.{u}}
    (first : A ⊆ stageOneAssignments I T) (second : C ⊆ stageOneAssignments I T)
    (contained : assignmentIndices I T C ⊆ X)
    (exactLists : assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T C =
      assignmentOnIndices X T A) : AssignmentIndexAgreement C A := by
  intro t atC atA
  obtain ⟨uC, wC, entryC⟩ := atC
  obtain ⟨uA, wA, entryA⟩ := atA
  have fieldsC := (stageOneAssignment_mem_assignments I T t uC wC).1 (second entryC)
  have fieldsA := (stageOneAssignment_mem_assignments I T t uA wA).1 (first entryA)
  have inX : t ∈ X := contained ((mem_assignmentIndices I T C t).2
    ⟨fieldsC.1, uC, fieldsC.2.1, wC, fieldsC.2.2, entryC⟩)
  have inQuery : t ∈ assignmentIndices I T (assignmentOnIndices X T A) := by
    rw [assignmentIndices_on, ZFSet.mem_inter]
    exact ⟨(mem_assignmentIndices I T A t).2
      ⟨fieldsA.1, uA, fieldsA.2.1, wA, fieldsA.2.2, entryA⟩, inX⟩
  intro u w
  constructor
  · intro entry
    have fields := (stageOneAssignment_mem_assignments I T t u w).1 (second entry)
    have selected := (assignmentOnIndices_entry _ T C t u w).2
      ⟨entry, inQuery, fields.2.1, fields.2.2⟩
    rw [exactLists] at selected
    exact ((assignmentOnIndices_entry X T A t u w).1 selected).1
  · intro entry
    have fields := (stageOneAssignment_mem_assignments I T t u w).1 (first entry)
    have selected := (assignmentOnIndices_entry X T A t u w).2
      ⟨entry, inX, fields.2.1, fields.2.2⟩
    rw [← exactLists] at selected
    exact ((assignmentOnIndices_entry _ T C t u w).1 selected).1

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

private noncomputable def classSelectionDefinition (phi : SetFormula 7) :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      ZFSet.sep (fun z => Realize M.sets phi (extend z ![env 0, env 1, env 2, env 3, env 4, env 5]))
        (ZFSet.prod (env 0) (M.groundRelations (env 2) (env 3)))) := by
  let v := GroundSetTerm.var M (n := 6)
  let names := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 2, v 3]
  let bound := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 0, names]
  let term := GroundSetTerm.app (M.definable_separation separation phi)
    ![bound, v 0, v 1, v 2, v 3, v 4, v 5]
  refine term.definition.congr ?_
  intro env
  apply congrArg (fun params : Fin 6 → ZFSet.{u} => ZFSet.sep
    (fun z => Realize M.sets phi (extend z params))
      (ZFSet.prod (env 0) (M.groundRelations (env 2) (env 3))))
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j

noncomputable def definable_assignmentClassGraph (side : Fin 2) :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      M.assignmentClassGraph side (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  unfold assignmentClassGraph
  exact classSelectionDefinition M pairing unions powers separation _

noncomputable def definable_assignmentOnIndices :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} =>
      assignmentOnIndices (env 0) (env 1) (env 2)) := by
  let v := GroundSetTerm.var M (n := 3)
  let pairs := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 1, v 1]
  let assignments := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 0, pairs]
  let term := GroundSetTerm.app (M.definable_separation separation (.mem 0 1)) ![v 2, assignments]
  exact term.definition

noncomputable def storedAssignmentClassGraph (A : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u}) (side : Fin 2) : ZFSet.{u} :=
  M.assignmentClassGraph side (assignmentOnIndices (fields 0) (fields 6) A)
    (fields (Fin.cases 5 (fun _ => 4) side)) (fields 6) (fields 7) (fields 8) (fields 9)

noncomputable def definable_storedAssignmentClassGraph (side : Fin 2) :
    GroundDefinableFunction M (fun env : Fin 16 → ZFSet.{u} =>
      M.storedAssignmentClassGraph (env 0) (fun j => env j.succ) side) := by
  let v := GroundSetTerm.var M (n := 16)
  let selected := GroundSetTerm.app (M.definable_assignmentOnIndices pairing unions powers separation)
    ![v 1, v 7, v 0]
  let term := GroundSetTerm.app (M.definable_assignmentClassGraph pairing unions powers separation side)
    ![selected, v (Fin.cases 6 (fun _ => 5) side), v 7, v 8, v 9, v 10]
  refine term.definition.congr ?_
  intro env
  have shift : (Fin.cases 6 (fun _ => 5) side : Fin 16) =
      (Fin.cases 5 (fun _ => 4) side : Fin 15).succ :=
    Fin.cases rfl (fun _ => rfl) side
  change M.assignmentClassGraph side (assignmentOnIndices (env 1) (env 7) (env 0))
    (env (Fin.cases 6 (fun _ => 5) side)) (env 7) (env 8) (env 9) (env 10) =
    M.assignmentClassGraph side (assignmentOnIndices (env 1) (env 7) (env 0))
      (env (Fin.cases 5 (fun _ => 4) side : Fin 15).succ) (env 7) (env 8) (env 9) (env 10)
  rw [shift]

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def storedPreparationRequests (A : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u}) : ZFSet.{u} :=
  let selected := assignmentOnIndices (fields 0) (fields 6) A
  relationImage selected (fields 14) (M.storedAssignmentClassGraph A fields 0) ∪
    relationImage selected (fields 14) (M.storedAssignmentClassGraph A fields 1)

private noncomputable def relationImageDefinition (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} =>
      relationImage (env 0) (env 1) (env 2)) where
  formula := (BoundedFormula.relationImageEqualityFormula 0 1 2 3).toFormula
  closed := fun _ members => M.relationImage_mem separation (members 0) (members 1) (members 2)
  correct := by
    intro env members z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
      BoundedFormula.truth_relationImageEqualityFormula]
    rfl

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_storedPreparationRequests :
    GroundDefinableFunction M (fun env : Fin 16 → ZFSet.{u} =>
      M.storedPreparationRequests (env 0) (fun j => env j.succ)) := by
  let v := GroundSetTerm.var M (n := 16)
  let selected := GroundSetTerm.app (M.definable_assignmentOnIndices pairing unions powers separation)
    ![v 1, v 7, v 0]
  let graph (side : Fin 2) := GroundSetTerm.app
    (M.definable_storedAssignmentClassGraph pairing unions powers separation side) v
  let image (side : Fin 2) := GroundSetTerm.app (relationImageDefinition M separation)
    ![selected, v 15, graph side]
  exact (GroundSetTerm.app (M.definable_binaryUnion pairing unions) ![image 0, image 1]).definition

include pairing unions powers separation in
theorem storedPreparationRequests_mem {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (fields : Fin 15 → ZFSet.{u}) (members : ∀ j, fields j ∈ M.sets) :
    M.storedPreparationRequests A fields ∈ M.sets :=
  (M.definable_storedPreparationRequests pairing unions powers separation).closed
    (extend A fields) (Fin.cases hA members)

theorem storedPreparationRequests_typed {G P L : Type u}
    [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (A : ZFSet.{u}) :
    M.storedPreparationRequests A (M.refinementLevelFormulaData a s b d level T T2 valid) =
      let selected := assignmentOnIndices (M.niceRefinementIndices a s b d level T T2 valid) T A
      let graphs := M.niceAssignmentClassGraphs a s b d level T T2 valid selected
      relationImage selected (M.groundRelations T s.carrier) (graphs 0) ∪
        relationImage selected (M.groundRelations T s.carrier) (graphs 1) := rfl

end PartitionPilot.Forcing.TransitiveGround

end OAI
