import OAI.SetTheory.PartitionPrinciple.Definability.AssignmentQueryFormulas
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralFullIndexSize

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

theorem assignmentOnIndices_indices_on {I T X A : ZFSet.{u}}
    (shape : A ⊆ stageOneAssignments I T) :
    assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T A =
      assignmentOnIndices X T A := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨hA, inside⟩ := (mem_assignmentOnIndices _ T A z).1 member
    obtain ⟨t, ht, v, hv, w, hw, rfl⟩ := (mem_stageOneAssignments _ T z).1 inside
    rw [assignmentIndices_on] at ht
    exact (assignmentOnIndices_entry X T A t v w).2
      ⟨hA, (ZFSet.mem_inter.1 ht).2, hv, hw⟩
  · intro member
    have hA := ((mem_assignmentOnIndices X T A z).1 member).1
    obtain ⟨t, ht, v, hv, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 (shape hA)
    exact (assignmentOnIndices_entry _ T A t v w).2
      ⟨hA, (mem_assignmentIndices I T (assignmentOnIndices X T A) t).2
        ⟨ht, v, hv, w, hw, member⟩, hv, hw⟩

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem assignmentQueryRelation_mem {I T C D : ZFSet.{u}}
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    assignmentQueryRelation I T C D ∈ M.sets := by
  let f := productFirst I (ZFSet.prod T T)
  have hf : f ∈ M.sets := M.productFirst_mem pairing unions powers separation hI
    (M.prod_mem pairing unions powers separation hT hT)
  let params := extend I (extend f Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.assignmentQueryRelationFormula 0 1 2) params
    (Fin.cases hI (Fin.cases hf (fun j => Fin.elim0 j)))
    (M.prod_mem pairing unions powers separation hC hD)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.assignmentQueryRelationFormula 0 1 2) (extend z params))
      (ZFSet.prod C D) = assignmentQueryRelation I T C D := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, assignmentQueryRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_assignmentQueryRelationFormula 0 1 2
      (extend z params) T rfl)
  exact equal ▸ selected

theorem realizedAssignmentQueries_mem {I T C D : ZFSet.{u}}
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    realizedAssignmentQueries I T C D ∈ M.sets :=
  M.relationImage_mem separation hD hC (M.relationConverse_mem pairing unions powers separation
    hC hD (M.assignmentQueryRelation_mem pairing unions powers separation hI hT hC hD))

theorem exists_assignmentQuerySelector
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I T C D : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    ∃ F ∈ M.sets, ZFSet.IsFunc (realizedAssignmentQueries I T C D) D F ∧
      F ⊆ assignmentQueryRelation I T C D := by
  apply M.uniformize_relation pairing unions powers separation choice
    (M.realizedAssignmentQueries_mem pairing unions powers separation hI hT hC hD) hD
    (M.assignmentQueryRelation_mem pairing unions powers separation hI hT hC hD)
  intro q member
  exact ((mem_realizedAssignmentQueries I T C D q).1 member).2

theorem exists_stageOneAssignmentQuerySelector
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows I T D : ZFSet.{u}} (hRows : rows ∈ M.sets) (hI : I ∈ M.sets)
    (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (hD : D ∈ M.sets) :
    ∃ F ∈ M.sets,
      ZFSet.IsFunc (realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D) D F ∧
      F ⊆ assignmentQueryRelation I T (M.stageOneCandidateBound rows I T) D :=
  M.exists_assignmentQuerySelector pairing unions powers separation choice hI hT
    (M.stageOneCandidateBound_mem pairing unions powers separation hRows hI hT omega) hD

end TransitiveGround

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundOmegaOneClosure
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    {n : Nat} {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}
    (defined : GroundDefinableFunction M f) (params : Fin n → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets)
    (inflationary : ∀ X ∈ M.sets, X ⊆ I → X ⊆ f (extend X params))
    (preserves : ∀ X ∈ M.sets, X ⊆ I → GroundBelow M X K →
      f (extend X params) ⊆ I ∧ GroundBelow M (f (extend X params)) K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (fun alpha prior output =>
        output = f (extend (refinementHistoryIndices alpha prior) params)) C history ∧
      let X := refinementHistoryIndices C history
      X ∈ M.sets ∧ X ⊆ I ∧ GroundBelow M X K ∧
      (∀ alpha Y, ZFSet.pair alpha Y ∈ history →
        Y ∈ M.sets ∧ Y ⊆ I ∧ GroundBelow M Y K) ∧
      (∀ alpha beta Y Z, ZFSet.pair alpha Y ∈ history →
        ZFSet.pair beta Z ∈ history → alpha ∈ beta → Y ⊆ Z) ∧
      ∀ B ∈ M.sets, M.groundEmbeddable B ZFSet.omega → B ⊆ X →
        ∃ beta ∈ C,
          let U := refinementHistoryIndices beta history
          U ∈ M.sets ∧ U ⊆ X ∧ GroundBelow M U K ∧ B ⊆ U ∧ f (extend U params) ⊆ X := by
  let C := M.groundOmegaOne pairing unions powers separation collection infinite
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have hC := spec.1
  obtain ⟨history, hh, trace⟩ := M.exists_historyUnionTrace pairing unions separation collection
    defined params members hC spec.2.1
  have bounds := M.historyUnionTrace_below pairing unions powers separation choice hK conditions
    (fun X => f (extend X params)) preserves C
    (conditions.groundOmegaOne_mem pairing unions powers separation collection infinite hK) history hh trace
  let X := refinementHistoryIndices C history
  have hX : X ∈ M.sets := M.refinementHistoryIndices_mem unions separation hC hh
  have step (beta Y : ZFSet.{u}) (entry : ZFSet.pair beta Y ∈ history) :
      Y = f (extend (refinementHistoryIndices beta history) params) := by
    have result := trace.2 beta (trace.1.pair_source entry) Y entry
    change Y = f (extend (refinementHistoryIndices beta (graphRestriction beta history)) params) at result
    rw [refinementHistoryIndices_restrict (fun _ hx => hx)] at result
    exact result
  have earlierUnion (beta : ZFSet.{u}) (member : beta ∈ C) :
      refinementHistoryIndices beta history ∈ M.sets ∧
      refinementHistoryIndices beta history ⊆ X ∧
      GroundBelow M (refinementHistoryIndices beta history) K := by
    have ground := M.refinementHistoryIndices_mem unions separation (M.transitive hC member) hh
    have subset := refinementHistoryIndices_mono (history := history) (spec.2.1.1 beta member)
    exact ⟨ground, subset, bounds.2.2.restrict separation ground hK subset⟩
  refine ⟨history, hh, trace, hX, bounds.2.1, bounds.2.2, ?_, ?_, ?_⟩
  · intro alpha Y entry
    exact ⟨M.transitive (M.union_mem unions (M.union_mem unions hh))
      (pair_second_mem_doubleUnion entry), bounds.1 alpha Y entry⟩
  · intro alpha beta Y Z first second before x inside
    have earlier := earlierUnion beta (trace.1.pair_source second)
    rw [step beta Z second]
    exact inflationary _ earlier.1 (fun _ hx => bounds.2.1 (earlier.2.1 hx))
      ((mem_refinementHistoryIndices beta history x).2 ⟨alpha, before, Y, first, inside⟩)
  · intro B hB small subset
    obtain ⟨beta, member, captured⟩ := M.historyUnion_countable_capture
      pairing unions powers separation collection infinite choice hh hB small subset
    have earlier := earlierUnion beta member
    refine ⟨beta, member, earlier.1, earlier.2.1, earlier.2.2, captured, ?_⟩
    obtain ⟨Y, entry⟩ := trace.1.total member
    rw [← step beta Y entry]
    intro x inside
    exact (mem_refinementHistoryIndices C history x).2 ⟨beta, member, Y, entry, inside⟩

theorem assignmentQueryClosure_representatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows I T D c X : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (hX : X ∈ M.sets)
    (shape : D ⊆ M.stageOneCandidateBound rows I T)
    (selector : ZFSet.IsFunc
      (realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D) D c)
    (selected : c ⊆ assignmentQueryRelation I T (M.stageOneCandidateBound rows I T) D)
    (capture : ∀ B ∈ M.sets, M.groundEmbeddable B ZFSet.omega → B ⊆ X →
      ∃ U, B ⊆ U ∧ representativeIndexStep I T
        (realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D) c U ⊆ X) :
    ∀ row A, ZFSet.pair row A ∈ D →
      ∃ C, ZFSet.pair row C ∈ D ∧ assignmentIndices I T C ⊆ X ∧
        assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T C =
          assignmentOnIndices X T A := by
  intro row A member
  let L := assignmentOnIndices X T A
  let B := assignmentIndices I T L
  let Q := realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D
  have data := (M.pair_mem_stageOneCandidateBound rows I T row A).1 (shape member)
  have hL : L ∈ M.sets := M.assignmentOnIndices_mem pairing unions powers separation hX hT data.2.1
  have smallL := M.assignmentOnIndices_small pairing unions powers separation hX hT data.2.1
    omega data.2.2.2
  have listShape : L ⊆ stageOneAssignments I T :=
    fun _ h => data.2.2.1 ((mem_assignmentOnIndices X T A _).1 h).1
  have queryCandidate : ZFSet.pair row L ∈ M.stageOneCandidateBound rows I T :=
    (M.pair_mem_stageOneCandidateBound rows I T row L).2 ⟨data.1, hL, listShape, smallL⟩
  have query : ZFSet.pair row L ∈ Q :=
    (mem_realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D _).2
      ⟨queryCandidate, ZFSet.pair row A, member,
        (assignmentQueryRelation_entry I T (M.stageOneCandidateBound rows I T) D row L row A).2
          ⟨queryCandidate, member, rfl, assignmentOnIndices_indices_on data.2.2.1⟩⟩
  have hB : B ∈ M.sets := M.assignmentIndices_mem pairing unions powers separation hI hT hL
  have smallB := M.assignmentIndices_small pairing unions powers separation choice hI hT hL omega smallL
  have subsetB : B ⊆ X := by
    intro i hi
    change i ∈ assignmentIndices I T (assignmentOnIndices X T A) at hi
    rw [assignmentIndices_on] at hi
    exact (ZFSet.mem_inter.1 hi).2
  obtain ⟨U, captured, closed⟩ := capture B hB smallB subsetB
  obtain ⟨p, entry, _⟩ := selector.2 (ZFSet.pair row L) query
  have inD := (ZFSet.pair_mem_prod.1 (selector.1 entry)).2
  obtain ⟨other, _, C, _, _, _, rfl⟩ :=
    (M.mem_stageOneCandidateBound rows I T p).1 (shape inD)
  have matched := (assignmentQueryRelation_entry I T (M.stageOneCandidateBound rows I T) D
    row L other C).1 (selected entry)
  obtain rfl := matched.2.2.1
  refine ⟨C, inD, ?_, matched.2.2.2⟩
  have localQuery : AssignmentQueryWithin U T (ZFSet.pair row L) :=
    ⟨row, L, rfl, (assignment_subset_iff_indices_subset listShape).2 captured⟩
  exact fun _ h => closed (representativeIndexStep_covers query localQuery entry h)

theorem exists_assignmentRepresentativeClosure
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows I T D K : ZFSet.{u}} (hRows : rows ∈ M.sets) (hI : I ∈ M.sets)
    (hT : T ∈ M.sets) (hD : D ∈ M.sets) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    (smallRows : GroundBelow M rows K) (smallT : GroundBelow M T K)
    (shape : D ⊆ M.stageOneCandidateBound rows I T) :
    ∃ X ∈ M.sets, X ⊆ I ∧ GroundBelow M X K ∧
      ∀ row A, ZFSet.pair row A ∈ D →
        ∃ C, ZFSet.pair row C ∈ D ∧ assignmentIndices I T C ⊆ X ∧
          assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T C =
            assignmentOnIndices X T A := by
  have omega := M.omega_mem separation infinite
  let Q := realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D
  have hQ : Q ∈ M.sets := M.realizedAssignmentQueries_mem pairing unions powers separation hI hT
    (M.stageOneCandidateBound_mem pairing unions powers separation hRows hI hT omega) hD
  have queries : Q ⊆ M.stageOneCandidateBound rows I T :=
    fun _ h => ((mem_realizedAssignmentQueries I T (M.stageOneCandidateBound rows I T) D _).1 h).1
  obtain ⟨c, hc, selector, selected⟩ := M.exists_stageOneAssignmentQuerySelector
    pairing unions powers separation choice hRows hI hT omega hD
  let params : Fin 4 → ZFSet.{u} := extend I (extend T (extend Q (extend c Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hI (Fin.cases hT (Fin.cases hQ (Fin.cases hc (fun j => Fin.elim0 j))))
  have inflationary : ∀ X ∈ M.sets, X ⊆ I →
      X ⊆ representativeIndexStep I T Q c X :=
    fun X _ _ => representativeIndexStep_contains I T Q c X
  have preserves : ∀ X ∈ M.sets, X ⊆ I → GroundBelow M X K →
      representativeIndexStep I T Q c X ⊆ I ∧
        GroundBelow M (representativeIndexStep I T Q c X) K := by
    intro X hX subset smallX
    exact ⟨representativeIndexStep_subset subset,
      M.representativeIndexStep_below pairing unions powers separation infinite choice
        hRows hI hT hQ hc hD hX hK conditions selector queries shape smallRows smallT smallX⟩
  obtain ⟨history, _, _, hX, subsetX, smallX, _, _, capture⟩ :=
    M.exists_groundOmegaOneClosure pairing unions powers separation collection infinite choice
      hK conditions (M.definable_representativeIndexStep pairing unions separation)
      params members inflationary preserves
  refine ⟨_, hX, subsetX, smallX,
    M.assignmentQueryClosure_representatives pairing unions powers separation choice
      hI hT omega hX shape selector selected ?_⟩
  intro B hB countable subset
  obtain ⟨beta, _, _, _, _, bounded, closed⟩ := capture B hB countable subset
  exact ⟨refinementHistoryIndices beta history, bounded, closed⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
