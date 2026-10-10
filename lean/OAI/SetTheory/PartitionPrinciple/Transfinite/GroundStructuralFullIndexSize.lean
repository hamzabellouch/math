import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStructuralForcingHistoryConstruction
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRepresentativeIndexSteps
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRefinementFullIndexSize

namespace OAI

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {A B N K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem smallSubsets (hB : B ∈ M.sets) (hN : N ∈ M.sets) (hK : K ∈ M.sets)
    (strong : GroundStrongLimit M K) (small : GroundBelow M B K) :
    GroundBelow M (M.groundSmallSubsets B N) K :=
  (strong.power_closed pairing unions powers separation hB hK small).restrict
    separation (M.groundSmallSubsets_mem powers separation hB hN) hK
    (fun _ member => (ZFSet.mem_sep.1 member).1)

theorem smallPartialFunctions (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hN : N ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (first : GroundBelow M A K) (second : GroundBelow M B K) :
    GroundBelow M (M.smallPartialFunctions A B N) K :=
  (partialFunctions pairing unions powers separation hA hB hK ordinal strong first second).restrict
    separation (M.smallPartialFunctions_mem pairing unions powers separation hA hB hN) hK
    (fun _ member => (ZFSet.mem_sep.1 member).1)

end PartitionPilot.Forcing.GroundBelow

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {I C K : ZFSet.{u}}

theorem binaryRowCarrier
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    (indices : GroundBelow M I K) (columns : GroundBelow M C K) :
    GroundBelow M (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega) K := by
  have hOmega := M.transitive hK conditions.2.1
  have hTwo := M.transitive hOmega (natSetCode_mem_omega 2)
  have twoBelow := of_member pairing unions powers separation hK
    (conditions.1.1 ZFSet.omega conditions.2.1 _ (natSetCode_mem_omega 2))
  exact smallPartialFunctions pairing unions powers separation
    (M.prod_mem pairing unions powers separation hI hC) hTwo hOmega hK
    conditions.1 conditions.2.2.2
    (product pairing unions powers separation hI hC hK conditions.1 conditions.2.2.2 indices columns)
    twoBelow

end PartitionPilot.Forcing.GroundBelow

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets)

open scoped ZFSet

include pairing unions powers separation in
theorem refinementDataHistoryIndexFamily {stages history T : ZFSet.{u}}
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (valid : RefinementDataHistory stages history T) :
    let F := refinementDataHistoryField stages history 0
    F ∈ M.sets ∧ functionGraphRange stages F ∈ M.sets ∧
      ZFSet.IsFunc stages (⋃₀ ⋃₀ F) F ∧
      refinementDataHistoryIndices stages history =
        ⋃₀ relationImage stages (⋃₀ ⋃₀ F) F := by
  let F := refinementDataHistoryField stages history 0
  have hF : F ∈ M.sets :=
    M.refinementDataHistoryField_mem pairing unions powers separation hStages hHistory 0
  exact ⟨hF, M.functionGraphRange_mem unions separation hStages hF,
    valid.index_function.to_isFunc, rfl⟩

include pairing unions powers separation in
theorem refinementDataHistoryIndices_below {stages history T K : ZFSet.{u}}
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (strong : GroundStrongLimit M K) (stageSize : GroundBelow M stages K)
    (valid : RefinementDataHistory stages history T)
    (fibers : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history → GroundBelow M (d 0) K) :
    GroundBelow M (refinementDataHistoryIndices stages history) K := by
  obtain ⟨hF, _hRange, function, union_eq⟩ :=
    M.refinementDataHistoryIndexFamily pairing unions powers separation hStages hHistory valid
  rw [union_eq]
  apply GroundBelow.indexed_sUnion pairing unions powers separation choice hStages
    (M.union_mem unions (M.union_mem unions hF)) hF hK ordinal regular strong stageSize function
  intro beta A entry
  obtain ⟨_, d, stored, rfl⟩ :=
    (pair_mem_refinementDataHistoryField stages history beta A 0).1 entry
  exact fibers beta d stored

include pairing unions powers separation in
theorem refinementDataHistoryIndices_below_of_mem {stages history T K : ZFSet.{u}}
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hHistory : history ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (strong : GroundStrongLimit M K) (stageMem : stages ∈ K)
    (valid : RefinementDataHistory stages history T)
    (fibers : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history → GroundBelow M (d 0) K) :
    GroundBelow M (refinementDataHistoryIndices stages history) K :=
  M.refinementDataHistoryIndices_below pairing unions powers separation choice
    (M.transitive hK stageMem) hHistory hK ordinal regular strong
    (GroundBelow.of_member pairing unions powers separation hK stageMem) valid fibers

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows I T stages history K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem stageOneAssignments (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (indices : GroundBelow M I K) (terms : GroundBelow M T K) :
    GroundBelow M (PartitionPilot.Forcing.stageOneAssignments I T) K :=
  product pairing unions powers separation hI
    (M.prod_mem pairing unions powers separation hT hT) hK ordinal strong indices
    (product pairing unions powers separation hT hT hK ordinal strong terms terms)

theorem stageOneCandidateBound (hRows : rows ∈ M.sets) (hI : I ∈ M.sets)
    (hT : T ∈ M.sets) (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (rowSize : GroundBelow M rows K) (indices : GroundBelow M I K)
    (terms : GroundBelow M T K) : GroundBelow M (M.stageOneCandidateBound rows I T) K :=
  product pairing unions powers separation hRows
    (M.groundSmallSubsets_mem powers separation
      (M.stageOneAssignments_mem pairing unions powers separation hI hT) omega)
    hK ordinal strong rowSize
    (smallSubsets pairing unions powers separation
      (M.stageOneAssignments_mem pairing unions powers separation hI hT) omega hK strong
      (stageOneAssignments pairing unions powers separation hI hT hK ordinal strong indices terms))

theorem refinementHistoryForcing (hRows : rows ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (rowSize : GroundBelow M rows K)
    (indices : GroundBelow M (refinementDataHistoryIndices stages history) K)
    (terms : GroundBelow M T K) :
    GroundBelow M (M.refinementHistoryForcing rows T stages history) K :=
  (stageOneCandidateBound pairing unions powers separation hRows
    (M.refinementDataHistoryIndices_mem pairing unions powers separation hStages hHistory)
    hT hK omega ordinal strong rowSize indices terms).restrict separation
    (M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hHistory omega) hK
    (fun z member => ((M.mem_refinementHistoryForcing rows T stages history z).1 member).1)

end PartitionPilot.Forcing.GroundBelow

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (collection : CollectionSchema M.sets)
variable {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (G nodes nodeOrder basis T T2 : ZFSet.{u})
variable (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
variable (hb : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
variable (smallNodes : GroundBelow M nodes K) (smallT : GroundBelow M T K)
variable (smallT2 : GroundBelow M T2 K)
include pairing unions powers separation infinite collection hK conditions
include hG hn hno hb hT hT2 smallNodes smallT smallT2

theorem structuralRefinement_stored_indices_below
    {history level P order top action : ZFSet.{u}} (hh : history ∈ M.sets)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (smallP : GroundBelow M P K) :
    M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0 ∈ M.sets ∧
      GroundBelow M (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) K := by
  have fields := M.nonemptyTupleCode_field_mem 4 ![level, P, order, top, action]
    (M.transitive hh stored)
  exact M.rawRefinementFormulaData_indices_below pairing unions powers separation infinite hK conditions collection
    P order top action G nodes nodeOrder basis T T2 level
    (fields 1) (fields 2) (fields 3) (fields 4) hG hn hno hb hT hT2 (fields 0)
    smallP smallNodes smallT smallT2

theorem structuralRefinementHistory_indices_below
    {stages history level : ZFSet.{u}} (hh : history ∈ M.sets)
    (data : Fin 15 → ZFSet.{u})
    (entry : ZFSet.pair level (refinementFormulaDataCode data) ∈
      M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)
    (smallCarrier : GroundBelow M (data 7) K) :
    data 0 ∈ M.sets ∧ GroundBelow M (data 0) K := by
  obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
    M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
  exact M.structuralRefinement_stored_indices_below pairing unions powers separation infinite collection hK conditions
    G nodes nodeOrder basis T T2 hG hn hno hb hT hT2 smallNodes smallT smallT2 hh stored smallCarrier

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

open scoped ZFSet

theorem representativeIndexStep_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows I T Q c D X K : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hQ : Q ∈ M.sets) (hc : c ∈ M.sets) (hD : D ∈ M.sets) (hX : X ∈ M.sets)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (selector : ZFSet.IsFunc Q D c)
    (queries : Q ⊆ M.stageOneCandidateBound rows I T)
    (selected : D ⊆ M.stageOneCandidateBound rows I T)
    (smallRows : GroundBelow M rows K) (smallT : GroundBelow M T K)
    (smallX : GroundBelow M X K) :
    GroundBelow M (representativeIndexStep I T Q c X) K := by
  let QX := assignmentQueriesWithin Q X T
  let E := relationImage QX D c
  let J := stageOneAssignments I T
  let S := M.groundSmallSubsets J ZFSet.omega
  let projection := productSecond rows S
  let R := relationImage E S projection
  let U := ⋃₀ R
  have omega := M.omega_mem separation infinite
  have hQX : QX ∈ M.sets := M.assignmentQueriesWithin_mem separation hQ hX hT
  have queryBound : QX ⊆ M.stageOneCandidateBound rows X T := by
    intro q member
    obtain ⟨hq, row, L, rfl, inside⟩ := (mem_assignmentQueriesWithin Q X T q).1 member
    obtain ⟨hr, hL, _, countable⟩ := (M.pair_mem_stageOneCandidateBound rows I T row L).1 (queries hq)
    exact (M.pair_mem_stageOneCandidateBound rows X T row L).2 ⟨hr, hL, inside, countable⟩
  have smallQX : GroundBelow M QX K :=
    (GroundBelow.stageOneCandidateBound pairing unions powers separation hRows hX hT hK omega
      conditions.1 conditions.2.2.2 smallRows smallX smallT).restrict separation hQX hK queryBound
  have hE : E ∈ M.sets := M.relationImage_mem separation hQX hD hc
  have smallE : GroundBelow M E K := smallQX.function_image pairing unions powers separation choice
    hQX hD hK hc selector
  have hJ : J ∈ M.sets := M.stageOneAssignments_mem pairing unions powers separation hI hT
  have hS : S ∈ M.sets := M.groundSmallSubsets_mem powers separation hJ omega
  have hProjection : projection ∈ M.sets := M.productSecond_mem pairing unions powers separation hRows hS
  have hR : R ∈ M.sets := M.relationImage_mem separation hE hS hProjection
  have hU : U ∈ M.sets := M.union_mem unions hR
  have smallR : GroundBelow M R K := smallE.function_image pairing unions powers separation choice
    hE hS hK hProjection (productSecond_function rows S)
  have smallU : GroundBelow M U K := GroundBelow.sUnion pairing unions powers separation choice
    hR hK conditions.1 conditions.2.2.1 conditions.2.2.2 smallR (fun A member =>
      GroundBelow.of_countable conditions.2.1 ((M.mem_groundSmallSubsets J ZFSet.omega A).1
        ((mem_relationImage E S projection A).1 member).1).2.2)
  have smallIndices : GroundBelow M (assignmentIndices I T U) K :=
    smallU.function_image pairing unions powers separation choice hU hI hK
      (M.productFirst_mem pairing unions powers separation hI
        (M.prod_mem pairing unions powers separation hT hT)) (productFirst_function I (ZFSet.prod T T))
  have additionsGround := M.representativeIndexAdditions_mem separation hI hT hQ hc hX
  have additionsSubset : representativeIndexAdditions I T Q c X ⊆ assignmentIndices I T U := by
    intro i member
    obtain ⟨hi, q, hq, within, row, A, entry, v, hv, w, hw, inside⟩ :=
      (mem_representativeIndexAdditions I T Q c X i).1 member
    have inD := (ZFSet.pair_mem_prod.1 (selector.1 entry)).2
    have candidate := selected inD
    have pair : row ∈ rows ∧ A ∈ S := ZFSet.pair_mem_prod.1 candidate
    have inE : ZFSet.pair row A ∈ E := (mem_relationImage QX D c _).2
      ⟨inD, q, (mem_assignmentQueriesWithin Q X T q).2 ⟨hq, within⟩, entry⟩
    have inR : A ∈ R := (mem_relationImage E S projection A).2
      ⟨pair.2, ZFSet.pair row A, inE,
        (mem_productSecond rows S _).2 ⟨row, pair.1, A, pair.2, rfl⟩⟩
    exact (mem_assignmentIndices I T U i).2
      ⟨hi, v, hv, w, hw, ZFSet.mem_sUnion.2 ⟨A, inR, inside⟩⟩
  exact GroundBelow.binary_union pairing unions powers separation infinite choice hX additionsGround hK
    conditions.2.1 conditions.1 conditions.2.2.1 conditions.2.2.2 smallX
    (smallIndices.restrict separation additionsGround hK additionsSubset)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem structuralIndexFamily_below
    (G nodes nodeOrder basis T T2 : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hG : G ∈ M.sets) (hNodes : nodes ∈ M.sets) (hNodeOrder : nodeOrder ∈ M.sets)
    (hBasis : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    {stages history K : ZFSet.{u}} (hHistory : history ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (strong : GroundStrongLimit M K) (stageMem : stages ∈ K)
    (valid : RefinementDataHistory stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) T)
    (fibers : ∀ beta P order top action,
      ZFSet.pair beta (forcingStageCode P order top action) ∈ history →
        GroundBelow M (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 beta 0) K) :
    GroundBelow M (refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)) K := by
  have hStages := M.transitive hK stageMem
  have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![G, nodes, nodeOrder, basis, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hNodes (Fin.cases hNodeOrder (Fin.cases hBasis
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hStages (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
  apply M.refinementDataHistoryIndices_below_of_mem pairing unions powers separation choice
    packed hK ordinal regular strong stageMem valid
  intro beta data entry
  obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
    M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
  exact fibers beta P order top action stored

theorem structuralForcingTrace_indices_below
    (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hG : G ∈ M.sets) (hNodes : nodes ∈ M.sets) (hNodeOrder : nodeOrder ∈ M.sets)
    (hBasis : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    {stages history K : ZFSet.{u}} (hHistory : history ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (strong : GroundStrongLimit M K) (stageMem : stages ∈ K)
    (trace : OrdinalRecursionTrace
      (fun level prior stage => stage = M.structuralForcingStage rows rowOrder rowTop rowAction
        G nodes nodeOrder nodeAction basis T T2 level prior) stages history)
    (fibers : ∀ beta P order top action,
      ZFSet.pair beta (forcingStageCode P order top action) ∈ history →
        GroundBelow M (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 beta 0) K) :
    GroundBelow M (refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)) K := by
  have run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 (ordinalSetProperty_member ordinal stageMem) trace
  exact M.structuralIndexFamily_below G nodes nodeOrder basis T T2 pairing unions powers separation
    collection choice hG hNodes hNodeOrder hBasis hT hT2 hHistory hK ordinal regular strong
    stageMem run.carriers.data fibers

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (collection : CollectionSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hRows : rows ∈ M.sets) (hG : G ∈ M.sets) (hn : nodes ∈ M.sets)
variable (hno : nodeOrder ∈ M.sets) (hb : basis ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
variable {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (smallRows : GroundBelow M rows K) (smallNodes : GroundBelow M nodes K)
variable (smallT : GroundBelow M T K) (smallT2 : GroundBelow M T2 K)
include pairing unions powers separation infinite collection choice hRows hG hn hno hb hT hT2
  hK conditions smallRows smallNodes smallT smallT2
local notation "step" => fun level prior stage => stage =
  M.structuralForcingStage rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 level prior

theorem structuralForcingTrace_below :
    ∀ stages ∈ K, ∀ history ∈ M.sets, OrdinalRecursionTrace step stages history →
      GroundBelow M (refinementDataHistoryIndices stages
        (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)) K ∧
      GroundBelow M (M.refinementHistoryForcing rows T stages
        (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)) K := by
  intro stages
  induction stages using ZFSet.inductionOn with
  | h stages ih =>
    intro stageMem history hh trace
    have hs := M.transitive hK stageMem
    have ordinal := ordinalSetProperty_member conditions.1 stageMem
    have fibers : ∀ beta P order top action,
        ZFSet.pair beta (forcingStageCode P order top action) ∈ history →
        GroundBelow M (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 beta 0) K := by
      intro beta P order top action stored
      have member := trace.1.pair_source stored
      have hBeta := M.transitive hs member
      have betaOrdinal := ordinalSetProperty_member ordinal member
      have lower := ih beta member (conditions.1.1 stages stageMem beta member)
        (graphRestriction beta history) (M.graphRestriction_mem unions separation hBeta hh)
        (trace.restrict betaOrdinal (ordinal.1 beta member))
      have equal := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1
        ((trace.2 beta member _ stored).trans
          (M.structuralForcingStage_eq rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2
            beta (graphRestriction beta history)))
      have smallP : GroundBelow M P K := equal.1.symm ▸ lower.2
      exact (M.structuralRefinement_stored_indices_below pairing unions powers separation infinite collection
        hK conditions G nodes nodeOrder basis T T2 hG hn hno hb hT hT2 smallNodes smallT smallT2
        hh stored smallP).2
    have indices := M.structuralForcingTrace_indices_below rows rowOrder rowTop rowAction G nodes
      nodeOrder nodeAction basis T T2 pairing unions powers separation collection choice
      hG hn hno hb hT hT2 hh hK conditions.1 conditions.2.2.1 conditions.2.2.2 stageMem trace fibers
    have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![G, nodes, nodeOrder, basis, T, T2, stages, history]
      (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT (Fin.cases hT2
        (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
    exact ⟨indices, GroundBelow.refinementHistoryForcing pairing unions powers separation
      hRows hT hs packed hK (M.omega_mem separation infinite) conditions.1 conditions.2.2.2
      smallRows indices smallT⟩

theorem structuralForcingTrace_prefix_below {history : ZFSet.{u}} (hh : history ∈ M.sets)
    (trace : OrdinalRecursionTrace step K history) :
    ∀ level ∈ K,
      GroundBelow M (refinementDataHistoryIndices level
        (graphRestriction level (M.structuralRefinementHistory G nodes nodeOrder basis T T2 K history))) K ∧
      GroundBelow M (M.refinementHistoryForcing rows T level
        (graphRestriction level (M.structuralRefinementHistory G nodes nodeOrder basis T T2 K history))) K := by
  intro level member
  have hLevel := M.transitive hK member
  have ordinal := ordinalSetProperty_member conditions.1 member
  have result := M.structuralForcingTrace_below rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction
    basis T T2 pairing unions powers separation infinite collection choice hRows hG hn hno hb hT hT2
    hK conditions smallRows smallNodes smallT smallT2 level member (graphRestriction level history)
    (M.graphRestriction_mem unions separation hLevel hh)
    (trace.restrict ordinal (conditions.1.1 level member))
  rw [M.structuralRefinementHistory_history_restrict,
    M.structuralRefinementHistory_domain_restrict G nodes nodeOrder basis T T2 (conditions.1.1 level member)] at result
  exact result

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (collection : CollectionSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hRows : rows ∈ M.sets) (hG : G ∈ M.sets) (hn : nodes ∈ M.sets)
variable (hno : nodeOrder ∈ M.sets) (hb : basis ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
variable {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (smallRows : GroundBelow M rows K) (smallNodes : GroundBelow M nodes K)
variable (smallT : GroundBelow M T K) (smallT2 : GroundBelow M T2 K)
include pairing unions powers separation infinite collection choice hRows hG hn hno hb hT hT2
  hK conditions smallRows smallNodes smallT smallT2
local notation "step" => fun level prior stage => stage =
  M.structuralForcingStage rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 level prior

theorem structuralForcingTrace_indices_embeds {history : ZFSet.{u}}
    (hh : history ∈ M.sets) (trace : OrdinalRecursionTrace step K history) :
    M.groundEmbeddable (refinementDataHistoryIndices K
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 K history)) K := by
  have prefixes := M.structuralForcingTrace_prefix_below rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 pairing unions powers separation infinite collection choice
    hRows hG hn hno hb hT hT2 hK conditions smallRows smallNodes smallT smallT2 hh trace
  have run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 conditions.1 trace
  have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![G, nodes, nodeOrder, basis, T, T2, K, history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT (Fin.cases hT2
      (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  exact M.refinementDataHistoryIndices_embeds pairing unions powers separation infinite collection choice
    hK packed conditions run.carriers.data (fun alpha member => (prefixes alpha member).1)

end PartitionPilot.Forcing.TransitiveGround

end OAI
