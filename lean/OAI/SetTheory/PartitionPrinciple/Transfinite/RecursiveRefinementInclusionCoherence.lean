import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRowCompleteProjection

namespace OAI

section

namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha beta : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (middleOrdinal : ordinalSetProperty alpha)
variable (lowerOrdinal : ordinalSetProperty beta) (subset : alpha ⊆ stages) (below : beta ⊆ alpha)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (hAlpha : alpha ∈ M.sets) (hBeta : beta ∈ M.sets) (hRows : rows ∈ M.sets)
variable (top : ZFSet.{u}) (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder)
variable (mono : ∀ level (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair level (refinementFormulaDataCode d) ∈ history →
    ∀ A lower stronger, stageOneRawTests M d A lower →
      ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "V" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
local notation "W" => M.refinementHistoryForcing rows T beta (graphRestriction beta history)
local notation "nestedW" => M.refinementHistoryForcing rows T beta (graphRestriction beta (graphRestriction alpha history))
local notation "first" => inclusionFunction (run.restrict middleOrdinal subset) middleOrdinal lowerOrdinal below
  pairing unions powers separation infinite choice hAlpha (M.graphRestriction_mem unions separation hAlpha hHistory)
  hT hBeta hRows top topMem topRows
  (fun level d entry => mono level d (And.left (Iff.mp pair_mem_graphRestriction entry)))
local notation "second" => run.inclusionFunction ordinal middleOrdinal subset
  pairing unions powers separation infinite choice hStages hHistory hT hAlpha hRows top topMem topRows mono
local notation "direct" => run.inclusionFunction ordinal lowerOrdinal (fun _ h => subset (below h))
  pairing unions powers separation infinite choice hStages hHistory hT hBeta hRows top topMem topRows mono

theorem inclusionFunction_graph_comp :
    relationCompose W V U
      ((SetMembers.presentation nestedW).graph (SetMembers.presentation V) first)
      ((SetMembers.presentation V).graph (SetMembers.presentation U) second) =
      (SetMembers.presentation W).graph (SetMembers.presentation U) direct := by
  have firstCode := (run.restrict middleOrdinal subset).inclusionFunction_raw middleOrdinal lowerOrdinal below
    pairing unions powers separation infinite choice hAlpha (M.graphRestriction_mem unions separation hAlpha hHistory)
    hT hBeta hRows top topMem topRows
    (fun level d entry => mono level d (And.left (Iff.mp pair_mem_graphRestriction entry)))
  have directCode := run.inclusionFunction_raw ordinal lowerOrdinal (fun _ h => subset (below h))
    pairing unions powers separation infinite choice hStages hHistory hT hBeta hRows top topMem topRows mono
  have intoMiddle (x : ZFSet.{u}) (member : x ∈ W) : x ∈ V := by
    have nested : x ∈ nestedW := by rwa [graphRestriction_restrict below]
    let p := SetMembers.ofMem x nested
    have mem := SetMembers.raw_mem (first p)
    rwa [firstCode p, SetMembers.raw_ofMem] at mem
  have intoUpper (x : ZFSet.{u}) (member : x ∈ W) : x ∈ U := by
    let p := SetMembers.ofMem x member
    have mem := SetMembers.raw_mem (direct p)
    rwa [directCode p, SetMembers.raw_ofMem] at mem
  rw [(run.restrict middleOrdinal subset).inclusionFunction_graph, run.inclusionFunction_graph,
    run.inclusionFunction_graph, graphRestriction_restrict below]
  apply ZFSet.ext
  intro z
  rw [mem_relationCompose, mem_identityFunctionGraph]
  constructor
  · rintro ⟨x, hx, y, _, w, _, rfl, firstEdge, secondEdge⟩
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph W x y).1 firstEdge
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph V x w).1 secondEdge
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, x, intoMiddle x hx, x, intoUpper x hx, rfl,
      (pair_mem_identityFunctionGraph W x x).2 ⟨rfl, hx⟩,
      (pair_mem_identityFunctionGraph V x x).2 ⟨rfl, intoMiddle x hx⟩⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

end

end OAI
