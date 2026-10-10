import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementVisibleLiftInsertions

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (small : M.sets.Countable)
variable (C E : L) (U R : (M.nameDomain s).names)
variable (member : (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val) ∈ M.niceRefinementIndices a s b d level T T2 valid)
include pairing unions powers separation collection carrier order nodes hT indices system small member

theorem stageTwoConditions_insert_diagonal
    (infinite : Realize M.sets infinity Fin.elim0)
    {rows I levels stages row A : ZFSet.{u}} (hI : I ∈ M.sets)
    (function : ZFSet.IsFunc (stageOneAssignments I T) stages levels)
    (u : (M.nameDomain s).names) (term : u.val.val ∈ T)
    (atLevel : ZFSet.pair (stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val) u.val.val u.val.val) level ∈ levels)
    (old : ZFSet.pair row A ∈ M.stageTwoConditions rows I levels level (M.refinementLevelFormulaData a s b d level T T2 valid))
    (p : P) (encoded : s.encode p = ZFSet.pair row (assignmentCut levels level A))
    (diagonal : ∀ v ∈ T, ∀ z ∈ T, stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val) v z ∈ A → v = z)
    (active : Name.ForcesMem p u.val U.val) :
    ZFSet.pair row (insert (stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val) u.val.val u.val.val) A) ∈
      M.stageTwoConditions rows I levels level (M.refinementLevelFormulaData a s b d level T T2 valid) ∧
    assignmentCut levels level (insert (stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val) u.val.val u.val.val) A) =
      assignmentCut levels level A := by
  have oldTests := ((M.pair_mem_stageTwoConditions rows I levels level (M.refinementLevelFormulaData a s b d level T T2 valid) row A).1 old).2.2.2.2.2
  rw [← encoded] at oldTests
  have inserted := M.refinementLevelRawTests_insert_diagonal a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system small C E U R member p oldTests diagonal u term active
  have obligations := (stageOneRawTests_insert_iff M (M.refinementLevelFormulaData a s b d level T T2 valid) (t := (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val)) (u := u.val.val) (w := u.val.val)
    member term term).1 inserted
  rw [encoded] at obligations
  have ground := M.transitive (M.stageOneAssignments_mem pairing unions powers separation hI hT)
    (ZFSet.pair_mem_prod.1 (function.1 atLevel)).1
  exact M.stageTwoConditions_insert pairing unions powers separation infinite (M.refinementLevelFormulaData a s b d level T T2 valid) function atLevel ground old
    obligations.2.1 obligations.2.2.1 obligations.2.2.2.1 obligations.2.2.2.2

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
