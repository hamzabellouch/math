import OAI.SetTheory.PartitionPrinciple.Definability.PreservedMainPrefixHistoryFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def mainPrefixExtensionRelation (B : ZFSet.{u}) : ZFSet.{u} :=
  M.definableRelation (mainPrefixExtensionFormula (0 : Fin 2) 1) Fin.elim0 B B

theorem mainPrefixExtensionRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {B : ZFSet.{u}} (hB : B ∈ M.sets) : M.mainPrefixExtensionRelation B ∈ M.sets :=
  M.definableRelation_mem pairing unions powers separation
    (mainPrefixExtensionFormula (0 : Fin 2) 1) Fin.elim0 (fun i => Fin.elim0 i) hB hB

theorem mainPrefixExtensionRelation_entry {B : ZFSet.{u}} (hB : B ∈ M.sets)
    (old next : ZFSet.{u}) :
    ZFSet.pair old next ∈ M.mainPrefixExtensionRelation B ↔
      old ∈ B ∧ next ∈ B ∧ MainPrefixExtends old next := by
  rw [mainPrefixExtensionRelation, M.pair_mem_definableRelation]
  constructor
  · rintro ⟨ho, hn, relation⟩
    exact ⟨ho, hn, (M.realize_mainPrefixExtensionFormula 0 1 _
      (Fin.cases (M.transitive hB ho) (Fin.cases (M.transitive hB hn) (fun i => Fin.elim0 i)))).1 relation⟩
  · rintro ⟨ho, hn, relation⟩
    exact ⟨ho, hn, (M.realize_mainPrefixExtensionFormula 0 1 _
      (Fin.cases (M.transitive hB ho) (Fin.cases (M.transitive hB hn) (fun i => Fin.elim0 i)))).2 relation⟩

end TransitiveGround

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem appendCone_extends (target : GroundLinkedMainStage M K Labels C D rD)
    (cone : run.diagram.Cone target.main) {row : ZFSet.{u}} (ground : row ∈ M.sets)
    (function : FunctionGraphOn (ZFSet.prod {run.indices} run.indices) row)
    (entries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔ z = (cone.leg i).map.code)
    (covered : cone.append.CoversOldBirths) :
    MainPrefixExtends run.code (run.appendCone target cone ground function entries covered).code := by
  let extended := run.appendCone target cone ground function entries covered
  apply (mainPrefixExtends_iff_restrictions run.graph_code extended.graph_code).2
  refine ⟨?_, run.appendCone_stageGraph_restrict target cone ground function entries covered,
    run.appendCone_transitionGraph_restrict target cone ground function entries covered⟩
  rw [run.appendCone_indices target cone ground function entries covered]
  exact fun _ h => ZFSet.mem_insert_of_mem _ h

end GroundMainPrefix
end PartitionPilot.Forcing

end

end OAI
