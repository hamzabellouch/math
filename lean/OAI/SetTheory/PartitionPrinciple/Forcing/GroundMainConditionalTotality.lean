import OAI.SetTheory.PartitionPrinciple.Definability.PreservedMainPrefixHistoryFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

def mainPrefixConditionalParams (K Labels C D rD N f : ZFSet.{u}) : Fin 7 → ZFSet.{u} :=
  extend K (extend Labels (extend C (extend D (extend rD (extend N (extend f Fin.elim0))))))

noncomputable def mainPrefixConditionalRelation (S K Labels C D rD N f : ZFSet.{u}) : ZFSet.{u} :=
  M.definableRelation (mainPrefixConditionalStepFormula 2 3 4 5 6 7 8 (0 : Fin 9) 1)
    (mainPrefixConditionalParams K Labels C D rD N f) S S

theorem mainPrefixConditionalRelation_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S K Labels C D rD N f : ZFSet.{u}} (hS : S ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets) :
    M.mainPrefixConditionalRelation S K Labels C D rD N f ∈ M.sets :=
  M.definableRelation_mem pairing unions powers separation _ _
    (Fin.cases hK (Fin.cases hLabels (Fin.cases hC (Fin.cases hD (Fin.cases hrD
      (Fin.cases hN (Fin.cases hf (fun j => Fin.elim0 j)))))))) hS hS

theorem mainPrefixConditionalRelation_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {S K Labels C D rD N f : ZFSet.{u}} (hS : S ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets)
    (omega : N = ZFSet.omega) (ordinal : ordinalSetProperty K) (old next : ZFSet.{u}) :
    ZFSet.pair old next ∈ M.mainPrefixConditionalRelation S K Labels C D rD N f ↔
      old ∈ S ∧ next ∈ S ∧ MainPrefixConditionalStepCode M K Labels C D rD N f old next := by
  rw [mainPrefixConditionalRelation, M.pair_mem_definableRelation]
  apply and_congr_right
  intro oldMember
  apply and_congr_right
  intro nextMember
  exact M.realize_mainPrefixConditionalStepFormula pairing unions powers separation collection
    2 3 4 5 6 7 8 0 1
    (extend old (extend next (mainPrefixConditionalParams K Labels C D rD N f)))
    (Fin.cases (M.transitive hS oldMember) (Fin.cases (M.transitive hS nextMember)
      (Fin.cases hK (Fin.cases hLabels (Fin.cases hC (Fin.cases hD (Fin.cases hrD
        (Fin.cases hN (Fin.cases hf (fun j => Fin.elim0 j)))))))))) omega ordinal

theorem choose_mainPrefixConditionalSteps
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S K Labels C D rD N f : ZFSet.{u}} (hS : S ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets)
    (omega : N = ZFSet.omega) (ordinal : ordinalSetProperty K)
    (total : ∀ old ∈ S, ∃ next ∈ S, MainPrefixConditionalStepCode M K Labels C D rD N f old next) :
    ∃ g ∈ M.sets, ZFSet.IsFunc S S g ∧
      g ⊆ M.mainPrefixConditionalRelation S K Labels C D rD N f ∧
      ∀ old next, ZFSet.pair old next ∈ g →
        next ∈ S ∧ MainPrefixConditionalStepCode M K Labels C D rD N f old next := by
  have entries := M.mainPrefixConditionalRelation_entry pairing unions powers separation collection
    hS hK hLabels hC hD hrD hN hf omega ordinal
  obtain ⟨g, ground, function, included⟩ := M.uniformize_relation pairing unions powers separation choice
    hS hS (M.mainPrefixConditionalRelation_ground pairing unions powers separation
      hS hK hLabels hC hD hrD hN hf) (by
        intro old oldMember
        obtain ⟨next, nextMember, code⟩ := total old oldMember
        exact ⟨next, nextMember, (entries old next).2 ⟨oldMember, nextMember, code⟩⟩)
  exact ⟨g, ground, function, included, fun old next entry =>
    ((entries old next).1 (included entry)).2⟩

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundMainCandidateLevel
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem conditionalSteps_total
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Labels C D rD f : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (hLabels : Labels ∈ M.sets)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (function : ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K Labels C D rD)
      (ZFSet.prod level.carrier level.carrier) f)
    (selected : f ⊆ M.taskBearingSuccessorRelation
      (M.linkedMainStageCandidates level.carrier K Labels C D rD) level.carrier K Labels C D rD)
    (old : ZFSet.{u})
    (member : old ∈ level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD) :
    ∃ next ∈ level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD,
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next := by
  obtain ⟨T, _, indexMember, nonempty, inhabited, ordinal, run, indices, equal, preserved, rank⟩ :=
    level.exists_prefix_of_mem_recursionPrefixes pairing unions powers separation member
  let := ordinalMainIndexPreorder ordinal
  have actualIndex : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite :=
    indices.symm ▸ indexMember
  rcases ordinal_successor_or_nonzeroLimit ordinal nonempty with successor | limit
  · obtain ⟨b, _, successor⟩ := successor
    obtain ⟨next, _, nextMember, code⟩ := run.exists_selectedStepCode collection infinite hK standard hLabels
      preserved rank actualIndex (indices.trans successor) level function selected
    exact ⟨next, nextMember, Or.inl (equal ▸ code)⟩
  · obtain ⟨i₀⟩ := inhabited
    obtain ⟨next, _, nextMember, code⟩ := run.exists_limitStepCode preserved i₀ collection infinite choice
      columns_eq actualIndex rank hK standard level
    refine ⟨next, nextMember, Or.inr ⟨T, run.stageGraph, run.transitionGraph, ?_, limit, equal ▸ code⟩⟩
    exact equal.symm.trans (congrArg
      (fun U => mainPrefixCode U run.stageGraph run.transitionGraph) indices)

theorem exists_groundConditionalPrefixFunction
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Labels C D rD f : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (hLabels : Labels ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (hf : f ∈ M.sets)
    (function : ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K Labels C D rD)
      (ZFSet.prod level.carrier level.carrier) f)
    (selected : f ⊆ M.taskBearingSuccessorRelation
      (M.linkedMainStageCandidates level.carrier K Labels C D rD) level.carrier K Labels C D rD) :
    let S := level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD
    ∃ g ∈ M.sets, ZFSet.IsFunc S S g ∧
      g ⊆ M.mainPrefixConditionalRelation S K Labels C D rD ZFSet.omega f ∧
      ∀ old next, ZFSet.pair old next ∈ g →
        next ∈ S ∧ MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next := by
  have hOmega := M.transitive hK
    (standard.groundOmegaOne_mem pairing unions powers separation collection infinite hK)
  have hC : C ∈ M.sets := columns_eq.symm ▸ hOmega
  have hS := level.recursionPrefixes_ground pairing unions powers separation collection infinite
    hK standard.1.1 hOmega hLabels hC hD hrD
  exact M.choose_mainPrefixConditionalSteps pairing unions powers separation collection choice
    hS hK hLabels hC hD hrD (M.omega_mem separation infinite) hf rfl standard.1.1
    (level.conditionalSteps_total pairing unions powers separation collection infinite choice
      hK standard hLabels columns_eq function selected)

end PartitionPilot.Forcing.GroundMainCandidateLevel

end

end OAI
