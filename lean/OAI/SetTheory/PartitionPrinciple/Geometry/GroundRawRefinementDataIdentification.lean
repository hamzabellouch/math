import OAI.SetTheory.PartitionPrinciple.Definability.GroundPackedRefinementFormulaData
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRawNiceNameGraphs
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRawRowAssignmentActions

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_refinementIndices :
    GroundDefinableFunction M (fun env : Fin 11 → ZFSet.{u} =>
      M.refinementIndices (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)
        (env 6) (env 7) (env 8) (env 9) (env 10)) := by
  let v := GroundSetTerm.var M (n := 11)
  let first := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 5, v 8]
  let second := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 6, v 8]
  let level := GroundSetTerm.app (M.definable_singleton pairing) ![v 0]
  let bound := GroundSetTerm.app (M.definable_refinementIndexBound pairing unions powers separation)
    ![level, v 1, first, second]
  let formula : SetFormula 9 := refinementIndexSelectionFormula 0 1 2 3 4 5 6 7 8
  let term := GroundSetTerm.app (M.definable_separation separation formula)
    ![bound, v 0, v 2, v 3, v 4, v 7, v 8, v 9, v 10]
  refine { formula := term.definition.formula
           closed := fun env members => M.refinementIndices_mem pairing unions powers separation
             (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
             (members 6) (members 7) (members 8) (members 9) (members 10)
           correct := ?_ }
  intro env members z hz
  rw [term.definition.correct env members z hz]
  have args : (fun j : Fin 8 => (![bound, v 0, v 2, v 3, v 4, v 7, v 8, v 9, v 10]
      (j.succ)).eval env) = ![env 0, env 2, env 3, env 4, env 7, env 8, env 9, env 10] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))) j
  have equal : term.eval env = M.refinementIndices (env 0) (env 1) (env 2) (env 3) (env 4)
      (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) := by
    change ZFSet.sep (fun w => Realize M.sets formula (extend w _)) (bound.eval env) = _
    rw [args]
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_sep, M.mem_refinementIndices]
    apply and_congr_right
    intro hw
    exact M.realize_refinementIndexSelectionFormula 0 1 2 3 4 5 6 7 8 _
      (Fin.cases (M.transitive (bound.ground env members) hw)
        (Fin.cases (members 0) (Fin.cases (members 2) (Fin.cases (members 3)
          (Fin.cases (members 4) (Fin.cases (members 7) (Fin.cases (members 8)
            (Fin.cases (members 9) (Fin.cases (members 10) (fun j => Fin.elim0 j))))))))))
  rw [equal]

noncomputable def definable_refinementIndexFieldGraph (j : Fin 6) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => refinementIndexFieldGraph (env 0) (env 1) j) where
  formula := exactSetFormula 0 (.conj (BoundedFormula.productElementFormula 0 2 3).toFormula
    (refinementIndexFieldFormula 0 2 j))
  closed := fun _ members => M.refinementIndexFieldGraph_mem pairing unions powers separation
    (members 0) (members 1) j
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
      (fun _ h => M.transitive (M.refinementIndexFieldGraph_mem pairing unions powers separation
        (members 0) (members 1) j) h)
    intro w hw
    have all : ∀ k, (extend w (extend z env)) k ∈ M.sets := Fin.cases hw (Fin.cases hz members)
    change (Realize M.sets (BoundedFormula.productElementFormula 0 2 3).toFormula _ ∧
      Realize M.sets (refinementIndexFieldFormula 0 2 j) _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ all, BoundedFormula.truth_productElementFormula,
      M.realize_refinementIndexFieldFormula 0 2 j _ all]
    rw [refinementIndexFieldGraph, ZFSet.mem_sep]
    rfl

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def rawRefinementFormulaData
    (P order top actionGraph G nodes nodeOrder basis T T2 level : ZFSet.{u}) : Fin 15 → ZFSet.{u} :=
  let maps := rawActionMapFamily G actionGraph P
  let first := M.rawNiceNameCandidateGraph nodes T P G basis maps
  let second := M.rawNiceNameCandidateGraph nodes T2 P G basis maps
  let I := M.refinementIndices level nodes nodeOrder first second T T2 (ZFSet.prod T {top}) P order top
  let B1 := M.groundRelations T P
  let B2 := M.groundRelations T2 P
  let F1 := refinementIndexFieldGraph I nodes 1
  let F2 := refinementIndexFieldGraph I nodes 2
  let F3 := refinementIndexFieldGraph I B1 3
  let F4 := refinementIndexFieldGraph I B2 4
  let F5 := refinementIndexFieldGraph I B2 5
  ![I, F1, F2, F3, F4, F5, T, P, order, top, nodes, nodeOrder,
    M.refinementIndexNameGraph 2 I F3 F4 F5 T P order top,
    M.rawNiceVisibilityGraph nodes T P G basis maps top, B1]

noncomputable def rawRefinementFormulaDataCode
    (P order top actionGraph G nodes nodeOrder basis T T2 level : ZFSet.{u}) : ZFSet.{u} :=
  refinementFormulaDataCode (M.rawRefinementFormulaData P order top actionGraph G nodes nodeOrder basis T T2 level)

noncomputable def definable_rawRefinementFormulaDataCode
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 11 → ZFSet.{u} =>
      M.rawRefinementFormulaDataCode (env 0) (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10)) := by
  let v := GroundSetTerm.var M (n := 11)
  let maps := GroundSetTerm.app (M.definable_rawActionMapFamily pairing unions powers separation collection)
    ![v 4, v 3, v 0]
  let first := GroundSetTerm.app (M.definable_rawNiceNameCandidateGraph pairing unions powers separation collection)
    ![v 5, v 8, v 0, v 4, v 7, maps]
  let second := GroundSetTerm.app (M.definable_rawNiceNameCandidateGraph pairing unions powers separation collection)
    ![v 5, v 9, v 0, v 4, v 7, maps]
  let family := GroundSetTerm.app (M.definable_familySetCode pairing unions powers separation) ![v 8, v 2]
  let indices := GroundSetTerm.app (M.definable_refinementIndices pairing unions powers separation)
    ![v 10, v 5, v 6, first, second, v 8, v 9, family, v 0, v 1, v 2]
  let B1 := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 8, v 0]
  let B2 := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 9, v 0]
  let field (j : Fin 6) (bound : GroundSetTerm M 11) :=
    GroundSetTerm.app (M.definable_refinementIndexFieldGraph pairing unions powers separation j) ![indices, bound]
  let F1 := field 1 (v 5)
  let F2 := field 2 (v 5)
  let F3 := field 3 B1
  let F4 := field 4 B2
  let F5 := field 5 B2
  let mapNames := GroundSetTerm.app (M.definable_refinementIndexNameGraph pairing unions powers separation 2)
    ![indices, F3, F4, F5, v 8, v 0, v 1, v 2]
  let visibility := GroundSetTerm.app (M.definable_rawNiceVisibilityGraph pairing unions powers separation collection)
    ![v 5, v 8, v 0, v 4, v 7, maps, v 2]
  let term := GroundSetTerm.app (M.definable_nonemptyTuple pairing 14)
    ![indices, F1, F2, F3, F4, F5, v 8, v 0, v 1, v 2, v 5, v 6, mapNames, visibility, B1]
  refine term.definition.congr ?_
  intro env
  change nonemptyTupleCode 14 (fun j =>
    (![indices, F1, F2, F3, F4, F5, v 8, v 0, v 1, v 2, v 5, v 6, mapNames, visibility, B1] j).eval env) =
      nonemptyTupleCode 14 (M.rawRefinementFormulaData (env 0) (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10))
  congr 1
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (fun k => Fin.elim0 k))))))))))))))) j

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
include pairing unions powers separation collection carrier group nodes supports maps valid valid2

theorem rawRefinementFormulaData_eq :
    M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
      t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level =
        M.refinementLevelFormulaData a s b d level T T2 valid := by
  unfold rawRefinementFormulaData
  dsimp only
  rw [rawActionMapFamily_eq,
    M.rawNiceNameCandidateGraph_eq pairing unions powers separation collection a s t b d.principalFix
      carrier group supports maps valid nodes,
    M.rawNiceNameCandidateGraph_eq pairing unions powers separation collection a s t b d.principalFix
      carrier group supports maps valid2 nodes,
    M.rawNiceVisibilityGraph_eq pairing unions powers separation collection a s t b d.principalFix
      carrier group supports maps valid nodes]
  rw [← Name.familySet_code (s := s) ⊤ T valid]
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (fun k => Fin.elim0 k))))))))))))))) j

theorem rawRefinementFormulaDataCode_eq :
    M.rawRefinementFormulaDataCode s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
      t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level =
        M.refinementLevelFormulaDataCode a s b d level T T2 valid :=
  congrArg refinementFormulaDataCode (M.rawRefinementFormulaData_eq a s t b d
    pairing unions powers separation collection carrier group nodes supports maps level T T2 valid valid2)

end PartitionPilot.Forcing.TransitiveGround

end OAI
