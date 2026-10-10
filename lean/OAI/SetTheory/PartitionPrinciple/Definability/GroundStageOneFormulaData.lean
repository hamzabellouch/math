import OAI.SetTheory.PartitionPrinciple.Forcing.GroundDefinableRefinementNameGraphs

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)

noncomputable def stageOneFormulaData : Fin 15 → ZFSet.{u} :=
  let I := M.niceRefinementIndices a s b d ∅ T T2 valid
  let bounds := M.niceRefinementIndexBounds s b ∅ T T2
  ![I, refinementIndexFieldGraph I (bounds 1) 1, refinementIndexFieldGraph I (bounds 2) 2,
    refinementIndexFieldGraph I (bounds 3) 3, refinementIndexFieldGraph I (bounds 4) 4,
    refinementIndexFieldGraph I (bounds 5) 5, T, s.carrier, s.conditionOrder, s.encode ⊤,
    b.carrier, b.conditionOrder, M.niceRefinementNameGraph a s b d 2 ∅ T T2 valid,
    M.niceVisibilityGraph a s b T d.principalFix, M.groundRelations T s.carrier]

theorem stageOneFormulaData_members
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hT : T ∈ M.sets) (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (valid2 : ∀ z ∈ T2, IsName s z)
    (indices : NiceRefinementIndexSystem M a s b d ∅ T T2 valid valid2)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (system : NiceNameSystem M a s b d base directed T valid) :
    ∀ j, M.stageOneFormulaData a s b d T T2 valid j ∈ M.sets := by
  have mapGround := M.niceRefinementNameGraph_mem a s b d indices pairing unions powers separation
    hT carrier order 2
  have classes := M.groundRelations_mem pairing unions powers separation hT carrier
  exact Fin.cases indices.index_ground (Fin.cases (indices.field_ground 1)
    (Fin.cases (indices.field_ground 2) (Fin.cases (indices.field_ground 3)
      (Fin.cases (indices.field_ground 4) (Fin.cases (indices.field_ground 5)
        (Fin.cases hT (Fin.cases carrier (Fin.cases order
          (Fin.cases (M.transitive carrier (s.encode_mem ⊤)) (Fin.cases nodes
            (Fin.cases nodeOrder (Fin.cases mapGround (Fin.cases system.visibility_graph_ground
              (Fin.cases classes (fun j => Fin.elim0 j)))))))))))))))

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
