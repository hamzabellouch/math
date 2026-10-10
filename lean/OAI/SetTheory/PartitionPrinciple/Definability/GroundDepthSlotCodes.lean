import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFiniteWordLaws

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def depthSlotEntryFormula : BoundedFormula 5 :=
  exMem 1 (exMem 3 (exMem 3 (exMem 4
    (.conj (orderedTripleFormula 4 3 2 1)
      (.conj (tripleMembershipFormula 6 3 0 7) (tripleMembershipFormula 0 2 1 8))))))

theorem truth_depthSlotEntryFormula (env : Fin 5 → ZFSet.{u}) :
    Truth depthSlotEntryFormula env ↔
      ∃ n ∈ env 1, ∃ j ∈ env 2, ∃ k ∈ env 1, ∃ t ∈ env 1,
        env 0 = ZFSet.pair (ZFSet.pair n j) k ∧
          ZFSet.pair (ZFSet.pair (env 2) n) t ∈ env 3 ∧
          ZFSet.pair (ZFSet.pair t j) k ∈ env 4 := by
  simp only [depthSlotEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem depthSlotGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) : depthSlotGraph ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  have hThree := M.natSetCode_mem separation infinite 3
  have hMul := M.natMulGraph_mem pairing unions powers separation infinite
  have hAdd := M.natAddGraph_mem pairing unions powers separation infinite
  let params := extend ZFSet.omega (extend (natSetCode 3) (extend natMulGraph (extend natAddGraph Fin.elim0)))
  have selected := M.bounded_separation_mem separation BoundedFormula.depthSlotEntryFormula params
    (Fin.cases hOmega (Fin.cases hThree (Fin.cases hMul (Fin.cases hAdd (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hOmega hThree) hOmega)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.depthSlotEntryFormula (extend z params))
      (ZFSet.prod (ZFSet.prod ZFSet.omega (natSetCode 3)) ZFSet.omega) = depthSlotGraph := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep, BoundedFormula.truth_depthSlotEntryFormula, depthSlotGraph]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
