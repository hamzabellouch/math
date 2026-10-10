import OAI.SetTheory.PartitionPrinciple.Definability.GroundDefinableRelationProducts

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_singleton :
    GroundDefinableFunction M (fun env : Fin 1 → ZFSet.{u} => {env 0}) where
  formula := exactSetFormula 0 (.equal 0 2)
  closed := fun _ members => by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing (members 0) (members 0)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
    · intro w hw
      exact (ZFSet.mem_singleton.1 hw).symm ▸ members 0
    · intro w _
      exact ZFSet.mem_singleton.symm

noncomputable def definable_binaryUnion :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => env 0 ∪ env 1) where
  formula := exactSetFormula 0 (disj (.mem 0 2) (.mem 0 3))
  closed := fun _ members => M.binary_union_mem pairing unions (members 0) (members 1)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
      (fun _ h => M.transitive (M.binary_union_mem pairing unions (members 0) (members 1)) h)
    intro w _
    rw [realize_disj]
    exact ZFSet.mem_union.symm

noncomputable def definable_orderedPairNameFamily :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => orderedPairNameFamily (env 0) (env 1) (env 2)) where
  formula := exactSetFormula 0 (orderedPairNameFamilyMemberFormula 0 2 3 4)
  closed := fun _ members => M.orderedPairNameFamily_mem pairing unions powers separation
    (members 0) (members 1) (members 2)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
      (fun _ h => M.transitive (M.orderedPairNameFamily_mem pairing unions powers separation
        (members 0) (members 1) (members 2)) h)
    intro w hw
    exact M.realize_orderedPairNameFamilyMemberFormula pairing 0 2 3 4 _
      (Fin.cases hw (Fin.cases hz members))

noncomputable def definable_refinementIndexBound :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      refinementIndexBound (env 0) (env 1) (env 2) (env 3)) := by
  let v := GroundSetTerm.var M (n := 4)
  let prod (x y : GroundSetTerm M 4) :=
    GroundSetTerm.app (M.definable_product pairing unions powers separation) ![x, y]
  exact (prod (v 0) (prod (v 1) (prod (v 1) (prod (v 2) (prod (v 3) (v 3)))))).definition

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
