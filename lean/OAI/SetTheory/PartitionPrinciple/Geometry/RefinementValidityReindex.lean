import OAI.SetTheory.PartitionPrinciple.Definability.RefinementValidityCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem refinementValidity_empty (T : ZFSet.{u}) :
    RefinementValidityCode T ∅ ∅ ∅ := by
  have relation : EquivalenceRelationCode (∅ : ZFSet.{u}) ∅ :=
    ⟨by simp, by simp, by simp, by simp⟩
  exact ⟨by simp, relation, relation, fun _ h => h⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_refinementValidityFormula_reindex {n : Nat}
    (f : Fin 4 → Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i : Fin 4, env (f i) ∈ M.sets) :
    Realize M.sets (reindex f BoundedFormula.refinementValidityFormula.toFormula) env ↔
      RefinementValidityCode (env (f 3)) (env (f 0)) (env (f 1)) (env (f 2)) := by
  rw [realize_reindex]
  exact M.realize_refinementValidityFormula (fun i => env (f i)) members

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
