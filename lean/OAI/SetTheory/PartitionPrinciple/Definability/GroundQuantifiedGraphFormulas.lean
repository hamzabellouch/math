import OAI.SetTheory.PartitionPrinciple.Models.GroundOrdinalPartitionInjectionAssembly

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def allGraphFields {n} (graph : Fin n) (body : SetFormula (n + 2)) : SetFormula n :=
  .all (.all (imp (BoundedFormula.pairMembershipFormula 1 0 graph.succ.succ).toFormula body))

def allPairFields {n} (pair : Fin n) (body : SetFormula (n + 2)) : SetFormula n :=
  .all (.all (imp (BoundedFormula.orderedPairFormula pair.succ.succ 1 0).toFormula body))

def allSetMembers {n} (bound : Fin n) (body : SetFormula (n + 1)) : SetFormula n :=
  .all (imp (.mem 0 bound.succ) body)

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_allGraphFields {n} (graph : Fin n) (body : SetFormula (n + 2))
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (allGraphFields graph body) env ↔
      ∀ x y, ZFSet.pair x y ∈ env graph →
        Realize M.sets body (extend y (extend x env)) := by
  simp only [allGraphFields, Realize, realize_imp]
  constructor
  · intro holds x y entry
    have pairGround := M.transitive (members graph) entry
    have hx := M.pair_left pairGround
    have hy := M.pair_right pairGround
    exact holds x hx y hy ((BoundedFormula.realize_toFormula M _ _
      (Fin.cases hy (Fin.cases hx members))).2
        ((BoundedFormula.truth_pairMembershipFormula _ _ _ _).2 entry))
  · intro holds x hx y hy entry
    exact holds x y ((BoundedFormula.truth_pairMembershipFormula _ _ _ _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hy (Fin.cases hx members))).1 entry))

theorem realize_allPairFields {n} (pair : Fin n) (body : SetFormula (n + 2))
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (allPairFields pair body) env ↔
      ∀ x y, env pair = ZFSet.pair x y →
        Realize M.sets body (extend y (extend x env)) := by
  simp only [allPairFields, Realize, realize_imp]
  constructor
  · intro holds x y equal
    have pairGround : ZFSet.pair x y ∈ M.sets := equal ▸ members pair
    have hx := M.pair_left pairGround
    have hy := M.pair_right pairGround
    exact holds x hx y hy ((BoundedFormula.realize_toFormula M _ _
      (Fin.cases hy (Fin.cases hx members))).2
        ((BoundedFormula.truth_orderedPairFormula _ _ _ _).2 equal))
  · intro holds x hx y hy equal
    exact holds x y ((BoundedFormula.truth_orderedPairFormula _ _ _ _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hy (Fin.cases hx members))).1 equal))

theorem realize_allSetMembers {n} (bound : Fin n) (body : SetFormula (n + 1))
    (env : Fin n → ZFSet.{u}) (ground : env bound ∈ M.sets) :
    Realize M.sets (allSetMembers bound body) env ↔
      ∀ x ∈ env bound, Realize M.sets body (extend x env) := by
  simp only [allSetMembers, Realize, realize_imp]
  exact ⟨fun h x hx => h x (M.transitive ground hx) hx,
    fun h x _ hx => h x hx⟩

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
