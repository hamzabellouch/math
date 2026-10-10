import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRawRefinementStageWitnesses
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementFinitePowerSystems

namespace OAI

section

namespace PartitionPilot.Forcing.RawRefinementStageWitness
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {G L : Type u} [Group G] [PartialOrder L]
variable {t : Presentation G} {b : Presentation L} {d : PosetAction G L}
variable {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {T T2 level P order top action : ZFSet.{u}}

theorem finitePower_systems (witness : RawRefinementStageWitness M t b d base directed T T2 level P order top action)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : P ∈ M.sets) (groundOrder : order ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets) (hT : T ∈ M.sets) :
    ∃ (orderLaw : PartialOrderCode P order) (topMem : top ∈ P)
      (greatest : ∀ p ∈ P, ZFSet.pair p top ∈ order),
      letI := orderLaw.toPartialOrder
      letI := orderLaw.toOrderTop top topMem greatest
      ∃ e : PosetAction G (SetMembers P),
        e.actionGraph (SetMembers.presentation P) t = action ∧
        RefinementStageSystem M e (SetMembers.presentation P) t b d base directed level T T2 ∧
        ∀ n : Nat, let X := iteratedPairNameFamily top T n
          ∃ valid : ∀ z ∈ X, IsName (SetMembers.presentation P) z,
            X ∈ M.sets ∧
            (∀ g (tau : Name (SetMembers.presentation P)), tau.val ∈ X →
              (e.act (SetMembers.presentation P) g tau).val ∈ X) ∧
            (∀ tau : Name (SetMembers.presentation P), tau.val ∈ X →
              HereditarilySymmetric e (SetMembers.presentation P) (d.principalSupportFamily base directed) tau) ∧
            NiceNameSystem M e (SetMembers.presentation P) b d base directed X valid := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  refine ⟨orderLaw, topMem, greatest, e, graph, system, ?_⟩
  intro n
  have nextOrder : (SetMembers.presentation P).conditionOrder ∈ M.sets := by
    rw [orderLaw.conditionOrder_eq]
    exact groundOrder
  have topEq : (SetMembers.presentation P).encode ⊤ = top := SetMembers.raw_ofMem top topMem
  have power := system.finitePower_system pairing unions powers separation collection
    carrier nextOrder group nodes supports hT n
  simpa only [topEq] using power

end PartitionPilot.Forcing.RawRefinementStageWitness

end

end OAI
