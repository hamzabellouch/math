import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRawRefinementStageWitnesses

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G L : Type u} [Group G] [PartialOrder L]

def RawRefinementStageZF (M : TransitiveGround.{u})
    (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 level P order top action : ZFSet.{u}) : Prop :=
  ∃ (orderLaw : PartialOrderCode P order) (topMem : top ∈ P)
    (greatest : ∀ p ∈ P, ZFSet.pair p top ∈ order),
    letI := orderLaw.toPartialOrder
    letI := orderLaw.toOrderTop top topMem greatest
    ∃ e : PosetAction G (SetMembers P),
      e.actionGraph (SetMembers.presentation P) t = action ∧
      RefinementStageSystem M e (SetMembers.presentation P) t b d base directed level T T2 ∧
      let s := SetMembers.presentation P
      let F := d.principalSupportFamily base directed
      ∀ p : SetMembers P, ∃ H : ConditionFilter (SetMembers P),
        H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
        H.GenericFor (formulaFamily (M.nameDomain s)) ∧
        H.GenericFor (formulaFamily (e.symmetricDomain s (M.nameDomain s) F)) ∧
        M.sets ⊆ (e.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q} ∧
        ZFRealization ((e.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q})

namespace RawRefinementStageWitness
variable {M : TransitiveGround.{u}} {t : Presentation G} {b : Presentation L}
variable {d : PosetAction G L} {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {T T2 level P order top action : ZFSet.{u}}
variable (witness : RawRefinementStageWitness M t b d base directed T T2 level P order top action)

include witness

theorem symmetricZF
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (small : M.sets.Countable)
    (carrier : P ∈ M.sets) (groundOrder : order ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets) :
    RawRefinementStageZF M t b d base directed T T2 level P order top action := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have nextOrder : (SetMembers.presentation P).conditionOrder ∈ M.sets := by
    rw [orderLaw.conditionOrder_eq]
    exact groundOrder
  refine ⟨orderLaw, topMem, greatest, e, graph, system, ?_⟩
  dsimp only
  intro p
  exact M.exists_ZF_interpretation e (SetMembers.presentation P) t b
    (d.principalSupportFamily base directed) d.principalFix
    (d.principalSupportFamily_basis base directed) small pairing unions powers separation collection infinite
    carrier nextOrder group nodes supports system.inputs.condition_maps p

end RawRefinementStageWitness
end PartitionPilot.Forcing

end

end OAI
