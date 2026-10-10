import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalRowSupport

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {Q : Type u} [PartialOrder Q] [OrderTop Q] (s : Presentation Q)

theorem exists_decided_visibilityProfile
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (z : (M.nameDomain s).names)
      (_hs : HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z.val)
      (_subset : Name.eval {p | H.mem p} z.val ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (p : Q) (_hp : H.mem p),
      let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
      ∃ ground : F ∈ M.sets,
        MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
        ∃ B ∈ M.sets, M.groundEmbeddable B ZFSet.omega ∧ B ⊆ F ∧
          (∀ x ∈ F, ∃ v ∈ B, ZFSet.pair v x ∈ geometry.order) ∧
          ∃ q, H.mem q ∧ q ≤ p ∧
            Forces (M.nameDomain s) visibilityProfileFormula
              (M.visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
                carrier geometry.actors_ground geometry.carrier_ground
                (geometry.decoded_supportBasis_ground pairing unions powers separation)
                maps hT valid F ground z) q ∧
            M.DecidesVisibilityProfile a s b d.principalFix T F z.val q := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a maps T hT valid terms children H genericCoded genericFormula descent z hs subset p hp
  let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
  have supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  have system := M.niceNameSystem a s t pairing unions powers separation collection carrier order
    maps hT valid terms b d ⊥ directed geometry.actors_ground geometry.carrier_ground supports children
  have filter : MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F := by
    have coded := M.visibleSupportProfile_filter a s b d ⊥ directed T H valid system genericFormula
      z hs subset geometry.meet.smallMeet descent
    have meetGraph : (b.product b).graph b (fun vw => geometry.meet.smallMeet vw.1 vw.2) =
        geometry.meetGraph := geometry.meet.smallMeet_graph_eq
    have orderGraph : b.conditionOrder = geometry.order := geometry.decoded_order_eq
    rw [meetGraph, orderGraph] at coded
    exact coded
  have inExtension := M.visibleSupportProfile_mem_ordinary a s t b d pairing unions powers separation
    collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid order
    infinite H genericFormula z
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order
    infinite H genericFormula
  have choiceN := M.ordinaryExtension_choice s pairing unions powers separation collection infinite
    choice carrier order H genericFormula
  have reflection := M.ordinaryExtension_sequenceReflection s pairing unions powers separation collection
    infinite choice carrier order small geometry.carrier_ground closed H genericCoded genericFormula
  obtain ⟨B, hB, _, countable, contained, coinitial, _, ground⟩ :=
    fulfilled.reflected_extension_basis reflection infinite choice
      (M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H)
      zf.1.2.2.2.1 zf.1.2.2.2.2.1 zf.1.2.2.2.2.2.1 zf.2.1 zf.1.2.2.2.2.2.2 choiceN
      smallD irreflexive inExtension filter
  refine ⟨ground, filter, B, hB, countable, contained, coinitial, ?_⟩
  exact M.exists_forced_visibleSupportProfile a s t b d pairing unions powers separation collection
    carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid small H
    genericFormula z ground p hp

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end

end OAI
