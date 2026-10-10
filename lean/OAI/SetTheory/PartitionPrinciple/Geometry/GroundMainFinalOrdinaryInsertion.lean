import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalSupportConstruction

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula
universe u v
variable {M N : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable (reflection : GroundSequenceReflection M N (run.finalGeometry i₀).carrier)
include fulfilled reflection

theorem reflected_extension_basis
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (includes : M.sets ⊆ N.sets)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F) :
    ∃ B ∈ M.sets, B ∈ N.sets ∧ M.groundEmbeddable B ZFSet.omega ∧ B ⊆ F ∧
      (∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ (run.finalGeometry i₀).order) ∧
      M.generatedMeetFilter (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
        (run.finalGeometry i₀).meetGraph B = F ∧ F ∈ M.sets := by
  obtain ⟨B, hB, f, hf, injection, subset, coinitial⟩ :=
    fulfilled.chronology.exists_extension_basis i₀ includes pairingN unionsN powersN separationN
      infiniteN choiceN smallD irreflexive hF filter
  obtain ⟨ground, countable, equal, filterGround⟩ := reflection.coinitial_filter
    pairing unions powers separation infinite choice pairingN unionsN powersN separationN infiniteN
    (run.finalGeometry i₀).carrier_ground (run.finalGeometry i₀).order_ground
    (run.finalGeometry i₀).meet_ground (run.finalGeometry i₀).meet hB ⟨f, hf, injection⟩
    filter subset coinitial
  exact ⟨B, ground, hB, countable, subset, coinitial, equal, filterGround⟩

theorem extension_insertion
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (includes : M.sets ⊆ N.sets)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {c e d F : ZFSet.{u}}
    (hc : c ∈ (run.finalGeometry i₀).carrier) (he : e ∈ (run.finalGeometry i₀).carrier)
    (hd : d ∈ (run.finalGeometry i₀).carrier) (hF : F ∈ N.sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F)
    (lower : ZFSet.pair c e ∈ (run.finalGeometry i₀).order)
    (strict : ZFSet.pair e c ∉ (run.finalGeometry i₀).order)
    (bound : ZFSet.pair c d ∈ (run.finalGeometry i₀).order)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ (run.finalGeometry i₀).order) :
    F ∈ M.sets ∧ ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
      caps ∈ N.sets ∧ actors ∈ N.sets ∧
      FinalInsertionFamiliesCode Labels (run.finalGeometry i₀).carrier (run.finalGeometry i₀).actors
        (run.finalGeometry i₀).order (run.finalGeometry i₀).meetGraph (run.finalGeometry i₀).action
        c e d F caps actors := by
  obtain ⟨_, _, _, _, _, _, _, ground⟩ := fulfilled.reflected_extension_basis reflection
    infinite choice includes pairingN unionsN powersN separationN infiniteN choiceN smallD irreflexive hF filter
  obtain ⟨caps, hCaps, actors, hActors, family⟩ :=
    fulfilled.insertion c hc e he d hd F ground filter lower strict bound above
  exact ⟨ground, caps, hCaps, actors, hActors, includes hCaps, includes hActors, family⟩

theorem extension_countable_localization
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    {X : ZFSet.{u}} (hX : X ∈ N.sets) (subset : X ⊆ (run.finalGeometry i₀).carrier)
    (small : N.groundEmbeddable X ZFSet.omega) :
    X ∈ M.sets ∧ M.groundEmbeddable X ZFSet.omega ∧
      (∃ j, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair y x ∈ (run.finalInclusions i₀).pointMap j) ∧
      ∃ b ∈ (run.finalGeometry i₀).carrier,
        ∀ x ∈ X, ZFSet.pair x b ∈ (run.finalGeometry i₀).order := by
  obtain ⟨ground, countable⟩ := reflection.countable_subset pairing unions powers separation infinite choice
    pairingN unionsN powersN separationN infiniteN (run.finalGeometry i₀).carrier_ground hX subset small
  have localized := fulfilled.countable_localization X ground subset countable
  exact ⟨ground, countable, localized.1, localized.2⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment



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
variable {Q : Type u} [Preorder Q] [OrderTop Q] (s : Presentation Q)
include fulfilled

theorem ordinary_extension_insertion
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter Q) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    (pairingN : Realize (M.ordinaryExtension s H).sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize (M.ordinaryExtension s H).sets SetFormula.union Fin.elim0)
    (powersN : Realize (M.ordinaryExtension s H).sets powerSet Fin.elim0)
    (separationN : SeparationSchema (M.ordinaryExtension s H).sets)
    (infiniteN : Realize (M.ordinaryExtension s H).sets infinity Fin.elim0)
    (choiceN : Realize (M.ordinaryExtension s H).sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {c e d F : ZFSet.{u}}
    (hc : c ∈ (run.finalGeometry i₀).carrier) (he : e ∈ (run.finalGeometry i₀).carrier)
    (hd : d ∈ (run.finalGeometry i₀).carrier) (hF : F ∈ (M.ordinaryExtension s H).sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F)
    (lower : ZFSet.pair c e ∈ (run.finalGeometry i₀).order)
    (strict : ZFSet.pair e c ∉ (run.finalGeometry i₀).order)
    (bound : ZFSet.pair c d ∈ (run.finalGeometry i₀).order)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ (run.finalGeometry i₀).order) :
    F ∈ M.sets ∧ ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
      caps ∈ (M.ordinaryExtension s H).sets ∧ actors ∈ (M.ordinaryExtension s H).sets ∧
      FinalInsertionFamiliesCode Labels (run.finalGeometry i₀).carrier (run.finalGeometry i₀).actors
        (run.finalGeometry i₀).order (run.finalGeometry i₀).meetGraph (run.finalGeometry i₀).action
        c e d F caps actors := by
  have reflection := M.ordinaryExtension_sequenceReflection s pairing unions powers separation
    collection infinite choice carrier order small (run.finalGeometry i₀).carrier_ground
    closed H genericCoded genericFormula
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H
  exact fulfilled.extension_insertion reflection infinite choice includes pairingN unionsN powersN
    separationN infiniteN choiceN smallD irreflexive hc he hd hF filter lower strict bound above

theorem ordinary_extension_countable_localization
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter Q) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    (pairingN : Realize (M.ordinaryExtension s H).sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize (M.ordinaryExtension s H).sets SetFormula.union Fin.elim0)
    (powersN : Realize (M.ordinaryExtension s H).sets powerSet Fin.elim0)
    (separationN : SeparationSchema (M.ordinaryExtension s H).sets)
    (infiniteN : Realize (M.ordinaryExtension s H).sets infinity Fin.elim0)
    {X : ZFSet.{u}} (hX : X ∈ (M.ordinaryExtension s H).sets)
    (subset : X ⊆ (run.finalGeometry i₀).carrier)
    (countable : (M.ordinaryExtension s H).groundEmbeddable X ZFSet.omega) :
    X ∈ M.sets ∧ M.groundEmbeddable X ZFSet.omega ∧
      (∃ j, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair y x ∈ (run.finalInclusions i₀).pointMap j) ∧
      ∃ b ∈ (run.finalGeometry i₀).carrier,
        ∀ x ∈ X, ZFSet.pair x b ∈ (run.finalGeometry i₀).order := by
  have reflection := M.ordinaryExtension_sequenceReflection s pairing unions powers separation
    collection infinite choice carrier order small (run.finalGeometry i₀).carrier_ground
    closed H genericCoded genericFormula
  exact fulfilled.extension_countable_localization reflection infinite choice
    pairingN unionsN powersN separationN infiniteN hX subset countable

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end

end OAI
