import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalOrdinaryInsertion
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalRowOrdinaryZFC

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

section
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
include fulfilled

theorem ordinary_ZF_insertion_of_choice
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter Q) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
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
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order
    infinite H genericFormula
  exact fulfilled.ordinary_extension_insertion s collection infinite choice carrier order small closed
    H genericCoded genericFormula zf.1.2.2.2.1 zf.1.2.2.2.2.1 zf.1.2.2.2.2.2.1
    zf.2.1 zf.1.2.2.2.2.2.2 choiceN smallD irreflexive hc he hd hF filter lower strict bound above

theorem ordinary_ZF_countable_localization
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter Q) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    {X : ZFSet.{u}} (hX : X ∈ (M.ordinaryExtension s H).sets)
    (subset : X ⊆ (run.finalGeometry i₀).carrier)
    (countable : (M.ordinaryExtension s H).groundEmbeddable X ZFSet.omega) :
    X ∈ M.sets ∧ M.groundEmbeddable X ZFSet.omega ∧
      (∃ j, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair y x ∈ (run.finalInclusions i₀).pointMap j) ∧
      ∃ b ∈ (run.finalGeometry i₀).carrier,
        ∀ x ∈ X, ZFSet.pair x b ∈ (run.finalGeometry i₀).order := by
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order
    infinite H genericFormula
  exact fulfilled.ordinary_extension_countable_localization s collection infinite choice carrier order
    small closed H genericCoded genericFormula zf.1.2.2.2.1 zf.1.2.2.2.2.1 zf.1.2.2.2.2.2.1
    zf.2.1 zf.1.2.2.2.2.2.2 hX subset countable

end

section
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
include fulfilled

theorem ordinary_insertion
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter Q) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
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
  have choiceN := M.ordinaryExtension_choice s pairing unions powers separation collection infinite
    choice carrier order H genericFormula
  exact fulfilled.ordinary_ZF_insertion_of_choice s collection infinite choice carrier order small
    closed H genericCoded genericFormula choiceN smallD irreflexive hc he hd hF filter lower strict bound above

end

section
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
include fulfilled

theorem ordinary_submodel_insertion
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter Q) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    (N : TransitiveGround.{u}) (includes : M.sets ⊆ N.sets)
    (included : N.sets ⊆ (M.ordinaryExtension s H).sets)
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
  obtain ⟨ground, caps, hCaps, actors, hActors, _, _, family⟩ :=
    fulfilled.ordinary_insertion s collection infinite choice carrier order small closed
      H genericCoded genericFormula smallD irreflexive hc he hd (included hF)
      filter lower strict bound above
  exact ⟨ground, caps, hCaps, actors, hActors, includes hCaps, includes hActors, family⟩

theorem ordinary_submodel_countable_localization
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter Q) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    (N : TransitiveGround.{u}) (included : N.sets ⊆ (M.ordinaryExtension s H).sets)
    {X : ZFSet.{u}} (hX : X ∈ N.sets)
    (subset : X ⊆ (run.finalGeometry i₀).carrier)
    (countable : N.groundEmbeddable X ZFSet.omega) :
    X ∈ M.sets ∧ M.groundEmbeddable X ZFSet.omega ∧
      (∃ j, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair y x ∈ (run.finalInclusions i₀).pointMap j) ∧
      ∃ b ∈ (run.finalGeometry i₀).carrier,
        ∀ x ∈ X, ZFSet.pair x b ∈ (run.finalGeometry i₀).order := by
  obtain ⟨f, hf, injection⟩ := countable
  exact fulfilled.ordinary_ZF_countable_localization s collection infinite choice carrier order
    small closed H genericCoded genericFormula (included hX) subset ⟨f, included hf, injection⟩

end

section
open SetFormula SetRealization Compression.RecursiveMaps
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
variable {G : Type u} [Group G] (a : PosetAction G Q) (supports : NormalSubgroupFamily G)
include fulfilled

theorem symmetric_insertion
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter Q) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {c e d F : ZFSet.{u}}
    (hc : c ∈ (run.finalGeometry i₀).carrier) (he : e ∈ (run.finalGeometry i₀).carrier)
    (hd : d ∈ (run.finalGeometry i₀).carrier) (hF : F ∈ (M.symmetricExtension s a supports H).sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F)
    (lower : ZFSet.pair c e ∈ (run.finalGeometry i₀).order)
    (strict : ZFSet.pair e c ∉ (run.finalGeometry i₀).order)
    (bound : ZFSet.pair c d ∈ (run.finalGeometry i₀).order)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ (run.finalGeometry i₀).order) :
    F ∈ M.sets ∧ ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
      caps ∈ (M.symmetricExtension s a supports H).sets ∧ actors ∈ (M.symmetricExtension s a supports H).sets ∧
      FinalInsertionFamiliesCode Labels (run.finalGeometry i₀).carrier (run.finalGeometry i₀).actors
        (run.finalGeometry i₀).order (run.finalGeometry i₀).meetGraph (run.finalGeometry i₀).action
        c e d F caps actors := by
  exact fulfilled.ordinary_submodel_insertion s collection infinite choice carrier order small closed
    H genericCoded genericFormula (M.symmetricExtension s a supports H)
    (M.ground_subset_symmetricExtension s a supports pairing unions powers separation collection carrier H)
    (M.symmetricExtension_subset_ordinaryExtension s a supports H)
    smallD irreflexive hc he hd hF filter lower strict bound above

theorem symmetric_countable_localization
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter Q) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    {X : ZFSet.{u}} (hX : X ∈ (M.symmetricExtension s a supports H).sets)
    (subset : X ⊆ (run.finalGeometry i₀).carrier)
    (countable : (M.symmetricExtension s a supports H).groundEmbeddable X ZFSet.omega) :
    X ∈ M.sets ∧ M.groundEmbeddable X ZFSet.omega ∧
      (∃ j, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair y x ∈ (run.finalInclusions i₀).pointMap j) ∧
      ∃ b ∈ (run.finalGeometry i₀).carrier,
        ∀ x ∈ X, ZFSet.pair x b ∈ (run.finalGeometry i₀).order := by
  exact fulfilled.ordinary_submodel_countable_localization s collection infinite choice carrier order
    small closed H genericCoded genericFormula (M.symmetricExtension s a supports H)
    (M.symmetricExtension_subset_ordinaryExtension s a supports H) hX subset countable

end

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

theorem row_symmetric_insertion
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (groundChoice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let conditions := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let supports := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)),
      H.GenericFor (M.codedFamily conditions) →
      H.GenericFor (formulaFamily (M.nameDomain conditions)) →
      ∀ c ∈ geometry.carrier, ∀ e ∈ geometry.carrier, ∀ d ∈ geometry.carrier,
      ∀ F ∈ (M.symmetricExtension conditions act supports H).sets,
      MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F →
      ZFSet.pair c e ∈ geometry.order → ZFSet.pair e c ∉ geometry.order →
      ZFSet.pair c d ∈ geometry.order → (∀ x ∈ F, ZFSet.pair e x ∈ geometry.order) →
      F ∈ M.sets ∧ ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
        caps ∈ (M.symmetricExtension conditions act supports H).sets ∧ actors ∈ (M.symmetricExtension conditions act supports H).sets ∧
        FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors
          geometry.order geometry.meetGraph geometry.action c e d F caps actors := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
  let conditions := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let supports := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
  have hX := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have hY := M.natSetCode_mem separation infinite 2
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns)
    (natSetCode 2) ZFSet.omega ⟨_, hX⟩
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY
  have order := M.countableFunctionOrder_mem pairing unions powers separation infinite hX hY
  have closed := M.countable_function_internally_closed pairing unions powers separation
    infinite groundChoice hX hY
  dsimp only
  intro H coded ordinary c hc e he d hd F hF filter lower strict bound above
  exact fulfilled.symmetric_insertion conditions act supports collection infinite groundChoice
    carrier order small closed H coded ordinary smallD irreflexive hc he hd hF filter lower strict bound above

theorem row_symmetric_countable_localization
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (groundChoice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let conditions := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let supports := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)),
      H.GenericFor (M.codedFamily conditions) →
      H.GenericFor (formulaFamily (M.nameDomain conditions)) →
      ∀ X ∈ (M.symmetricExtension conditions act supports H).sets, X ⊆ geometry.carrier →
      (M.symmetricExtension conditions act supports H).groundEmbeddable X ZFSet.omega →
      X ∈ M.sets ∧ M.groundEmbeddable X ZFSet.omega ∧
        (∃ j, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
          ZFSet.pair y x ∈ (run.finalInclusions i₀).pointMap j) ∧
        ∃ b ∈ geometry.carrier, ∀ x ∈ X, ZFSet.pair x b ∈ geometry.order := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
  let conditions := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let supports := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
  have hX := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have hY := M.natSetCode_mem separation infinite 2
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns)
    (natSetCode 2) ZFSet.omega ⟨_, hX⟩
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY
  have order := M.countableFunctionOrder_mem pairing unions powers separation infinite hX hY
  have closed := M.countable_function_internally_closed pairing unions powers separation
    infinite groundChoice hX hY
  dsimp only
  intro H coded ordinary X hX subset countable
  exact fulfilled.symmetric_countable_localization conditions act supports collection infinite groundChoice
    carrier order small closed H coded ordinary hX subset countable

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
