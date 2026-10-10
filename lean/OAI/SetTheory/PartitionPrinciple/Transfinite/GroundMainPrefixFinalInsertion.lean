import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFilterPullbackRecovery
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainPrefixInsertionFamilyTransport
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIndexedImageCovers
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalExtensionBases
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixFinalStrictGrowth
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixInsertionSuccessors

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def pointStageCover : ZFSet.{u} :=
  indexedImageCover run.indices run.carrierUnion run.limitPoints run.limitPointInclusions

theorem pointStageCover_ground : run.pointStageCover ∈ M.sets :=
  M.indexedImageCover_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPoints_ground run.limitPointInclusions_ground

theorem pointStageCover_entry (i : I) (y : ZFSet.{u}) :
    ZFSet.pair y (run.key i) ∈ run.pointStageCover ↔
      ∃ x ∈ (run.diagram.stage i).stage.carrier, ZFSet.pair x y ∈ run.limitPointMap i := by
  rw [pointStageCover, pair_mem_indexedImageCover]
  constructor
  · rintro ⟨_, _, x, _, f, indexed, entry⟩
    have equal := (run.limitPointInclusions_entry i f).1 indexed
    subst f
    exact ⟨x, (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).1, entry⟩
  · rintro ⟨x, hx, entry⟩
    exact ⟨(ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2,
      ZFSet.mem_range.2 ⟨i, rfl⟩, x, run.pointPresentation.carrier_bound i hx,
      run.limitPointMap i, (run.limitPointInclusions_entry i _).2 rfl, entry⟩

theorem pointStageCover_total {y : ZFSet.{u}} (member : y ∈ run.limitPoints) :
    ∃ i ∈ run.indices, ZFSet.pair y i ∈ run.pointStageCover := by
  obtain ⟨i, x, hx, equal⟩ := run.pointPresentation.limitPoint_coverage member
  exact ⟨run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩,
    (run.pointStageCover_entry i y).2
      ⟨x, hx, (run.pointPresentation.inclusion_entry i x y).2 ⟨hx, equal⟩⟩⟩

theorem exists_groundPointStageCover
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X : ZFSet.{u}} (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints) :
    ∃ f ∈ M.sets, ZFSet.IsFunc X run.indices f ∧ f ⊆ run.pointStageCover ∧
      ∀ y t, ZFSet.pair y t ∈ f → ∃ i : I, run.key i = t ∧
        ∃ x ∈ (run.diagram.stage i).stage.carrier, ZFSet.pair x y ∈ run.limitPointMap i := by
  obtain ⟨f, ground, function, included⟩ :=
    M.uniformize_relation pairing unions powers separation choice hX run.indices_ground
      run.pointStageCover_ground (fun _ hy => run.pointStageCover_total (subset hy))
  refine ⟨f, ground, function, included, ?_⟩
  intro y t entry
  have index := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 index
  exact ⟨i, rfl, (run.pointStageCover_entry i y).1 (included entry)⟩

theorem finalInsertionFamilies_transport (j : I)
    {caps actors c₀ d₀ c e d F : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hCaps : caps ∈ M.sets) (hActors : actors ∈ M.sets)
    (capInjection : InjectionCode Labels (run.diagram.stage j).stage.carrier caps)
    (actorInjection : InjectionCode Labels (run.diagram.stage j).stage.actors actors)
    (imageC : ZFSet.pair c₀ c ∈ run.limitPointMap j)
    (imageD : ZFSet.pair d₀ d ∈ run.limitPointMap j)
    (fixes : ∀ label k, ZFSet.pair label k ∈ actors →
      ∀ z ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair z c₀ ∈ (run.diagram.stage j).stage.order →
        ZFSet.pair (ZFSet.pair k z) z ∈ (run.diagram.stage j).stage.action)
    (dominates : ∀ label k cap, ZFSet.pair label k ∈ actors → ZFSet.pair label cap ∈ caps →
      ∀ y ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair (ZFSet.pair k d₀) y ∈ (run.diagram.stage j).stage.action →
        ZFSet.pair y cap ∈ (run.diagram.stage j).stage.order)
    (profiles : ∀ label cap cap', ZFSet.pair label cap ∈ caps →
      ZFSet.pair cap cap' ∈ run.limitPointMap j →
      CodedCapProfile run.limitPoints run.limitOrder run.limitMeetGraph c e cap' F)
    (meets : ∀ first second cap₁ cap₂, ZFSet.pair first cap₁ ∈ caps →
      ZFSet.pair second cap₂ ∈ caps → first ≠ second →
      ZFSet.pair (ZFSet.pair cap₁ cap₂) c₀ ∈ (run.diagram.stage j).stage.meetGraph) :
    run.finalInsertionCaps j caps ∈ M.sets ∧ run.finalInsertionActors j actors ∈ M.sets ∧
      FinalInsertionFamiliesCode Labels run.limitPoints run.limitActors run.limitOrder
        run.limitMeetGraph run.limitAction c e d F
        (run.finalInsertionCaps j caps) (run.finalInsertionActors j actors) := by
  refine ⟨run.finalInsertionCaps_ground j hLabels hCaps,
    run.finalInsertionActors_ground j hLabels hActors, ?_⟩
  refine ⟨run.finalInsertionCaps_injection j capInjection,
    run.finalInsertionActors_injection j actorInjection, ?_, ?_, ?_, ?_⟩
  · intro label k' entry
    obtain ⟨k, oldActor, imageK⟩ := (run.finalInsertionActors_entry j actorInjection).1 entry
    have agreement := ((run.diagram.stage j).stage.action_code.agreement_identity_iff_fixes).2
      (fixes label k oldActor)
    have finalAgreement := run.limitMaps_agreement j k (run.diagram.stage j).stage.identity
      k' (run.limitIdentity j) c₀ c imageK (run.limitActorMap_groupEmbedding j j).one imageC agreement
    exact ((run.limitAction_code j).agreement_identity_iff_fixes).1 finalAgreement
  · intro label k' cap' actorEntry capEntry y _ acted
    obtain ⟨k, oldActor, imageK⟩ := (run.finalInsertionActors_entry j actorInjection).1 actorEntry
    obtain ⟨cap, oldCap, imageCap⟩ := (run.finalInsertionCaps_entry j capInjection).1 capEntry
    have hk := (ZFSet.pair_mem_prod.1 (actorInjection.function.1 oldActor)).2
    have hd₀ := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 imageD)).1
    obtain ⟨y₀, stageActed, _⟩ := (run.diagram.stage j).stage.action_code.function.2
      (ZFSet.pair k d₀) (ZFSet.pair_mem_prod.2 ⟨hk, hd₀⟩)
    have hy₀ := (ZFSet.pair_mem_prod.1 ((run.diagram.stage j).stage.action_code.function.1 stageActed)).2
    obtain ⟨y', imageY, _⟩ := (run.limitPointMap_injection j).function.2 y₀ hy₀
    have targetActed := run.limitMaps_equivariant j k k' d₀ y₀ d y' imageK imageD imageY stageActed
    have actionFunction : FunctionGraphOn (ZFSet.prod run.limitActors run.limitPoints) run.limitAction :=
      ⟨run.limitPoints, run.limitAction_function⟩
    have equal : y = y' := actionFunction.unique acted targetActed
    rw [equal]
    exact (run.limitPointMap_meetEmbedding j).monotone y₀ cap y' cap'
      (dominates label k cap oldActor oldCap y₀ hy₀ stageActed) imageY imageCap
  · intro label cap' entry
    obtain ⟨cap, oldCap, imageCap⟩ := (run.finalInsertionCaps_entry j capInjection).1 entry
    exact profiles label cap cap' oldCap imageCap
  · intro first second cap₁' cap₂' firstEntry secondEntry different
    obtain ⟨cap₁, firstCap, firstImage⟩ := (run.finalInsertionCaps_entry j capInjection).1 firstEntry
    obtain ⟨cap₂, secondCap, secondImage⟩ := (run.finalInsertionCaps_entry j capInjection).1 secondEntry
    exact (run.limitPointMap_meetEmbedding j).map_meet cap₁ cap₂ c₀ cap₁' cap₂' c
      (meets first second cap₁ cap₂ firstCap secondCap different) firstImage secondImage imageC

end GroundMainPrefix

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (indices : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
include collection infinite choice indices

theorem exists_countablePointStageCover {X : ZFSet.{u}}
    (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints)
    (small : M.groundEmbeddable X ZFSet.omega) :
    ∃ j : I, ∃ f ∈ M.sets, ZFSet.IsFunc X run.indices f ∧ f ⊆ run.pointStageCover ∧
      (∀ x t, ZFSet.pair x t ∈ f → t ∈ run.key j) ∧
      ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair y x ∈ run.limitPointMap j := by
  obtain ⟨f, ground, function, included, covers⟩ :=
    run.exists_groundPointStageCover choice hX subset
  have rangeGround := M.relationImage_mem separation hX run.indices_ground ground
  have rangeSmall := M.groundEmbeddable_function_image pairing unions powers separation choice
    hX run.indices_ground (M.omega_mem separation infinite) ground function small
  have rangeSubset : relationImage X run.indices f ⊆
      M.groundOmegaOne pairing unions powers separation collection infinite := by
    intro t ht
    rw [← indices]
    exact ((mem_relationImage _ _ _ _).1 ht).1
  obtain ⟨bound, inOmega, strict⟩ := M.groundOmegaOne_countable_bound
    pairing unions powers separation collection infinite choice rangeGround rangeSubset rangeSmall
  have inIndices : bound ∈ run.indices := by rw [indices]; exact inOmega
  obtain ⟨j, equal⟩ := ZFSet.mem_range.1 inIndices
  have strictEntry : ∀ x t, ZFSet.pair x t ∈ f → t ∈ run.key j := by
    intro x t entry
    rw [equal]
    have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact strict t ((mem_relationImage _ _ _ _).2 ⟨bounds.2, x, bounds.1, entry⟩)
  refine ⟨j, f, ground, function, included, strictEntry, ?_⟩
  intro x hx
  obtain ⟨t, entry, _⟩ := function.2 x hx
  obtain ⟨i, key, y, hy, image⟩ := covers x t entry
  have before : i ≤ j := (run.key_order i j).2 (Or.inr (by rw [key]; exact strictEntry x t entry))
  obtain ⟨z, transition⟩ := run.pointSystem.map_entry_total before hy
  exact ⟨z, (run.pointSystem.map_entry_bounds before transition).2,
    run.limitPointMap_later_entry before transition image⟩

theorem exists_countablePointLocalization {X : ZFSet.{u}}
    (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints)
    (small : M.groundEmbeddable X ZFSet.omega) :
    ∃ j : I, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
      ZFSet.pair y x ∈ run.limitPointMap j := by
  obtain ⟨j, _, _, _, _, _, covered⟩ :=
    run.exists_countablePointStageCover collection infinite choice indices hX subset small
  exact ⟨j, covered⟩

theorem exists_countablePointUpperBound {X : ZFSet.{u}}
    (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints)
    (small : M.groundEmbeddable X ZFSet.omega) :
    ∃ j : I, ∃ b ∈ M.sets, b ∈ run.limitPoints ∧
      ZFSet.pair (run.diagram.stage j).stage.top b ∈ run.limitPointMap j ∧
      ∀ x ∈ X, ZFSet.pair x b ∈ run.limitOrder := by
  obtain ⟨j, covered⟩ :=
    run.exists_countablePointLocalization collection infinite choice indices hX subset small
  obtain ⟨b, image, _⟩ := (run.limitPointMap_injection j).function.2
    (run.diagram.stage j).stage.top (run.diagram.stage j).stage.top_mem
  have member := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 image)).2
  refine ⟨j, b, M.transitive run.limitPoints_ground member, member, image, ?_⟩
  intro x hx
  obtain ⟨y, hy, atStage⟩ := covered x hx
  exact (run.limitPointMap_order_iff j y (run.diagram.stage j).stage.top x b atStage image).2
    ((run.diagram.stage j).stage.greatest y hy)

end GroundMainPrefix

section
universe u v

namespace CodedCapProfile

theorem of_pushFilter_eq {L r μ c E cap H e F : ZFSet.{u}}
    (profile : CodedCapProfile L r μ c E cap (relationImage H L e))
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (equal : pushFilterCode L r e H = F) : CodedCapProfile L r μ c E cap F := by
  have positive_iff (x : ZFSet.{u}) (hx : x ∈ L) :
      (∃ y ∈ relationImage H L e, ZFSet.pair y x ∈ r) ↔ x ∈ F := by
    rw [← equal, mem_pushFilterCode]
    constructor
    · rintro ⟨y, hy, lower⟩
      obtain ⟨hyL, h, hh, image⟩ := (mem_relationImage H L e y).1 hy
      exact ⟨hx, h, hh, y, hyL, image, lower⟩
    · rintro ⟨_, h, hh, y, hy, image, lower⟩
      exact ⟨y, (mem_relationImage H L e y).2 ⟨hy, h, hh, image⟩, lower⟩
  refine ⟨profile.target_mem, profile.separator_mem, profile.cap_mem, filter.subset,
    filter.nonempty, ?_, profile.target_below_cap, profile.cap_not_below_target,
    profile.separator_not_below_cap⟩
  intro x hx above
  have original := profile.profile x hx above
  constructor
  · rintro ⟨f, hf, lower⟩
    exact original.1 ((positive_iff x hx).2 (filter.upward f hf x hx lower))
  · intro negative
    exact original.2 (fun positive => negative
      ⟨x, (positive_iff x hx).1 positive, meet.order.refl x hx⟩)

end CodedCapProfile

namespace GroundMainPrefix
open SetFormula
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitInsertionProfile {i j : I} (before : i ≤ j)
    (preserved : run.PreservesOldProfiles)
    {H F c E cap c' E' cap' : ZFSet.{u}} (hH : H ∈ M.sets)
    (subset : H ⊆ (run.diagram.stage i).stage.carrier)
    (filter : MeetFilterCode run.limitPoints run.limitOrder run.limitMeetGraph F)
    (equal : pushFilterCode run.limitPoints run.limitOrder (run.limitPointMap i) H = F)
    (profile : CodedCapProfile (run.diagram.stage j).stage.carrier
      (run.diagram.stage j).stage.order (run.diagram.stage j).stage.meetGraph c E cap
      (relationImage H (run.diagram.stage j).stage.carrier (run.diagram.transition before).map.points))
    (imageC : ZFSet.pair c c' ∈ run.limitPointMap j)
    (imageE : ZFSet.pair E E' ∈ run.limitPointMap j)
    (imageCap : ZFSet.pair cap cap' ∈ run.limitPointMap j) :
    CodedCapProfile run.limitPoints run.limitOrder run.limitMeetGraph c' E' cap' F := by
  have whole : relationImage H (run.diagram.stage j).stage.carrier
      (run.diagram.transition before).map.points ∈ M.sets :=
    M.relationImage_mem separation hH (run.diagram.stage j).stage.carrier_ground
      (run.diagram.transition before).map.points_ground
  have hc' := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 imageC)).2
  have hE' := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 imageE)).2
  have hcap' := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 imageCap)).2
  have finalProfile := run.limitPointMap_oldProfilePreservation preserved j _
    ((M.mem_groundPower _ _).2 ⟨whole, profile.filter_subset⟩)
    c profile.target_mem E profile.separator_mem cap profile.cap_mem profile
    c' hc' E' hE' cap' hcap' imageC imageE imageCap
  have imageEqual :
      relationImage (relationImage H (run.diagram.stage j).stage.carrier
        (run.diagram.transition before).map.points) run.limitPoints (run.limitPointMap j) =
      relationImage H run.limitPoints (run.limitPointMap i) :=
    (relationImage_composition_on subset).trans
      (congrArg (relationImage H run.limitPoints) (run.limitPointMap_comp before))
  rw [imageEqual] at finalProfile
  exact finalProfile.of_pushFilter_eq run.limitMeet_code filter equal

end GroundMainPrefix
end

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem final_insertion_at {i j : I} (before : i ≤ j)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (preserved : run.PreservesOldProfiles) (hLabels : Labels ∈ M.sets)
    {c₀ e₀ d₀ H c e d F : ZFSet.{u}}
    (hc₀ : c₀ ∈ (run.diagram.stage i).stage.carrier)
    (he₀ : e₀ ∈ (run.diagram.stage i).stage.carrier)
    (hd₀ : d₀ ∈ (run.diagram.stage i).stage.carrier) (hH : H ∈ M.sets)
    (localFilter : MeetFilterCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph H)
    (filter : MeetFilterCode run.limitPoints run.limitOrder run.limitMeetGraph F)
    (equal : pushFilterCode run.limitPoints run.limitOrder (run.limitPointMap i) H = F)
    (imageC : ZFSet.pair c₀ c ∈ run.limitPointMap i)
    (imageE : ZFSet.pair e₀ e ∈ run.limitPointMap i)
    (imageD : ZFSet.pair d₀ d ∈ run.limitPointMap i)
    (lower : ZFSet.pair c₀ e₀ ∈ (run.diagram.stage i).stage.order)
    (strict : ZFSet.pair e₀ c₀ ∉ (run.diagram.stage i).stage.order)
    (above : ∀ x ∈ H, ZFSet.pair e₀ x ∈ (run.diagram.stage i).stage.order) :
    ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
      FinalInsertionFamiliesCode Labels run.limitPoints run.limitActors run.limitOrder
        run.limitMeetGraph run.limitAction c e d F caps actors := by
  obtain ⟨caps, hCaps, actors, hActors, capInjection, actorInjection, _, laws⟩ :=
    run.insertionFamilies_of_taskBearing before code choice hLabels hc₀ he₀ hH localFilter
      lower strict above
  obtain ⟨c₁, stepC⟩ := run.pointSystem.map_entry_total before hc₀
  obtain ⟨e₁, stepE⟩ := run.pointSystem.map_entry_total before he₀
  obtain ⟨d₁, stepD⟩ := run.pointSystem.map_entry_total before hd₀
  have finalC := run.limitPointMap_later_entry before stepC imageC
  have finalE := run.limitPointMap_later_entry before stepE imageE
  have finalD := run.limitPointMap_later_entry before stepD imageD
  obtain ⟨fixes, dominates, profiles, meets⟩ := laws c₁ e₁ stepC stepE
  have finalFamilies := run.finalInsertionFamilies_transport j hLabels hCaps hActors
    capInjection actorInjection finalC finalD fixes
    (fun label k cap actor capEntry y _ acted => dominates label k cap actor capEntry
      d₀ d₁ y stepD acted)
    (fun label cap cap' entry imageCap => run.limitInsertionProfile before preserved hH
      localFilter.subset filter equal (profiles label cap entry) finalC finalE imageCap)
    meets
  exact ⟨run.finalInsertionCaps j caps, finalFamilies.1,
    run.finalInsertionActors j actors, finalFamilies.2.1, finalFamilies.2.2⟩

theorem filterPullback_configuration (i : I) {c e d c₀ e₀ d₀ F : ZFSet.{u}}
    (imageC : ZFSet.pair c₀ c ∈ run.limitPointMap i)
    (imageE : ZFSet.pair e₀ e ∈ run.limitPointMap i)
    (imageD : ZFSet.pair d₀ d ∈ run.limitPointMap i)
    (lower : ZFSet.pair c e ∈ run.limitOrder) (strict : ZFSet.pair e c ∉ run.limitOrder)
    (bound : ZFSet.pair c d ∈ run.limitOrder)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ run.limitOrder) :
    ZFSet.pair c₀ e₀ ∈ (run.diagram.stage i).stage.order ∧
    ZFSet.pair e₀ c₀ ∉ (run.diagram.stage i).stage.order ∧
    ZFSet.pair c₀ d₀ ∈ (run.diagram.stage i).stage.order ∧
    ∀ x ∈ copyPullback (run.diagram.stage i).stage.carrier run.limitPoints
        (run.limitPointMap i) F, ZFSet.pair e₀ x ∈ (run.diagram.stage i).stage.order := by
  refine ⟨(run.limitPointMap_order_iff i c₀ e₀ c e imageC imageE).1 lower,
    (fun reverse => strict ((run.limitPointMap_order_iff i e₀ c₀ e c imageE imageC).2 reverse)),
    (run.limitPointMap_order_iff i c₀ d₀ c d imageC imageD).1 bound, ?_⟩
  intro x hx
  obtain ⟨_, y, hy, _, image⟩ := (mem_copyPullback _ _ _ _ x).1 hx
  exact (run.limitPointMap_order_iff i e₀ x e y imageE image).1 (above y hy)

namespace FinalChronology
variable {run} {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)
include chronology

theorem exists_groundFilterLocalization (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (indices : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (coordinateSmall : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F c e d : ZFSet.{u}} (hF : F ∈ M.sets)
    (filter : MeetFilterCode run.limitPoints run.limitOrder run.limitMeetGraph F)
    (hc : c ∈ run.limitPoints) (he : e ∈ run.limitPoints) (hd : d ∈ run.limitPoints) :
    ∃ i c₀ e₀ d₀ H,
      H = copyPullback (run.diagram.stage i).stage.carrier run.limitPoints (run.limitPointMap i) F ∧
      c₀ ∈ (run.diagram.stage i).stage.carrier ∧ e₀ ∈ (run.diagram.stage i).stage.carrier ∧
      d₀ ∈ (run.diagram.stage i).stage.carrier ∧
      ZFSet.pair c₀ c ∈ run.limitPointMap i ∧ ZFSet.pair e₀ e ∈ run.limitPointMap i ∧
      ZFSet.pair d₀ d ∈ run.limitPointMap i ∧ H ∈ M.sets ∧
      MeetFilterCode (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.order
        (run.diagram.stage i).stage.meetGraph H ∧
      pushFilterCode run.limitPoints run.limitOrder (run.limitPointMap i) H = F := by
  obtain ⟨B, hB, f, hf, injection, subset, coinitial⟩ :=
    chronology.exists_extension_basis i₀ (fun _ h => h) pairing unions powers separation
      infinite choice coordinateSmall irreflexive hF filter
  obtain ⟨j, covers⟩ := run.exists_countablePointLocalization collection infinite choice indices
    hB (fun _ hb => filter.subset (subset hb)) ⟨f, hf, injection⟩
  obtain ⟨k, c₁, e₁, d₁, hc₁, he₁, hd₁, rfl, rfl, rfl⟩ :=
    run.pointPresentation.triple_coverage hc he hd
  obtain ⟨i, ji, ki⟩ := run.common_upper j k
  obtain ⟨c₀, cStep⟩ := run.pointSystem.map_entry_total ki hc₁
  obtain ⟨e₀, eStep⟩ := run.pointSystem.map_entry_total ki he₁
  obtain ⟨d₀, dStep⟩ := run.pointSystem.map_entry_total ki hd₁
  have imageC := run.limitPointMap_later_entry ki cStep
    ((run.pointPresentation.inclusion_entry k c₁ _).2 ⟨hc₁, rfl⟩)
  have imageE := run.limitPointMap_later_entry ki eStep
    ((run.pointPresentation.inclusion_entry k e₁ _).2 ⟨he₁, rfl⟩)
  have imageD := run.limitPointMap_later_entry ki dStep
    ((run.pointPresentation.inclusion_entry k d₁ _).2 ⟨hd₁, rfl⟩)
  have coversAt : ∀ b ∈ B, ∃ a ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair a b ∈ run.limitPointMap i := by
    intro b hb
    obtain ⟨a, ha, image⟩ := covers b hb
    obtain ⟨a', step⟩ := run.pointSystem.map_entry_total ji ha
    exact ⟨a', (run.pointSystem.map_entry_bounds ji step).2,
      run.limitPointMap_later_entry ji step image⟩
  let H := copyPullback (run.diagram.stage i).stage.carrier run.limitPoints (run.limitPointMap i) F
  have ground : H ∈ M.sets := M.copyPullback_mem pairing unions powers separation
    (run.diagram.stage i).stage.carrier_ground run.limitPoints_ground (run.limitPointMap_ground i) hF
  have nonempty : H.Nonempty := by
    obtain ⟨x, hx⟩ := filter.nonempty
    obtain ⟨b, hb, _⟩ := coinitial x hx
    obtain ⟨a, ha, image⟩ := coversAt b hb
    exact ⟨a, (mem_copyPullback _ _ _ _ a).2 ⟨ha, b, subset hb, filter.subset (subset hb), image⟩⟩
  have localFilter := meetFilter_copyPullback (run.diagram.stage i).stage.meet filter
    (run.limitPointMap_meetEmbedding i) nonempty
  have recovered : pushFilterCode run.limitPoints run.limitOrder (run.limitPointMap i) H = F := by
    apply pushFilter_copyPullback_eq_of_coinitial (run.limitPointMap_injection i).function filter
    intro x hx
    obtain ⟨b, hb, lower⟩ := coinitial x hx
    obtain ⟨a, ha, image⟩ := coversAt b hb
    exact ⟨b, subset hb, a, ha, image, lower⟩
  exact ⟨i, c₀, e₀, d₀, H, rfl, (run.pointSystem.map_entry_bounds ki cStep).2,
    (run.pointSystem.map_entry_bounds ki eStep).2, (run.pointSystem.map_entry_bounds ki dStep).2,
    imageC, imageE, imageD, ground, localFilter, recovered⟩

end FinalChronology

end GroundMainPrefix

namespace GroundMainPrefix.FinalChronology
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)
include chronology

theorem final_insertion_of_trace (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (indices : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code) (preserved : run.PreservesOldProfiles)
    (hLabels : Labels ∈ M.sets) (coordinateSmall : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {c e d F : ZFSet.{u}} (hc : c ∈ run.limitPoints) (he : e ∈ run.limitPoints)
    (hd : d ∈ run.limitPoints) (hF : F ∈ M.sets)
    (filter : MeetFilterCode run.limitPoints run.limitOrder run.limitMeetGraph F)
    (lower : ZFSet.pair c e ∈ run.limitOrder) (strict : ZFSet.pair e c ∉ run.limitOrder)
    (bound : ZFSet.pair c d ∈ run.limitOrder)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ run.limitOrder) :
    ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
      FinalInsertionFamiliesCode Labels run.limitPoints run.limitActors run.limitOrder
        run.limitMeetGraph run.limitAction c e d F caps actors := by
  obtain ⟨i, c₀, e₀, d₀, H, pullback, hc₀, he₀, hd₀, imageC, imageE, imageD,
    hH, localFilter, equal⟩ := chronology.exists_groundFilterLocalization i₀ collection infinite
      choice indices coordinateSmall irreflexive hF filter hc he hd
  have configuration := run.filterPullback_configuration i imageC imageE imageD lower strict bound above
  have aboveH : ∀ x ∈ H, ZFSet.pair e₀ x ∈ (run.diagram.stage i).stage.order := by
    simpa only [pullback] using configuration.2.2.2
  have member : run.key i ∈ M.groundOmegaOne pairing unions powers separation collection infinite :=
    indices ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have next := M.groundOmegaOne_successor pairing unions powers separation collection infinite member
  obtain ⟨j, adjacent⟩ := ZFSet.mem_range.1 (indices.symm ▸ next)
  have before : i ≤ j := (run.key_order i j).2 (by
    rw [adjacent]
    exact Or.inr (ZFSet.mem_insert (run.key i) (run.key i)))
  exact run.final_insertion_at before
    (run.terminal_successor_taskBearing trace chosen tasks indices extension before adjacent)
    choice preserved hLabels hc₀ he₀ hd₀ hH localFilter filter equal imageC imageE imageD
    configuration.1 configuration.2.1 aboveH

end GroundMainPrefix.FinalChronology

end PartitionPilot.Forcing

end OAI
