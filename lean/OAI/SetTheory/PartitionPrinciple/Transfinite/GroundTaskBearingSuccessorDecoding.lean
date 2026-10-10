import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalRectangleFulfillment
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundLinkedTransitionRetarget
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainCompressionActorCode

namespace OAI


namespace PartitionPilot.Forcing
universe u

def StrictSuccessorTopCode (P Q R e top : ZFSet.{u}) : Prop :=
  ∀ x ∈ P, ∀ y ∈ Q, ZFSet.pair x y ∈ e →
    ZFSet.pair y top ∈ R ∧ ZFSet.pair top y ∉ R

namespace BoundedFormula

def strictSuccessorTopFormula {n} (P Q R e top : Fin n) : BoundedFormula n :=
  .allMem P (.allMem Q.succ (imp (pairMembershipFormula 1 0 e.succ.succ)
    (.conj (pairMembershipFormula 0 top.succ.succ R.succ.succ)
      (.neg (pairMembershipFormula top.succ.succ 0 R.succ.succ)))))

theorem truth_strictSuccessorTopFormula {n} (P Q R e top : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (strictSuccessorTopFormula P Q R e top) env ↔
      StrictSuccessorTopCode (env P) (env Q) (env R) (env e) (env top) := by
  simp only [strictSuccessorTopFormula, Truth, truth_imp, truth_pairMembershipFormula]
  rfl

theorem realize_strictSuccessorTopFormula (M : TransitiveGround.{u}) {n}
    (P Q R e top : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    SetFormula.Realize M.sets (strictSuccessorTopFormula P Q R e top).toFormula env ↔
      StrictSuccessorTopCode (env P) (env Q) (env R) (env e) (env top) :=
  (realize_toFormula M _ env members).trans (truth_strictSuccessorTopFormula P Q R e top env)

end BoundedFormula





structure MainSuccessorOutputCode (f : Fin 30 → ZFSet.{u}) : Prop where
  transition : MainTransitionLaws (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
    (f 8) (f 9) (f 10) (f 11) (f 12) (f 13) (f 14) (f 15) (f 16) (f 17) (f 18) (f 19)
  strict_top : StrictSuccessorTopCode (f 0) (f 1) (f 3) (f 18) (f 29)
  separation : SeparationFulfillmentCode (f 0) (f 2) (f 1) (f 3) (f 5) (f 7) (f 13) (f 18)
  rectangles : RectangleFulfillmentCode (f 0) (f 6) (f 2) (f 4) (f 12)
    (f 1) (f 7) (f 3) (f 5) (f 13) (f 18) (f 19)
  old_profiles : OldProfilePreservationCode (f 0) (f 2) (f 4) (f 1) (f 3) (f 5) (f 18) (f 26)
  task_caps : TaskCapFamilyCode (f 21) (f 0) (f 1) (f 3) (f 5) (f 18)
    (f 23) (f 24) (f 25) (f 26) (f 28)
  compression_actors : CompressionActorFulfillmentCode (f 21) (f 0) (f 6) (f 1) (f 7)
    (f 3) (f 13) (f 18) (f 19) (f 22) (f 27) (f 20) (f 28)

namespace BoundedFormula

def mainSuccessorOutputFormula {n} (f : Fin 30 → Fin n) : BoundedFormula n :=
  .conj (mainTransitionLawsFormula (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
    (f 8) (f 9) (f 10) (f 11) (f 12) (f 13) (f 14) (f 15) (f 16) (f 17) (f 18) (f 19))
    (.conj (strictSuccessorTopFormula (f 0) (f 1) (f 3) (f 18) (f 29))
      (.conj (separationFulfillmentFormula (f 0) (f 2) (f 1) (f 3) (f 5) (f 7) (f 13) (f 18))
        (.conj (rectangleFulfillmentFormula (f 0) (f 6) (f 2) (f 4) (f 12)
          (f 1) (f 7) (f 3) (f 5) (f 13) (f 18) (f 19))
          (.conj (oldProfilePreservationFormula (f 0) (f 2) (f 4) (f 1) (f 3) (f 5) (f 18) (f 26))
            (.conj (taskCapFamilyFormula (f 21) (f 0) (f 1) (f 3) (f 5) (f 18)
              (f 23) (f 24) (f 25) (f 26) (f 28))
              (compressionActorFulfillmentFormula (f 21) (f 0) (f 6) (f 1) (f 7)
                (f 3) (f 13) (f 18) (f 19) (f 22) (f 27) (f 20) (f 28)))))))

theorem truth_mainSuccessorOutputFormula {n} (f : Fin 30 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mainSuccessorOutputFormula f) env ↔ MainSuccessorOutputCode (fun j => env (f j)) := by
  simp only [mainSuccessorOutputFormula, Truth, truth_mainTransitionLawsFormula,
    truth_strictSuccessorTopFormula, truth_separationFulfillmentFormula,
    truth_rectangleFulfillmentFormula, truth_oldProfilePreservationFormula,
    truth_taskCapFamilyFormula, truth_compressionActorFulfillmentFormula]
  exact ⟨fun ⟨t, g, s, r, p, c, a⟩ => ⟨t, g, s, r, p, c, a⟩,
    fun code => ⟨code.transition, code.strict_top, code.separation, code.rectangles,
      code.old_profiles, code.task_caps, code.compression_actors⟩⟩

theorem realize_mainSuccessorOutputFormula (M : TransitiveGround.{u}) {n}
    (f : Fin 30 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    SetFormula.Realize M.sets (mainSuccessorOutputFormula f).toFormula env ↔
      MainSuccessorOutputCode (fun j => env (f j)) :=
  (realize_toFormula M _ env members).trans (truth_mainSuccessorOutputFormula f env)

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def MainSuccessorTaskBindingsCode (M : TransitiveGround.{u}) (Labels : ZFSet.{u})
    (f : Fin 30 → ZFSet.{u}) : Prop :=
  f 21 = M.groundEligibleTasks (f 0) (f 6) (f 2) (f 4) (f 12) Labels ∧
  f 22 = literalTaskFieldGraph (f 21) (f 0) (M.groundRelations (f 0) (f 0))
    (M.groundMeetFilters (f 0) (f 2) (f 4)) Labels 0 ∧
  f 23 = literalTaskFieldGraph (f 21) (f 0) (M.groundRelations (f 0) (f 0))
    (M.groundMeetFilters (f 0) (f 2) (f 4)) Labels 1 ∧
  f 24 = literalTaskFieldGraph (f 21) (f 0) (M.groundRelations (f 0) (f 0))
    (M.groundMeetFilters (f 0) (f 2) (f 4)) Labels 3 ∧
  f 25 = literalTaskFieldGraph (f 21) (f 0) (M.groundRelations (f 0) (f 0))
    (M.groundMeetFilters (f 0) (f 2) (f 4)) Labels 4 ∧
  f 26 = M.groundPower (f 0) ∧
  TaskRepresentativesCode (f 27)
    (M.groundEligibleTasks (f 0) (f 6) (f 2) (f 4) (f 12) Labels)
    (f 0) (f 6) (f 2) (f 12) (M.groundRelations (f 0) (f 0))
    (M.groundMeetFilters (f 0) (f 2) (f 4)) Labels

namespace SetFormula

def mainSuccessorTaskBindingsFormula {n} (Labels : Fin n) (f : Fin 30 → Fin n) : SetFormula n :=
  .conj (groundEligibleTasksFormula (f 21) (f 0) (f 6) (f 2) (f 4) (f 12) Labels)
    (.conj (groundLiteralTaskFieldFormula 0 (f 22) (f 21) (f 0) (f 2) (f 4) Labels)
      (.conj (groundLiteralTaskFieldFormula 1 (f 23) (f 21) (f 0) (f 2) (f 4) Labels)
        (.conj (groundLiteralTaskFieldFormula 3 (f 24) (f 21) (f 0) (f 2) (f 4) Labels)
          (.conj (groundLiteralTaskFieldFormula 4 (f 25) (f 21) (f 0) (f 2) (f 4) Labels)
            (.conj (relativePowerFormula (f 0) (f 26))
              (groundTaskRepresentativesFormula (f 27) (f 0) (f 6) (f 2) (f 4) (f 12) Labels))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainSuccessorTaskBindingsFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (Labels : Fin n) (f : Fin 30 → Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (meet : MeetOrderCode (env (f 0)) (env (f 2)) (env (f 4))) :
    Realize M.sets (mainSuccessorTaskBindingsFormula Labels f) env ↔
      MainSuccessorTaskBindingsCode M (env Labels) (fun j => env (f j)) :=
  (M.realize_groundEligibleTasksFormula pairing unions powers separation
    (f 21) (f 0) (f 6) (f 2) (f 4) (f 12) Labels env members meet).and
    ((M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
      0 (f 22) (f 21) (f 0) (f 2) (f 4) Labels env members meet).and
      ((M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
        1 (f 23) (f 21) (f 0) (f 2) (f 4) Labels env members meet).and
        ((M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
          3 (f 24) (f 21) (f 0) (f 2) (f 4) Labels env members meet).and
          ((M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
            4 (f 25) (f 21) (f 0) (f 2) (f 4) Labels env members meet).and
            ((M.realize_relativePowerFormula (f 0) (f 26) env members).and
              (M.realize_groundTaskRepresentativesFormula pairing unions powers separation
                (f 27) (f 0) (f 6) (f 2) (f 4) (f 12) Labels env members meet))))))

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
include certificate pairing unions powers separation infinite

theorem oldProfilePreservation (Filters : ZFSet.{u}) :
    OldProfilePreservationCode source.stage.carrier source.stage.order source.stage.meetGraph
      certificate.target.stage.carrier certificate.target.stage.order certificate.target.stage.meetGraph
      certificate.transition.map.points Filters := by
  intro F _ c _ e _ K _ profile c' _ e' _ K' _ imageC imageE imageK
  exact certificate.capProfile_preserved pairing unions powers separation infinite
    profile imageC imageE imageK

theorem ground_capProfile_preserved
    {c e K F c' e' K' : ZFSet.{u}} (hF : F ∈ M.sets)
    (profile : CodedCapProfile source.stage.carrier source.stage.order source.stage.meetGraph c e K F)
    (imageC : ZFSet.pair c c' ∈ certificate.transition.map.points)
    (imageE : ZFSet.pair e e' ∈ certificate.transition.map.points)
    (imageK : ZFSet.pair K K' ∈ certificate.transition.map.points) :
    relationImage F certificate.target.stage.carrier certificate.transition.map.points ∈ M.sets ∧
      CodedCapProfile certificate.target.stage.carrier certificate.target.stage.order
        certificate.target.stage.meetGraph c' e' K'
        (relationImage F certificate.target.stage.carrier certificate.transition.map.points) :=
  ⟨M.relationImage_mem separation hF certificate.target.stage.carrier_ground
      certificate.transition.map.points_ground,
    certificate.capProfile_preserved pairing unions powers separation infinite profile imageC imageE imageK⟩

end PartitionPilot.Forcing.GroundInitialMainSuccessorData



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem rectangle_fulfillment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) :
    RectangleFulfillmentCode source.stage.carrier source.stage.actors source.stage.order
      source.stage.meetGraph source.stage.action certificate.target.stage.carrier certificate.target.stage.actors
      certificate.target.stage.order certificate.target.stage.meetGraph certificate.target.stage.action
      certificate.transition.map.points certificate.transition.map.actors := by
  obtain ⟨points, order, meet, actors, _, _, _, action, _⟩ := certificate.target_fields
  rw [points, order, meet, actors, action, certificate.point_graph, certificate.actor_graph]
  exact certificate.external.inputs.externalBounded_rectangle_fulfillment
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground





noncomputable def successorOutputValues : Fin 30 → ZFSet.{u} :=
  extend (source.stage.carrier)
    (extend (certificate.target.stage.carrier)
    (extend (source.stage.order)
    (extend (certificate.target.stage.order)
    (extend (source.stage.meetGraph)
    (extend (certificate.target.stage.meetGraph)
    (extend (source.stage.actors)
    (extend (certificate.target.stage.actors)
    (extend (source.stage.multiplication)
    (extend (certificate.target.stage.multiplication)
    (extend (source.stage.identity)
    (extend (certificate.target.stage.identity)
    (extend (source.stage.action)
    (extend (certificate.target.stage.action)
    (extend (source.stage.bottom)
    (extend (certificate.target.stage.bottom)
    (extend (source.stage.height)
    (extend (certificate.target.stage.height)
    (extend (certificate.transition.map.points)
    (extend (certificate.transition.map.actors)
    (extend (source.stage.top)
    (extend (source.stage.compressionTasks Labels)
    (extend (source.stage.compressionSources Labels)
    (extend (source.stage.compressionTargets Labels)
    (extend (source.stage.compressionSeparators Labels)
    (extend (source.stage.compressionFilters Labels)
    (extend (M.groundPower source.stage.carrier)
    (extend (certificate.Reps)
    (extend (certificate.compressionCapImages)
    (extend (certificate.target.stage.top)
    (Fin.elim0))))))))))))))))))))))))))))))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hLabels : Labels ∈ M.sets)
include pairing unions powers separation infinite hLabels

theorem successorOutputValues_ground : ∀ j, certificate.successorOutputValues j ∈ M.sets := by
  obtain ⟨_, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground
    source.stage.meet_ground source.stage.action_ground hLabels source.stage.meet
  exact Fin.cases (source.stage.carrier_ground)
    (Fin.cases (certificate.target.stage.carrier_ground)
    (Fin.cases (source.stage.order_ground)
    (Fin.cases (certificate.target.stage.order_ground)
    (Fin.cases (source.stage.meet_ground)
    (Fin.cases (certificate.target.stage.meet_ground)
    (Fin.cases (source.stage.actors_ground)
    (Fin.cases (certificate.target.stage.actors_ground)
    (Fin.cases (source.stage.multiplication_ground)
    (Fin.cases (certificate.target.stage.multiplication_ground)
    (Fin.cases (source.stage.identity_ground)
    (Fin.cases (certificate.target.stage.identity_ground)
    (Fin.cases (source.stage.action_ground)
    (Fin.cases (certificate.target.stage.action_ground)
    (Fin.cases (source.stage.bottom_ground)
    (Fin.cases (certificate.target.stage.bottom_ground)
    (Fin.cases (source.stage.height_ground)
    (Fin.cases (certificate.target.stage.height_ground)
    (Fin.cases (certificate.transition.map.points_ground)
    (Fin.cases (certificate.transition.map.actors_ground)
    (Fin.cases (source.stage.top_ground)
    (Fin.cases (certificate.indices_ground)
    (Fin.cases (certificate.sources_ground)
    (Fin.cases ((fields 1).1)
    (Fin.cases ((fields 3).1)
    (Fin.cases (certificate.filters_ground)
    (Fin.cases (M.groundPower_mem powers source.stage.carrier_ground)
    (Fin.cases (certificate.representatives_ground)
    (Fin.cases (certificate.compressionCapImages_ground pairing unions powers separation infinite)
    (Fin.cases (certificate.target.stage.top_ground)
    ((fun j => Fin.elim0 j)))))))))))))))))))))))))))))))

theorem successorOutput : MainSuccessorOutputCode certificate.successorOutputValues := by
  refine ⟨certificate.transition.map.laws, ?_,
    certificate.separation_fulfillment pairing unions powers separation infinite,
    certificate.rectangle_fulfillment pairing unions powers separation infinite,
    certificate.oldProfilePreservation pairing unions powers separation infinite (M.groundPower source.stage.carrier),
    certificate.taskCapFamily pairing unions powers separation infinite hLabels,
    certificate.compressionActorFulfillment pairing unions powers separation infinite⟩
  intro x _ y _ image
  exact certificate.strict_new_top x y image

theorem realize_successorOutput :
    Realize M.sets (BoundedFormula.mainSuccessorOutputFormula (fun j => j)).toFormula
      certificate.successorOutputValues :=
  (BoundedFormula.realize_mainSuccessorOutputFormula M (fun j => j)
    certificate.successorOutputValues
    (certificate.successorOutputValues_ground pairing unions powers separation infinite hLabels)).2
    (certificate.successorOutput pairing unions powers separation infinite hLabels)

end PartitionPilot.Forcing.GroundInitialMainSuccessorData



namespace PartitionPilot.Forcing
universe u

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

theorem rawFields_stage_projections :
    linked.rawFields 0 = linked.main.stage.carrier ∧
    linked.rawFields 1 = linked.main.stage.order ∧
    linked.rawFields 2 = linked.main.stage.meetGraph ∧
    linked.rawFields 3 = linked.main.stage.actors ∧
    linked.rawFields 4 = linked.main.stage.multiplication ∧
    linked.rawFields 5 = linked.main.stage.inverse ∧
    linked.rawFields 6 = linked.main.stage.identity ∧
    linked.rawFields 7 = linked.main.stage.action ∧
    linked.rawFields 8 = linked.main.stage.bottom ∧
    linked.rawFields 9 = linked.main.stage.top ∧
    linked.rawFields 10 = linked.main.stage.height :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GroundLinkedMainStage

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem successorOutputValues_projections :
    certificate.successorOutputValues 0 = source.stage.carrier ∧
    certificate.successorOutputValues 1 = certificate.target.stage.carrier ∧
    certificate.successorOutputValues 2 = source.stage.order ∧
    certificate.successorOutputValues 3 = certificate.target.stage.order ∧
    certificate.successorOutputValues 4 = source.stage.meetGraph ∧
    certificate.successorOutputValues 5 = certificate.target.stage.meetGraph ∧
    certificate.successorOutputValues 6 = source.stage.actors ∧
    certificate.successorOutputValues 7 = certificate.target.stage.actors ∧
    certificate.successorOutputValues 8 = source.stage.multiplication ∧
    certificate.successorOutputValues 9 = certificate.target.stage.multiplication ∧
    certificate.successorOutputValues 10 = source.stage.identity ∧
    certificate.successorOutputValues 11 = certificate.target.stage.identity ∧
    certificate.successorOutputValues 12 = source.stage.action ∧
    certificate.successorOutputValues 13 = certificate.target.stage.action ∧
    certificate.successorOutputValues 14 = source.stage.bottom ∧
    certificate.successorOutputValues 15 = certificate.target.stage.bottom ∧
    certificate.successorOutputValues 16 = source.stage.height ∧
    certificate.successorOutputValues 17 = certificate.target.stage.height ∧
    certificate.successorOutputValues 18 = certificate.transition.map.points ∧
    certificate.successorOutputValues 19 = certificate.transition.map.actors ∧
    certificate.successorOutputValues 20 = source.stage.top ∧
    certificate.successorOutputValues 21 = source.stage.compressionTasks Labels ∧
    certificate.successorOutputValues 22 = source.stage.compressionSources Labels ∧
    certificate.successorOutputValues 23 = source.stage.compressionTargets Labels ∧
    certificate.successorOutputValues 24 = source.stage.compressionSeparators Labels ∧
    certificate.successorOutputValues 25 = source.stage.compressionFilters Labels ∧
    certificate.successorOutputValues 26 = M.groundPower source.stage.carrier ∧
    certificate.successorOutputValues 27 = certificate.Reps ∧
    certificate.successorOutputValues 28 = certificate.compressionCapImages ∧
    certificate.successorOutputValues 29 = certificate.target.stage.top :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GroundInitialMainSuccessorData
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u v w

def linkedSuccessorOutputFields {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) : Fin 30 → A :=
  Fin.cases (s 0) (Fin.cases (t 0) (Fin.cases (s 1) (Fin.cases (t 1) (Fin.cases (s 2) (Fin.cases (t 2) (Fin.cases (s 3) (Fin.cases (t 3) (Fin.cases (s 4) (Fin.cases (t 4) (Fin.cases (s 6) (Fin.cases (t 6) (Fin.cases (s 7) (Fin.cases (t 7) (Fin.cases (s 8) (Fin.cases (t 8) (Fin.cases (s 10) (Fin.cases (t 10) (Fin.cases (points) (Fin.cases (actors) (Fin.cases (s 9) (Fin.cases (extra 0) (Fin.cases (extra 1) (Fin.cases (extra 2) (Fin.cases (extra 3) (Fin.cases (extra 4) (Fin.cases (extra 5) (Fin.cases (extra 6) (Fin.cases (extra 7) ((fun _ => t 9))))))))))))))))))))))))))))))

theorem linkedSuccessorOutputFields_map {A : Type v} {B : Type w}
    (map : A → B) (s t : Fin 24 → A) (points actors : A) (extra : Fin 8 → A) :
    (fun j => map (linkedSuccessorOutputFields s t points actors extra j)) =
      linkedSuccessorOutputFields (fun j => map (s j)) (fun j => map (t j))
        (map points) (map actors) (fun j => map (extra j)) := by
  funext j
  exact Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) ((fun k => Fin.elim0 k))))))))))))))))))))))))))))))) j

def TaskBearingMainSuccessorRawCode (M : TransitiveGround.{u})
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : ZFSet.{u})
    (source target : Fin 24 → ZFSet.{u}) (extra : Fin 8 → ZFSet.{u}) : Prop :=
  LinkedMainTransitionRawCode M K Labels C D rD N sourceCode targetCode z points actors
    sourceBirth targetBirth source target ∧
  source 11 ∈ target 11 ∧
  MainSuccessorOutputCode (linkedSuccessorOutputFields source target points actors extra) ∧
  MainSuccessorTaskBindingsCode M Labels (linkedSuccessorOutputFields source target points actors extra)

namespace SetFormula

def taskBearingMainSuccessorRawFormula {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : Fin n)
    (source target : Fin 24 → Fin n) (extra : Fin 8 → Fin n) : SetFormula n :=
  .conj (linkedMainTransitionRawFormula K Labels C D rD N sourceCode targetCode z
    points actors sourceBirth targetBirth source target)
    (.conj (.mem (source 11) (target 11))
      (.conj (BoundedFormula.mainSuccessorOutputFormula
        (linkedSuccessorOutputFields source target points actors extra)).toFormula
        (mainSuccessorTaskBindingsFormula Labels
          (linkedSuccessorOutputFields source target points actors extra))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_taskBearingMainSuccessorRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : Fin n)
    (source target : Fin 24 → Fin n) (extra : Fin 8 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (taskBearingMainSuccessorRawFormula K Labels C D rD N
      sourceCode targetCode z points actors sourceBirth targetBirth source target extra) env ↔
      TaskBearingMainSuccessorRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env sourceCode) (env targetCode) (env z) (env points) (env actors)
        (env sourceBirth) (env targetBirth) (fun j => env (source j))
        (fun j => env (target j)) (fun j => env (extra j)) := by
  have links := M.realize_linkedMainTransitionRawFormula pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth
    source target env members omega ordinal
  have outputs := BoundedFormula.realize_mainSuccessorOutputFormula M
    (linkedSuccessorOutputFields source target points actors extra) env members
  rw [linkedSuccessorOutputFields_map] at outputs
  change (Realize M.sets (linkedMainTransitionRawFormula K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth source target) env ∧
    env (source 11) ∈ env (target 11) ∧
    Realize M.sets (BoundedFormula.mainSuccessorOutputFormula
      (linkedSuccessorOutputFields source target points actors extra)).toFormula env ∧
    Realize M.sets (mainSuccessorTaskBindingsFormula Labels
      (linkedSuccessorOutputFields source target points actors extra)) env) ↔ _
  rw [links, outputs]
  have bindings (raw : LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD)
      (env N) (env sourceCode) (env targetCode) (env z) (env points) (env actors)
      (env sourceBirth) (env targetBirth) (fun j => env (source j)) (fun j => env (target j))) :
      Realize M.sets (mainSuccessorTaskBindingsFormula Labels
        (linkedSuccessorOutputFields source target points actors extra)) env ↔
      MainSuccessorTaskBindingsCode M (env Labels)
        (linkedSuccessorOutputFields (fun j => env (source j)) (fun j => env (target j))
          (env points) (env actors) (fun j => env (extra j))) := by
    have recognized := M.realize_mainSuccessorTaskBindingsFormula pairing unions powers separation
      Labels (linkedSuccessorOutputFields source target points actors extra) env members
      raw.1.2.2.1.1.meet
    rwa [linkedSuccessorOutputFields_map] at recognized
  exact ⟨fun ⟨raw, cutoff, out, bound⟩ => ⟨raw, cutoff, out, (bindings raw).1 bound⟩,
    fun ⟨raw, cutoff, out, bound⟩ => ⟨raw, cutoff, out, (bindings raw).2 bound⟩⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def TaskBearingMainSuccessorCode (M : TransitiveGround.{u})
    (K Labels C D rD N sourceCode targetCode z : ZFSet.{u}) : Prop :=
  ∃ fields : Fin 60 → ZFSet.{u}, (∀ j, fields j ∈ M.sets) ∧
    TaskBearingMainSuccessorRawCode M K Labels C D rD N sourceCode targetCode z
      (fields 48) (fields 49) (fields 50) (fields 51)
      (fun j => fields (j.castAdd 36))
      (fun j => fields (Fin.natAdd 24 (j.castAdd 12)))
      (fun j => fields (Fin.natAdd 52 j))

namespace SetFormula

def taskBearingMainSuccessorFormula {n}
    (K Labels C D rD N sourceCode targetCode z : Fin n) : SetFormula n :=
  let old := suffixIndex n 60
  let fresh := prefixIndex n 60
  exBlock 60 (taskBearingMainSuccessorRawFormula (old K) (old Labels) (old C) (old D)
    (old rD) (old N) (old sourceCode) (old targetCode) (old z)
    (fresh 48) (fresh 49) (fresh 50) (fresh 51)
    (fun j => fresh (j.castAdd 36))
    (fun j => fresh (Fin.natAdd 24 (j.castAdd 12)))
    (fun j => fresh (Fin.natAdd 52 j)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_taskBearingMainSuccessorFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (taskBearingMainSuccessorFormula K Labels C D rD N sourceCode targetCode z) env ↔
      TaskBearingMainSuccessorCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env sourceCode) (env targetCode) (env z) := by
  rw [taskBearingMainSuccessorFormula, realize_exBlock]
  have actual (fields : Fin 60 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    M.realize_taskBearingMainSuccessorRawFormula pairing unions powers separation collection
      (suffixIndex n 60 K) (suffixIndex n 60 Labels) (suffixIndex n 60 C) (suffixIndex n 60 D)
      (suffixIndex n 60 rD) (suffixIndex n 60 N) (suffixIndex n 60 sourceCode)
      (suffixIndex n 60 targetCode) (suffixIndex n 60 z)
      (prefixIndex n 60 48) (prefixIndex n 60 49) (prefixIndex n 60 50) (prefixIndex n 60 51)
      (fun j => prefixIndex n 60 (j.castAdd 36))
      (fun j => prefixIndex n 60 (Fin.natAdd 24 (j.castAdd 12)))
      (fun j => prefixIndex n 60 (Fin.natAdd 52 j))
      (extendMany 60 fields env) (extendMany_members 60 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  exact ⟨fun ⟨fields, ground, recognized⟩ => ⟨fields, ground, (actual fields ground).1 recognized⟩,
    fun ⟨fields, ground, raw⟩ => ⟨fields, ground, (actual fields ground).2 raw⟩⟩

end TransitiveGround

namespace TaskBearingMainSuccessorCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N sourceCode targetCode z : ZFSet.{u}}

theorem linked_transition
    (code : TaskBearingMainSuccessorCode M K Labels C D rD N sourceCode targetCode z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (omega : N = ZFSet.omega) :
    LinkedMainTransitionCode M K Labels C D rD sourceCode targetCode z := by
  obtain ⟨fields, ground, raw⟩ := code
  exact raw.1.exists_transition pairing unions powers separation
    (fun j => ground (j.castAdd 36)) (fun j => ground (Fin.natAdd 24 (j.castAdd 12)))
    (ground 48) (ground 49) hC hD hrD omega

end TaskBearingMainSuccessorCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TaskBearingMainSuccessorCode
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}

theorem output_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    ∃ extra : Fin 8 → ZFSet.{u}, (∀ j, extra j ∈ M.sets) ∧
      MainSuccessorOutputCode (linkedSuccessorOutputFields source.rawFields target.rawFields
        transition.map.points transition.map.actors extra) ∧
      MainSuccessorTaskBindingsCode M Labels (linkedSuccessorOutputFields source.rawFields target.rawFields
        transition.map.points transition.map.actors extra) := by
  obtain ⟨fields, ground, raw⟩ := code
  have sourceEq := source.rawFields_code.fields_unique raw.1.1
  have targetEq := target.rawFields_code.fields_unique raw.1.2.1
  have pairEq : ZFSet.pair transition.map.points transition.map.actors =
      ZFSet.pair (fields 48) (fields 49) := raw.1.2.2.2.2.1.1
  have maps := ZFSet.pair_inj.1 pairEq
  have output := raw.2.2.1
  have bindings := raw.2.2.2
  rw [← sourceEq, ← targetEq, ← maps.1, ← maps.2] at output bindings
  exact ⟨(fun j => fields (Fin.natAdd 52 j)),
    (fun j => ground (Fin.natAdd 52 j)), output, bindings⟩

theorem old_profiles_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    OldProfilePreservationCode source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph
      target.main.stage.carrier target.main.stage.order target.main.stage.meetGraph
      transition.map.points (M.groundPower source.main.stage.carrier) := by
  obtain ⟨extra, _, output, bindings⟩ := code.output_on_linked
  have families := bindings.2.2.2.2.2.1
  have preservation := output.old_profiles
  rw [families] at preservation
  exact preservation

end PartitionPilot.Forcing.TaskBearingMainSuccessorCode



namespace PartitionPilot.Forcing.TaskBearingMainSuccessorCode
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD targetCode z : ZFSet.{u}}
variable {source : GroundLinkedMainStage M K Labels C D rD}

theorem exists_from_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source.code targetCode z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    ∃ target : GroundLinkedMainStage M K Labels C D rD, target.code = targetCode ∧
      ∃ transition : GroundChronologicalMainTransition source.main target.main,
        transition.map.code = z ∧ transition.CoversOldBirths ∧
        OldProfilePreservationCode source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph
          target.main.stage.carrier target.main.stage.order target.main.stage.meetGraph
          transition.map.points (M.groundPower source.main.stage.carrier) := by
  obtain ⟨first, target, sourceEqual, targetEqual, decoded, mapEqual, covered⟩ :=
    code.linked_transition pairing unions powers separation source.main.stage.columns_ground
      source.main.stage.coordinates_ground source.main.stage.coordinate_order_ground rfl
  let transition := decoded.retargetLinked sourceEqual (rfl : target.code = target.code)
  have exactMap : transition.map.code = z :=
    (decoded.retargetLinked_code sourceEqual rfl).trans mapEqual
  have actual : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code := by
    rw [targetEqual, exactMap]
    exact code
  exact ⟨target, targetEqual, transition, exactMap,
    decoded.retargetLinked_coversOldBirths sourceEqual rfl covered,
    actual.old_profiles_on_linked⟩

end PartitionPilot.Forcing.TaskBearingMainSuccessorCode

end OAI
