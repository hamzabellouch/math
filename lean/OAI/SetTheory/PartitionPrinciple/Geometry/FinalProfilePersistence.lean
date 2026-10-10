import OAI.SetTheory.PartitionPrinciple.Transfinite.MainBirthExtensions

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

open CountableColumns RationalHeights
variable (Label : Type 1)
local instance : Nonempty Column := ⟨natural 0⟩

noncomputable def FinalPoint : Type 1 := (diagram Label).orders.system.Union
noncomputable def FinalActor : Type 1 := (diagram Label).groups.system.Union

noncomputable instance finalGroup : Group (FinalActor Label) :=
  inferInstanceAs (Group (diagram Label).groups.system.Union)

noncomputable def finalOrder : MeetOrder (FinalPoint Label) := (diagram Label).orders.unionOrder

noncomputable def finalAction : CosetGeometry.OrderAction (FinalActor Label) (finalOrder Label) :=
  (diagram Label).actions.unionAction

noncomputable def finalHeight : StrictHeight (finalOrder Label)
    (lexOrder CountableColumns.order).toHeightOrder := (diagram Label).heights.unionHeight

noncomputable def finalBottom : FinalPoint Label := (diagram Label).unionBottom

theorem finalBottom_least (x : FinalPoint Label) : (finalOrder Label).le (finalBottom Label) x :=
  (diagram Label).unionBottom_least x

noncomputable def finalInclusion (a : Column) : MeetEmbedding (stage Label a).order (finalOrder Label) :=
  (diagram Label).orders.inclusion a

noncomputable def finalGroupInclusion (a : Column) : (stage Label a).Actor →* FinalActor Label :=
  (diagram Label).groups.inclusion a

theorem finalGroupInclusion_injective (a : Column) : Function.Injective (finalGroupInclusion Label a) :=
  (diagram Label).groups.inclusion_injective a

theorem final_points_coherent {a b : Column} (h : a ≤ b) (x : (stage Label a).Point) :
    (finalInclusion Label b).toFun ((transition Label h).points.toFun x) =
      (finalInclusion Label a).toFun x := (diagram Label).orders.system.point_map h x

theorem final_actors_coherent {a b : Column} (h : a ≤ b) (g : (stage Label a).Actor) :
    finalGroupInclusion Label b ((transition Label h).actors g) = finalGroupInclusion Label a g :=
  (diagram Label).groups.system.point_map h g

theorem final_point_cover (x : FinalPoint Label) : ∃ a y, (finalInclusion Label a).toFun y = x :=
  (diagram Label).orders.system.cover x

theorem final_actor_cover (g : FinalActor Label) : ∃ a h, finalGroupInclusion Label a h = g :=
  (diagram Label).groups.system.cover g

theorem final_height_stage (a : Column) (x : (stage Label a).Point) :
    (finalHeight Label).value ((finalInclusion Label a).toFun x) = (stage Label a).height.value x := rfl

theorem final_action_stage (a : Column) (g : (stage Label a).Actor) (x : (stage Label a).Point) :
    ((finalAction Label).iso (finalGroupInclusion Label a g)).toFun ((finalInclusion Label a).toFun x) =
      (finalInclusion Label a).toFun (((stage Label a).action.iso g).toFun x) :=
  (diagram Label).actions.act_point a g x

theorem final_agreement (a : Column) (g k : (stage Label a).Actor) (v : (stage Label a).Point)
    (agree : ∀ x, (stage Label a).order.le x v →
      ((stage Label a).action.iso g).toFun x = ((stage Label a).action.iso k).toFun x)
    (x : FinalPoint Label) (lower : (finalOrder Label).le x ((finalInclusion Label a).toFun v)) :
    ((finalAction Label).iso (finalGroupInclusion Label a g)).toFun x =
      ((finalAction Label).iso (finalGroupInclusion Label a k)).toFun x :=
  (diagram Label).actions.union_agreement (diagram Label).agreements a g k v agree x lower

theorem final_no_maximal (x : FinalPoint Label) :
    ∃ y, (finalOrder Label).le x y ∧ ¬ (finalOrder Label).le y x := by
  rcases final_point_cover Label x with ⟨a, x, rfl⟩
  let b := start a
  have h : a < b := lt_start a
  refine ⟨(finalInclusion Label b).toFun (stage Label b).top, ?_, ?_⟩
  · rw [← final_points_coherent Label h.le x]
    exact ((finalInclusion Label b).le_iff _ _).mpr ((stage Label b).greatest _)
  · intro lower
    rw [← final_points_coherent Label h.le x] at lower
    exact strict_top Label h x (((finalInclusion Label b).le_iff _ _).mp lower)

theorem final_no_greatest : ¬ ∃ top : FinalPoint Label, ∀ x, (finalOrder Label).le x top := by
  rintro ⟨top, greatest⟩
  rcases final_no_maximal Label top with ⟨y, _, strict⟩
  exact strict (greatest y)

end PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

end

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage

universe u

theorem Transition.preservesProfiles_transport {s t t' : MainStage.{u}}
    (f : Transition s t) (eq : t = t') :
    PreservesProfiles (f.transport rfl eq).points ↔ PreservesProfiles f.points := by
  cases eq
  rfl

open CountableColumns

theorem ordinalStep_preservesProfiles (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a))
    (preserves : ∀ {i j} (h : i ≤ j), PreservesProfiles (d.transition h).points)
    (i : Set.Iio a) : PreservesProfiles ((ordinalStep Label a d).leg i).points := by
  classical
  have inhabited : Nonempty (Set.Iio a) := ⟨i⟩
  by_cases hasLast : ∃ last : Set.Iio a, ∀ i, i ≤ last
  · have eq : ordinalStep Label a d =
        (d.lastCone hasLast.choose hasLast.choose_spec).extend (d := d)
          ((d.stage hasLast.choose).nextTransition Label) :=
      (dite_eq_left inhabited).trans (dite_eq_left hasLast)
    rw [eq]
    exact preservesProfiles_comp (d.transition (hasLast.choose_spec i)).points
      ((d.stage hasLast.choose).nextTransition Label).points
      (preserves (hasLast.choose_spec i)) ((d.stage hasLast.choose).next_preservesProfiles Label)
  · let := inhabited
    have eq : ordinalStep Label a d = d.limitCone :=
      (dite_eq_left inhabited).trans (dite_eq_right hasLast)
    rw [eq]
    exact d.limit_preservesProfiles preserves i

namespace OrdinalRun
variable (Label : Type 1)

theorem transition_preservesProfiles_at (b : Column) :
    ∀ a (h : a ≤ b), PreservesProfiles (transition Label h).points := by
  refine (show WellFounded ((· < ·) : Column → Column → Prop) from wellFounded_lt).induction
    (C := fun b => ∀ a (h : a ≤ b), PreservesProfiles (transition Label h).points) b ?_
  intro b ih a h
  rcases lt_or_eq_of_le h with lower | rfl
  · apply (Transition.preservesProfiles_transport (transition Label h)
      (Transfinite.stage_generated (ordinalStep Label) b)).mp
    have maps : (transition Label h).transport rfl
        (Transfinite.stage_generated (ordinalStep Label) b) =
        (ordinalStep Label b (before Label b)).leg ⟨a, lower⟩ :=
      Transfinite.transition_generated (ordinalStep Label) b ⟨a, lower⟩
    rw [maps]
    exact ordinalStep_preservesProfiles Label b (before Label b)
      (fun {_ j} hj => ih j.val j.property _ hj) ⟨a, lower⟩
  · rw [transition_self]
    exact preservesProfiles_identity (stage Label a).order

theorem final_preservesProfiles (a : Column) : PreservesProfiles (finalInclusion Label a) :=
  (diagram Label).union_preservesProfiles
    (fun {_ j} h => transition_preservesProfiles_at Label j _ h) a

end OrdinalRun

end PartitionPilot.Compression.RecursiveMaps.MainStage

end

end OAI
