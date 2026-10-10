import OAI.SetTheory.PartitionPrinciple.Forcing.ExternalFilterBases

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Chronological
universe u

namespace MainStage

theorem all_filters_of_eq {s t : MainStage.{u}} (eq : s = t)
    (small : AllFiltersCountable t.order) : AllFiltersCountable s.order := by cases eq; exact small

theorem initial_all_filters_countable : AllFiltersCountable initial.{u}.order := by
  let : Countable initial.{u}.Point := inferInstanceAs (Countable (ULift.{u} Bool))
  exact all_filters_of_countable initial.order

theorem internal_all_filters_countable (s : MainStage.{u}) (Label : Type u)
    (small : AllFiltersCountable s.order) : AllFiltersCountable (s.internal Label).order :=
  (s.tasks Label).union_all_filters_countable small

theorem next_all_filters_countable (s : MainStage.{u}) (Label : Type u)
    (small : AllFiltersCountable s.order) : AllFiltersCountable (s.next Label).order :=
  (s.requests Label).extension_all_filters_countable (s.internal Label).action
    (s.internal_all_filters_countable Label small)

namespace Diagram
variable {I : Type u} [LinearOrder I] [Countable I] (d : Diagram I)

theorem countable_union_all_filters_countable (small : ∀ i, AllFiltersCountable (d.stage i).order) :
    AllFiltersCountable d.orders.unionOrder :=
  all_filters_of_countable_cover d.orders.system.Point d.orders.order d.orders.inclusion
    d.orders.system.cover small

theorem limit_all_filters_countable [Nonempty I]
    (small : ∀ i, AllFiltersCountable (d.stage i).order) : AllFiltersCountable d.limit.order :=
  FixedTop.all_filters_countable _ (d.countable_union_all_filters_countable small)

end Diagram

open CountableColumns

theorem ordinalStep_all_filters_countable (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a))
    (small : ∀ i, AllFiltersCountable (d.stage i).order) :
    AllFiltersCountable (ordinalStep Label a d).apex.order := by
  classical
  by_cases inhabited : Nonempty (Set.Iio a)
  · by_cases hasLast : ∃ last : Set.Iio a, ∀ i, i ≤ last
    · exact all_filters_of_eq (ordinalStep_last Label a d hasLast.choose hasLast.choose_spec)
        ((d.stage hasLast.choose).next_all_filters_countable Label (small hasLast.choose))
    · let := inhabited
      have eq : ordinalStep Label a d = d.limitCone :=
        (dite_eq_left inhabited).trans (dite_eq_right hasLast)
      exact all_filters_of_eq (congrArg Diagram.Cone.apex eq) (d.limit_all_filters_countable small)
  · exact all_filters_of_eq (ordinalStep_empty Label a d inhabited) initial_all_filters_countable

namespace OrdinalRun
variable (Label : Type 1)

theorem stage_all_filters_countable (a : Column) : AllFiltersCountable (stage Label a).order := by
  have wf : WellFounded ((· < ·) : Column → Column → Prop) := wellFounded_lt
  induction a using wf.induction with
  | h a ih =>
    apply all_filters_of_eq (Transfinite.stage_generated (ordinalStep Label) a)
    exact ordinalStep_all_filters_countable Label a (before Label a) (fun i => ih i.val i.property)

theorem stage_filter_basis (a : Column) (F : MeetFilter (stage Label a).order) : CountableBasis F :=
  stage_all_filters_countable Label a F

theorem countableOrdinalLabels_stage_filter_basis (a : Column)
    (F : MeetFilter (countableOrdinalLabels.stage a).order) : CountableBasis F :=
  stage_filter_basis Column a F

end OrdinalRun

end MainStage
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
