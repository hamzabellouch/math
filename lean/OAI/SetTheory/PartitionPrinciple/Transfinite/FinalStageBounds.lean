import OAI.SetTheory.PartitionPrinciple.Forcing.FinalFilterLocalization

namespace OAI

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

open CountableColumns BirthLabels
variable (Label : Type 1)

noncomputable def birthStep (a : Column)
    (past : ∀ b, b < a → BirthRecord (stage Label b) b) : BirthRecord (stage Label a) a := by
  classical
  let seed : EarlierBirths Label a := fun i => past i.val i.property
  exact if coherent : EarlierCoherent Label a seed then extendBirths Label a seed coherent
    else BirthRecord.constant (stage Label a) a

noncomputable def birthRun : ∀ a : Column, BirthRecord (stage Label a) a :=
  wellFounded_lt.fix (birthStep Label)

theorem birthRun_eq (a : Column) :
    birthRun Label a = birthStep Label a (fun b _ => birthRun Label b) := wellFounded_lt.fix_eq _ a

theorem birthRun_coherent_at (a : Column) : ∀ b (h : b ≤ a) (x : (stage Label b).Point),
    (birthRun Label a).birth ((transition Label h).points.toFun x) = (birthRun Label b).birth x := by
  refine (show WellFounded ((· < ·) : Column → Column → Prop) from wellFounded_lt).induction
    (C := fun a => ∀ b (h : b ≤ a) (x : (stage Label b).Point),
      (birthRun Label a).birth ((transition Label h).points.toFun x) = (birthRun Label b).birth x) a ?_
  intro a ih
  let seed : EarlierBirths Label a := fun i => birthRun Label i.val
  have coherent : EarlierCoherent Label a seed := by
    intro i j h x
    exact ih j.val j.property i.val h x
  have generated : birthRun Label a = extendBirths Label a seed coherent :=
    (birthRun_eq Label a).trans (dite_eq_left (c := EarlierCoherent Label a seed) coherent)
  intro b h x
  rcases lt_or_eq_of_le h with lower | rfl
  · rw [generated]
    exact extendBirths_preserves Label a seed coherent ⟨b, lower⟩ x
  · rw [transition_self]
    rfl

theorem birthRun_earlier_coherent (a : Column) :
    EarlierCoherent Label a (fun i => birthRun Label i.val) :=
  fun {_ j} h x => birthRun_coherent_at Label j.val _ h x

theorem birthRun_generated (a : Column) :
    birthRun Label a = extendBirths Label a (fun i => birthRun Label i.val)
      (birthRun_earlier_coherent Label a) :=
  (birthRun_eq Label a).trans
    (dite_eq_left (c := EarlierCoherent Label a (fun i => birthRun Label i.val))
      (birthRun_earlier_coherent Label a))

theorem birthRun_source (a : Column) (x : (stage Label a).Point) :
    (∃ i : Set.Iio a, ∃ y, (transition Label i.property.le).points.toFun y = x ∧
      (birthRun Label a).birth x = (birthRun Label i.val).birth y) ∨
      main ((birthRun Label a).birth x) = a := by
  rw [birthRun_generated Label a]
  exact extendBirths_source Label a (fun i => birthRun Label i.val)
    (birthRun_earlier_coherent Label a) x

end PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

open Chronological CountableColumns
universe v
variable (Label : Type 1) (BirthIndex : Type v) [LinearOrder BirthIndex]

structure BoundedBirthCertificate where
  birth : FinalPoint Label → BirthIndex
  old_meet : OldMeet (P := finalOrder Label) birth
  bound : BirthIndex → Column
  covered : ∀ x, ∃ y, (finalInclusion Label (bound (birth x))).toFun y = x

variable {Label BirthIndex} [WellFoundedLT BirthIndex]

omit [WellFoundedLT BirthIndex] in
theorem BoundedBirthCertificate.fiber_basis
    (c : BoundedBirthCertificate Label BirthIndex) (F : MeetFilter (finalOrder Label))
    (t : BirthIndex) :
    CountableBelow F (fun x => Essential c.birth F x ∧ c.birth x = t) := by
  apply countableBelow_mono F
    (countableBelow_copy (finalInclusion Label (c.bound t)) F
      (stage_all_filters_countable Label (c.bound t)))
  intro x hx
  refine ⟨hx.1.1, ?_⟩
  have represented := c.covered x
  rw [hx.2] at represented
  exact represented

theorem BoundedBirthCertificate.all_filters_countable
    (c : BoundedBirthCertificate Label BirthIndex) : AllFiltersCountable (finalOrder Label) := by
  intro F
  apply countable_basis_of_layers c.birth F
  · exact essential_stages_countable c.birth (finalHeight Label)
      CountableColumns.descending_property c.old_meet F
  · exact c.fiber_basis F

theorem BoundedBirthCertificate.localizes
    (c : BoundedBirthCertificate Label BirthIndex) (F : MeetFilter (finalOrder Label)) :
    LocalizedFilter Label F := basis_localized Label F (c.all_filters_countable F)

end PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

open Chronological CountableColumns BirthLabels
variable (Label : Type 1)

theorem birthRun_origin (a : Column) : ∀ x : (stage Label a).Point,
    ∃ y, (finalInclusion Label (main ((birthRun Label a).birth x))).toFun y =
      (finalInclusion Label a).toFun x := by
  refine (show WellFounded ((· < ·) : Column → Column → Prop) from wellFounded_lt).induction
    (C := fun a => ∀ x : (stage Label a).Point,
      ∃ y, (finalInclusion Label (main ((birthRun Label a).birth x))).toFun y =
        (finalInclusion Label a).toFun x) a ?_
  intro a ih x
  rcases birthRun_source Label a x with ⟨i, y, eq, born⟩ | fresh
  · rw [born]
    rcases ih i.val i.property y with ⟨z, hz⟩
    exact ⟨z, hz.trans ((final_points_coherent Label i.property.le y).symm.trans
      (congrArg (finalInclusion Label a).toFun eq))⟩
  · rw [fresh]
    exact ⟨x, rfl⟩

noncomputable def finalBirth : FinalPoint Label → Index :=
  (diagram Label).orders.system.descend (fun a => (birthRun Label a).birth)
    (fun {_ b} h x => birthRun_coherent_at Label b _ h x)

theorem finalBirth_stage (a : Column) (x : (stage Label a).Point) :
    finalBirth Label ((finalInclusion Label a).toFun x) = (birthRun Label a).birth x := rfl

theorem finalBirth_old_meet : OldMeet (P := finalOrder Label) (finalBirth Label) :=
  oldMeet_of_covered_stages (fun a => (stage Label a).order) (finalBirth Label)
    (fun a => (birthRun Label a).birth) (finalInclusion Label) (fun _ _ => rfl)
    ((diagram Label).orders.system.pair_cover (diagram Label).orders.system)
    (fun a => (birthRun Label a).old_meet)

theorem finalBirth_origin (x : FinalPoint Label) :
    ∃ y, (finalInclusion Label (main (finalBirth Label x))).toFun y = x := by
  rcases final_point_cover Label x with ⟨a, x, rfl⟩
  exact birthRun_origin Label a x

theorem finalBirth_main_le (a : Column) (x : (stage Label a).Point) :
    main (finalBirth Label ((finalInclusion Label a).toFun x)) ≤ a :=
  main_le ((birthRun Label a).bounded x)

theorem finalBirth_main_eq_canonical (x : FinalPoint Label) :
    main (finalBirth Label x) = (diagram Label).orders.system.birth x := by
  apply le_antisymm
  · rcases (diagram Label).orders.system.present_birth x with ⟨y, eq⟩
    have bounded := finalBirth_main_le Label ((diagram Label).orders.system.birth x) y
    change main (finalBirth Label ((diagram Label).orders.system.point
      ((diagram Label).orders.system.birth x) y)) ≤ _ at bounded
    rw [eq] at bounded
    exact bounded
  · exact ((diagram Label).orders.system.birth_le_iff x _).mpr (finalBirth_origin Label x)

noncomputable def finalBirthCertificate : BoundedBirthCertificate Label Index where
  birth := finalBirth Label
  old_meet := finalBirth_old_meet Label
  bound := main
  covered := finalBirth_origin Label

theorem final_all_filters_countable : AllFiltersCountable (finalOrder Label) :=
  (finalBirthCertificate Label).all_filters_countable

theorem final_filter_basis (F : MeetFilter (finalOrder Label)) : CountableBasis F :=
  final_all_filters_countable Label F

theorem final_filters_localized (F : MeetFilter (finalOrder Label)) : LocalizedFilter Label F :=
  (finalBirthCertificate Label).localizes F

theorem countableOrdinalLabels_final_filter_basis (F : MeetFilter (finalOrder Column)) :
    CountableBasis F := final_filter_basis Column F

end PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

open CountableColumns
universe v w
variable (Label : Type 1)

theorem final_countable_upper_bound (B : Set (FinalPoint Label)) (small : B.Countable) :
    ∃ top, ∀ x ∈ B, (finalOrder Label).le x top := by
  rcases countable_points_in_stage Label B small with ⟨a, cover⟩
  refine ⟨(finalInclusion Label a).toFun (stage Label a).top, ?_⟩
  intro x hx
  rcases cover x hx with ⟨y, rfl⟩
  exact ((finalInclusion Label a).le_iff _ _).mpr ((stage Label a).greatest y)

theorem countable_actors_in_stage (B : Set (FinalActor Label)) (small : B.Countable) :
    ∃ a, ∀ g ∈ B, ∃ h, finalGroupInclusion Label a h = g := by
  classical
  let := small.to_subtype
  let index (g : B) : Column := Classical.choose (final_actor_cover Label g.val)
  have represented (g : B) : ∃ h, finalGroupInclusion Label (index g) h = g.val :=
    Classical.choose_spec (final_actor_cover Label g.val)
  refine ⟨upperBound index, ?_⟩
  intro g hg
  rcases represented ⟨g, hg⟩ with ⟨h, eq⟩
  have lower : index ⟨g, hg⟩ < upperBound index := upperBound_above index ⟨g, hg⟩
  exact ⟨(transition Label lower.le).actors h, (final_actors_coherent Label lower.le h).trans eq⟩

theorem countable_data_in_stage {I : Type v} {J : Type w} [Countable I] [Countable J]
    (points : I → FinalPoint Label) (actors : J → FinalActor Label) :
    ∃ a, (∀ i, ∃ x, (finalInclusion Label a).toFun x = points i) ∧
      (∀ j, ∃ g, finalGroupInclusion Label a g = actors j) := by
  rcases countable_points_in_stage Label (Set.range points) (Set.countable_range points) with ⟨a, hp⟩
  rcases countable_actors_in_stage Label (Set.range actors) (Set.countable_range actors) with ⟨b, hg⟩
  refine ⟨max a b, ?_, ?_⟩
  · intro i
    rcases hp (points i) (Set.mem_range_self i) with ⟨x, hx⟩
    exact ⟨(transition Label (le_max_left a b)).points.toFun x,
      (final_points_coherent Label (le_max_left a b) x).trans hx⟩
  · intro j
    rcases hg (actors j) (Set.mem_range_self j) with ⟨g, hg⟩
    exact ⟨(transition Label (le_max_right a b)).actors g,
      (final_actors_coherent Label (le_max_right a b) g).trans hg⟩

end PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

end OAI
