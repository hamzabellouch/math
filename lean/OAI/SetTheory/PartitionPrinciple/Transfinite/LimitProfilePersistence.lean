import OAI.SetTheory.PartitionPrinciple.Geometry.MainDiagrams
import OAI.SetTheory.PartitionPrinciple.Geometry.MainProfilePersistence

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.Diagram

open RationalHeights
universe u
variable {I : Type u} [LinearOrder I] (d : Diagram I)

def lastCone (last : I) (greatest : ∀ i, i ≤ last) : d.Cone where
  apex := d.stage last
  leg i := d.transition (greatest i)
  coherent h := (d.comp h (greatest _)).symm

theorem union_bottom_same (i j : I) :
    d.orders.system.point i (d.stage i).bottom =
      d.orders.system.point j (d.stage j).bottom := by
  have raised (k : I) (h : k ≤ max i j) :
      d.orders.system.point k (d.stage k).bottom =
        d.orders.system.point (max i j) (d.stage (max i j)).bottom :=
    (d.orders.system.point_map h (d.stage k).bottom).symm.trans
      (congrArg (d.orders.system.point (max i j)) (d.transition h).bottom)
  exact (raised i (le_max_left i j)).trans (raised j (le_max_right i j)).symm

variable [Nonempty I]

noncomputable def unionBottom : d.orders.system.Union :=
  d.orders.system.point (Classical.choice ‹Nonempty I›)
    (d.stage (Classical.choice ‹Nonempty I›)).bottom

theorem unionBottom_at (i : I) :
    d.orders.system.point i (d.stage i).bottom = d.unionBottom :=
  d.union_bottom_same i _

theorem unionBottom_least (x : d.orders.system.Union) :
    d.orders.unionOrder.le d.unionBottom x := by
  rcases d.orders.system.cover x with ⟨i, x, rfl⟩
  rw [← d.unionBottom_at i]
  exact (d.orders.le_stage i _ x).mpr ((d.stage i).least x)

variable [Countable I]

noncomputable def limitHeight : StrictHeight d.orders.boundedOrder
    (lexOrder CountableColumns.order).toHeightOrder :=
  d.heights.limitHeight (fun i => ((d.stage i).height.value (d.stage i).top).1)
    (d.heights.stage_bound_from_top (fun i => (d.stage i).top) (fun i => (d.stage i).greatest))

noncomputable def limit : MainStage.{u} where
  Point := Option d.orders.system.Union
  order := d.orders.boundedOrder
  Actor := d.groups.system.Union
  action := d.actions.topAction
  bottom := some d.unionBottom
  least x := by
    cases x with
    | none => exact True.intro
    | some x => exact d.unionBottom_least x
  top := none
  greatest := FixedTop.greatest d.orders.unionOrder
  height := d.limitHeight
  countable_height := d.heights.limitHeight_countable _ _ (fun i => (d.stage i).countable_height)

noncomputable def limitTransition (i : I) : Transition (d.stage i) d.limit where
  points := d.orders.boundedInclusion i
  actors := d.groups.inclusion i
  actors_injective := d.groups.inclusion_injective i
  equivariant := d.actions.topAction_stage i
  bottom := congrArg some (d.unionBottom_at i)
  height _ := rfl
  agreement := d.actions.top_agreement d.agreements i

noncomputable def limitCone : d.Cone where
  apex := d.limit
  leg := d.limitTransition
  coherent h := Transition.ext _ _
    (fun x => congrArg some (d.orders.system.point_map h x))
    (fun g => d.groups.system.point_map h g)

theorem limit_strict_top (i : I) (x : (d.stage i).Point) :
    ¬ d.limit.order.le d.limit.top ((d.limitTransition i).points.toFun x) :=
  (d.orders.bounded_strict_top i x).2

theorem limit_point_cover (x : d.limit.Point) :
    x = d.limit.top ∨ ∃ i y, (d.limitTransition i).points.toFun y = x := by
  cases x with
  | none => exact Or.inl rfl
  | some x =>
    rcases d.orders.system.cover x with ⟨i, y, rfl⟩
    exact Or.inr ⟨i, y, rfl⟩

theorem limit_actor_cover (g : d.limit.Actor) :
    ∃ i h, (d.limitTransition i).actors h = g := d.groups.system.cover g

theorem limit_height_stage (i : I) (x : (d.stage i).Point) :
    d.limit.height.value ((d.limitTransition i).points.toFun x) = (d.stage i).height.value x := rfl

end PartitionPilot.Compression.RecursiveMaps.MainStage.Diagram



namespace PartitionPilot.Compression.RecursiveMaps

universe u

theorem FixedTop.preservesProfiles {A : Type u} (P : MeetOrder A) :
    PreservesProfiles (FixedTop.embedding P).toMeetEmbedding := by
  intro c v K F nonempty separate profile
  apply profile_persists_one_step _ c v K F nonempty profile separate
  intro x
  cases x with
  | none => exact Or.inr (Or.inr (FixedTop.greatest P))
  | some x => exact Or.inl ⟨x, rfl⟩

namespace MainStage.Diagram
variable {I : Type u} [LinearOrder I] (d : Diagram I)

theorem union_preservesProfiles
    (preserves : ∀ {i j} (h : i ≤ j), PreservesProfiles (d.transition h).points)
    (i : I) : PreservesProfiles (d.orders.inclusion i) := by
  intro c v K F nonempty separate profile x above
  rcases d.orders.system.cover x with ⟨j, x, rfl⟩
  have eq := d.orders.system.point_map (le_max_right i j) x
  rw [← eq] at above ⊢
  exact profileOver_at_embedding (d.transition (le_max_left i j)).points
    (d.orders.inclusion (max i j)) (d.orders.inclusion i)
    (d.orders.system.point_map (le_max_left i j)) c v K F
    (preserves (le_max_left i j) c v K F nonempty separate profile) _ above

theorem limit_preservesProfiles [Nonempty I] [Countable I]
    (preserves : ∀ {i j} (h : i ≤ j), PreservesProfiles (d.transition h).points)
    (i : I) : PreservesProfiles (d.limitTransition i).points :=
  preservesProfiles_comp (d.orders.inclusion i) (FixedTop.embedding d.orders.unionOrder).toMeetEmbedding
    (d.union_preservesProfiles preserves i) (FixedTop.preservesProfiles d.orders.unionOrder)

end MainStage.Diagram

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
