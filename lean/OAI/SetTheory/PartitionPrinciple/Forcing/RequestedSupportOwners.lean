import OAI.SetTheory.PartitionPrinciple.Geometry.OutwardSchedule
import OAI.SetTheory.PartitionPrinciple.Geometry.RootedSupportOrder

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

theorem leastSupport_root_copy_iff (x : f.Node a) :
    (f.diagram a).scheme.LeastSupport (TileStars.root J f.Letters R) x ↔
      ∃ y, (f.copy a 1).toFun y = x := by
  refine ((f.diagram a).scheme.leastSupport_root_iff x).trans ?_
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (f.copy_one a y).trans hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (f.copy_one a y).symm.trans hy⟩

theorem leastSupport_coset_iff (c : CosetGeometry.Vertex J f.Letters) (x : f.Node a) :
    (f.diagram a).scheme.LeastSupport (.inl c) x ↔
      c = CosetGeometry.root J f.Letters ∧ ∃ y, (f.copy a 1).toFun y = x := by
  constructor
  · intro least
    by_cases zero : (f.diagram a).scheme.depth (.inl c) = 0
    · have root := (f.diagram a).scheme.zero_eq_root (.inl c) zero
      have hc : c = CosetGeometry.root J f.Letters := Sum.inl.inj root
      subst c
      exact ⟨rfl, (f.leastSupport_root_copy_iff a x).mp least⟩
    · rcases least.1 with ⟨y, rfl⟩
      exact False.elim (((f.diagram a).scheme.leastSupport_vertex_iff (.inl c) zero y).mp least
        (f.old_local_full a c zero y))
  · rintro ⟨rfl, old⟩
    exact (f.leastSupport_root_copy_iff a x).mpr old

theorem tile_depth_ne_zero (w : External J f.Letters) (r : R) :
    (f.diagram a).scheme.depth (.inr (w, r)) ≠ 0 := by
  intro zero
  exact Sum.inr_ne_inl ((f.diagram a).scheme.zero_eq_root (.inr (w, r)) zero)

theorem leastSupport_tile_iff (w : External J f.Letters) (r : R)
    (y : (f.tile r).Space) :
    (f.diagram a).scheme.LeastSupport (.inr (w, r)) ((f.placedTile a w r).toFun y) ↔
      ¬ (f.tile r).order.le y
        ((f.diagram a).localGlue (.inr (w, r)) (f.tile_depth_ne_zero a w r)).rightAnchor :=
  (f.diagram a).scheme.leastSupport_vertex_iff (.inr (w, r)) (f.tile_depth_ne_zero a w r) y

theorem leastSupport_cases (v : TileStars.Vertex J f.Letters R) (x : f.Node a)
    (least : (f.diagram a).scheme.LeastSupport v x) :
    (v = TileStars.root J f.Letters R ∧ ∃ y, (f.copy a 1).toFun y = x) ∨
      ∃ w r, ∃ y : (f.tile r).Space, v = .inr (w, r) ∧
        (f.placedTile a w r).toFun y = x ∧
        ¬ (f.tile r).order.le y
          ((f.diagram a).localGlue (.inr (w, r)) (f.tile_depth_ne_zero a w r)).rightAnchor := by
  cases v with
  | inl c =>
    rcases (f.leastSupport_coset_iff a c x).mp least with ⟨rfl, old⟩
    exact Or.inl ⟨rfl, old⟩
  | inr c =>
    rcases least.1 with ⟨y, rfl⟩
    exact Or.inr ⟨c.1, c.2, y, rfl, rfl, (f.leastSupport_tile_iff a c.1 c.2 y).mp least⟩

theorem new_point_has_fresh_tile (x : f.Node a)
    (newPoint : ¬ ∃ y, (f.copy a 1).toFun y = x) :
    ∃ w r, ∃ y : (f.tile r).Space,
      (f.diagram a).scheme.LeastSupport (.inr (w, r)) x ∧
      (f.placedTile a w r).toFun y = x ∧
      ¬ (f.tile r).order.le y
        ((f.diagram a).localGlue (.inr (w, r)) (f.tile_depth_ne_zero a w r)).rightAnchor := by
  rcases (f.diagram a).scheme.existsUnique_leastSupport x with ⟨v, least, _⟩
  rcases f.leastSupport_cases a v x least with ⟨_, old⟩ | ⟨w, r, y, rfl, eq, fresh⟩
  · exact False.elim (newPoint old)
  · exact ⟨w, r, y, least, eq, fresh⟩

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
