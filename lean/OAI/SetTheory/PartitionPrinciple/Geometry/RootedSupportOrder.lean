import OAI.SetTheory.PartitionPrinciple.Forcing.RootedSupportOwners

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

universe u
variable {V : Type u} (d : Scheme V)

theorem supports_lower {v : V} {x y : d.Node}
    (supported : d.Supports v y) (lower : d.gluedOrder.le x y) : d.Supports v x := by
  rcases supported with ⟨b, rfl⟩
  exact (d.vertex v).ideal b x lower

theorem leastSupport_depth_mono {v w : V} {x y : d.Node}
    (first : d.LeastSupport v x) (second : d.LeastSupport w y)
    (lower : d.gluedOrder.le x y) : d.depth v ≤ d.depth w :=
  first.2 w (d.supports_lower second.1 lower)

theorem leastSupport_eq_of_depth_eq {v w : V} {x y : d.Node}
    (first : d.LeastSupport v x) (second : d.LeastSupport w y)
    (lower : d.gluedOrder.le x y) (same : d.depth v = d.depth w) : v = w := by
  apply d.leastSupport_unique first
  refine ⟨d.supports_lower second.1 lower, ?_⟩
  intro z hz
  rw [← same]
  exact first.2 z hz

theorem supports_coordinate_unique {v : V} {x : d.Node} (supported : d.Supports v x) :
    ∃! a, (d.vertex v).toFun a = x := by
  rcases supported with ⟨a, ha⟩
  exact ⟨a, ha, fun b hb => embedding_injective (d.vertex v).toMeetEmbedding (hb.trans ha.symm)⟩

theorem leastSupport_iff_not_parent (v : V) (h : d.depth v ≠ 0) (x : d.Node) :
    d.LeastSupport v x ↔ d.Supports v x ∧ ¬ d.Supports (d.parent v) x := by
  constructor
  · intro least
    refine ⟨least.1, ?_⟩
    intro parent
    have bound := least.2 (d.parent v) parent
    have smaller := d.parent_depth v h
    omega
  · rintro ⟨⟨a, rfl⟩, notparent⟩
    exact (d.leastSupport_vertex_iff v h a).mpr
      (fun ha => notparent ((d.supports_parent_iff v h a).mpr ha))

theorem leastSupport_coordinates {v : V} {x y : d.Node}
    (first : d.LeastSupport v x) (second : d.LeastSupport v y)
    (lower : d.gluedOrder.le x y) :
    ∃ a b, (d.vertex v).toFun a = x ∧ (d.vertex v).toFun b = y ∧
      (d.order v).le a b ∧ (a = b ↔ x = y) := by
  rcases first.1 with ⟨a, rfl⟩
  rcases second.1 with ⟨b, rfl⟩
  refine ⟨a, b, rfl, rfl, ((d.vertex v).le_iff _ _).mp lower, ?_⟩
  exact ⟨congrArg (d.vertex v).toFun,
    embedding_injective (d.vertex v).toMeetEmbedding⟩

end PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

end

end OAI
