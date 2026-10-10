import OAI.SetTheory.PartitionPrinciple.Geometry.RootedSupportOrder

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

universe u
variable {V : Type u} (d : Scheme V)

noncomputable def owner (x : d.Node) : V :=
  Classical.choose (d.existsUnique_leastSupport x)

theorem owner_least (x : d.Node) : d.LeastSupport (d.owner x) x :=
  (Classical.choose_spec (d.existsUnique_leastSupport x)).1

theorem owner_eq_iff (x : d.Node) (v : V) :
    d.owner x = v ↔ d.LeastSupport v x := by
  constructor
  · intro eq
    rw [← eq]
    exact d.owner_least x
  · exact d.leastSupport_unique (d.owner_least x)

theorem owner_depth_mono {x y : d.Node} (lower : d.gluedOrder.le x y) :
    d.depth (d.owner x) ≤ d.depth (d.owner y) :=
  d.leastSupport_depth_mono (d.owner_least x) (d.owner_least y) lower

theorem owner_eq_of_depth_eq {x y : d.Node} (lower : d.gluedOrder.le x y)
    (same : d.depth (d.owner x) = d.depth (d.owner y)) : d.owner x = d.owner y :=
  d.leastSupport_eq_of_depth_eq (d.owner_least x) (d.owner_least y) lower same

theorem owner_root_iff (x : d.Node) : d.owner x = d.root ↔ d.Supports d.root x :=
  (d.owner_eq_iff x d.root).trans (d.leastSupport_root_iff x)

noncomputable def ownerCoordinate (x : d.Node) : d.Space (d.owner x) :=
  Classical.choose (d.owner_least x).1

theorem ownerCoordinate_entry (x : d.Node) :
    (d.vertex (d.owner x)).toFun (d.ownerCoordinate x) = x :=
  Classical.choose_spec (d.owner_least x).1

theorem ownerCoordinate_unique (x : d.Node) (a : d.Space (d.owner x))
    (entry : (d.vertex (d.owner x)).toFun a = x) : a = d.ownerCoordinate x :=
  embedding_injective (d.vertex (d.owner x)).toMeetEmbedding
    (entry.trans (d.ownerCoordinate_entry x).symm)

theorem ownerCoordinate_fresh (x : d.Node) (nonroot : d.depth (d.owner x) ≠ 0) :
    ¬ (d.order (d.owner x)).le (d.ownerCoordinate x) (d.childAnchor (d.owner x) nonroot) := by
  apply (d.leastSupport_vertex_iff (d.owner x) nonroot (d.ownerCoordinate x)).mp
  rw [d.ownerCoordinate_entry]
  exact d.owner_least x

end PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

end

end OAI
