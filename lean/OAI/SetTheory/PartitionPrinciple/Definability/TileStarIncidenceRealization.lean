import OAI.SetTheory.PartitionPrinciple.Geometry.GroundTileStarIncidence

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps.CosetGeometry
universe u
variable {J S R : Type u} [Group J]
variable (e : Presentation (External J S)) (s : Presentation S) (r : Presentation R)
variable (q : Presentation (Vertex J S)) (request : S → R)
variable {C req gens mul : ZFSet.{u}}
variable (classed : ∀ w v, ZFSet.pair (e.encode w) (q.encode v) ∈ C ↔ point J S w = v)
variable (requested : ∀ a b, ZFSet.pair (s.encode a) (r.encode b) ∈ req ↔ request a = b)
variable (generated : ∀ a b, ZFSet.pair (s.encode a) (e.encode b) ∈ gens ↔ generator J S a = b)
variable (multiplied : ∀ a b c, ZFSet.pair (ZFSet.pair (e.encode a) (e.encode b)) (e.encode c) ∈ mul ↔ a * b = c)
local notation "vP" => tileStarVertexPresentation e r q
local notation "eP" => tileStarEdgePresentation e s r
local notation "dP" => tileStarDartPresentation e s r

include classed requested generated multiplied in
theorem tileStar_source_entry (d : TileStars.Dart J S R) :
    TileStarSourceEntry e.carrier r.carrier s.carrier q.carrier (tileStarEdgeCarrier e.carrier r.carrier s.carrier)
      C req gens mul ((dP).encode d) ((vP).encode (TileStars.source J S R request d)) := by
  rcases d with ⟨⟨w, a⟩ | ⟨w, a⟩, b⟩ <;> cases b
  · exact ⟨(eP).encode (.inl (w, a)), (eP).encode_mem _, Or.inl
      ⟨e.encode w, e.encode_mem w, r.encode a, r.encode_mem a, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  · exact ⟨(eP).encode (.inl (w, a)), (eP).encode_mem _, Or.inl
      ⟨e.encode w, e.encode_mem w, r.encode a, r.encode_mem a, rfl, Or.inl
        ⟨rfl, q.encode (point J S w), q.encode_mem _, (classed _ _).2 rfl, rfl⟩⟩⟩
  · exact ⟨(eP).encode (.inr (w, a)), (eP).encode_mem _, Or.inr
      ⟨e.encode w, e.encode_mem w, s.encode a, s.encode_mem a, rfl, Or.inr
        ⟨rfl, e.encode (generator J S a), e.encode_mem _, e.encode (w * generator J S a), e.encode_mem _,
          q.encode (point J S (w * generator J S a)), q.encode_mem _, (generated _ _).2 rfl,
          (multiplied _ _ _).2 rfl, (classed _ _).2 rfl, rfl⟩⟩⟩
  · exact ⟨(eP).encode (.inr (w, a)), (eP).encode_mem _, Or.inr
      ⟨e.encode w, e.encode_mem w, s.encode a, s.encode_mem a, rfl, Or.inl
        ⟨rfl, r.encode (request a), r.encode_mem _, (requested _ _).2 rfl, rfl⟩⟩⟩

include classed requested generated multiplied in
theorem tileStar_source_entry_iff (d : TileStars.Dart J S R) (v : TileStars.Vertex J S R) :
    TileStarSourceEntry e.carrier r.carrier s.carrier q.carrier (tileStarEdgeCarrier e.carrier r.carrier s.carrier)
      C req gens mul ((dP).encode d) ((vP).encode v) ↔ TileStars.source J S R request d = v := by
  constructor
  · rintro ⟨edge, _, first | second⟩
    · obtain ⟨w, hw, a, ha, rfl, forward | backward⟩ := first
      all_goals obtain ⟨w, rfl⟩ := (e.mem_carrier w).1 hw
      all_goals obtain ⟨a, rfl⟩ := (r.mem_carrier a).1 ha
      · obtain ⟨hd, c, hc, member, hv⟩ := forward
        obtain ⟨c, rfl⟩ := (q.mem_carrier c).1 hc
        have deq : d = (.inl (w, a), true) := (dP).injective hd
        have veq : v = .inl c := (vP).injective hv
        rw [deq, veq]
        exact congrArg Sum.inl ((classed w c).1 member)
      · obtain ⟨hd, hv⟩ := backward
        have deq : d = (.inl (w, a), false) := (dP).injective hd
        have veq : v = .inr (w, a) := (vP).injective hv
        rw [deq, veq]
        rfl
    · obtain ⟨w, hw, a, ha, rfl, forward | backward⟩ := second
      all_goals obtain ⟨w, rfl⟩ := (e.mem_carrier w).1 hw
      all_goals obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
      · obtain ⟨hd, b, hb, member, hv⟩ := forward
        obtain ⟨b, rfl⟩ := (r.mem_carrier b).1 hb
        have deq : d = (.inr (w, a), true) := (dP).injective hd
        have veq : v = .inr (w, b) := (vP).injective hv
        rw [deq, veq]
        exact congrArg (fun b => Sum.inr (w, b)) ((requested a b).1 member)
      · obtain ⟨hd, k, hk, b, hb, c, hc, gen, product, member, hv⟩ := backward
        obtain ⟨k, rfl⟩ := (e.mem_carrier k).1 hk
        obtain ⟨b, rfl⟩ := (e.mem_carrier b).1 hb
        obtain ⟨c, rfl⟩ := (q.mem_carrier c).1 hc
        have deq : d = (.inr (w, a), false) := (dP).injective hd
        have veq : v = .inl c := (vP).injective hv
        rw [deq, veq]
        change Sum.inl (point J S (w * generator J S a)) = Sum.inl c
        rw [(generated a k).1 gen, (multiplied w k b).1 product, (classed b c).1 member]
  · intro equal
    rw [← equal]
    exact tileStar_source_entry e s r q request classed requested generated multiplied d

include classed requested generated multiplied in
theorem tileStar_source_iff (d : TileStars.Dart J S R) (v : TileStars.Vertex J S R) :
    ZFSet.pair ((dP).encode d) ((vP).encode v) ∈
      tileStarSourceGraph e.carrier r.carrier s.carrier q.carrier C req gens mul ↔
        TileStars.source J S R request d = v := by
  rw [pair_mem_tileStarSourceGraph]
  exact ⟨fun h => (tileStar_source_entry_iff e s r q request classed requested generated multiplied d v).1 h.2.2,
    fun h => ⟨(dP).encode_mem d, (vP).encode_mem v,
      (tileStar_source_entry_iff e s r q request classed requested generated multiplied d v).2 h⟩⟩

theorem tileStar_reverse_iff (d v : TileStars.Dart J S R) :
    ZFSet.pair ((dP).encode d) ((dP).encode v) ∈ tileStarReverseGraph e.carrier r.carrier s.carrier ↔
      TileStars.reverse J S R d = v := by
  rw [pair_mem_tileStarReverseGraph]
  constructor
  · rintro ⟨_, _, edge, he, ⟨hd, hv⟩ | ⟨hd, hv⟩⟩
    all_goals obtain ⟨edge, rfl⟩ := ((eP).mem_carrier edge).1 he
    · have deq : d = (edge, false) := (dP).injective hd
      have veq : v = (edge, true) := (dP).injective hv
      rw [deq, veq]; rfl
    · have deq : d = (edge, true) := (dP).injective hd
      have veq : v = (edge, false) := (dP).injective hv
      rw [deq, veq]; rfl
  · intro equal
    refine ⟨(dP).encode_mem d, (dP).encode_mem v, ?_⟩
    rw [← equal]
    rcases d with ⟨edge, b⟩
    cases b
    · exact ⟨(eP).encode edge, (eP).encode_mem edge, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(eP).encode edge, (eP).encode_mem edge, Or.inr ⟨rfl, rfl⟩⟩

include classed requested generated multiplied in
theorem tileStar_target_iff (d : TileStars.Dart J S R) (v : TileStars.Vertex J S R) :
    ZFSet.pair ((dP).encode d) ((vP).encode v) ∈
      tileStarTargetGraph e.carrier r.carrier s.carrier q.carrier C req gens mul ↔
        TileStars.target J S R request d = v := by
  rw [tileStarTargetGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, a, ha, hd, hv⟩
    obtain ⟨a, rfl⟩ := ((dP).mem_carrier a).1 ha
    have rev := (tileStar_reverse_iff e s r d a).1 hd
    have src := (tileStar_source_iff e s r q request classed requested generated multiplied a v).1 hv
    change TileStars.source J S R request (TileStars.reverse J S R d) = v
    rw [rev]
    exact src
  · intro equal
    exact ⟨(dP).encode_mem d, (vP).encode_mem v, (dP).encode (TileStars.reverse J S R d),
      (dP).encode_mem _, (tileStar_reverse_iff e s r _ _).2 rfl,
      (tileStar_source_iff e s r q request classed requested generated multiplied _ _).2 equal⟩

theorem presentedGraph_eq {A B : Type u} (a : Presentation A) (b : Presentation B)
    (f : A → B) {F : ZFSet.{u}} (shape : F ⊆ ZFSet.prod a.carrier b.carrier)
    (entries : ∀ x y, ZFSet.pair (a.encode x) (b.encode y) ∈ F ↔ f x = y) :
    F = a.graph b f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
    obtain ⟨x, rfl⟩ := (a.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (b.mem_carrier y).1 hy
    exact (a.pair_mem_graph b f x y).2 ((entries x y).1 hz)
  · intro hz
    obtain ⟨x, rfl⟩ := (a.mem_graph b f z).1 hz
    exact (entries x (f x)).2 rfl

include classed requested generated multiplied in
theorem tileStar_endpoint_graphs :
    tileStarSourceGraph e.carrier r.carrier s.carrier q.carrier C req gens mul =
      (dP).graph (vP) (TileStars.source J S R request) ∧
    tileStarTargetGraph e.carrier r.carrier s.carrier q.carrier C req gens mul =
      (dP).graph (vP) (TileStars.target J S R request) ∧
    tileStarReverseGraph e.carrier r.carrier s.carrier = (dP).graph (dP) (TileStars.reverse J S R) := by
  exact ⟨presentedGraph_eq (dP) (vP) _ (fun _ h => (ZFSet.mem_sep.1 h).1)
      (tileStar_source_iff e s r q request classed requested generated multiplied),
    presentedGraph_eq (dP) (vP) _ (by
      intro z hz
      unfold tileStarTargetGraph relationCompose at hz
      exact (ZFSet.mem_sep.1 hz).1)
      (tileStar_target_iff e s r q request classed requested generated multiplied),
    presentedGraph_eq (dP) (dP) _ (fun _ h => (ZFSet.mem_sep.1 h).1)
      (tileStar_reverse_iff e s r)⟩

include classed requested generated multiplied in
theorem tileStar_endpoint_functions :
    ZFSet.IsFunc (tileStarDartCarrier e.carrier r.carrier s.carrier) (tileStarVertexCarrier q.carrier e.carrier r.carrier)
      (tileStarSourceGraph e.carrier r.carrier s.carrier q.carrier C req gens mul) ∧
    ZFSet.IsFunc (tileStarDartCarrier e.carrier r.carrier s.carrier) (tileStarVertexCarrier q.carrier e.carrier r.carrier)
      (tileStarTargetGraph e.carrier r.carrier s.carrier q.carrier C req gens mul) ∧
    ZFSet.IsFunc (tileStarDartCarrier e.carrier r.carrier s.carrier) (tileStarDartCarrier e.carrier r.carrier s.carrier)
      (tileStarReverseGraph e.carrier r.carrier s.carrier) := by
  obtain ⟨source, target, reverse⟩ := tileStar_endpoint_graphs e s r q request classed requested generated multiplied
  rw [source, target, reverse]
  exact ⟨(dP).graph_isFunc (vP) _, (dP).graph_isFunc (vP) _, (dP).graph_isFunc (dP) _⟩

include classed requested generated multiplied in
theorem tileStar_incidence_iff (d : TileStars.Dart J S R) (v : TileStars.Vertex J S R) :
    ZFSet.pair ((dP).encode d) ((vP).encode v) ∈ dartIncidenceGraph
      (tileStarSourceGraph e.carrier r.carrier s.carrier q.carrier C req gens mul)
      (tileStarTargetGraph e.carrier r.carrier s.carrier q.carrier C req gens mul) ↔
      TileStars.source J S R request d = v ∨ TileStars.target J S R request d = v := by
  rw [dartIncidenceGraph, ZFSet.mem_union, tileStar_source_iff e s r q request classed requested generated multiplied,
    tileStar_target_iff e s r q request classed requested generated multiplied]

include classed requested generated multiplied in
theorem tileStar_adjacency_iff (x y : TileStars.Vertex J S R) :
    ZFSet.pair ((vP).encode x) ((vP).encode y) ∈ dartAdjacencyGraph
      (tileStarDartCarrier e.carrier r.carrier s.carrier) (tileStarVertexCarrier q.carrier e.carrier r.carrier)
      (tileStarSourceGraph e.carrier r.carrier s.carrier q.carrier C req gens mul)
      (tileStarTargetGraph e.carrier r.carrier s.carrier q.carrier C req gens mul) ↔
      ∃ d : TileStars.Dart J S R, TileStars.source J S R request d = x ∧ TileStars.target J S R request d = y := by
  rw [dartAdjacencyGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, d, hd, hs, ht⟩
    obtain ⟨d, rfl⟩ := ((dP).mem_carrier d).1 hd
    exact ⟨d, (tileStar_source_iff e s r q request classed requested generated multiplied d x).1
      ((pair_mem_relationConverse _ _ _ _ _).1 hs).2.2,
      (tileStar_target_iff e s r q request classed requested generated multiplied d y).1 ht⟩
  · rintro ⟨d, hs, ht⟩
    exact ⟨(vP).encode_mem x, (vP).encode_mem y, (dP).encode d, (dP).encode_mem d,
      (pair_mem_relationConverse _ _ _ _ _).2 ⟨(dP).encode_mem d, (vP).encode_mem x,
        (tileStar_source_iff e s r q request classed requested generated multiplied d x).2 hs⟩,
      (tileStar_target_iff e s r q request classed requested generated multiplied d y).2 ht⟩

end PartitionPilot.Forcing

end

end OAI
