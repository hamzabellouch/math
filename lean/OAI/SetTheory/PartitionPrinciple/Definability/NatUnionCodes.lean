import OAI.SetTheory.PartitionPrinciple.Transfinite.SetRankBounds

namespace OAI


namespace PartitionPilot.SetRealization.Presentation

universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B) (f : A → B)

noncomputable def graph : ZFSet.{u} :=
  (s.product t).subset (fun a => f a.1 = a.2)

theorem pair_mem_graph (a : A) (b : B) :
    ZFSet.pair (s.encode a) (t.encode b) ∈ s.graph t f ↔ f a = b :=
  (s.product t).encode_mem_subset (fun a => f a.1 = a.2) (a, b)

theorem mem_graph (x : ZFSet.{u}) :
    x ∈ s.graph t f ↔ ∃ a, ZFSet.pair (s.encode a) (t.encode (f a)) = x := by
  rw [graph, mem_subset]
  constructor
  · rintro ⟨⟨a, b⟩, h, eq⟩
    change f a = b at h
    subst b
    exact ⟨a, eq⟩
  · rintro ⟨a, eq⟩
    exact ⟨(a, f a), rfl, eq⟩

theorem graph_isFunc : ZFSet.IsFunc s.carrier t.carrier (s.graph t f) := by
  refine ⟨(s.product t).subset_carrier _, ?_⟩
  intro x hx
  rcases (s.mem_carrier x).1 hx with ⟨a, rfl⟩
  refine ⟨t.encode (f a), (s.pair_mem_graph t f a (f a)).2 rfl, ?_⟩
  intro y hy
  rcases (s.mem_graph t f _).1 hy with ⟨b, eq⟩
  have parts := ZFSet.pair_inj.1 eq
  have ba := s.injective parts.1
  simpa only [ba] using parts.2.symm

theorem graph_mem_funs : s.graph t f ∈ ZFSet.funs s.carrier t.carrier :=
  ZFSet.mem_funs.2 (s.graph_isFunc t f)

theorem graph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (hs : ZFSet.rank s.carrier < o) (ht : ZFSet.rank t.carrier < o) :
    ZFSet.rank (s.graph t f) < o :=
  (s.product t).subset_rank_lt (s.product_rank_lt limit t hs ht) _

end PartitionPilot.SetRealization.Presentation



namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

def FunctionGraphOn (A f : ZFSet.{u}) : Prop :=
  ∃ B, ZFSet.IsFunc A B f

def graphRestriction (A f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod A (⋃₀ ⋃₀ f)) f

theorem pair_first_mem_doubleUnion {x y f : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ f) : x ∈ ⋃₀ ⋃₀ f := by
  exact ZFSet.mem_sUnion.2 ⟨{x}, ZFSet.mem_sUnion.2
    ⟨ZFSet.pair x y, entry, ZFSet.mem_pair.2 (Or.inl rfl)⟩,
    ZFSet.mem_singleton.2 rfl⟩

theorem pair_second_mem_doubleUnion {x y f : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ f) : y ∈ ⋃₀ ⋃₀ f := by
  exact ZFSet.mem_sUnion.2 ⟨{x, y}, ZFSet.mem_sUnion.2
    ⟨ZFSet.pair x y, entry, ZFSet.mem_pair.2 (Or.inr rfl)⟩,
    ZFSet.mem_pair.2 (Or.inr rfl)⟩

theorem pair_mem_graphRestriction {A f x y : ZFSet.{u}} :
    ZFSet.pair x y ∈ graphRestriction A f ↔ ZFSet.pair x y ∈ f ∧ x ∈ A := by
  constructor
  · intro h
    exact ⟨(ZFSet.mem_sep.1 h).1, (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 h).2).1⟩
  · rintro ⟨entry, hx⟩
    exact ZFSet.mem_sep.2 ⟨entry, ZFSet.pair_mem_prod.2
      ⟨hx, pair_second_mem_doubleUnion entry⟩⟩

theorem mem_graphRestriction {A f z : ZFSet.{u}} :
    z ∈ graphRestriction A f ↔ ∃ x ∈ A, ∃ y, z = ZFSet.pair x y ∧ ZFSet.pair x y ∈ f := by
  constructor
  · intro h
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 h).2
    exact ⟨x, hx, y, rfl, (ZFSet.mem_sep.1 h).1⟩
  · rintro ⟨x, hx, y, rfl, entry⟩
    exact pair_mem_graphRestriction.2 ⟨entry, hx⟩

theorem graphRestriction_subset (A f : ZFSet.{u}) : graphRestriction A f ⊆ f :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem graphRestriction_restrict {A B f : ZFSet.{u}} (subset : B ⊆ A) :
    graphRestriction B (graphRestriction A f) = graphRestriction B f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact pair_mem_graphRestriction.2 ⟨(pair_mem_graphRestriction.1 entry).1, hx⟩
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact pair_mem_graphRestriction.2
      ⟨pair_mem_graphRestriction.2 ⟨entry, subset hx⟩, hx⟩

theorem graphRestriction_eq_sep {A B C f : ZFSet.{u}} (h : ZFSet.IsFunc A B f) :
    graphRestriction C f = ZFSet.sep (fun z => z ∈ ZFSet.prod C B) f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact ZFSet.mem_sep.2 ⟨entry, ZFSet.pair_mem_prod.2
      ⟨hx, (ZFSet.pair_mem_prod.1 (h.1 entry)).2⟩⟩
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).2
    exact pair_mem_graphRestriction.2 ⟨(ZFSet.mem_sep.1 hz).1, hx⟩

theorem graphRestriction_insert_of_not_mem {A f x y : ZFSet.{u}} (fresh : x ∉ A) :
    graphRestriction A (insert (ZFSet.pair x y) f) = graphRestriction A f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨a, ha, b, rfl, entry⟩ := mem_graphRestriction.1 hz
    rcases ZFSet.mem_insert_iff.1 entry with eq | entry
    · exact False.elim (fresh ((ZFSet.pair_inj.1 eq).1 ▸ ha))
    · exact pair_mem_graphRestriction.2 ⟨entry, ha⟩
  · intro hz
    obtain ⟨a, ha, b, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact pair_mem_graphRestriction.2 ⟨ZFSet.mem_insert_iff.2 (Or.inr entry), ha⟩

namespace FunctionGraphOn

theorem to_isFunc {A f : ZFSet.{u}} (h : FunctionGraphOn A f) :
    ZFSet.IsFunc A (⋃₀ ⋃₀ f) f := by
  obtain ⟨B, shape, total⟩ := h
  refine ⟨?_, total⟩
  intro z hz
  obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
  exact ZFSet.pair_mem_prod.2 ⟨hx, pair_second_mem_doubleUnion hz⟩

theorem shape {A f : ZFSet.{u}} (h : FunctionGraphOn A f) :
    ∀ z ∈ f, ∃ x ∈ A, ∃ y, z = ZFSet.pair x y := by
  intro z hz
  obtain ⟨x, hx, y, _, eq⟩ := ZFSet.mem_prod.1 (h.to_isFunc.1 hz)
  exact ⟨x, hx, y, eq⟩

theorem total {A f x : ZFSet.{u}} (h : FunctionGraphOn A f) (hx : x ∈ A) :
    ∃ y, ZFSet.pair x y ∈ f := by
  obtain ⟨y, entry, _⟩ := h.to_isFunc.2 x hx
  exact ⟨y, entry⟩

theorem pair_source {A f x y : ZFSet.{u}} (h : FunctionGraphOn A f)
    (entry : ZFSet.pair x y ∈ f) : x ∈ A :=
  (ZFSet.pair_mem_prod.1 (h.to_isFunc.1 entry)).1

theorem unique {A f x y z : ZFSet.{u}} (h : FunctionGraphOn A f)
    (hy : ZFSet.pair x y ∈ f) (hz : ZFSet.pair x z ∈ f) : y = z := by
  obtain ⟨w, _, unique⟩ := h.to_isFunc.2 x (h.pair_source hy)
  exact (unique y hy).trans (unique z hz).symm

theorem restrict {A B f : ZFSet.{u}} (h : FunctionGraphOn A f) (subset : B ⊆ A) :
    FunctionGraphOn B (graphRestriction B f) := by
  refine ⟨⋃₀ ⋃₀ f, ?_, ?_⟩
  · intro z hz
    exact (ZFSet.mem_sep.1 hz).2
  · intro x hx
    obtain ⟨y, entry⟩ := h.total (subset hx)
    refine ⟨y, pair_mem_graphRestriction.2 ⟨entry, hx⟩, ?_⟩
    intro z hz
    exact h.unique (pair_mem_graphRestriction.1 hz).1 entry

theorem restriction_eq {A f : ZFSet.{u}} (h : FunctionGraphOn A f) :
    graphRestriction A f = f := by
  apply ZFSet.ext
  intro z
  constructor
  · exact fun hz => graphRestriction_subset A f hz
  · intro hz
    exact ZFSet.mem_sep.2 ⟨hz, h.to_isFunc.1 hz⟩

theorem eq_of_agree {A f g : ZFSet.{u}} (hf : FunctionGraphOn A f)
    (hg : FunctionGraphOn A g)
    (agree : ∀ x y z, ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z) : f = g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (hf.to_isFunc.1 hz)
    obtain ⟨w, hw⟩ := hg.total hx
    exact (agree x y w hz hw).symm ▸ hw
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (hg.to_isFunc.1 hz)
    obtain ⟨w, hw⟩ := hf.total hx
    exact agree x w y hw hz ▸ hw

theorem empty : FunctionGraphOn (∅ : ZFSet.{u}) ∅ :=
  ⟨∅, ZFSet.empty_subset _, fun x hx => False.elim (ZFSet.notMem_empty x hx)⟩

theorem insert {A f x : ZFSet.{u}} (h : FunctionGraphOn A f) (fresh : x ∉ A)
    (y : ZFSet.{u}) : FunctionGraphOn (Insert.insert x A) (Insert.insert (ZFSet.pair x y) f) := by
  classical
  refine ⟨Insert.insert y (⋃₀ ⋃₀ f), ?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | hz
    · exact ZFSet.pair_mem_prod.2
        ⟨ZFSet.mem_insert_iff.2 (Or.inl rfl), ZFSet.mem_insert_iff.2 (Or.inl rfl)⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (h.to_isFunc.1 hz)
      exact ZFSet.pair_mem_prod.2
        ⟨ZFSet.mem_insert_iff.2 (Or.inr ha), ZFSet.mem_insert_iff.2 (Or.inr hb)⟩
  · intro a ha
    rcases ZFSet.mem_insert_iff.1 ha with rfl | ha
    · refine ⟨y, ZFSet.mem_insert_iff.2 (Or.inl rfl), ?_⟩
      intro b hb
      rcases ZFSet.mem_insert_iff.1 hb with eq | hb
      · exact (ZFSet.pair_inj.1 eq).2
      · exact False.elim (fresh (h.pair_source hb))
    · obtain ⟨b, entry⟩ := h.total ha
      refine ⟨b, ZFSet.mem_insert_iff.2 (Or.inr entry), ?_⟩
      intro c hc
      rcases ZFSet.mem_insert_iff.1 hc with eq | hc
      · exact False.elim (fresh ((ZFSet.pair_inj.1 eq).1 ▸ ha))
      · exact h.unique hc entry

theorem successor {A f : ZFSet.{u}} (h : FunctionGraphOn A f) (y : ZFSet.{u}) :
    FunctionGraphOn (Insert.insert A A) (Insert.insert (ZFSet.pair A y) f) :=
  h.insert (ZFSet.mem_irrefl A) y

end FunctionGraphOn

theorem functionGraphOn_sUnion {A W : ZFSet.{u}}
    (shape : ∀ f ∈ W, ∃ B, B ⊆ A ∧ FunctionGraphOn B f)
    (cover : ∀ x ∈ A, ∃ f ∈ W, ∃ y, ZFSet.pair x y ∈ f)
    (agree : ∀ f ∈ W, ∀ g ∈ W, ∀ x y z,
      ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z) :
    FunctionGraphOn A (⋃₀ W) := by
  refine ⟨⋃₀ ⋃₀ (⋃₀ W), ?_, ?_⟩
  · intro z hz
    obtain ⟨f, hf, entry⟩ := ZFSet.mem_sUnion.1 hz
    obtain ⟨B, subset, func⟩ := shape f hf
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (func.to_isFunc.1 entry)
    exact ZFSet.pair_mem_prod.2 ⟨subset hx, pair_second_mem_doubleUnion hz⟩
  · intro x hx
    obtain ⟨f, hf, y, entry⟩ := cover x hx
    refine ⟨y, ZFSet.mem_sUnion.2 ⟨f, hf, entry⟩, ?_⟩
    intro z hz
    obtain ⟨g, hg, rel⟩ := ZFSet.mem_sUnion.1 hz
    exact agree g hg f hf x z y rel entry

end PartitionPilot.Forcing



namespace PartitionPilot.SetRealization.Presentation
universe u
variable {A B : Type u} (s : Presentation A) (e : B ≃ A)

def reindex : Presentation B where
  carrier := s.carrier
  encode b := s.encode (e b)
  injective := s.injective.comp e.injective
  mem_carrier x := by
    rw [s.mem_carrier]
    exact ⟨fun ⟨a, eq⟩ => ⟨e.symm a, by simpa only [e.apply_symm_apply] using eq⟩,
      fun ⟨b, eq⟩ => ⟨e b, eq⟩⟩

theorem reindex_carrier : (s.reindex e).carrier = s.carrier := rfl

theorem reindex_encode (b : B) : (s.reindex e).encode b = s.encode (e b) := rfl

theorem graph_reindex {C : Type u} (t : Presentation C) (f : C → B) :
    t.graph (s.reindex e) f = t.graph s (fun x => e (f x)) := by
  apply ZFSet.ext
  intro z
  rw [mem_graph, mem_graph]
  rfl

end PartitionPilot.SetRealization.Presentation



namespace PartitionPilot.Forcing
universe u

def NatUnionCode (stages : Nat → ZFSet.{u}) (union : ZFSet.{u}) : Prop :=
  ∀ x, x ∈ union ↔ ∃ n, x ∈ stages n

namespace NatUnionCode

theorem subset {stages : Nat → ZFSet.{u}} {union : ZFSet.{u}}
    (code : NatUnionCode stages union) (n : Nat) : stages n ⊆ union :=
  fun _ hx => (code _).2 ⟨n, hx⟩

theorem constant (A : ZFSet.{u}) : NatUnionCode (fun _ => A) A := by
  intro x
  exact ⟨fun hx => ⟨0, hx⟩, fun ⟨_, hx⟩ => hx⟩

theorem prod_left {stages : Nat → ZFSet.{u}} {union : ZFSet.{u}}
    (code : NatUnionCode stages union) (A : ZFSet.{u}) :
    NatUnionCode (fun n => ZFSet.prod A (stages n)) (ZFSet.prod A union) := by
  intro z
  constructor
  · rintro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    obtain ⟨n, hn⟩ := (code y).1 hy
    exact ⟨n, ZFSet.pair_mem_prod.2 ⟨hx, hn⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hn
    exact ZFSet.pair_mem_prod.2 ⟨hx, code.subset n hy⟩

theorem prod {A B : Nat → ZFSet.{u}} {U V : ZFSet.{u}}
    (left : NatUnionCode A U) (right : NatUnionCode B V)
    (leftMono : ∀ n m, n ≤ m → A n ⊆ A m)
    (rightMono : ∀ n m, n ≤ m → B n ⊆ B m) :
    NatUnionCode (fun n => ZFSet.prod (A n) (B n)) (ZFSet.prod U V) := by
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    obtain ⟨n, hn⟩ := (left x).1 hx
    obtain ⟨m, hm⟩ := (right y).1 hy
    exact ⟨max n m, ZFSet.pair_mem_prod.2
      ⟨leftMono n _ (le_max_left n m) hn, rightMono m _ (le_max_right n m) hm⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hn
    exact ZFSet.pair_mem_prod.2 ⟨left.subset n hx, right.subset n hy⟩

theorem isFunc {A B f : Nat → ZFSet.{u}} {U V F : ZFSet.{u}}
    (domain : NatUnionCode A U) (range : NatUnionCode B V) (graph : NatUnionCode f F)
    (functions : ∀ n, ZFSet.IsFunc (A n) (B n) (f n))
    (graphMono : ∀ n m, n ≤ m → f n ⊆ f m) : ZFSet.IsFunc U V F := by
  constructor
  · intro z hz
    obtain ⟨n, hn⟩ := (graph z).1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((functions n).1 hn)
    exact ZFSet.pair_mem_prod.2 ⟨domain.subset n hx, range.subset n hy⟩
  · intro x hx
    obtain ⟨n, hn⟩ := (domain x).1 hx
    obtain ⟨y, entry, _⟩ := (functions n).2 x hn
    refine ⟨y, graph.subset n entry, ?_⟩
    intro z hz
    obtain ⟨m, hm⟩ := (graph _).1 hz
    have first := graphMono n (max n m) (le_max_left n m) entry
    have second := graphMono m (max n m) (le_max_right n m) hm
    have inDomain := (ZFSet.pair_mem_prod.1 ((functions (max n m)).1 first)).1
    obtain ⟨_, _, unique⟩ := (functions (max n m)).2 x inDomain
    exact (unique z second).trans (unique y first).symm

theorem function_entry_iff {A B f : Nat → ZFSet.{u}} {U V F : ZFSet.{u}}
    (graph : NatUnionCode f F) (function : ZFSet.IsFunc U V F)
    (functions : ∀ n, ZFSet.IsFunc (A n) (B n) (f n))
    (n : Nat) {x y : ZFSet.{u}} (hx : x ∈ A n) :
    ZFSet.pair x y ∈ F ↔ ZFSet.pair x y ∈ f n := by
  constructor
  · intro entry
    obtain ⟨z, old, _⟩ := (functions n).2 x hx
    have oldUnion := graph.subset n old
    have inDomain := (ZFSet.pair_mem_prod.1 (function.1 oldUnion)).1
    obtain ⟨_, _, unique⟩ := function.2 x inDomain
    have equal : y = z := (unique y entry).trans (unique z oldUnion).symm
    exact equal.symm ▸ old
  · exact fun entry => graph.subset n entry

end NatUnionCode

end PartitionPilot.Forcing

end OAI
