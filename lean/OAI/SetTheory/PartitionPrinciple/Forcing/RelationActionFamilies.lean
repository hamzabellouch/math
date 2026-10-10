import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

structure RelationActionLaws (G : Type u) [Group G] (X : ZFSet.{u})
    (graph : G → ZFSet.{u}) : Prop where
  function : ∀ g, ZFSet.IsFunc X X (graph g)
  injection : ∀ g, InjectionCode X X (graph g)
  one : ∀ x ∈ X, ∀ y, ZFSet.pair x y ∈ graph 1 ↔ y = x
  mul : ∀ g h, ∀ x ∈ X, ∀ z, ZFSet.pair x z ∈ graph (g * h) ↔
    ∃ y ∈ X, ZFSet.pair x y ∈ graph h ∧ ZFSet.pair y z ∈ graph g

namespace RelationActionLaws
variable {G : Type u} [Group G] {X Y : ZFSet.{u}} {f h : G → ZFSet.{u}}

theorem union (first : RelationActionLaws G X f) (second : RelationActionLaws G Y h)
    (apart : ∀ z, z ∈ X → z ∈ Y → False) :
    RelationActionLaws G (X ∪ Y) (fun g => f g ∪ h g) := by
  refine ⟨fun g => disjointFunction_union (first.function g) (second.function g) apart,
    fun g => disjointInjection_union (first.injection g) (second.injection g) apart, ?_, ?_⟩
  · intro x hx y
    rcases ZFSet.mem_union.1 hx with left | right
    · rw [ZFSet.mem_union, first.one x left y]
      exact ⟨fun entry => entry.elim id (fun other => False.elim
        (apart x left (ZFSet.pair_mem_prod.1 ((second.function 1).1 other)).1)), Or.inl⟩
    · rw [ZFSet.mem_union, second.one x right y]
      exact ⟨fun entry => entry.elim (fun other => False.elim
        (apart x (ZFSet.pair_mem_prod.1 ((first.function 1).1 other)).1 right)) id, Or.inr⟩
  · intro g k x hx z
    constructor
    · intro member
      rcases ZFSet.mem_union.1 member with left | right
      · have source := (ZFSet.pair_mem_prod.1 ((first.function (g * k)).1 left)).1
        obtain ⟨y, hy, ek, eg⟩ := (first.mul g k x source z).1 left
        exact ⟨y, ZFSet.mem_union.2 (Or.inl hy), ZFSet.mem_union.2 (Or.inl ek),
          ZFSet.mem_union.2 (Or.inl eg)⟩
      · have source := (ZFSet.pair_mem_prod.1 ((second.function (g * k)).1 right)).1
        obtain ⟨y, hy, ek, eg⟩ := (second.mul g k x source z).1 right
        exact ⟨y, ZFSet.mem_union.2 (Or.inr hy), ZFSet.mem_union.2 (Or.inr ek),
          ZFSet.mem_union.2 (Or.inr eg)⟩
    · rintro ⟨y, _, ek, eg⟩
      rcases ZFSet.mem_union.1 ek with left | right
      · have fields := ZFSet.pair_mem_prod.1 ((first.function k).1 left)
        rcases ZFSet.mem_union.1 eg with same | other
        · exact ZFSet.mem_union.2 (Or.inl ((first.mul g k x fields.1 z).2
            ⟨y, fields.2, left, same⟩))
        · exact False.elim (apart y fields.2 (ZFSet.pair_mem_prod.1 ((second.function g).1 other)).1)
      · have fields := ZFSet.pair_mem_prod.1 ((second.function k).1 right)
        rcases ZFSet.mem_union.1 eg with other | same
        · exact False.elim (apart y (ZFSet.pair_mem_prod.1 ((first.function g).1 other)).1 fields.2)
        · exact ZFSet.mem_union.2 (Or.inr ((second.mul g k x fields.1 z).2
            ⟨y, fields.2, right, same⟩))

theorem image_one (laws : RelationActionLaws G X f) {A : ZFSet.{u}} (subset : A ⊆ X) :
    relationImage A X (f 1) = A := by
  apply ZFSet.ext
  intro y
  constructor
  · intro member
    obtain ⟨_, x, hx, entry⟩ := (mem_relationImage A X (f 1) y).1 member
    exact (laws.one x (subset hx) y).1 entry ▸ hx
  · intro member
    exact (mem_relationImage A X (f 1) y).2
      ⟨subset member, y, member, (laws.one y (subset member) y).2 rfl⟩

theorem image_mul (laws : RelationActionLaws G X f) (g k : G)
    {A : ZFSet.{u}} (subset : A ⊆ X) :
    relationImage A X (f (g * k)) = relationImage (relationImage A X (f k)) X (f g) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨hz, x, hx, entry⟩ := (mem_relationImage A X (f (g * k)) z).1 member
    obtain ⟨y, hy, ek, eg⟩ := (laws.mul g k x (subset hx) z).1 entry
    exact (mem_relationImage _ X (f g) z).2
      ⟨hz, y, (mem_relationImage A X (f k) y).2 ⟨hy, x, hx, ek⟩, eg⟩
  · intro member
    obtain ⟨hz, y, hy, eg⟩ := (mem_relationImage _ X (f g) z).1 member
    obtain ⟨hy, x, hx, ek⟩ := (mem_relationImage A X (f k) y).1 hy
    exact (mem_relationImage A X (f (g * k)) z).2
      ⟨hz, x, hx, (laws.mul g k x (subset hx) z).2 ⟨y, hy, ek, eg⟩⟩

end RelationActionLaws
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RelationActionLaws
universe u v
variable {G : Type u} [Group G] {ι : Type v}

theorem of_disjoint_family (X : ι → ZFSet.{u}) (branch : ι → G → ZFSet.{u})
    (Y : ZFSet.{u}) (whole : G → ZFSet.{u})
    (cover : ∀ x, x ∈ Y ↔ ∃ i, x ∈ X i)
    (entries : ∀ g z, z ∈ whole g ↔ ∃ i, z ∈ branch i g)
    (apart : ∀ i j x, x ∈ X i → x ∈ X j → i = j)
    (laws : ∀ i, RelationActionLaws G (X i) (branch i)) :
    RelationActionLaws G Y whole := by
  have bounds (g : G) : whole g ⊆ ZFSet.prod Y Y := by
    intro z hz
    obtain ⟨i, hi⟩ := (entries g z).1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (((laws i).function g).1 hi)
    exact ZFSet.pair_mem_prod.2 ⟨(cover x).2 ⟨i, hx⟩, (cover y).2 ⟨i, hy⟩⟩
  have functions (g : G) : ZFSet.IsFunc Y Y (whole g) := by
    refine ⟨bounds g, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := (cover x).1 hx
    obtain ⟨y, edge, unique⟩ := ((laws i).function g).2 x hi
    refine ⟨y, (entries g _).2 ⟨i, edge⟩, ?_⟩
    intro z hz
    obtain ⟨j, other⟩ := (entries g _).1 hz
    have same := apart i j x hi (ZFSet.pair_mem_prod.1 (((laws j).function g).1 other)).1
    subst j
    exact unique z other
  refine ⟨functions, ?_, ?_, ?_⟩
  · intro g
    refine ⟨functions g, ?_⟩
    intro x y z hx hy
    obtain ⟨i, ei⟩ := (entries g _).1 hx
    obtain ⟨j, ej⟩ := (entries g _).1 hy
    have same := apart i j z (ZFSet.pair_mem_prod.1 (((laws i).function g).1 ei)).2
      (ZFSet.pair_mem_prod.1 (((laws j).function g).1 ej)).2
    subst j
    exact ((laws i).injection g).injective x y z ei ej
  · intro x hx y
    constructor
    · intro edge
      obtain ⟨i, hi⟩ := (entries 1 _).1 edge
      exact ((laws i).one x (ZFSet.pair_mem_prod.1 (((laws i).function 1).1 hi)).1 y).1 hi
    · intro equal
      obtain ⟨i, hi⟩ := (cover x).1 hx
      exact (entries 1 _).2 ⟨i, ((laws i).one x hi y).2 equal⟩
  · intro g h x _ z
    constructor
    · intro edge
      obtain ⟨i, hi⟩ := (entries (g * h) _).1 edge
      have source := (ZFSet.pair_mem_prod.1 (((laws i).function (g * h)).1 hi)).1
      obtain ⟨y, hy, eh, eg⟩ := ((laws i).mul g h x source z).1 hi
      exact ⟨y, (cover y).2 ⟨i, hy⟩, (entries h _).2 ⟨i, eh⟩, (entries g _).2 ⟨i, eg⟩⟩
    · rintro ⟨y, _, eh, eg⟩
      obtain ⟨i, ei⟩ := (entries h _).1 eh
      obtain ⟨j, ej⟩ := (entries g _).1 eg
      have fields := ZFSet.pair_mem_prod.1 (((laws i).function h).1 ei)
      have same := apart i j y fields.2 (ZFSet.pair_mem_prod.1 (((laws j).function g).1 ej)).1
      subst j
      exact (entries (g * h) _).2 ⟨i, ((laws i).mul g h x fields.1 z).2 ⟨y, fields.2, ei, ej⟩⟩

end PartitionPilot.Forcing.RelationActionLaws

end

end OAI
