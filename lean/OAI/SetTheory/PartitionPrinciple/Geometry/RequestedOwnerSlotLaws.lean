import OAI.SetTheory.PartitionPrinciple.Definability.ExternalCopyRelations
import OAI.SetTheory.PartitionPrinciple.Definability.RootedSupportOwnerFunction
import OAI.SetTheory.PartitionPrinciple.Forcing.RequestedSupportOwners

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests
open Attachment CosetGeometry
universe u
variable {A : Type u} {P : MeetOrder A}

namespace Request

def vertexSlot : (r : Request P) → Option r.Child → Nat
  | _, none => 0
  | .separation _, some _ => 1
  | .compression _ _, some _ => 1
  | .rectangle _, some j => if j.down then 2 else 1

theorem vertexSlot_lt_three (r : Request P) (i : Option r.Child) : r.vertexSlot i < 3 := by
  cases r with
  | separation W => cases i <;> simp [vertexSlot]
  | compression K copy => cases i <;> simp [vertexSlot]
  | rectangle rect =>
    cases i with
    | none => simp [vertexSlot]
    | some i => cases i with | up b => cases b <;> simp [vertexSlot]

theorem vertexSlot_injective (r : Request P) : Function.Injective r.vertexSlot := by
  cases r with
  | separation W =>
    intro i j equal
    cases i <;> cases j <;> simp_all [vertexSlot, Child]
    exact congrArg some (Subsingleton.elim _ _)
  | compression K copy =>
    intro i j equal
    cases i <;> cases j <;> simp_all [vertexSlot, Child]
    exact congrArg some (Subsingleton.elim _ _)
  | rectangle rect =>
    intro i j equal
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => cases j with | up b => cases b <;> simp_all [vertexSlot]
    | some i =>
      cases j with
      | none => cases i with | up b => cases b <;> simp_all [vertexSlot]
      | some j =>
        cases i with | up b =>
          cases j with | up c =>
            cases b <;> cases c <;> simp_all [vertexSlot]

end Request

namespace Family
variable {R : Type u} (f : Family P R)

def VertexSlotSupports (r : R) (j : Nat) (x : (f.tile r).Space) : Prop :=
  ∃ i : Option (f.Child r), (f.request r).vertexSlot i = j ∧
    ∃ y, (f.flatVertex r i).toFun y = x

theorem vertexSlotSupports_bound {r : R} {j : Nat} {x : (f.tile r).Space}
    (supported : f.VertexSlotSupports r j x) : j < 3 := by
  obtain ⟨i, rfl, _⟩ := supported
  exact (f.request r).vertexSlot_lt_three i

theorem vertexSlotSupports_cover (r : R) (x : (f.tile r).Space) :
    ∃ j, f.VertexSlotSupports r j x := by
  obtain ⟨i, y, equal⟩ := f.flatVertex_cover r x
  exact ⟨(f.request r).vertexSlot i, i, rfl, y, equal⟩

theorem vertexSlotSupports_lower {r : R} {j : Nat} {x y : (f.tile r).Space}
    (supported : f.VertexSlotSupports r j y) (lower : (f.tile r).order.le x y) :
    f.VertexSlotSupports r j x := by
  obtain ⟨i, code, z, rfl⟩ := supported
  obtain ⟨v, equal⟩ := (f.flatVertex r i).ideal z x lower
  exact ⟨i, code, v, equal⟩

noncomputable def leastVertexSlot (r : R) (x : (f.tile r).Space) : Nat := by
  classical
  exact Nat.find (f.vertexSlotSupports_cover r x)

theorem leastVertexSlot_support (r : R) (x : (f.tile r).Space) :
    f.VertexSlotSupports r (f.leastVertexSlot r x) x := by
  classical
  exact Nat.find_spec (f.vertexSlotSupports_cover r x)

theorem leastVertexSlot_lt_three (r : R) (x : (f.tile r).Space) :
    f.leastVertexSlot r x < 3 :=
  f.vertexSlotSupports_bound (f.leastVertexSlot_support r x)

theorem leastVertexSlot_le {r : R} {j : Nat} {x : (f.tile r).Space}
    (supported : f.VertexSlotSupports r j x) : f.leastVertexSlot r x ≤ j := by
  classical
  exact Nat.find_min' (f.vertexSlotSupports_cover r x) supported

theorem leastVertexSlot_eq_iff (r : R) (x : (f.tile r).Space) (j : Nat) :
    f.leastVertexSlot r x = j ↔
      f.VertexSlotSupports r j x ∧ ∀ k, k < j → ¬ f.VertexSlotSupports r k x := by
  constructor
  · rintro rfl
    refine ⟨f.leastVertexSlot_support r x, ?_⟩
    intro k lower supported
    exact (Nat.not_lt_of_ge (f.leastVertexSlot_le supported)) lower
  · rintro ⟨supported, minimal⟩
    apply Nat.le_antisymm (f.leastVertexSlot_le supported)
    exact Nat.le_of_not_gt (fun lower => minimal _ lower (f.leastVertexSlot_support r x))

theorem leastVertexSlot_mono {r : R} {x y : (f.tile r).Space}
    (lower : (f.tile r).order.le x y) : f.leastVertexSlot r x ≤ f.leastVertexSlot r y :=
  f.leastVertexSlot_le (f.vertexSlotSupports_lower (f.leastVertexSlot_support r y) lower)

end Family
end PartitionPilot.Compression.RecursiveMaps.TileRequests



namespace PartitionPilot.Compression.RecursiveMaps
open Attachment CosetGeometry
universe u

namespace RootedGluing.Scheme
variable {V : Type u} (d : Scheme V)

theorem leastSupport_meet_depth_lt {x y : d.Node} {v w k : V}
    (first : d.LeastSupport v x) (second : d.LeastSupport w y)
    (third : d.LeastSupport k (d.gluedOrder.meet x y))
    (same : d.depth v = d.depth w) (different : v ≠ w) : d.depth k < d.depth v := by
  have bound := d.leastSupport_depth_mono third first (d.gluedOrder.meet_le_left x y)
  apply Nat.lt_of_le_of_ne bound
  intro equal
  have left := d.leastSupport_eq_of_depth_eq third first
    (d.gluedOrder.meet_le_left x y) equal
  have right := d.leastSupport_eq_of_depth_eq third second
    (d.gluedOrder.meet_le_right x y) (equal.trans same)
  exact different (left.symm.trans right)

theorem owner_meet_depth_lt {x y : d.Node}
    (same : d.depth (d.owner x) = d.depth (d.owner y)) (different : d.owner x ≠ d.owner y) :
    d.depth (d.owner (d.gluedOrder.meet x y)) < d.depth (d.owner x) :=
  d.leastSupport_meet_depth_lt (d.owner_least x) (d.owner_least y)
    (d.owner_least (d.gluedOrder.meet x y)) same different

end RootedGluing.Scheme

namespace TileRequests.Family
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

def SlotSupports (w : External J f.Letters) (r : R) (j : Nat) (x : f.Node a) : Prop :=
  ∃ i : Option (f.Child r), (f.request r).vertexSlot i = j ∧
    ∃ y, (f.copy a (f.flatWord w r i)).toFun y = x

theorem slotSupports_iff (w : External J f.Letters) (r : R) (j : Nat) (x : f.Node a) :
    f.SlotSupports a w r j x ↔
      ∃ y : (f.tile r).Space, f.VertexSlotSupports r j y ∧ (f.placedTile a w r).toFun y = x := by
  constructor
  · rintro ⟨i, code, y, rfl⟩
    exact ⟨(f.flatVertex r i).toFun y, ⟨i, code, y, rfl⟩, f.flatVertex_copy a w r i y⟩
  · rintro ⟨y, ⟨i, code, z, rfl⟩, equal⟩
    exact ⟨i, code, z, (f.flatVertex_copy a w r i z).symm.trans equal⟩

theorem slotSupports_placed_iff (w : External J f.Letters) (r : R) (j : Nat)
    (x : (f.tile r).Space) :
    f.SlotSupports a w r j ((f.placedTile a w r).toFun x) ↔ f.VertexSlotSupports r j x := by
  rw [f.slotSupports_iff]
  constructor
  · rintro ⟨y, supported, equal⟩
    have same := embedding_injective (f.placedTile a w r).toMeetEmbedding equal
    exact same ▸ supported
  · intro supported
    exact ⟨x, supported, rfl⟩

theorem slotSupports_bound {w : External J f.Letters} {r : R} {j : Nat} {x : f.Node a}
    (supported : f.SlotSupports a w r j x) : j < 3 := by
  obtain ⟨i, rfl, _⟩ := supported
  exact (f.request r).vertexSlot_lt_three i

theorem slotSupports_lower {w : External J f.Letters} {r : R} {j : Nat} {x y : f.Node a}
    (supported : f.SlotSupports a w r j y) (lower : (f.gluedOrder a).le x y) :
    f.SlotSupports a w r j x := by
  obtain ⟨i, code, z, rfl⟩ := supported
  obtain ⟨v, equal⟩ := (f.copy a (f.flatWord w r i)).ideal z x lower
  exact ⟨i, code, v, equal⟩

theorem slotSupports_tile {w : External J f.Letters} {r : R} {j : Nat} {x : f.Node a}
    (supported : f.SlotSupports a w r j x) : (f.diagram a).scheme.Supports (.inr (w, r)) x := by
  obtain ⟨y, _, equal⟩ := (f.slotSupports_iff a w r j x).1 supported
  exact ⟨y, equal⟩

theorem tile_slot_cover (w : External J f.Letters) (r : R) (x : (f.tile r).Space) :
    ∃ j, j < 3 ∧ f.SlotSupports a w r j ((f.placedTile a w r).toFun x) :=
  ⟨f.leastVertexSlot r x, f.leastVertexSlot_lt_three r x,
    (f.slotSupports_placed_iff a w r _ x).2 (f.leastVertexSlot_support r x)⟩

theorem fresh_owner_slot_cover (x : f.Node a) (fresh : ¬ ∃ y, (f.copy a 1).toFun y = x) :
    ∃ w r j, j < 3 ∧ (f.diagram a).scheme.LeastSupport (.inr (w, r)) x ∧
      f.SlotSupports a w r j x := by
  obtain ⟨w, r, y, least, rfl, _⟩ := f.new_point_has_fresh_tile a x fresh
  obtain ⟨j, bound, supported⟩ := f.tile_slot_cover a w r y
  exact ⟨w, r, j, bound, least, supported⟩

theorem slotSupports_owner_cutoff {w : External J f.Letters} {r : R} {j : Nat}
    {x : f.Node a} {v : TileStars.Vertex J f.Letters R}
    (supported : f.SlotSupports a w r j x) (least : (f.diagram a).scheme.LeastSupport v x) :
    (f.diagram a).scheme.depth v < (f.diagram a).scheme.depth (.inr (w, r)) ∨
      (v = .inr (w, r) ∧ ∃ y : (f.tile r).Space,
        (f.placedTile a w r).toFun y = x ∧ f.leastVertexSlot r y ≤ j) := by
  have bound := least.2 (.inr (w, r)) (f.slotSupports_tile a supported)
  rcases Nat.lt_or_eq_of_le bound with lower | equal
  · exact Or.inl lower
  · have tileLeast : (f.diagram a).scheme.LeastSupport (.inr (w, r)) x := by
      refine ⟨f.slotSupports_tile a supported, ?_⟩
      intro z supportZ
      rw [← equal]
      exact least.2 z supportZ
    have same := (f.diagram a).scheme.leastSupport_unique least tileLeast
    obtain ⟨y, localSupport, entry⟩ := (f.slotSupports_iff a w r j x).1 supported
    exact Or.inr ⟨same, y, entry, f.leastVertexSlot_le localSupport⟩

end TileRequests.Family
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
