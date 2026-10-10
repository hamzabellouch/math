import OAI.SetTheory.PartitionPrinciple.Forcing.ChronologicalTransport

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation.Input

open Attachment Chronological

universe u

variable {A B Stage : Type u} [LinearOrder Stage]
    {P : MeetOrder A} {Q : MeetOrder B} (g : Input P Q)

def birth (oldBirth : A → Stage) (s : Stage) : g.Node → Stage
  | .inl a => oldBirth a
  | .inr _ => s

theorem birth_le (oldBirth : A → Stage) (s : Stage) (old : ∀ a, oldBirth a < s) :
    ∀ x, g.birth oldBirth s x ≤ s := by
  intro x
  cases x with
  | inl a => exact le_of_lt (old a)
  | inr _ => exact le_refl s

theorem old_meet_preserved (oldBirth : A → Stage) (s : Stage)
    (old : ∀ a, oldBirth a < s) (previous : OldMeet (P := P) oldBirth) :
    OldMeet (P := g.order) (g.birth oldBirth s) := by
  intro x y earlier notLower
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have eq : g.order.meet (.inl a) (.inl b) = Sum.inl (P.meet a b) :=
        (g.left.map_meet a b).symm
      rw [eq]
      exact previous a b earlier notLower
    | inr y => exact False.elim (lt_asymm earlier (old a))
  | inr x =>
    cases y with
    | inl a =>
      rw [g.new_shadow_meet]
      exact old _
    | inr y => exact False.elim (lt_irrefl s earlier)

noncomputable def earlier_layer {Space : Stage → Type u}
    {order : ∀ t, MeetOrder (Space t)} (oldBirth : A → Stage) (s t : Stage)
    (earlier : t < s) (layer : GrowthLayer Space order P oldBirth t) :
    GrowthLayer Space order g.order (g.birth oldBirth s) t := by
  apply layer.transport g.left (fun _ => rfl)
  intro x hx
  cases x with
  | inl a => exact ⟨a, rfl⟩
  | inr x =>
    change s = t at hx
    exact False.elim (lt_irrefl s (hx ▸ earlier))

noncomputable def incoming_layer (Space : Stage → Type u)
    (order : ∀ t, MeetOrder (Space t)) (oldBirth : A → Stage) (s : Stage)
    (old : ∀ a, oldBirth a < s) (I : Type u) [Countable I]
    (index : I → Stage) (earlier : ∀ i, index i < s)
    (copy : ∀ i, MeetEmbedding (order (index i)) Q)
    (cover : ∀ b, ∃ i y, (copy i).toFun y = b) :
    GrowthLayer Space order g.order (g.birth oldBirth s) s := by
  apply GrowthLayer.copies I inferInstance index earlier (fun i => compose (copy i) g.right)
  intro x hx
  cases x with
  | inl a =>
    change oldBirth a = s at hx
    exact False.elim (lt_irrefl s (hx ▸ old a))
  | inr b =>
    rcases cover b.val with ⟨i, y, eq⟩
    exact ⟨i, y, (congrArg g.right.toFun eq).trans (g.represent_new b.val b.property)⟩

theorem profile_persists (c e K : A) (F : A → Prop) (inhabited : ∃ f, F f)
    (profile : Profile P c e K F) (separated : ¬ P.le e K) :
    ProfileOver g.left c e K F :=
  attachment_preserves_profile g.data g.component_meets c e K F inhabited profile separated

end PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation.Input

namespace PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation

open Chronological

universe u

noncomputable def binary_incoming_layer {A T Stage : Type u} [LinearOrder Stage]
    {P : MeetOrder A} {R : MeetOrder T} (tile : Input R R) (g : Input P tile.order)
    (Space : Stage → Type u) (order : ∀ t, MeetOrder (Space t))
    (oldBirth : A → Stage) (s t : Stage) (old : ∀ a, oldBirth a < s) (earlier : t < s)
    (template : MeetIso (order t) R) :
    GrowthLayer Space order g.order (g.birth oldBirth s) s := by
  apply g.incoming_layer Space order oldBirth s old (ULift.{u} Bool) (fun _ => t) (fun _ => earlier)
    (fun i => compose template.toMeetEmbedding (BinaryTiles.vertex R tile i.down))
  intro x
  rcases BinaryTiles.vertex_cover R tile x with ⟨i, y, eq⟩
  refine ⟨⟨i⟩, template.inverse y, ?_⟩
  change (BinaryTiles.vertex R tile i).toFun (template.toFun (template.inverse y)) = x
  rw [template.right_inverse]
  exact eq

end PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation

end

end OAI
