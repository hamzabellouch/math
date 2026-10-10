import OAI.SetTheory.PartitionPrinciple.Transfinite.CoinitialityPreservation

namespace OAI


namespace PartitionPilot

section

open Compression.RecursiveMaps Compression.RecursiveMaps.Chronological
universe u

namespace Attachment.Templates
variable {O I : Type u} {P : MeetOrder O} (b : Attachment.Templates.{u,u,u} P I)

theorem all_filters_countable (oldSmall : AllFiltersCountable P)
    (templateSmall : ∀ i, AllFiltersCountable (b.order i)) : AllFiltersCountable b.extension := by
  apply all_filters_of_separated_sum b.extension b.oldEmbedding (fun _ => rfl)
    b.Space b.order b.templateEmbedding Sigma.fst
    (fun x => ⟨x.2.val, b.represent_new x.1 x.2.val x.2.property⟩)
    _ oldSmall templateSmall
  intro x y different
  exact attachment_bridge b twoLayerBirth ⟨1⟩ (fun _ => Nat.zero_lt_one) x y different

end Attachment.Templates

namespace Compression.RecursiveMaps.TaskSystem
variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

theorem stage_all_filters_countable (small : AllFiltersCountable P) (n : Nat) :
    AllFiltersCountable (f.order n) := by
  induction n with
  | zero => exact small
  | succ n ih =>
    apply (f.stages n).batch.all_filters_countable ih
    intro i
    exact all_filters_of_surjective (inverseIso (f.templateOriginal n i)).toMeetEmbedding
      (fun x => ⟨(f.templateOriginal n i).toFun x, (f.templateOriginal n i).left_inverse x⟩) small

theorem union_all_filters_countable (small : AllFiltersCountable P) :
    AllFiltersCountable f.unionOrder :=
  all_filters_of_countable_cover f.Point f.order f.inclusionEmbedding f.union_cover
    (f.stage_all_filters_countable small)

end Compression.RecursiveMaps.TaskSystem

end



namespace Compression.RecursiveMaps

open Chronological
universe u

namespace PrincipalBatch.Family
variable {A I : Type u} {P : MeetOrder A} (b : PrincipalBatch.Family P I)

theorem all_filters_countable (oldSmall : AllFiltersCountable P)
    (tileSmall : ∀ i, AllFiltersCountable (b.order i)) : AllFiltersCountable b.extension := by
  apply all_filters_of_separated_sum b.extension b.old.toMeetEmbedding (fun _ => rfl)
    b.Space b.order (fun i => (b.tile i).toMeetEmbedding) Sigma.fst _ _ oldSmall tileSmall
  · intro x
    exact ⟨x.2.val, congrArg (b.componentMap x.1)
      ((b.glue x.1).represent_new x.2.val x.2.property)⟩
  · intro x y different
    apply Or.inl
    rw [b.different_fresh_meet x y different]
    exact Nat.zero_lt_one

end PrincipalBatch.Family

namespace RootedGluing.Scheme
variable {V : Type u} (d : RootedGluing.Scheme V)

theorem stages_all_filters_countable (small : ∀ v, AllFiltersCountable (d.order v)) (n : Nat) :
    AllFiltersCountable (d.stages n).order := by
  induction n with
  | zero => exact small d.root
  | succ n ih => exact (d.stages n).batch.all_filters_countable ih (fun v => small v.val)

theorem glued_all_filters_countable (small : ∀ v, AllFiltersCountable (d.order v)) :
    AllFiltersCountable d.gluedOrder :=
  all_filters_of_countable_cover d.chain.Point d.chain.order
    (fun n => (d.chain.inclusion n).toMeetEmbedding) d.chain.cover (d.stages_all_filters_countable small)

end RootedGluing.Scheme

end Compression.RecursiveMaps



namespace Compression.RecursiveMaps.TileRequests

open Chronological CosetGeometry
universe u

namespace Tile
variable {A Child : Type u} [Countable Child] {P : MeetOrder A} (tile : Tile P Child)

theorem all_filters_countable (small : AllFiltersCountable P) : AllFiltersCountable tile.order :=
  all_filters_of_countable_cover (fun _ : Option Child => A) (fun _ => P)
    (fun i => (tile.vertex i).toMeetEmbedding) tile.vertex_cover (fun _ => small)

end Tile

namespace Family
variable {A J R : Type u} [Group J] {P : MeetOrder A} (f : Family P R)

theorem tile_all_filters_countable (small : AllFiltersCountable P) (r : R) :
    AllFiltersCountable (f.tile r).order := (f.tile r).all_filters_countable small

theorem local_all_filters_countable (small : AllFiltersCountable P)
    (v : TileStars.Vertex J f.Letters R) : AllFiltersCountable (f.localOrder v) := by
  cases v with
  | inl _ => exact small
  | inr c => exact f.tile_all_filters_countable small c.2

theorem glued_all_filters_countable (a : OrderAction J P) (small : AllFiltersCountable P) :
    AllFiltersCountable (f.gluedOrder a) :=
  (f.diagram a).scheme.glued_all_filters_countable (f.local_all_filters_countable small)

theorem extension_all_filters_countable (a : OrderAction J P) (small : AllFiltersCountable P) :
    AllFiltersCountable (f.extensionOrder a) :=
  FixedTop.all_filters_countable _ (f.glued_all_filters_countable a small)

end Family

end Compression.RecursiveMaps.TileRequests

end PartitionPilot

end OAI
