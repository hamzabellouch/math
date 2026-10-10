import OAI.SetTheory.PartitionPrinciple.Geometry.OutwardSchedule
import OAI.SetTheory.PartitionPrinciple.Transfinite.SuccessorBirths

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

namespace TaskSystem

open Chronological
universe u
variable {A G Task Label Stage : Type u} [LinearOrder Stage] {P : MeetOrder A}
    (f : TaskSystem P G Task Label)

noncomputable def batchBirth (n : Nat) (oldBirth : (f.stages n).Old → Stage) (s : Stage) :
    (f.stages n).Old ⊕ (f.stages n).batch.Fresh → Stage :=
  (f.stages n).batch.birth oldBirth s

theorem batch_new_old_meet (n : Nat) (oldBirth : (f.stages n).Old → Stage) (s : Stage)
    (old : ∀ x, oldBirth x < s) :
    NewOldMeet (P := (f.stages n).batch.extension) (f.batchBirth n oldBirth s) s :=
  (f.stages n).batch.new_old_meet oldBirth s old

theorem batch_old_meet_preserved (n : Nat) (oldBirth : (f.stages n).Old → Stage) (s : Stage)
    (old : ∀ x, oldBirth x < s) (previous : OldMeet (P := (f.stages n).oldOrder) oldBirth) :
    OldMeet (P := (f.stages n).batch.extension) (f.batchBirth n oldBirth s) :=
  (f.stages n).batch.old_meet_preserved oldBirth s old previous

noncomputable def batch_earlier_layer (n : Nat)
    {Space : Stage → Type u} {orders : ∀ t, MeetOrder (Space t)}
    (oldBirth : (f.stages n).Old → Stage) (s t : Stage) (earlier : t < s)
    (layer : GrowthLayer Space orders (f.stages n).oldOrder oldBirth t) :
    GrowthLayer Space orders (f.stages n).batch.extension (f.batchBirth n oldBirth s) t :=
  (f.stages n).batch.earlier_layer oldBirth s t earlier layer

noncomputable def batch_incoming_layer (n : Nat)
    (Space : Stage → Type u) (orders : ∀ t, MeetOrder (Space t))
    (oldBirth : (f.stages n).Old → Stage) (s t : Stage) (old : ∀ x, oldBirth x < s)
    (earlier : t < s) (original : MeetIso (orders t) P) :
    GrowthLayer Space orders (f.stages n).batch.extension (f.batchBirth n oldBirth s) s :=
  (f.stages n).batch.incoming_layer Space orders oldBirth s old (fun _ => t)
    (fun _ => earlier)
    (fun i => RootedGluing.chainIso original (inverseIso (f.templateOriginal n i)))

end TaskSystem



namespace TaskSystem

open Chronological
universe u
variable {A G Task Label Stage : Type u} {P : MeetOrder A}
    (f : TaskSystem P G Task Label) (seed : A → Stage) (stamp : Nat → Stage)

noncomputable def recordedStageBirth : (n : Nat) → f.Point n → Stage
  | 0, x => seed x
  | n + 1, .inl x => recordedStageBirth n x
  | n + 1, .inr _ => stamp n

def recordedUnionBirth : f.Union → Stage
  | .inl x => seed x
  | .inr x => stamp x.1

theorem recordedBirth_stage (n : Nat) (x : f.Point n) :
    f.recordedUnionBirth seed stamp (f.inclusion n x) =
      f.recordedStageBirth seed stamp n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases x with
    | inl x => exact ih x
    | inr x => rfl

theorem recordedBirth_original (x : A) :
    f.recordedUnionBirth seed stamp (f.originalEmbedding.toFun x) = seed x := rfl

theorem recordedBirth_next (n : Nat) (x : f.Point n) :
    f.recordedStageBirth seed stamp (n + 1) ((f.step n).toFun x) =
      f.recordedStageBirth seed stamp n x := rfl

theorem recordedBirth_cases (x : f.Union) :
    (∃ y, f.recordedUnionBirth seed stamp x = seed y) ∨
      ∃ n, f.recordedUnionBirth seed stamp x = stamp n := by
  cases x with
  | inl x => exact Or.inl ⟨x, rfl⟩
  | inr x => exact Or.inr ⟨x.1, rfl⟩

variable [LinearOrder Stage]
    (seed_before : ∀ x n, seed x < stamp n)
    (stamps_before : ∀ n m, n < m → stamp n < stamp m)

include seed_before stamps_before in
theorem recordedStageBirth_lt_later (n m : Nat) (lower : n ≤ m) (x : f.Point n) :
    f.recordedStageBirth seed stamp n x < stamp m := by
  induction n with
  | zero => exact seed_before x m
  | succ n ih =>
    cases x with
    | inl x => exact ih (Nat.le_trans (Nat.le_succ n) lower) x
    | inr x => exact stamps_before n m (Nat.lt_of_succ_le lower)

include seed_before stamps_before in
theorem recordedStageBirth_old_meet (initial : OldMeet (P := P) seed) (n : Nat) :
    OldMeet (P := f.order n) (f.recordedStageBirth seed stamp n) := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    have same : f.recordedStageBirth seed stamp (n + 1) =
        f.batchBirth n (f.recordedStageBirth seed stamp n) (stamp n) := by
      funext x
      cases x <;> rfl
    rw [same]
    exact f.batch_old_meet_preserved n _ _
      (f.recordedStageBirth_lt_later seed stamp seed_before stamps_before n n le_rfl) ih

include seed_before stamps_before in
theorem recordedUnionBirth_old_meet (initial : OldMeet (P := P) seed) :
    OldMeet (P := f.unionOrder) (f.recordedUnionBirth seed stamp) :=
  oldMeet_of_covered_stages f.order (f.recordedUnionBirth seed stamp)
    (f.recordedStageBirth seed stamp) f.inclusionEmbedding
    (f.recordedBirth_stage seed stamp) f.pair_cover
    (f.recordedStageBirth_old_meet seed stamp seed_before stamps_before initial)


end TaskSystem



namespace PrincipalBatch.Family

open Chronological
universe u
variable {A I Stage : Type u} [LinearOrder Stage] {P : MeetOrder A}
    (b : PrincipalBatch.Family P I)

noncomputable def stepBirth (U : I → Prop) (i : I) (outside : ¬ U i)
    (oldBirth : b.Cutoff U → Stage) (s : Stage) : b.Cutoff (addComponent U i) → Stage :=
  fun x => (b.stepInput U i).birth oldBirth s ((b.stepIso U i outside).inverse x)

omit [LinearOrder Stage] in
theorem stepBirth_iso (U : I → Prop) (i : I) (outside : ¬ U i)
    (oldBirth : b.Cutoff U → Stage) (s : Stage) (x : (b.stepInput U i).Node) :
    b.stepBirth U i outside oldBirth s ((b.stepIso U i outside).toFun x) =
      (b.stepInput U i).birth oldBirth s x := by
  change (b.stepInput U i).birth oldBirth s
    ((b.stepIso U i outside).inverse ((b.stepIso U i outside).toFun x)) = _
  rw [(b.stepIso U i outside).left_inverse]

omit [LinearOrder Stage] in
theorem stepBirth_old (U : I → Prop) (i : I) (outside : ¬ U i)
    (oldBirth : b.Cutoff U → Stage) (s : Stage) (x : b.Cutoff U) :
    b.stepBirth U i outside oldBirth s
      ((b.cutoffInclusion (fun _ h => Or.inl h : ∀ j, U j → addComponent U i j)).toFun x) =
      oldBirth x :=
  b.stepBirth_iso U i outside oldBirth s (.inl x)

theorem stepBirth_le (U : I → Prop) (i : I) (outside : ¬ U i)
    (oldBirth : b.Cutoff U → Stage) (s : Stage) (old : ∀ x, oldBirth x < s)
    (x : b.Cutoff (addComponent U i)) : b.stepBirth U i outside oldBirth s x ≤ s :=
  (b.stepInput U i).birth_le oldBirth s old ((b.stepIso U i outside).inverse x)

theorem step_new_old_meet (U : I → Prop) (i : I) (outside : ¬ U i)
    (oldBirth : b.Cutoff U → Stage) (s : Stage) (old : ∀ x, oldBirth x < s) :
    NewOldMeet (P := b.cutoffOrder (addComponent U i)) (b.stepBirth U i outside oldBirth s) s :=
  ((b.stepInput U i).new_old_meet oldBirth s old).transport
    (b.stepIso U i outside).toMeetEmbedding (b.stepBirth_iso U i outside oldBirth s)
    (fun y => ⟨(b.stepIso U i outside).inverse y, (b.stepIso U i outside).right_inverse y⟩)

theorem step_old_meet_preserved (U : I → Prop) (i : I) (outside : ¬ U i)
    (oldBirth : b.Cutoff U → Stage) (s : Stage) (old : ∀ x, oldBirth x < s)
    (previous : OldMeet (P := b.cutoffOrder U) oldBirth) :
    OldMeet (P := b.cutoffOrder (addComponent U i)) (b.stepBirth U i outside oldBirth s) :=
  ((b.stepInput U i).old_meet_preserved oldBirth s old previous).transport
    (b.stepIso U i outside).toMeetEmbedding (b.stepBirth_iso U i outside oldBirth s)
    (fun y => ⟨(b.stepIso U i outside).inverse y, (b.stepIso U i outside).right_inverse y⟩)

noncomputable def step_earlier_layer (U : I → Prop) (i : I) (outside : ¬ U i)
    {Space : Stage → Type u} {orders : ∀ t, MeetOrder (Space t)}
    (oldBirth : b.Cutoff U → Stage) (s t : Stage) (earlier : t < s)
    (layer : GrowthLayer Space orders (b.cutoffOrder U) oldBirth t) :
    GrowthLayer Space orders (b.cutoffOrder (addComponent U i))
      (b.stepBirth U i outside oldBirth s) t :=
  ((b.stepInput U i).earlier_layer oldBirth s t earlier layer).transport
    (b.stepIso U i outside).toMeetEmbedding (b.stepBirth_iso U i outside oldBirth s)
    (fun y _ => ⟨(b.stepIso U i outside).inverse y, (b.stepIso U i outside).right_inverse y⟩)

noncomputable def step_incoming_layer (U : I → Prop) (i : I) (outside : ¬ U i)
    (Space : Stage → Type u) (orders : ∀ t, MeetOrder (Space t))
    (oldBirth : b.Cutoff U → Stage) (s : Stage) (old : ∀ x, oldBirth x < s)
    (K : Type u) [Countable K] (index : K → Stage) (earlier : ∀ k, index k < s)
    (copy : ∀ k, MeetEmbedding (orders (index k)) (b.order i))
    (cover : ∀ x, ∃ k y, (copy k).toFun y = x) :
    GrowthLayer Space orders (b.cutoffOrder (addComponent U i))
      (b.stepBirth U i outside oldBirth s) s :=
  ((b.stepInput U i).incoming_layer Space orders oldBirth s old K index earlier copy cover).transport
    (b.stepIso U i outside).toMeetEmbedding (b.stepBirth_iso U i outside oldBirth s)
    (fun y _ => ⟨(b.stepIso U i outside).inverse y, (b.stepIso U i outside).right_inverse y⟩)

theorem step_no_birth (U : I → Prop) (i : I) (outside : ¬ U i)
    (oldBirth : b.Cutoff U → Stage) (s : Stage) (old : ∀ x, oldBirth x < s)
    (noFresh : ∀ _ : (b.glue i).Fresh, False) (x : b.Cutoff (addComponent U i)) :
    b.stepBirth U i outside oldBirth s x < s := by
  change (b.stepInput U i).birth oldBirth s ((b.stepIso U i outside).inverse x) < s
  cases (b.stepIso U i outside).inverse x with
  | inl a => exact old a
  | inr y => exact False.elim (noFresh y)

end PrincipalBatch.Family



namespace TileRequests

open Chronological
universe u

namespace Tile
variable {A Child : Type u} {P : MeetOrder A} (tile : Tile P Child)

def vertex : Option Child → IdealEmbedding P tile.order
  | none => tile.root
  | some j => tile.child j

theorem vertex_cover (x : tile.Space) : ∃ j y, (tile.vertex j).toFun y = x := by
  rcases tile.cover x with ⟨y, eq⟩ | ⟨j, y, eq⟩
  · exact ⟨none, y, eq⟩
  · exact ⟨some j, y, eq⟩

noncomputable def incoming_layer {B Stage : Type u} [LinearOrder Stage] [Countable Child]
    {Q : MeetOrder B} (g : PrincipalAmalgamation.Input Q tile.order)
    (Space : Stage → Type u) (orders : ∀ t, MeetOrder (Space t))
    (oldBirth : B → Stage) (s t : Stage) (old : ∀ x, oldBirth x < s)
    (earlier : t < s) (original : MeetIso (orders t) P) :
    GrowthLayer Space orders g.order (g.birth oldBirth s) s := by
  apply g.incoming_layer Space orders oldBirth s old (Option Child) (fun _ => t)
    (fun _ => earlier) (fun j => compose original.toMeetEmbedding (tile.vertex j).toMeetEmbedding)
  intro x
  rcases tile.vertex_cover x with ⟨j, y, eq⟩
  refine ⟨j, original.inverse y, ?_⟩
  change (tile.vertex j).toFun (original.toFun (original.inverse y)) = x
  rw [original.right_inverse]
  exact eq

end Tile

namespace Request
variable {A : Type u} {P : MeetOrder A}

instance child_countable (r : Request P) : Countable r.Child := by
  cases r <;> dsimp [Child] <;> infer_instance

end Request

namespace Family
variable {A R : Type u} {P : MeetOrder A} (f : Family P R)

instance child_countable (r : R) : Countable (f.Child r) := Request.child_countable (f.request r)

noncomputable def tile_incoming_layer (r : R) {B Stage : Type u} [LinearOrder Stage]
    {Q : MeetOrder B} (g : PrincipalAmalgamation.Input Q (f.tile r).order)
    (Space : Stage → Type u) (orders : ∀ t, MeetOrder (Space t))
    (oldBirth : B → Stage) (s t : Stage) (old : ∀ x, oldBirth x < s)
    (earlier : t < s) (original : MeetIso (orders t) P) :
    GrowthLayer Space orders g.order (g.birth oldBirth s) s :=
  (f.tile r).incoming_layer g Space orders oldBirth s t old earlier original

end Family
end TileRequests



namespace TileRequests.Family

open Chronological CosetGeometry
universe u
variable {A J R Stage : Type u} [Group J] [LinearOrder Stage] {P : MeetOrder A}
    (f : Family P R) (a : OrderAction J P)

noncomputable def orderedBirth (n : Nat) (v : f.Layer a n)
    (oldBirth : f.Cutoff a n ((f.diagram a).scheme.layerBefore n v) → Stage) (s : Stage) :
    f.Cutoff a n (PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v) →
      Stage :=
  ((f.diagram a).scheme.stages n).batch.stepBirth ((f.diagram a).scheme.layerBefore n v) v
    ((f.diagram a).scheme.layerBefore_irrefl n v) oldBirth s

omit [LinearOrder Stage] in
theorem ordered_birth_preserves (n : Nat) (v : f.Layer a n)
    (oldBirth : f.Cutoff a n ((f.diagram a).scheme.layerBefore n v) → Stage) (s : Stage)
    (x : f.Cutoff a n ((f.diagram a).scheme.layerBefore n v)) :
    f.orderedBirth a n v oldBirth s
      ((((f.diagram a).scheme.stages n).batch.cutoffInclusion
        (fun _ h => Or.inl h : ∀ j, (f.diagram a).scheme.layerBefore n v j →
          PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v j)).toFun x) =
      oldBirth x :=
  ((f.diagram a).scheme.stages n).batch.stepBirth_old _ v
    ((f.diagram a).scheme.layerBefore_irrefl n v) oldBirth s x

theorem ordered_new_old_meet (n : Nat) (v : f.Layer a n)
    (oldBirth : f.Cutoff a n ((f.diagram a).scheme.layerBefore n v) → Stage) (s : Stage)
    (old : ∀ x, oldBirth x < s) :
    NewOldMeet (P := f.cutoffOrder a n
      (PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v))
      (f.orderedBirth a n v oldBirth s) s :=
  ((f.diagram a).scheme.stages n).batch.step_new_old_meet _ v
    ((f.diagram a).scheme.layerBefore_irrefl n v) oldBirth s old

theorem ordered_old_meet_preserved (n : Nat) (v : f.Layer a n)
    (oldBirth : f.Cutoff a n ((f.diagram a).scheme.layerBefore n v) → Stage) (s : Stage)
    (old : ∀ x, oldBirth x < s)
    (previous : OldMeet (P := f.cutoffOrder a n ((f.diagram a).scheme.layerBefore n v)) oldBirth) :
    OldMeet (P := f.cutoffOrder a n
      (PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v))
      (f.orderedBirth a n v oldBirth s) :=
  ((f.diagram a).scheme.stages n).batch.step_old_meet_preserved _ v
    ((f.diagram a).scheme.layerBefore_irrefl n v) oldBirth s old previous

noncomputable def ordered_earlier_layer (n : Nat) (v : f.Layer a n)
    {Space : Stage → Type u} {orders : ∀ t, MeetOrder (Space t)}
    (oldBirth : f.Cutoff a n ((f.diagram a).scheme.layerBefore n v) → Stage) (s t : Stage)
    (earlier : t < s)
    (layer : GrowthLayer Space orders
      (f.cutoffOrder a n ((f.diagram a).scheme.layerBefore n v)) oldBirth t) :
    GrowthLayer Space orders (f.cutoffOrder a n
      (PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v))
      (f.orderedBirth a n v oldBirth s) t :=
  ((f.diagram a).scheme.stages n).batch.step_earlier_layer _ v
    ((f.diagram a).scheme.layerBefore_irrefl n v) oldBirth s t earlier layer

noncomputable def ordered_incoming_layer (n : Nat) (v : f.Layer a n)
    (Space : Stage → Type u) (orders : ∀ t, MeetOrder (Space t))
    (oldBirth : f.Cutoff a n ((f.diagram a).scheme.layerBefore n v) → Stage) (s t : Stage)
    (old : ∀ x, oldBirth x < s) (earlier : t < s) (original : MeetIso (orders t) P) :
    GrowthLayer Space orders (f.cutoffOrder a n
      (PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v))
      (f.orderedBirth a n v oldBirth s) s := by
  rcases v with ⟨v, depth⟩
  cases v with
  | inl c =>
    apply finiteLayer Space orders
    apply (Set.finite_empty).subset
    intro x hx
    have oldPoint := ((f.diagram a).scheme.stages n).batch.step_no_birth
      ((f.diagram a).scheme.layerBefore n ⟨.inl c, depth⟩) ⟨.inl c, depth⟩
      ((f.diagram a).scheme.layerBefore_irrefl n ⟨.inl c, depth⟩) oldBirth s old
      (f.old_layer_no_fresh a n ⟨.inl c, depth⟩ c rfl) x
    exact False.elim ((ne_of_lt oldPoint) hx)
  | inr c =>
    apply ((f.diagram a).scheme.stages n).batch.step_incoming_layer
      ((f.diagram a).scheme.layerBefore n ⟨.inr c, depth⟩) ⟨.inr c, depth⟩
      ((f.diagram a).scheme.layerBefore_irrefl n ⟨.inr c, depth⟩)
      Space orders oldBirth s old (Option (f.Child c.2)) (fun _ => t) (fun _ => earlier)
      (fun j => compose original.toMeetEmbedding ((f.tile c.2).vertex j).toMeetEmbedding)
    intro x
    rcases (f.tile c.2).vertex_cover x with ⟨j, y, eq⟩
    refine ⟨j, original.inverse y, ?_⟩
    change ((f.tile c.2).vertex j).toFun (original.toFun (original.inverse y)) = x
    rw [original.right_inverse]
    exact eq

end TileRequests.Family



namespace PrincipalBatch.Family

open Attachment Chronological
universe u
variable {A I Stage : Type u} {P : MeetOrder A} (b : PrincipalBatch.Family P I)

def recordBirth (oldBirth : A → Stage) (stamp : I → Stage) : b.Node → Stage
  | .inl x => oldBirth x
  | .inr x => stamp x.1

theorem different_fresh_meet (x y : b.Fresh) (different : x.1 ≠ y.1) :
    b.extension.meet (.inr x) (.inr y) =
      b.old.toFun (P.meet ((b.glue x.1).shadow x.2.val) ((b.glue y.1).shadow y.2.val)) :=
  meet_eq b.data b.component_meets (cross_meet b.data x y different
    (b.different_fresh_incomparable x y different)
    (b.different_fresh_incomparable y x different.symm))

theorem record_old_meet [LinearOrder Stage] (oldBirth : A → Stage) (stamp : I → Stage)
    (before : ∀ x i, oldBirth x < stamp i) (previous : OldMeet (P := P) oldBirth) :
    OldMeet (P := b.extension) (b.recordBirth oldBirth stamp) := by
  intro x y earlier notLower
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have eq : b.extension.meet (.inl x) (.inl y) = .inl (P.meet x y) :=
        (b.old.map_meet x y).symm
      rw [eq]
      exact previous x y earlier notLower
    | inr y => exact False.elim (lt_asymm earlier (before x y.1))
  | inr x =>
    cases y with
    | inl y =>
      have eq : b.extension.meet (.inr x) (.inl y) =
          .inl (P.meet ((b.glue x.1).shadow x.2.val) y) := b.fresh_old_meet x y
      rw [eq]
      exact before _ x.1
    | inr y =>
      have different : x.1 ≠ y.1 := by
        intro eq
        exact (ne_of_lt earlier) (congrArg stamp eq).symm
      rw [b.different_fresh_meet x y different]
      exact before _ x.1

end PrincipalBatch.Family



namespace RootedGluing.Scheme

universe u
variable {V Stage : Type u} (d : Scheme V)
    (seed : d.Space d.root → Stage) (stamp : ∀ n, (d.stages n).Layer → Stage)

noncomputable def stageBirth : (n : Nat) → (d.stages n).Point → Stage
  | 0, x => seed x
  | n + 1, .inl x => stageBirth n x
  | n + 1, .inr x => stamp n x.1

theorem stageBirth_next (n : Nat) (x : (d.stages n).Point) :
    d.stageBirth seed stamp (n + 1) ((d.chain.next n).toFun x) = d.stageBirth seed stamp n x := rfl

theorem stageBirth_up {n m : Nat} (lower : n ≤ m) (x : (d.stages n).Point) :
    d.stageBirth seed stamp m (d.chain.up lower x) = d.stageBirth seed stamp n x := by
  induction lower with
  | refl => erw [d.chain.up_self]
  | @step m lower ih => erw [d.chain.up_succ lower, d.stageBirth_next, ih]

noncomputable def unionBirth : d.Node → Stage :=
  Quotient.lift (fun x => d.stageBirth seed stamp x.1 x.2) (by
    intro x y related
    rcases related with ⟨k, hx, hy, eq⟩
    exact (d.stageBirth_up seed stamp hx x.2).symm.trans
      ((congrArg (d.stageBirth seed stamp k) eq).trans (d.stageBirth_up seed stamp hy y.2)))

theorem unionBirth_stage (n : Nat) (x : (d.stages n).Point) :
    d.unionBirth seed stamp (d.chain.point n x) = d.stageBirth seed stamp n x := rfl

theorem unionBirth_original (x : d.Space d.root) :
    d.unionBirth seed stamp ((d.vertex d.root).toFun x) = seed x := by
  rw [d.vertex_at d.root 0 d.depth_root.le]
  rfl

noncomputable def partialBirth (n : Nat) (U : (d.stages n).Layer → Prop) : d.Partial n U → Stage :=
  fun x => d.stageBirth seed stamp (n + 1) x.val

theorem partialBirth_global (n : Nat) (U : (d.stages n).Layer → Prop) (x : d.Partial n U) :
    d.unionBirth seed stamp ((d.partialEmbedding n U).toFun x) = d.partialBirth seed stamp n U x := rfl

theorem partialBirth_inclusion (n : Nat) {U W : (d.stages n).Layer → Prop}
    (lower : ∀ v, U v → W v) (x : d.Partial n U) :
    d.partialBirth seed stamp n W (((d.stages n).batch.cutoffInclusion lower).toFun x) =
      d.partialBirth seed stamp n U x := rfl

theorem partialBirth_later {n m : Nat} (later : n < m)
    (U : (d.stages n).Layer → Prop) (W : (d.stages m).Layer → Prop) (x : d.Partial n U) :
    d.partialBirth seed stamp m W ((d.partialLater later U W).toFun x) =
      d.partialBirth seed stamp n U x := by
  rw [← d.partialBirth_global, d.partialLater_global, d.partialBirth_global]

theorem partialBirth_step_iso (n : Nat) (U : (d.stages n).Layer → Prop)
    (v : (d.stages n).Layer) (outside : ¬ U v) (x : ((d.stages n).batch.stepInput U v).Node) :
    d.partialBirth seed stamp n (PrincipalBatch.Family.addComponent U v)
      (((d.stages n).batch.stepIso U v outside).toFun x) =
      ((d.stages n).batch.stepInput U v).birth (d.partialBirth seed stamp n U) (stamp n v) x := by
  cases x <;> rfl

theorem partialBirth_step (n : Nat) (U : (d.stages n).Layer → Prop)
    (v : (d.stages n).Layer) (outside : ¬ U v) :
    d.partialBirth seed stamp n (PrincipalBatch.Family.addComponent U v) =
      (d.stages n).batch.stepBirth U v outside (d.partialBirth seed stamp n U) (stamp n v) := by
  funext x
  have eq := d.partialBirth_step_iso seed stamp n U v outside
    (((d.stages n).batch.stepIso U v outside).inverse x)
  erw [((d.stages n).batch.stepIso U v outside).right_inverse] at eq
  exact eq

open Chronological
variable [LinearOrder Stage]
    (seed_before : ∀ x n v, seed x < stamp n v)
    (depth_before : ∀ n m v w, n < m → stamp n v < stamp m w)
    (layer_before : ∀ n v w, d.layerBefore n w v → stamp n v < stamp n w)

include seed_before depth_before in
theorem stageBirth_lt_later (n m : Nat) (lower : n ≤ m)
    (x : (d.stages n).Point) (v : (d.stages m).Layer) :
    d.stageBirth seed stamp n x < stamp m v := by
  induction n with
  | zero => exact seed_before x m v
  | succ n ih =>
    cases x with
    | inl x => exact ih (Nat.le_trans (Nat.le_succ n) lower) x
    | inr x => exact depth_before n m x.1 v (Nat.lt_of_succ_le lower)

include seed_before depth_before layer_before in
theorem partialBirth_before (n : Nat) (v : (d.stages n).Layer)
    (x : d.Partial n (d.layerBefore n v)) :
    d.partialBirth seed stamp n (d.layerBefore n v) x < stamp n v := by
  rcases x with ⟨x, hx⟩
  cases x with
  | inl x => exact d.stageBirth_lt_later seed stamp seed_before depth_before n n le_rfl x v
  | inr x => exact layer_before n x.1 v hx

include seed_before depth_before in
theorem stageBirth_old_meet (initial : OldMeet (P := d.order d.root) seed) (n : Nat) :
    OldMeet (P := (d.stages n).order) (d.stageBirth seed stamp n) := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    have same : d.stageBirth seed stamp (n + 1) =
        (d.stages n).batch.recordBirth (d.stageBirth seed stamp n) (stamp n) := by
      funext x
      cases x <;> rfl
    rw [same]
    exact (d.stages n).batch.record_old_meet (d.stageBirth seed stamp n) (stamp n)
      (fun x v => d.stageBirth_lt_later seed stamp seed_before depth_before n n le_rfl x v) ih

include seed_before depth_before in
theorem unionBirth_old_meet (initial : OldMeet (P := d.order d.root) seed) :
    OldMeet (P := d.gluedOrder) (d.unionBirth seed stamp) :=
  oldMeet_of_covered_stages (fun n => (d.stages n).order) (d.unionBirth seed stamp)
    (d.stageBirth seed stamp) (fun n => (d.chain.inclusion n).toMeetEmbedding)
    (fun _ _ => rfl) d.chain.pair_cover (d.stageBirth_old_meet seed stamp seed_before depth_before initial)

include seed_before depth_before in
theorem partialBirth_old_meet (initial : OldMeet (P := d.order d.root) seed)
    (n : Nat) (U : (d.stages n).Layer → Prop) :
    OldMeet (P := d.partialOrder n U) (d.partialBirth seed stamp n U) := by
  intro x y earlier notLower
  have old := d.unionBirth_old_meet seed stamp seed_before depth_before initial
    ((d.partialEmbedding n U).toFun x) ((d.partialEmbedding n U).toFun y) earlier
    (fun lower => notLower (((d.partialEmbedding n U).le_iff x y).mp lower))
  rw [← (d.partialEmbedding n U).map_meet, d.partialBirth_global] at old
  exact old


end RootedGluing.Scheme



namespace TileRequests.Family

open Chronological CosetGeometry
universe u
variable {A J R Stage : Type u} [Group J] {P : MeetOrder A}
    (f : Family P R) (a : OrderAction J P)
    (seed : A → Stage) (stamp : ∀ n, f.Layer a n → Stage)

noncomputable def externalBirth : f.Node a → Stage := (f.diagram a).scheme.unionBirth seed stamp

noncomputable def cutoffBirth (n : Nat) (U : f.Layer a n → Prop) : f.Cutoff a n U → Stage :=
  (f.diagram a).scheme.partialBirth seed stamp n U

theorem externalBirth_original (x : A) :
    f.externalBirth a seed stamp ((f.copy a 1).toFun x) = seed x := by
  rw [f.copy_one]
  exact (f.diagram a).scheme.unionBirth_original seed stamp x

theorem cutoffBirth_global (n : Nat) (U : f.Layer a n → Prop) (x : f.Cutoff a n U) :
    f.externalBirth a seed stamp ((f.cutoffEmbedding a n U).toFun x) =
      f.cutoffBirth a seed stamp n U x := rfl

theorem cutoffBirth_ordered (n : Nat) (v : f.Layer a n) :
    f.cutoffBirth a seed stamp n
      (PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v) =
      f.orderedBirth a n v (f.cutoffBirth a seed stamp n ((f.diagram a).scheme.layerBefore n v))
        (stamp n v) :=
  (f.diagram a).scheme.partialBirth_step seed stamp n ((f.diagram a).scheme.layerBefore n v) v
    ((f.diagram a).scheme.layerBefore_irrefl n v)

variable [LinearOrder Stage]
    (seed_before : ∀ x n v, seed x < stamp n v)
    (depth_before : ∀ n m v w, n < m → stamp n v < stamp m w)
    (layer_before : ∀ n v w, (f.diagram a).scheme.layerBefore n w v → stamp n v < stamp n w)

include seed_before depth_before layer_before in
theorem cutoffBirth_before (n : Nat) (v : f.Layer a n)
    (x : f.Cutoff a n ((f.diagram a).scheme.layerBefore n v)) :
    f.cutoffBirth a seed stamp n ((f.diagram a).scheme.layerBefore n v) x < stamp n v :=
  (f.diagram a).scheme.partialBirth_before seed stamp seed_before depth_before layer_before n v x

include seed_before depth_before in
theorem externalBirth_old_meet (initial : OldMeet (P := P) seed) :
    OldMeet (P := f.gluedOrder a) (f.externalBirth a seed stamp) :=
  (f.diagram a).scheme.unionBirth_old_meet seed stamp seed_before depth_before initial

include seed_before depth_before in
theorem cutoffBirth_old_meet (initial : OldMeet (P := P) seed)
    (n : Nat) (U : f.Layer a n → Prop) :
    OldMeet (P := f.cutoffOrder a n U) (f.cutoffBirth a seed stamp n U) :=
  (f.diagram a).scheme.partialBirth_old_meet seed stamp seed_before depth_before initial n U

include seed_before depth_before layer_before in
theorem cutoffBirth_new_old_meet (n : Nat) (v : f.Layer a n) :
    NewOldMeet (P := f.cutoffOrder a n
      (PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v))
      (f.cutoffBirth a seed stamp n
        (PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v)) (stamp n v) := by
  rw [f.cutoffBirth_ordered]
  exact f.ordered_new_old_meet a n v _ (stamp n v)
    (f.cutoffBirth_before a seed stamp seed_before depth_before layer_before n v)

noncomputable def cutoffBirth_incoming_layer (n : Nat) (v : f.Layer a n)
    (Space : Stage → Type u) (orders : ∀ t, MeetOrder (Space t)) (t : Stage)
    (earlier : t < stamp n v) (original : MeetIso (orders t) P) :
    GrowthLayer Space orders (f.cutoffOrder a n
      (PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v))
      (f.cutoffBirth a seed stamp n
        (PrincipalBatch.Family.addComponent ((f.diagram a).scheme.layerBefore n v) v)) (stamp n v) := by
  rw [f.cutoffBirth_ordered]
  exact f.ordered_incoming_layer a n v Space orders _ (stamp n v) t
    (f.cutoffBirth_before a seed stamp seed_before depth_before layer_before n v) earlier original


end TileRequests.Family




universe u
namespace RootedGluing.Scheme
variable {V Stage : Type u} (d : Scheme V)
    (seed : d.Space d.root → Stage) (stamp : ∀ n, (d.stages n).Layer → Stage)

theorem stageBirth_cases (n : Nat) (x : (d.stages n).Point) :
    (∃ y, d.stageBirth seed stamp n x = seed y) ∨
      ∃ m, m < n ∧ ∃ v, d.stageBirth seed stamp n x = stamp m v := by
  induction n with
  | zero => exact Or.inl ⟨x, rfl⟩
  | succ n ih =>
    cases x with
    | inl x =>
      rcases ih x with original | ⟨m, lower, v, eq⟩
      · exact Or.inl original
      · exact Or.inr ⟨m, Nat.lt_trans lower (Nat.lt_succ_self n), v, eq⟩
    | inr x => exact Or.inr ⟨n, Nat.lt_succ_self n, x.1, rfl⟩

theorem unionBirth_cases (x : d.Node) :
    (∃ y, d.unionBirth seed stamp x = seed y) ∨
      ∃ n v, d.unionBirth seed stamp x = stamp n v := by
  rcases d.chain.cover x with ⟨n, x, rfl⟩
  erw [d.unionBirth_stage]
  rcases d.stageBirth_cases seed stamp n x with original | ⟨m, _, v, eq⟩
  · exact Or.inl original
  · exact Or.inr ⟨m, v, eq⟩

end RootedGluing.Scheme

namespace TileRequests.Family
open CosetGeometry
variable {A J R Stage : Type u} [Group J] {P : MeetOrder A}
    (f : Family P R) (a : OrderAction J P)
    (seed : A → Stage) (stamp : ∀ n, f.Layer a n → Stage)

theorem externalBirth_cases (x : f.Node a) :
    (∃ y, f.externalBirth a seed stamp x = seed y) ∨
      ∃ n v, f.externalBirth a seed stamp x = stamp n v :=
  (f.diagram a).scheme.unionBirth_cases seed stamp x

end TileRequests.Family


end PartitionPilot.Compression.RecursiveMaps

end OAI
