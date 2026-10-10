import OAI.SetTheory.PartitionPrinciple.Transfinite.PartialBatchLimits

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

open Attachment
universe u
variable {V : Type u} (d : Scheme V)

def Partial (n : Nat) (U : (d.stages n).Layer → Prop) := (d.stages n).batch.Cutoff U

noncomputable def partialOrder (n : Nat) (U : (d.stages n).Layer → Prop) : MeetOrder (d.Partial n U) :=
  (d.stages n).batch.cutoffOrder U

noncomputable def partialEmbedding (n : Nat) (U : (d.stages n).Layer → Prop) :
    IdealEmbedding (d.partialOrder n U) d.gluedOrder :=
  ((d.stages n).batch.cutoffEmbedding U).comp (d.chain.inclusion (n + 1))

theorem partialEmbedding_old (n : Nat) (U : (d.stages n).Layer → Prop) (x : (d.stages n).Point) :
    (d.partialEmbedding n U).toFun (((d.stages n).batch.cutoffOld U).toFun x) = d.chain.point n x :=
  d.point_next n x

theorem partialEmbedding_tile (n : Nat) (U : (d.stages n).Layer → Prop)
    (v : (d.stages n).Layer) (hv : U v) (x : d.Space v.val) :
    (d.partialEmbedding n U).toFun (((d.stages n).batch.cutoffTile U v hv).toFun x) =
      (d.vertex v.val).toFun x := by
  exact ((d.vertex_at v.val (n + 1) v.property.le x).trans
    (congrArg (d.chain.point (n + 1)) ((d.stages n).successor_new v x))).symm

noncomputable def partialOldVertex (n : Nat) (U : (d.stages n).Layer → Prop)
    (v : V) (hv : d.depth v ≤ n) : IdealEmbedding (d.order v) (d.partialOrder n U) :=
  ((d.stages n).vertex v hv).comp ((d.stages n).batch.cutoffOld U)

theorem partialOldVertex_global (n : Nat) (U : (d.stages n).Layer → Prop)
    (v : V) (hv : d.depth v ≤ n) (x : d.Space v) :
    (d.partialEmbedding n U).toFun ((d.partialOldVertex n U v hv).toFun x) =
      (d.vertex v).toFun x := by
  change (d.partialEmbedding n U).toFun (((d.stages n).batch.cutoffOld U).toFun
    (((d.stages n).vertex v hv).toFun x)) = _
  rw [d.partialEmbedding_old]
  exact (d.vertex_at v n hv x).symm

theorem partial_no_later_nodes (n : Nat) (U : (d.stages n).Layer → Prop)
    (x : d.Partial n U) (y : d.Node)
    (lower : d.gluedOrder.le y ((d.partialEmbedding n U).toFun x)) :
    ∃ z, (d.partialEmbedding n U).toFun z = y := (d.partialEmbedding n U).ideal x y lower

noncomputable def partialLater {n m : Nat} (later : n < m)
    (U : (d.stages n).Layer → Prop) (W : (d.stages m).Layer → Prop) :
    IdealEmbedding (d.partialOrder n U) (d.partialOrder m W) :=
  (((d.stages n).batch.cutoffEmbedding U).comp (d.chain.raise (Nat.succ_le_of_lt later))).comp
    ((d.stages m).batch.cutoffOld W)

theorem partialLater_global {n m : Nat} (later : n < m)
    (U : (d.stages n).Layer → Prop) (W : (d.stages m).Layer → Prop) (x : d.Partial n U) :
    (d.partialEmbedding m W).toFun ((d.partialLater later U W).toFun x) =
      (d.partialEmbedding n U).toFun x := by
  exact (d.partialEmbedding_old m W (d.chain.up (Nat.succ_le_of_lt later) x.val)).trans
    (d.chain.include_up (Nat.succ_le_of_lt later) x.val)

theorem partial_cover (z : d.Node) :
    ∃ n, ∃ x : d.Partial n (fun _ => False), (d.partialEmbedding n (fun _ => False)).toFun x = z := by
  rcases d.chain.cover z with ⟨n, x, rfl⟩
  exact ⟨n, ((d.stages n).batch.cutoffOld (fun _ => False)).toFun x, d.partialEmbedding_old n _ x⟩

theorem partial_outside_meet (n : Nat) (U : (d.stages n).Layer → Prop)
    (v : (d.stages n).Layer) (outside : ¬ U v)
    (x : ((d.stages n).batch.glue v).Fresh) (y : d.Partial n U) :
    d.gluedOrder.meet (d.chain.point (n + 1) (.inr ⟨v, x⟩)) ((d.partialEmbedding n U).toFun y) =
      d.gluedOrder.meet (d.chain.point n (((d.stages n).batch.glue v).shadow x.val))
        ((d.partialEmbedding n U).toFun y) := by
  rw [← d.point_next n (((d.stages n).batch.glue v).shadow x.val)]
  change d.chain.unionOrder.meet ((d.chain.inclusion (n + 1)).toFun (.inr ⟨v, x⟩))
      ((d.chain.inclusion (n + 1)).toFun y.val) =
    d.chain.unionOrder.meet ((d.chain.inclusion (n + 1)).toFun
      ((d.stages n).batch.old.toFun (((d.stages n).batch.glue v).shadow x.val)))
      ((d.chain.inclusion (n + 1)).toFun y.val)
  exact ((d.chain.inclusion (n + 1)).map_meet _ _).symm.trans
    ((congrArg (d.chain.inclusion (n + 1)).toFun
      ((d.stages n).batch.outside_meet U v outside x y)).trans
      ((d.chain.inclusion (n + 1)).map_meet _ _))

theorem partial_new_vertex_meet (n : Nat) (U : (d.stages n).Layer → Prop)
    (v : (d.stages n).Layer) (outside : ¬ U v)
    (x : ((d.stages n).batch.glue v).Fresh) (y : d.Partial n U) :
    d.gluedOrder.meet ((d.vertex v.val).toFun x.val) ((d.partialEmbedding n U).toFun y) =
      d.gluedOrder.meet
        ((d.vertex (d.parent v.val)).toFun
          ((d.link v.val ((d.stages n).layer_nonzero v)).toFun
            (cut (d.order v.val) (d.childAnchor v.val ((d.stages n).layer_nonzero v)) x.val)).val)
        ((d.partialEmbedding n U).toFun y) := by
  have fresh : ((d.stages n).batch.tile v).toFun x.val = .inr ⟨v, x⟩ :=
    congrArg ((d.stages n).batch.componentMap v)
      (((d.stages n).batch.glue v).represent_new x.val x.property)
  have vx := (d.vertex_at v.val (n + 1) v.property.le x.val).trans
    (congrArg (d.chain.point (n + 1)) (((d.stages n).successor_new v x.val).trans fresh))
  rw [vx, d.partial_outside_meet n U v outside x y]
  congr 1
  exact (d.vertex_at (d.parent v.val) n ((d.stages n).parent_present v) _).symm

end PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme



namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces

universe u
variable {J S R : Type u} [Group J] {request : S → R} (g : Spaces J S R request)

def FullRight {v w : Vertex J S R} (i : PrincipalAmalgamation.Input (g.order v) (g.order w)) : Prop :=
  ∀ x, (g.order w).le x i.rightAnchor

theorem fullRight_reindex {v w v' w' : Vertex J S R} (hv : v = v') (hw : w = w')
    (i : PrincipalAmalgamation.Input (g.order v) (g.order w)) :
    g.FullRight (g.reindexInput hv hw i) ↔ g.FullRight i := by
  cases hv
  cases hw
  rfl

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

theorem edge_full_at_old (d : TileStars.Dart J f.Letters R) (v : CosetGeometry.Vertex J f.Letters)
    (targetOld : TileStars.target J f.Letters R Sigma.fst d = .inl v) :
    (f.diagram a).FullRight ((f.diagram a).edgeInput d) := by
  rcases d with ⟨e, b⟩
  cases e with
  | inl c =>
    cases b with
    | false => exact f.greatest
    | true => exact False.elim (Sum.inr_ne_inl targetOld)
  | inr c =>
    cases b with
    | false => exact False.elim (Sum.inr_ne_inl targetOld)
    | true => exact f.greatest

theorem old_local_full (v : CosetGeometry.Vertex J f.Letters)
    (h : TileStars.depth J f.Letters R Sigma.fst (.inl v) ≠ 0) :
    (f.diagram a).FullRight ((f.diagram a).localGlue (.inl v) h) := by
  have nonroot : Sum.inl v ≠ TileStars.root J f.Letters R :=
    fun eq => h ((TileStars.depth_zero_iff J f.Letters R Sigma.fst _).mpr eq)
  exact ((f.diagram a).fullRight_reindex
    (TileStars.parent_eq J f.Letters R Sigma.fst (.inl v) nonroot).symm
    (TileStars.incoming_target J f.Letters R Sigma.fst (.inl v) nonroot) _).mpr
    (f.edge_full_at_old a _ v (TileStars.incoming_target J f.Letters R Sigma.fst (.inl v) nonroot))

theorem old_layer_no_fresh (n : Nat) (v : ((f.diagram a).scheme.stages n).Layer)
    (c : CosetGeometry.Vertex J f.Letters) (oldVertex : v.val = .inl c)
    (x : (((f.diagram a).scheme.stages n).batch.glue v).Fresh) : False := by
  rcases v with ⟨v, hv⟩
  cases oldVertex
  exact x.property (f.old_local_full a c
    (((f.diagram a).scheme.stages n).layer_nonzero ⟨.inl c, hv⟩) x.val)

theorem fresh_layer_is_tile (n : Nat) (x : ((f.diagram a).scheme.stages n).batch.Fresh) :
    ∃ w r, x.1.val = .inr (w, r) := by
  cases hv : x.1.val with
  | inl v => exact False.elim (f.old_layer_no_fresh a n x.1 v hv x.2)
  | inr c => exact ⟨c.1, c.2, rfl⟩

def Layer (n : Nat) := ((f.diagram a).scheme.stages n).Layer
def Cutoff (n : Nat) (U : f.Layer a n → Prop) := (f.diagram a).scheme.Partial n U
noncomputable def cutoffOrder (n : Nat) (U : f.Layer a n → Prop) : MeetOrder (f.Cutoff a n U) :=
  (f.diagram a).scheme.partialOrder n U
noncomputable def cutoffEmbedding (n : Nat) (U : f.Layer a n → Prop) :
    IdealEmbedding (f.cutoffOrder a n U) (f.gluedOrder a) :=
  (f.diagram a).scheme.partialEmbedding n U

noncomputable def cutoffPlacedTile (n : Nat) (U : f.Layer a n → Prop)
    (w : External J f.Letters) (r : R)
    (depth : TileStars.depth J f.Letters R Sigma.fst (.inr (w, r)) = n + 1)
    (selected : U ⟨.inr (w, r), depth⟩) : IdealEmbedding (f.tile r).order (f.cutoffOrder a n U) :=
  ((f.diagram a).scheme.stages n).batch.cutoffTile U ⟨.inr (w, r), depth⟩ selected

theorem cutoffPlacedTile_global (n : Nat) (U : f.Layer a n → Prop)
    (w : External J f.Letters) (r : R)
    (depth : TileStars.depth J f.Letters R Sigma.fst (.inr (w, r)) = n + 1)
    (selected : U ⟨.inr (w, r), depth⟩) (x : (f.tile r).Space) :
    (f.cutoffEmbedding a n U).toFun ((f.cutoffPlacedTile a n U w r depth selected).toFun x) =
      (f.placedTile a w r).toFun x :=
  (f.diagram a).scheme.partialEmbedding_tile n U ⟨.inr (w, r), depth⟩ selected x

noncomputable def cutoffTileRoot (n : Nat) (U : f.Layer a n → Prop)
    (w : External J f.Letters) (r : R)
    (depth : TileStars.depth J f.Letters R Sigma.fst (.inr (w, r)) = n + 1)
    (selected : U ⟨.inr (w, r), depth⟩) : IdealEmbedding P (f.cutoffOrder a n U) :=
  (f.tile r).root.comp (f.cutoffPlacedTile a n U w r depth selected)

noncomputable def cutoffTileChild (n : Nat) (U : f.Layer a n → Prop)
    (w : External J f.Letters) (r : R)
    (depth : TileStars.depth J f.Letters R Sigma.fst (.inr (w, r)) = n + 1)
    (selected : U ⟨.inr (w, r), depth⟩) (j : f.Child r) : IdealEmbedding P (f.cutoffOrder a n U) :=
  ((f.tile r).child j).comp (f.cutoffPlacedTile a n U w r depth selected)

theorem cutoffTileRoot_global (n : Nat) (U : f.Layer a n → Prop)
    (w : External J f.Letters) (r : R)
    (depth : TileStars.depth J f.Letters R Sigma.fst (.inr (w, r)) = n + 1)
    (selected : U ⟨.inr (w, r), depth⟩) (x : A) :
    (f.cutoffEmbedding a n U).toFun ((f.cutoffTileRoot a n U w r depth selected).toFun x) =
      (f.copy a w).toFun x :=
  (f.cutoffPlacedTile_global a n U w r depth selected _).trans (f.root_identification a w r x)

theorem cutoffTileChild_global (n : Nat) (U : f.Layer a n → Prop)
    (w : External J f.Letters) (r : R)
    (depth : TileStars.depth J f.Letters R Sigma.fst (.inr (w, r)) = n + 1)
    (selected : U ⟨.inr (w, r), depth⟩) (j : f.Child r) (x : A) :
    (f.cutoffEmbedding a n U).toFun ((f.cutoffTileChild a n U w r depth selected j).toFun x) =
      (f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun x :=
  (f.cutoffPlacedTile_global a n U w r depth selected _).trans (f.child_identification a w r j x)

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family



namespace PartitionPilot.Compression.RecursiveMaps.RootedGluing

universe u

@[instance_reducible] noncomputable def chosenWellOrder (I : Type u) : LinearOrder I :=
  Classical.choose (exists_wellFoundedLT I)

theorem chosenWellOrder_wf (I : Type u) :
    letI := chosenWellOrder I
    WellFoundedLT I := Classical.choose_spec (exists_wellFoundedLT I)

namespace Scheme
variable {V : Type u} (d : Scheme V)

noncomputable def layerBefore (n : Nat) (v w : (d.stages n).Layer) : Prop :=
  letI := chosenWellOrder ((d.stages n).Layer)
  w < v

theorem layerBefore_irrefl (n : Nat) (v : (d.stages n).Layer) : ¬ d.layerBefore n v v := by
  let := chosenWellOrder ((d.stages n).Layer)
  exact lt_irrefl v

theorem layerBefore_wf (n : Nat) : WellFounded (fun v w => d.layerBefore n w v) := by
  let := chosenWellOrder ((d.stages n).Layer)
  let := chosenWellOrder_wf ((d.stages n).Layer)
  exact wellFounded_lt

def Position := (n : Nat) ×' (d.stages n).Layer

noncomputable def positionBefore : d.Position → d.Position → Prop :=
  PSigma.Lex Nat.lt (fun n v w => d.layerBefore n w v)

theorem positionBefore_wf : WellFounded d.positionBefore :=
  WellFounded.psigma_lex Nat.lt_wfRel.wf d.layerBefore_wf

theorem parent_position_before (p q : d.Position) (parent : p.2.val = d.parent q.2.val) :
    d.positionBefore p q := by
  have hp := p.2.property
  have hq := q.2.property
  have step := d.parent_depth q.2.val ((d.stages q.1).layer_nonzero q.2)
  rw [← parent] at step
  have less : p.1 < q.1 := by omega
  exact @PSigma.Lex.left Nat (fun n => (d.stages n).Layer) Nat.lt
    (fun n v w => d.layerBefore n w v) p.1 p.2 q.1 q.2 less

noncomputable def orderedAttachment (n : Nat) (v : (d.stages n).Layer) :
    MeetIso ((d.stages n).batch.stepInput (d.layerBefore n v) v).order
      ((d.stages n).batch.cutoffOrder
        (PrincipalBatch.Family.addComponent (d.layerBefore n v) v)) :=
  (d.stages n).batch.stepIso (d.layerBefore n v) v (d.layerBefore_irrefl n v)

noncomputable def orderedCutoffEmbedding (n : Nat) (v : (d.stages n).Layer) :
    IdealEmbedding (d.partialOrder n (d.layerBefore n v)) d.gluedOrder :=
  d.partialEmbedding n (d.layerBefore n v)

theorem ordered_limit (n : Nat) (v : (d.stages n).Layer)
    (earlier : ∃ s, d.layerBefore n v s)
    (limit : ∀ i, d.layerBefore n v i → ∃ s, d.layerBefore n s i ∧ d.layerBefore n v s)
    (x : (d.stages n).batch.Node) :
    (d.stages n).batch.Present (d.layerBefore n v) x ↔
      ∃ s, d.layerBefore n v s ∧ (d.stages n).batch.Present (d.layerBefore n s) x := by
  let := chosenWellOrder ((d.stages n).Layer)
  exact (d.stages n).batch.before_limit v earlier limit x

theorem ordered_layer_cover (n : Nat) (x : (d.stages n).batch.Node) :
    (d.stages n).batch.Present (fun _ => False) x ∨
      ∃ v, (d.stages n).batch.Present
        (PrincipalBatch.Family.addComponent (d.layerBefore n v) v) x := by
  cases x with
  | inl x => exact Or.inl True.intro
  | inr x => exact Or.inr ⟨x.1, Or.inr rfl⟩

theorem ordered_new_vertex_meet (n : Nat) (v : (d.stages n).Layer)
    (x : ((d.stages n).batch.glue v).Fresh) (y : d.Partial n (d.layerBefore n v)) :
    d.gluedOrder.meet ((d.vertex v.val).toFun x.val)
      ((d.orderedCutoffEmbedding n v).toFun y) =
      d.gluedOrder.meet
        ((d.vertex (d.parent v.val)).toFun
          ((d.link v.val ((d.stages n).layer_nonzero v)).toFun
            (Attachment.cut (d.order v.val) (d.childAnchor v.val ((d.stages n).layer_nonzero v))
              x.val)).val)
        ((d.orderedCutoffEmbedding n v).toFun y) :=
  d.partial_new_vertex_meet n (d.layerBefore n v) v (d.layerBefore_irrefl n v) x y

end Scheme

end PartitionPilot.Compression.RecursiveMaps.RootedGluing

end

end OAI
