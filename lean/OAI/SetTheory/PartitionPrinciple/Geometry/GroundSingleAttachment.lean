import OAI.SetTheory.PartitionPrinciple.Definability.PairPushFilterFamilies
import OAI.SetTheory.PartitionPrinciple.Geometry.SeparationTileCodes

namespace OAI


namespace PartitionPilot.Forcing

universe u

structure SingleAttachmentInputs (P Q rP rQ μP μQ ell F a e : ZFSet.{u}) : Prop where
  oldOrder : MeetOrderCode P rP μP
  templateOrder : MeetOrderCode Q rQ μQ
  anchor_mem : a ∈ Q
  base_function : ZFSet.IsFunc (attachmentIdeal Q rQ a) P ell
  base_order : ∀ x y x' y', ZFSet.pair x x' ∈ ell → ZFSet.pair y y' ∈ ell →
    (ZFSet.pair x' y' ∈ rP ↔ ZFSet.pair x y ∈ rQ)
  base_meet : ∀ x y z x' y' z', ZFSet.pair (ZFSet.pair x y) z ∈ μQ →
    ZFSet.pair x x' ∈ ell → ZFSet.pair y y' ∈ ell → ZFSet.pair z z' ∈ ell →
      ZFSet.pair (ZFSet.pair x' y') z' ∈ μP
  filter : MeetFilterCode P rP μP F
  separator_mem : e ∈ P
  base_le_separator : ∀ b, ZFSet.pair a b ∈ ell → ZFSet.pair b e ∈ rP
  separator_not_le_base : ∀ b, ZFSet.pair a b ∈ ell → ZFSet.pair e b ∉ rP
  separator_le_upper : ∀ y ∈ F, ZFSet.pair e y ∈ rP

namespace SingleAttachmentInputs

variable {P Q rP rQ μP μQ ell F a e : ZFSet.{u}}
variable (d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e)

abbrev Base := {q : {q : ZFSet.{u} // q ∈ Q} //
  d.templateOrder.toMeetOrder.le q ⟨a, d.anchor_mem⟩}

theorem base_mem (q : d.Base) : q.val.val ∈ attachmentIdeal Q rQ a :=
  (mem_attachmentIdeal Q rQ a q.val.val).2 ⟨q.val.property, q.property⟩

noncomputable def baseMap (q : d.Base) : {p : ZFSet.{u} // p ∈ P} :=
  ⟨(d.base_function.2 q.val.val (d.base_mem q)).choose,
    (ZFSet.pair_mem_prod.1 (d.base_function.1
      (d.base_function.2 q.val.val (d.base_mem q)).choose_spec.1)).2⟩

theorem baseMap_entry (q : d.Base) : ZFSet.pair q.val.val (d.baseMap q).val ∈ ell :=
  (d.base_function.2 q.val.val (d.base_mem q)).choose_spec.1

noncomputable def baseEmbedding :
    MeetEmbedding (Attachment.idealOrder d.templateOrder.toMeetOrder ⟨a, d.anchor_mem⟩)
      d.oldOrder.toMeetOrder where
  toFun := d.baseMap
  le_iff x y := d.base_order _ _ _ _ (d.baseMap_entry x) (d.baseMap_entry y)
  map_meet x y := by
    apply Subtype.ext
    have entry := d.base_meet _ _ _ _ _ _
      (d.templateOrder.toMeetOrder_meet_entry x.val y.val)
      (d.baseMap_entry x) (d.baseMap_entry y)
      (d.baseMap_entry ((Attachment.idealOrder d.templateOrder.toMeetOrder
        ⟨a, d.anchor_mem⟩).meet x y))
    obtain ⟨z, _, unique⟩ := d.oldOrder.operation.2
      (ZFSet.pair (d.baseMap x).val (d.baseMap y).val)
      (ZFSet.pair_mem_prod.2 ⟨(d.baseMap x).property, (d.baseMap y).property⟩)
    exact (unique _ entry).trans
      (unique _ (d.oldOrder.toMeetOrder_meet_entry (d.baseMap x) (d.baseMap y))).symm

noncomputable def templates : Attachment.Templates d.oldOrder.toMeetOrder Unit where
  Space _ := {q : ZFSet.{u} // q ∈ Q}
  order _ := d.templateOrder.toMeetOrder
  anchor _ := ⟨a, d.anchor_mem⟩
  embed _ := d.baseEmbedding
  upper _ x := x.val ∈ F
  upper_nonempty _ := by
    obtain ⟨x, hx⟩ := d.filter.nonempty
    exact ⟨⟨x, d.filter.subset hx⟩, hx⟩
  upper_up := by
    intro i x y hx lower
    exact d.filter.upward x.val hx y.val y.property lower
  upper_meet := by
    intro i x y hx hy
    exact d.filter.closed_meet x.val hx y.val hy _
      (d.oldOrder.toMeetOrder_meet_entry x y)
  separator _ := ⟨e, d.separator_mem⟩
  base_le_separator _ := d.base_le_separator _ (d.baseMap_entry _)
  separator_not_le_base _ := d.separator_not_le_base _ (d.baseMap_entry _)
  separator_le_upper _ _ hy := d.separator_le_upper _ hy

theorem shadow_entry (q : d.templates.Fresh) :
    ZFSet.pair q.2.val.val (d.templates.shadow q).val ∈
      attachmentShadowGraph Q P μQ ell a := by
  apply (pair_mem_attachmentShadowGraph Q P μQ ell a _ _).2
  refine ⟨q.2.val.property, (d.templates.shadow q).property,
    (d.templateOrder.toMeetOrder.meet q.2.val ⟨a, d.anchor_mem⟩).val,
    (d.templateOrder.toMeetOrder.meet q.2.val ⟨a, d.anchor_mem⟩).property,
    d.templateOrder.toMeetOrder_meet_entry _ _, ?_⟩
  exact d.baseMap_entry (Attachment.cut d.templateOrder.toMeetOrder ⟨a, d.anchor_mem⟩ q.2.val)

end SingleAttachmentInputs






structure AttachmentBatchInputs
    (P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}) : Prop where
  oldOrder : MeetOrderCode P rP μP
  spaces : FunctionGraphOn I Qs
  relations : FunctionGraphOn I rs
  meets : FunctionGraphOn I μs
  anchors : FunctionGraphOn I As
  embeddings : FunctionGraphOn I Es
  filters : FunctionGraphOn I Fs
  separators : FunctionGraphOn I Ss
  valid : ∀ i ∈ I, ∀ Q r μ a ell F e,
    ZFSet.pair i Q ∈ Qs → ZFSet.pair i r ∈ rs → ZFSet.pair i μ ∈ μs →
    ZFSet.pair i a ∈ As → ZFSet.pair i ell ∈ Es → ZFSet.pair i F ∈ Fs →
    ZFSet.pair i e ∈ Ss → SingleAttachmentInputs P Q rP r μP μ ell F a e

namespace AttachmentBatchInputs

variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

noncomputable abbrev space (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.spaces.value i
noncomputable abbrev rel (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.relations.value i
noncomputable abbrev meet (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.meets.value i
noncomputable abbrev anchor (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.anchors.value i
noncomputable abbrev embed (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.embeddings.value i
noncomputable abbrev filter (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.filters.value i
noncomputable abbrev separator (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.separators.value i

theorem space_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.space i) ∈ Qs :=
  d.spaces.value_entry i

theorem rel_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.rel i) ∈ rs :=
  d.relations.value_entry i

theorem meet_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.meet i) ∈ μs :=
  d.meets.value_entry i

theorem anchor_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.anchor i) ∈ As :=
  d.anchors.value_entry i

theorem embed_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.embed i) ∈ Es :=
  d.embeddings.value_entry i

theorem filter_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.filter i) ∈ Fs :=
  d.filters.value_entry i

theorem separator_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.separator i) ∈ Ss :=
  d.separators.value_entry i

theorem fiber (i : {i : ZFSet.{u} // i ∈ I}) :
    SingleAttachmentInputs P (d.space i) rP (d.rel i) μP (d.meet i)
      (d.embed i) (d.filter i) (d.anchor i) (d.separator i) :=
  d.valid i.val i.property _ _ _ _ _ _ _ (d.space_entry i) (d.rel_entry i)
    (d.meet_entry i) (d.anchor_entry i) (d.embed_entry i) (d.filter_entry i) (d.separator_entry i)

noncomputable def templates :
    Attachment.Templates d.oldOrder.toMeetOrder {i : ZFSet.{u} // i ∈ I} where
  Space i := {q : ZFSet.{u} // q ∈ d.space i}
  order i := (d.fiber i).templateOrder.toMeetOrder
  anchor i := ⟨d.anchor i, (d.fiber i).anchor_mem⟩
  embed i := (d.fiber i).baseEmbedding
  upper i x := x.val ∈ d.filter i
  upper_nonempty i := by
    obtain ⟨x, hx⟩ := (d.fiber i).filter.nonempty
    exact ⟨⟨x, (d.fiber i).filter.subset hx⟩, hx⟩
  upper_up := by
    intro i x y hx lower
    exact (d.fiber i).filter.upward x.val hx y.val y.property lower
  upper_meet := by
    intro i x y hx hy
    exact (d.fiber i).filter.closed_meet x.val hx y.val hy _
      (d.oldOrder.toMeetOrder_meet_entry x y)
  separator i := ⟨d.separator i, (d.fiber i).separator_mem⟩
  base_le_separator i := (d.fiber i).base_le_separator _ ((d.fiber i).baseMap_entry _)
  separator_not_le_base i := (d.fiber i).separator_not_le_base _ ((d.fiber i).baseMap_entry _)
  separator_le_upper i _ hy := (d.fiber i).separator_le_upper _ hy

end AttachmentBatchInputs

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.SingleAttachmentInputs

universe u
variable {P Q rP rQ μP μQ ell F a e : ZFSet.{u}}
variable (d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e)

abbrev Nodes := {p : ZFSet.{u} // p ∈ P} ⊕ d.templates.Fresh

def encode : d.Nodes → ZFSet.{u}
  | .inl p => p.val
  | .inr q => ZFSet.pair P q.2.val.val

noncomputable abbrev carrier (_d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e) := taggedExtension P (freshPart Q rQ a)
noncomputable abbrev order (_d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e) := singleAttachmentOrder P (freshPart Q rQ a) rP rQ
  (attachmentShadowGraph Q P μQ ell a) F
noncomputable abbrev meetGraph := canonicalMeetGraph d.carrier d.order

theorem fresh_mem (q : d.templates.Fresh) : q.2.val.val ∈ freshPart Q rQ a :=
  (mem_freshPart Q rQ a _).2 ⟨q.2.val.property, q.2.property⟩

theorem encode_mem (x : d.Nodes) : d.encode x ∈ d.carrier := by
  cases x with
  | inl p => exact old_mem_taggedExtension p.property
  | inr q => exact pair_mem_taggedExtension.2 (d.fresh_mem q)

theorem encode_injective : Function.Injective d.encode := by
  intro x y eq
  cases x with
  | inl p =>
    cases y with
    | inl s => exact congrArg Sum.inl (Subtype.ext eq)
    | inr q =>
      change p.val = ZFSet.pair P q.2.val.val at eq
      exact False.elim (pair_tag_not_mem P q.2.val.val (eq ▸ p.property))
  | inr q =>
    cases y with
    | inl p =>
      change ZFSet.pair P q.2.val.val = p.val at eq
      exact False.elim (pair_tag_not_mem P q.2.val.val (eq.symm ▸ p.property))
    | inr t =>
      apply congrArg Sum.inr
      rcases q with ⟨i, q⟩
      rcases t with ⟨j, t⟩
      cases i
      cases j
      exact congrArg (Sigma.mk ()) (Subtype.ext (Subtype.ext (ZFSet.pair_inj.1 eq).2))

theorem encode_surjective : ∀ z ∈ d.carrier, ∃ x : d.Nodes, d.encode x = z := by
  intro z hz
  rcases mem_taggedExtension.1 hz with old | ⟨q, hq, eq⟩
  · exact ⟨.inl ⟨z, old⟩, rfl⟩
  · have fresh := (mem_freshPart Q rQ a q).1 hq
    exact ⟨.inr ⟨(), ⟨⟨q, fresh.1⟩, fresh.2⟩⟩, eq.symm⟩

theorem fresh_lower_iff (q t : d.templates.Fresh) :
    d.templates.extension.le (.inr q) (.inr t) ↔
      ZFSet.pair q.2.val.val t.2.val.val ∈ rQ := by
  change Attachment.FreshLe d.templates.data q t ↔ _
  rw [Attachment.fresh_same_component d.templates.data (Subsingleton.elim _ _)]
  rcases q with ⟨i, q⟩
  rcases t with ⟨j, t⟩
  cases i
  cases j
  constructor
  · rintro ⟨h, lower⟩
    cases h
    exact lower
  · intro lower
    exact ⟨rfl, lower⟩

theorem le_encode (x y : d.Nodes) :
    ZFSet.pair (d.encode x) (d.encode y) ∈ d.order ↔ d.templates.extension.le x y := by
  rw [pair_mem_singleAttachmentOrder]
  have bounded : d.encode x ∈ d.carrier ∧ d.encode y ∈ d.carrier :=
    ⟨d.encode_mem x, d.encode_mem y⟩
  simp only [bounded.1, bounded.2, true_and]
  cases x with
  | inl p =>
    cases y with
    | inl s =>
      change singleAttachmentLe P _ rP rQ _ F p.val s.val ↔ ZFSet.pair p.val s.val ∈ rP
      constructor
      · rintro (h | h | h | h)
        · exact h.2.2
        · obtain ⟨_, q, _, t, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ s.property))
        · obtain ⟨⟨q, _, eq⟩, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ p.property))
        · obtain ⟨q, _, t, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ p.property))
      · intro lower
        exact Or.inl ⟨p.property, s.property, lower⟩
    | inr q =>
      change singleAttachmentLe P _ rP rQ _ F p.val (ZFSet.pair P q.2.val.val) ↔
        ZFSet.pair p.val (d.templates.shadow q).val ∈ rP
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P q.2.val.val h.2.1)
        · obtain ⟨_, t, _, s, _, eq, image, lower⟩ := h
          have same : q.2.val.val = t := (ZFSet.pair_inj.1 eq).2
          subst t
          have graph := attachmentShadowGraph_function d.templateOrder d.anchor_mem d.base_function
          obtain ⟨v, _, unique⟩ := graph.2 q.2.val.val q.2.val.property
          have sameValue := (unique s image).trans (unique _ (d.shadow_entry q)).symm
          exact sameValue ▸ lower
        · obtain ⟨⟨t, _, eq⟩, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
        · obtain ⟨t, _, s, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
      · intro lower
        exact Or.inr (Or.inl ⟨p.property, q.2.val.val, d.fresh_mem q,
          (d.templates.shadow q).val, (d.templates.shadow q).property, rfl,
          d.shadow_entry q, lower⟩)
  | inr q =>
    cases y with
    | inl p =>
      change singleAttachmentLe P _ rP rQ _ F (ZFSet.pair P q.2.val.val) p.val ↔ p.val ∈ F
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P q.2.val.val h.1)
        · exact False.elim (pair_tag_not_mem P q.2.val.val h.1)
        · exact h.2
        · obtain ⟨s, _, t, _, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
      · intro upper
        exact Or.inr (Or.inr (Or.inl ⟨⟨q.2.val.val, d.fresh_mem q, rfl⟩, upper⟩))
    | inr t =>
      rw [d.fresh_lower_iff]
      change singleAttachmentLe P _ rP rQ _ F
        (ZFSet.pair P q.2.val.val) (ZFSet.pair P t.2.val.val) ↔
          ZFSet.pair q.2.val.val t.2.val.val ∈ rQ
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P q.2.val.val h.1)
        · exact False.elim (pair_tag_not_mem P q.2.val.val h.1)
        · exact False.elim (pair_tag_not_mem P t.2.val.val (d.filter.subset h.2))
        · obtain ⟨s, _, v, _, eqQ, eqT, lower⟩ := h
          have sameQ := (ZFSet.pair_inj.1 eqQ).2
          have sameT := (ZFSet.pair_inj.1 eqT).2
          exact sameQ.symm ▸ sameT.symm ▸ lower
      · intro lower
        exact Or.inr (Or.inr (Or.inr ⟨q.2.val.val, d.fresh_mem q,
          t.2.val.val, d.fresh_mem t, rfl, rfl, lower⟩))

theorem partialOrder : PartialOrderCode d.carrier d.order where
  relation := singleAttachmentOrder_shape P _ rP rQ _ F
  refl z hz := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    exact (d.le_encode x x).2 (d.templates.extension.refl x)
  antisymm z hz w hw zw wz := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    obtain ⟨y, rfl⟩ := d.encode_surjective w hw
    exact congrArg d.encode (d.templates.extension.antisymm
      ((d.le_encode x y).1 zw) ((d.le_encode y x).1 wz))
  trans z hz w hw v hv zw wv := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    obtain ⟨y, rfl⟩ := d.encode_surjective w hw
    obtain ⟨t, rfl⟩ := d.encode_surjective v hv
    exact (d.le_encode x t).2 (d.templates.extension.trans
      ((d.le_encode x y).1 zw) ((d.le_encode y t).1 wv))

theorem encoded_meet_glb (x y : d.Nodes) :
    GreatestLowerBoundCode d.carrier d.order (d.encode x) (d.encode y)
      (d.encode (d.templates.extension.meet x y)) := by
  refine ⟨(d.le_encode _ _).2 (d.templates.extension.meet_le_left x y),
    (d.le_encode _ _).2 (d.templates.extension.meet_le_right x y), ?_⟩
  intro w hw wx wy
  obtain ⟨z, rfl⟩ := d.encode_surjective w hw
  exact (d.le_encode _ _).2 (d.templates.extension.le_meet
    ((d.le_encode _ _).1 wx) ((d.le_encode _ _).1 wy))

theorem meetOrder : MeetOrderCode d.carrier d.order d.meetGraph := by
  apply canonicalMeetGraph_code d.partialOrder
  intro x hx y hy
  obtain ⟨s, rfl⟩ := d.encode_surjective x hx
  obtain ⟨t, rfl⟩ := d.encode_surjective y hy
  exact ⟨d.encode (d.templates.extension.meet s t), d.encode_mem _, d.encoded_meet_glb s t⟩

theorem encoded_meet_entry (x y : d.Nodes) :
    ZFSet.pair (ZFSet.pair (d.encode x) (d.encode y))
      (d.encode (d.templates.extension.meet x y)) ∈ d.meetGraph :=
  (pair_mem_canonicalMeetGraph _ _ _ _ _).2
    ⟨d.encode_mem x, d.encode_mem y, d.encode_mem _, d.encoded_meet_glb x y⟩

end PartitionPilot.Forcing.SingleAttachmentInputs



namespace PartitionPilot.Forcing.SingleAttachmentInputs

universe u

theorem pushforward
    {P Q L rP rQ rL μP μQ μL ell F a e S e' : ZFSet.{u}}
    (d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e)
    (target : MeetOrderCode L rL μL)
    (embedding : MeetEmbeddingCode P L rP rL μP μL S)
    (separator : ZFSet.pair e e' ∈ S) :
    SingleAttachmentInputs L Q rL rQ μL μQ
      (relationCompose (attachmentIdeal Q rQ a) P L ell S)
      (pushFilterCode L rL S F) a e' where
  oldOrder := target
  templateOrder := d.templateOrder
  anchor_mem := d.anchor_mem
  base_function := relationCompose_function_of_subset d.base_function embedding.injection.function
    (fun _ hx => hx)
  base_order := by
    intro x y x' y' first second
    obtain ⟨_, _, u, _, xu, ux'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨_, _, v, _, yv, vy'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
    exact (embedding.order_iff d.oldOrder target ux' vy').trans (d.base_order x y u v xu yv)
  base_meet := by
    intro x y z x' y' z' meetXYZ first second third
    obtain ⟨_, _, u, _, xu, ux'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨_, _, v, _, yv, vy'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
    obtain ⟨_, _, w, _, zw, wz'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 third
    exact embedding.map_meet u v w x' y' z'
      (d.base_meet x y z u v w meetXYZ xu yv zw) ux' vy' wz'
  filter := meetFilter_pushFilter d.oldOrder target embedding d.filter
  separator_mem := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 separator)).2
  base_le_separator := by
    intro b entry
    obtain ⟨_, _, c, _, base, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact embedding.monotone c e b e' (d.base_le_separator c base) image separator
  separator_not_le_base := by
    intro b entry lower
    obtain ⟨_, _, c, _, base, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact d.separator_not_le_base c base ((embedding.order_iff d.oldOrder target separator image).1 lower)
  separator_le_upper := by
    intro y positive
    exact pushFilter_lower_bound target embedding d.separator_le_upper separator positive

end PartitionPilot.Forcing.SingleAttachmentInputs



namespace PartitionPilot.Forcing.SingleAttachmentInputs

universe u
variable {P Q rP rQ μP μQ ell F a e : ZFSet.{u}}
variable (d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e)
include d

theorem base_injection : InjectionCode (attachmentIdeal Q rQ a) P ell := by
  refine ⟨d.base_function, ?_⟩
  intro x y z hx hy
  have first := ZFSet.pair_mem_prod.1 (d.base_function.1 hx)
  have second := ZFSet.pair_mem_prod.1 (d.base_function.1 hy)
  have refl := d.oldOrder.order.refl z first.2
  exact d.templateOrder.order.antisymm x ((mem_attachmentIdeal Q rQ a x).1 first.1).1
    y ((mem_attachmentIdeal Q rQ a y).1 second.1).1
    ((d.base_order x y z z hx hy).1 refl) ((d.base_order y x z z hy hx).1 refl)

theorem template_graph_entry (q : {q : ZFSet.{u} // q ∈ Q}) :
    ZFSet.pair q.val (d.encode (d.templates.represent () q)) ∈
      attachmentTemplateEmbeddingGraph P Q rQ ell a := by
  classical
  by_cases below : d.templateOrder.toMeetOrder.le q ⟨a, d.anchor_mem⟩
  · rw [d.templates.represent_old () q below]
    apply (attachmentTemplateEmbeddingGraph_of_ideal
      ((mem_attachmentIdeal Q rQ a q.val).2 ⟨q.property, below⟩)).2
    exact d.baseMap_entry ⟨q, below⟩
  · rw [d.templates.represent_new () q below]
    exact (attachmentTemplateEmbeddingGraph_of_fresh d.base_function
      ((mem_freshPart Q rQ a q.val).2 ⟨q.property, below⟩)).2 rfl

theorem template_graph_entry_iff (q : {q : ZFSet.{u} // q ∈ Q}) (y : ZFSet.{u}) :
    ZFSet.pair q.val y ∈ attachmentTemplateEmbeddingGraph P Q rQ ell a ↔
      y = d.encode (d.templates.represent () q) := by
  constructor
  · intro entry
    obtain ⟨w, _, unique⟩ := (attachmentTemplateEmbeddingGraph_isFunc d.base_function).2 q.val q.property
    exact (unique y entry).trans (unique _ (d.template_graph_entry q)).symm
  · intro eq
    exact eq.symm ▸ d.template_graph_entry q

theorem encoded_embedding_order_iff {A r μ graph : ZFSet.{u}}
    (source : MeetOrderCode A r μ)
    (embedding : MeetEmbedding source.toMeetOrder d.templates.extension)
    (injection : InjectionCode A d.carrier graph)
    (entries : ∀ x : {x : ZFSet.{u} // x ∈ A},
      ZFSet.pair x.val (d.encode (embedding.toFun x)) ∈ graph)
    {x y x' y' : ZFSet.{u}} (hx : ZFSet.pair x x' ∈ graph) (hy : ZFSet.pair y y' ∈ graph) :
    ZFSet.pair x' y' ∈ d.order ↔ ZFSet.pair x y ∈ r := by
  have hxA := (ZFSet.pair_mem_prod.1 (injection.function.1 hx)).1
  have hyA := (ZFSet.pair_mem_prod.1 (injection.function.1 hy)).1
  obtain ⟨w, _, uniqueX⟩ := injection.function.2 x hxA
  obtain ⟨v, _, uniqueY⟩ := injection.function.2 y hyA
  have eqX := (uniqueX x' hx).trans (uniqueX _ (entries ⟨x, hxA⟩)).symm
  have eqY := (uniqueY y' hy).trans (uniqueY _ (entries ⟨y, hyA⟩)).symm
  rw [eqX, eqY, d.le_encode]
  exact embedding.le_iff ⟨x, hxA⟩ ⟨y, hyA⟩

theorem encoded_embedding_code {A r μ graph : ZFSet.{u}}
    (source : MeetOrderCode A r μ)
    (embedding : MeetEmbedding source.toMeetOrder d.templates.extension)
    (injection : InjectionCode A d.carrier graph)
    (entries : ∀ x : {x : ZFSet.{u} // x ∈ A},
      ZFSet.pair x.val (d.encode (embedding.toFun x)) ∈ graph) :
    MeetEmbeddingCode A d.carrier r d.order μ d.meetGraph graph := by
  refine ⟨injection, ?_, ?_⟩
  · intro x y x' y' lower hx hy
    exact (d.encoded_embedding_order_iff source embedding injection entries hx hy).2 lower
  · intro x y z x' y' z' meet hx hy hz
    have hxA := (ZFSet.pair_mem_prod.1 (injection.function.1 hx)).1
    have hyA := (ZFSet.pair_mem_prod.1 (injection.function.1 hy)).1
    have hzA := (ZFSet.pair_mem_prod.1 (injection.function.1 hz)).1
    let X : {x : ZFSet.{u} // x ∈ A} := ⟨x, hxA⟩
    let Y : {y : ZFSet.{u} // y ∈ A} := ⟨y, hyA⟩
    let Z : {z : ZFSet.{u} // z ∈ A} := ⟨z, hzA⟩
    have image_eq (t : {t : ZFSet.{u} // t ∈ A}) (v : ZFSet.{u})
        (entry : ZFSet.pair t.val v ∈ graph) : v = d.encode (embedding.toFun t) := by
      obtain ⟨w, _, unique⟩ := injection.function.2 t.val t.property
      exact (unique v entry).trans (unique _ (entries t)).symm
    have meet_eq : source.toMeetOrder.meet X Y = Z := by
      apply Subtype.ext
      obtain ⟨w, _, unique⟩ := source.operation.2 (ZFSet.pair x y)
        (ZFSet.pair_mem_prod.2 ⟨hxA, hyA⟩)
      exact (unique _ (source.toMeetOrder_meet_entry X Y)).trans (unique z meet).symm
    have mapped : embedding.toFun Z =
        d.templates.extension.meet (embedding.toFun X) (embedding.toFun Y) := by
      rw [← meet_eq]
      exact embedding.map_meet X Y
    rw [image_eq X x' hx, image_eq Y y' hy, image_eq Z z' hz, mapped]
    exact d.encoded_meet_entry (embedding.toFun X) (embedding.toFun Y)

theorem old_embedding_code :
    MeetEmbeddingCode P d.carrier rP d.order μP d.meetGraph (attachmentOldEmbeddingGraph P) := by
  apply d.encoded_embedding_code d.oldOrder d.templates.oldEmbedding
    (attachmentOldEmbeddingGraph_injection P (freshPart Q rQ a))
  intro p
  exact (pair_mem_attachmentOldEmbeddingGraph P p.val p.val).2 ⟨p.property, rfl⟩

theorem template_embedding_code :
    MeetEmbeddingCode Q d.carrier rQ d.order μQ d.meetGraph
      (attachmentTemplateEmbeddingGraph P Q rQ ell a) :=
  d.encoded_embedding_code d.templateOrder (d.templates.templateEmbedding ())
    (attachmentTemplateEmbeddingGraph_injection d.base_injection) d.template_graph_entry

theorem old_order_iff {x y x' y' : ZFSet.{u}}
    (hx : ZFSet.pair x x' ∈ attachmentOldEmbeddingGraph P)
    (hy : ZFSet.pair y y' ∈ attachmentOldEmbeddingGraph P) :
    ZFSet.pair x' y' ∈ d.order ↔ ZFSet.pair x y ∈ rP := by
  apply d.encoded_embedding_order_iff d.oldOrder d.templates.oldEmbedding
    (attachmentOldEmbeddingGraph_injection P (freshPart Q rQ a))
    (fun p => (pair_mem_attachmentOldEmbeddingGraph P p.val p.val).2 ⟨p.property, rfl⟩) hx hy

theorem template_order_iff {x y x' y' : ZFSet.{u}}
    (hx : ZFSet.pair x x' ∈ attachmentTemplateEmbeddingGraph P Q rQ ell a)
    (hy : ZFSet.pair y y' ∈ attachmentTemplateEmbeddingGraph P Q rQ ell a) :
    ZFSet.pair x' y' ∈ d.order ↔ ZFSet.pair x y ∈ rQ :=
  d.encoded_embedding_order_iff d.templateOrder (d.templates.templateEmbedding ())
    (attachmentTemplateEmbeddingGraph_injection d.base_injection) d.template_graph_entry hx hy

theorem template_old_agreement {q p : ZFSet.{u}} (entry : ZFSet.pair q p ∈ ell) :
    ZFSet.pair q p ∈ attachmentTemplateEmbeddingGraph P Q rQ ell a ∧
      ZFSet.pair p p ∈ attachmentOldEmbeddingGraph P := by
  have shape := ZFSet.pair_mem_prod.1 (d.base_function.1 entry)
  exact ⟨(attachmentTemplateEmbeddingGraph_of_ideal shape.1).2 entry,
    (pair_mem_attachmentOldEmbeddingGraph P p p).2 ⟨shape.2, rfl⟩⟩

theorem template_shadow_entry (q : {q : ZFSet.{u} // q ∈ Q}) :
    ZFSet.pair q.val
      (d.baseMap (Attachment.cut d.templateOrder.toMeetOrder ⟨a, d.anchor_mem⟩ q)).val ∈
        attachmentShadowGraph Q P μQ ell a := by
  apply (pair_mem_attachmentShadowGraph Q P μQ ell a _ _).2
  refine ⟨q.property, (d.baseMap _).property,
    (d.templateOrder.toMeetOrder.meet q ⟨a, d.anchor_mem⟩).val,
    (d.templateOrder.toMeetOrder.meet q ⟨a, d.anchor_mem⟩).property,
    d.templateOrder.toMeetOrder_meet_entry _ _, ?_⟩
  exact d.baseMap_entry (Attachment.cut d.templateOrder.toMeetOrder ⟨a, d.anchor_mem⟩ q)

theorem old_below_template_iff {q q' s : ZFSet.{u}}
    (templateEntry : ZFSet.pair q q' ∈ attachmentTemplateEmbeddingGraph P Q rQ ell a)
    (shadowEntry : ZFSet.pair q s ∈ attachmentShadowGraph Q P μQ ell a) :
    ∀ p ∈ P, ZFSet.pair p q' ∈ d.order ↔ ZFSet.pair p s ∈ rP := by
  intro p hp
  have qQ := (ZFSet.pair_mem_prod.1
    ((attachmentTemplateEmbeddingGraph_isFunc d.base_function).1 templateEntry)).1
  let qRaw : {q : ZFSet.{u} // q ∈ Q} := ⟨q, qQ⟩
  have encoded := (d.template_graph_entry_iff qRaw q').1 templateEntry
  have shadowFunction := attachmentShadowGraph_function d.templateOrder d.anchor_mem d.base_function
  obtain ⟨v, _, unique⟩ := shadowFunction.2 q qQ
  have shadow := (unique s shadowEntry).trans (unique _ (d.template_shadow_entry qRaw)).symm
  rw [encoded, shadow]
  change ZFSet.pair (d.encode (.inl ⟨p, hp⟩)) (d.encode (d.templates.represent () qRaw)) ∈ d.order ↔ _
  rw [d.le_encode]
  exact d.templates.old_below_represent () qRaw ⟨p, hp⟩

end PartitionPilot.Forcing.SingleAttachmentInputs



namespace PartitionPilot.Forcing.SingleAttachmentInputs

universe u
variable {P Q rP rQ μP μQ ell F a e : ZFSet.{u}}
variable (d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e)

theorem fresh_old_upper_iff {q p : ZFSet.{u}}
    (hq : q ∈ freshPart Q rQ a) (hp : p ∈ P) :
    ZFSet.pair (ZFSet.pair P q) p ∈ d.order ↔ p ∈ F := by
  have qParts := (mem_freshPart Q rQ a q).1 hq
  exact d.le_encode (.inr ⟨(), ⟨⟨q, qParts.1⟩, qParts.2⟩⟩) (.inl ⟨p, hp⟩)

theorem fresh_old_meet_code {q p s v : ZFSet.{u}}
    (hq : q ∈ freshPart Q rQ a) (hp : p ∈ P)
    (shadow : ZFSet.pair q s ∈ attachmentShadowGraph Q P μQ ell a)
    (oldMeet : ZFSet.pair (ZFSet.pair s p) v ∈ μP)
    (notAbove : ZFSet.pair (ZFSet.pair P q) p ∉ d.order) :
    ZFSet.pair (ZFSet.pair (ZFSet.pair P q) p) v ∈ d.meetGraph := by
  have qParts := (mem_freshPart Q rQ a q).1 hq
  let x : d.templates.Fresh := ⟨(), ⟨⟨q, qParts.1⟩, qParts.2⟩⟩
  let y : {p : ZFSet.{u} // p ∈ P} := ⟨p, hp⟩
  have graph := attachmentShadowGraph_function d.templateOrder d.anchor_mem d.base_function
  obtain ⟨w, _, unique⟩ := graph.2 q qParts.1
  have sameShadow : s = (d.templates.shadow x).val :=
    (unique s shadow).trans (unique _ (d.shadow_entry x)).symm
  have decoded := d.oldOrder.toMeetOrder_meet_entry (d.templates.shadow x) y
  obtain ⟨m, _, uniqueMeet⟩ := d.oldOrder.operation.2
    (ZFSet.pair (d.templates.shadow x).val p)
    (ZFSet.pair_mem_prod.2 ⟨(d.templates.shadow x).property, hp⟩)
  have sameMeet : v = (d.oldOrder.toMeetOrder.meet (d.templates.shadow x) y).val :=
    (uniqueMeet v (sameShadow ▸ oldMeet)).trans (uniqueMeet _ decoded).symm
  have notUpper : ¬ d.templates.upper x.1 y := by
    intro upper
    exact notAbove ((d.fresh_old_upper_iff hq hp).2 upper)
  have eq := d.templates.shadow_meet_eq x y notUpper
  have result := d.encoded_meet_entry (.inr x) (.inl y)
  rw [eq] at result
  exact sameMeet.symm ▸ result

theorem greatest_preserved {T : ZFSet.{u}} (hT : T ∈ P)
    (greatest : ∀ p ∈ P, ZFSet.pair p T ∈ rP) :
    ∀ z ∈ d.carrier, ZFSet.pair z T ∈ d.order := by
  intro z hz
  obtain ⟨x, rfl⟩ := d.encode_surjective z hz
  exact (d.le_encode x (.inl ⟨T, hT⟩)).2
    (d.templates.greatest_preserved ⟨T, hT⟩ (fun p => greatest p.val p.property) x)

theorem least_preserved {zero : ZFSet.{u}} (hzero : zero ∈ P)
    (least : ∀ p ∈ P, ZFSet.pair zero p ∈ rP) :
    ∀ z ∈ d.carrier, ZFSet.pair zero z ∈ d.order := by
  intro z hz
  obtain ⟨x, rfl⟩ := d.encode_surjective z hz
  exact (d.le_encode (.inl ⟨zero, hzero⟩) x).2
    (d.templates.least_preserved ⟨zero, hzero⟩ (fun p => least p.val p.property) x)

end PartitionPilot.Forcing.SingleAttachmentInputs



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem singleAttachment_ground_codes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P Q rP rQ μP μQ ell F a e : ZFSet.{u}}
    (d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e)
    (hP : P ∈ M.sets) (hQ : Q ∈ M.sets) (hrP : rP ∈ M.sets)
    (hrQ : rQ ∈ M.sets) (hμQ : μQ ∈ M.sets) (hell : ell ∈ M.sets)
    (hF : F ∈ M.sets) :
    d.carrier ∈ M.sets ∧ attachmentShadowGraph Q P μQ ell a ∈ M.sets ∧
      d.order ∈ M.sets ∧ d.meetGraph ∈ M.sets ∧
        attachmentOldEmbeddingGraph P ∈ M.sets ∧
          attachmentTemplateEmbeddingGraph P Q rQ ell a ∈ M.sets := by
  have ha := M.transitive hQ d.anchor_mem
  have hN := M.freshPart_mem separation hQ hrQ ha
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  have hs := M.attachmentShadowGraph_mem pairing unions powers separation hQ hP hμQ hell ha
  have hr := M.singleAttachmentOrder_mem pairing unions powers separation hP hN hrP hrQ hs hF
  exact ⟨hL, hs, hr, M.canonicalMeetGraph_mem pairing unions powers separation hL hr,
    M.attachmentOldEmbeddingGraph_mem pairing unions powers separation hP,
    M.attachmentTemplateEmbeddingGraph_mem pairing unions powers separation hP hQ hrQ hell ha⟩

theorem exists_singleAttachment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P Q rP rQ μP μQ ell F a e : ZFSet.{u}}
    (d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e)
    (hP : P ∈ M.sets) (hQ : Q ∈ M.sets) (hrP : rP ∈ M.sets)
    (hrQ : rQ ∈ M.sets) (hμQ : μQ ∈ M.sets) (hell : ell ∈ M.sets)
    (hF : F ∈ M.sets) :
    ∃ L ∈ M.sets, ∃ shadow ∈ M.sets, ∃ r ∈ M.sets, ∃ μ ∈ M.sets,
      ∃ oldMap ∈ M.sets, ∃ templateMap ∈ M.sets,
        L = taggedExtension P (freshPart Q rQ a) ∧
        shadow = attachmentShadowGraph Q P μQ ell a ∧
        r = singleAttachmentOrder P (freshPart Q rQ a) rP rQ shadow F ∧
        μ = canonicalMeetGraph L r ∧
        oldMap = attachmentOldEmbeddingGraph P ∧
        templateMap = attachmentTemplateEmbeddingGraph P Q rQ ell a ∧
        MeetOrderCode L r μ ∧
        ZFSet.IsFunc Q P shadow ∧
        MeetEmbeddingCode P L rP r μP μ oldMap ∧
        MeetEmbeddingCode Q L rQ r μQ μ templateMap ∧
        (∀ p ∈ P, ZFSet.pair p p ∈ oldMap) ∧
        (∀ q ∈ attachmentIdeal Q rQ a, ∀ p,
          ZFSet.pair q p ∈ templateMap ↔ ZFSet.pair q p ∈ ell) ∧
        (∀ q q' s, ZFSet.pair q q' ∈ templateMap → ZFSet.pair q s ∈ shadow →
          ∀ p ∈ P, ZFSet.pair p q' ∈ r ↔ ZFSet.pair p s ∈ rP) ∧
        (∀ q ∈ freshPart Q rQ a, ∀ p ∈ P, ∀ s v,
          ZFSet.pair q s ∈ shadow → ZFSet.pair (ZFSet.pair s p) v ∈ μP →
          ZFSet.pair (ZFSet.pair P q) p ∉ r →
          ZFSet.pair (ZFSet.pair (ZFSet.pair P q) p) v ∈ μ) := by
  obtain ⟨hL, hs, hr, hμ, hi, hj⟩ := M.singleAttachment_ground_codes
    pairing unions powers separation d hP hQ hrP hrQ hμQ hell hF
  exact ⟨d.carrier, hL, attachmentShadowGraph Q P μQ ell a, hs, d.order, hr,
    d.meetGraph, hμ, attachmentOldEmbeddingGraph P, hi,
    attachmentTemplateEmbeddingGraph P Q rQ ell a, hj,
    rfl, rfl, rfl, rfl, rfl, rfl, d.meetOrder,
    attachmentShadowGraph_function d.templateOrder d.anchor_mem d.base_function,
    d.old_embedding_code, d.template_embedding_code,
    fun p hp => (pair_mem_attachmentOldEmbeddingGraph P p p).2 ⟨hp, rfl⟩,
    (fun q hq p => attachmentTemplateEmbeddingGraph_of_ideal hq),
    (fun q q' s entry shadow => d.old_below_template_iff entry shadow),
    fun q hq p hp s v shadow oldMeet notAbove =>
      d.fresh_old_meet_code hq hp shadow oldMeet notAbove⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
