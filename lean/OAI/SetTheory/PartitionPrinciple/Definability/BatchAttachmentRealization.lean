import OAI.SetTheory.PartitionPrinciple.Definability.GroundBatchAttachmentGraphs

namespace OAI


namespace PartitionPilot.Forcing

section
universe u v w

structure CodedTemplateAttachment {J : Type v} {P r μ : ZFSet.{u}}
    (old : MeetOrderCode P r μ) (b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J)
    (N inside shadow upper : ZFSet.{u}) where
  freshCode : b.Fresh → ZFSet.{u}
  fresh_mem : ∀ q, freshCode q ∈ N
  fresh_injective : Function.Injective freshCode
  fresh_surjective : ∀ z ∈ N, ∃ q, freshCode q = z
  shadow_entry : ∀ q, ZFSet.pair (freshCode q) (b.shadow q).val ∈ shadow
  shadow_value : ∀ q s, ZFSet.pair (freshCode q) s ∈ shadow → s = (b.shadow q).val
  inside_iff : ∀ q t, ZFSet.pair (freshCode q) (freshCode t) ∈ inside ↔ b.Inside q t
  upper_iff : ∀ q p, ZFSet.pair (freshCode q) p.val ∈ upper ↔ b.upper q.1 p

namespace CodedTemplateAttachment
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

abbrev Nodes := {p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh

def encode : ({p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh) → ZFSet.{u}
  | .inl p => p.val
  | .inr q => ZFSet.pair P (d.freshCode q)

noncomputable abbrev carrier (_d : CodedTemplateAttachment old b N inside shadow upper) := taggedExtension P N
noncomputable abbrev order (_d : CodedTemplateAttachment old b N inside shadow upper) :=
  codedAttachmentOrder P N r inside shadow upper
noncomputable abbrev meetGraph := canonicalMeetGraph d.carrier d.order

theorem encode_mem (x : {p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh) : d.encode x ∈ d.carrier := by
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
      change p.val = ZFSet.pair P (d.freshCode q) at eq
      exact False.elim (pair_tag_not_mem P (d.freshCode q) (eq ▸ p.property))
  | inr q =>
    cases y with
    | inl p =>
      change ZFSet.pair P (d.freshCode q) = p.val at eq
      exact False.elim (pair_tag_not_mem P (d.freshCode q) (eq.symm ▸ p.property))
    | inr t => exact congrArg Sum.inr (d.fresh_injective (ZFSet.pair_inj.1 eq).2)

theorem encode_surjective : ∀ z ∈ d.carrier,
    ∃ x : {p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh, d.encode x = z := by
  intro z hz
  rcases mem_taggedExtension.1 hz with old | ⟨q, hq, eq⟩
  · exact ⟨.inl ⟨z, old⟩, rfl⟩
  · obtain ⟨t, rfl⟩ := d.fresh_surjective q hq
    exact ⟨.inr t, eq.symm⟩

theorem fresh_le_iff (q t : b.Fresh) :
    codedAttachmentFreshLe P inside shadow upper (d.freshCode q) (d.freshCode t) ↔
      b.extension.le (.inr q) (.inr t) := by
  change (_ ∨ _) ↔ (_ ∨ _)
  apply or_congr (d.inside_iff q t)
  constructor
  · rintro ⟨s, _, entry, above⟩
    have eq := d.shadow_value t s entry
    exact (d.upper_iff q (b.shadow t)).1 (eq ▸ above)
  · intro above
    exact ⟨(b.shadow t).val, (b.shadow t).property, d.shadow_entry t,
      (d.upper_iff q (b.shadow t)).2 above⟩

theorem le_encode (x y : ({p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh)) :
    ZFSet.pair (d.encode x) (d.encode y) ∈ d.order ↔ b.extension.le x y := by
  rw [pair_mem_codedAttachmentOrder]
  have bounded : d.encode x ∈ d.carrier ∧ d.encode y ∈ d.carrier :=
    ⟨d.encode_mem x, d.encode_mem y⟩
  simp only [bounded.1, bounded.2, true_and]
  cases x with
  | inl p =>
    cases y with
    | inl s =>
      change codedAttachmentLe P N r inside shadow upper p.val s.val ↔ ZFSet.pair p.val s.val ∈ r
      constructor
      · rintro (h | h | h | h)
        · exact h.2.2
        · obtain ⟨_, q, _, t, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ s.property))
        · obtain ⟨_, q, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ p.property))
        · obtain ⟨q, _, t, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ p.property))
      · intro lower
        exact Or.inl ⟨p.property, s.property, lower⟩
    | inr q =>
      change codedAttachmentLe P N r inside shadow upper p.val (ZFSet.pair P (d.freshCode q)) ↔
        ZFSet.pair p.val (b.shadow q).val ∈ r
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P (d.freshCode q) h.2.1)
        · obtain ⟨_, t, _, s, _, eq, image, lower⟩ := h
          have same : d.freshCode q = t := (ZFSet.pair_inj.1 eq).2
          subst t
          exact d.shadow_value q s image ▸ lower
        · obtain ⟨_, t, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
        · obtain ⟨t, _, s, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
      · intro lower
        exact Or.inr (Or.inl ⟨p.property, d.freshCode q, d.fresh_mem q,
          (b.shadow q).val, (b.shadow q).property, rfl,
          d.shadow_entry q, lower⟩)
  | inr q =>
    cases y with
    | inl p =>
      change codedAttachmentLe P N r inside shadow upper (ZFSet.pair P (d.freshCode q)) p.val ↔
        b.upper q.1 p
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P (d.freshCode q) h.1)
        · exact False.elim (pair_tag_not_mem P (d.freshCode q) h.1)
        · obtain ⟨_, t, _, eq, rel⟩ := h
          have same : d.freshCode q = t := (ZFSet.pair_inj.1 eq).2
          subst t
          exact (d.upper_iff q p).1 rel
        · obtain ⟨s, _, t, _, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
      · intro above
        exact Or.inr (Or.inr (Or.inl ⟨p.property, d.freshCode q, d.fresh_mem q,
          rfl, (d.upper_iff q p).2 above⟩))
    | inr t =>
      rw [← d.fresh_le_iff]
      change codedAttachmentLe P N r inside shadow upper
        (ZFSet.pair P (d.freshCode q)) (ZFSet.pair P (d.freshCode t)) ↔
          codedAttachmentFreshLe P inside shadow upper (d.freshCode q) (d.freshCode t)
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P (d.freshCode q) h.1)
        · exact False.elim (pair_tag_not_mem P (d.freshCode q) h.1)
        · exact False.elim (pair_tag_not_mem P (d.freshCode t) h.1)
        · obtain ⟨s, _, v, _, eqQ, eqT, lower⟩ := h
          have sameQ := (ZFSet.pair_inj.1 eqQ).2
          have sameT := (ZFSet.pair_inj.1 eqT).2
          exact sameQ.symm ▸ sameT.symm ▸ lower
      · intro lower
        exact Or.inr (Or.inr (Or.inr ⟨d.freshCode q, d.fresh_mem q,
          d.freshCode t, d.fresh_mem t, rfl, rfl, lower⟩))

theorem partialOrder : PartialOrderCode d.carrier d.order where
  relation := codedAttachmentOrder_shape P N r inside shadow upper
  refl z hz := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    exact (d.le_encode x x).2 (b.extension.refl x)
  antisymm z hz w hw zw wz := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    obtain ⟨y, rfl⟩ := d.encode_surjective w hw
    exact congrArg d.encode (b.extension.antisymm
      ((d.le_encode x y).1 zw) ((d.le_encode y x).1 wz))
  trans z hz w hw v hv zw wv := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    obtain ⟨y, rfl⟩ := d.encode_surjective w hw
    obtain ⟨t, rfl⟩ := d.encode_surjective v hv
    exact (d.le_encode x t).2 (b.extension.trans
      ((d.le_encode x y).1 zw) ((d.le_encode y t).1 wv))

theorem encoded_meet_glb (x y : ({p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh)) :
    GreatestLowerBoundCode d.carrier d.order (d.encode x) (d.encode y)
      (d.encode (b.extension.meet x y)) := by
  refine ⟨(d.le_encode _ _).2 (b.extension.meet_le_left x y),
    (d.le_encode _ _).2 (b.extension.meet_le_right x y), ?_⟩
  intro w hw wx wy
  obtain ⟨z, rfl⟩ := d.encode_surjective w hw
  exact (d.le_encode _ _).2 (b.extension.le_meet
    ((d.le_encode _ _).1 wx) ((d.le_encode _ _).1 wy))

theorem meetOrder : MeetOrderCode d.carrier d.order d.meetGraph := by
  apply canonicalMeetGraph_code d.partialOrder
  intro x hx y hy
  obtain ⟨s, rfl⟩ := d.encode_surjective x hx
  obtain ⟨t, rfl⟩ := d.encode_surjective y hy
  exact ⟨d.encode (b.extension.meet s t), d.encode_mem _, d.encoded_meet_glb s t⟩

theorem encoded_meet_entry (x y : ({p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh)) :
    ZFSet.pair (ZFSet.pair (d.encode x) (d.encode y))
      (d.encode (b.extension.meet x y)) ∈ d.meetGraph :=
  (pair_mem_canonicalMeetGraph _ _ _ _ _).2
    ⟨d.encode_mem x, d.encode_mem y, d.encode_mem _, d.encoded_meet_glb x y⟩

end CodedTemplateAttachment

end



section

universe u

noncomputable def batchAttachmentInsideGraph (I Qs rs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ Q ∈ ZFSet.sUnion (ZFSet.sUnion Qs),
    ∃ r ∈ ZFSet.sUnion (ZFSet.sUnion rs),
    ∃ q ∈ Q, ∃ t ∈ Q, z = ZFSet.pair (ZFSet.pair i q) (ZFSet.pair i t) ∧
      ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧ ZFSet.pair q t ∈ r)
    (ZFSet.prod (indexedAttachmentDomain I Qs) (indexedAttachmentDomain I Qs))

noncomputable def batchAttachmentUpperGraph (I P Qs Fs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ Q ∈ ZFSet.sUnion (ZFSet.sUnion Qs),
    ∃ F ∈ ZFSet.sUnion (ZFSet.sUnion Fs),
    ∃ q ∈ Q, ∃ p ∈ P, z = ZFSet.pair (ZFSet.pair i q) p ∧
      ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i F ∈ Fs ∧ p ∈ F)
    (ZFSet.prod (indexedAttachmentDomain I Qs) P)

theorem batchAttachmentInsideGraph_subset (I Qs rs : ZFSet.{u}) :
    batchAttachmentInsideGraph I Qs rs ⊆
      ZFSet.prod (indexedAttachmentDomain I Qs) (indexedAttachmentDomain I Qs) :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem batchAttachmentUpperGraph_subset (I P Qs Fs : ZFSet.{u}) :
    batchAttachmentUpperGraph I P Qs Fs ⊆ ZFSet.prod (indexedAttachmentDomain I Qs) P :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_batchAttachmentInsideGraph (I Qs rs z : ZFSet.{u}) :
    z ∈ batchAttachmentInsideGraph I Qs rs ↔
      ∃ i ∈ I, ∃ Q r q t, z = ZFSet.pair (ZFSet.pair i q) (ZFSet.pair i t) ∧
        ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧ q ∈ Q ∧ t ∈ Q ∧ ZFSet.pair q t ∈ r := by
  constructor
  · intro hz
    obtain ⟨i, hi, Q, _, r, _, q, hq, t, ht, eq, entryQ, entryR, lower⟩ := (ZFSet.mem_sep.1 hz).2
    exact ⟨i, hi, Q, r, q, t, eq, entryQ, entryR, hq, ht, lower⟩
  · rintro ⟨i, hi, Q, r, q, t, rfl, entryQ, entryR, hq, ht, lower⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain I Qs i q).2 ⟨hi, Q, entryQ, hq⟩,
        (pair_mem_indexedAttachmentDomain I Qs i t).2 ⟨hi, Q, entryQ, ht⟩⟩,
      i, hi, Q, pair_second_mem_doubleUnion entryQ, r, pair_second_mem_doubleUnion entryR,
      q, hq, t, ht, rfl, entryQ, entryR, lower⟩

theorem mem_batchAttachmentUpperGraph (I P Qs Fs z : ZFSet.{u}) :
    z ∈ batchAttachmentUpperGraph I P Qs Fs ↔
      ∃ i ∈ I, ∃ Q F q p, z = ZFSet.pair (ZFSet.pair i q) p ∧
        ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i F ∈ Fs ∧ q ∈ Q ∧ p ∈ P ∧ p ∈ F := by
  constructor
  · intro hz
    obtain ⟨i, hi, Q, _, F, _, q, hq, p, hp, eq, entryQ, entryF, upper⟩ := (ZFSet.mem_sep.1 hz).2
    exact ⟨i, hi, Q, F, q, p, eq, entryQ, entryF, hq, hp, upper⟩
  · rintro ⟨i, hi, Q, F, q, p, rfl, entryQ, entryF, hq, hp, upper⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain I Qs i q).2 ⟨hi, Q, entryQ, hq⟩, hp⟩,
      i, hi, Q, pair_second_mem_doubleUnion entryQ, F, pair_second_mem_doubleUnion entryF,
      q, hq, p, hp, rfl, entryQ, entryF, upper⟩

theorem pair_mem_batchAttachmentInsideGraph (I Qs rs i q j t : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i q) (ZFSet.pair j t) ∈ batchAttachmentInsideGraph I Qs rs ↔
      i = j ∧ i ∈ I ∧ ∃ Q r, ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧
        q ∈ Q ∧ t ∈ Q ∧ ZFSet.pair q t ∈ r := by
  rw [mem_batchAttachmentInsideGraph]
  constructor
  · rintro ⟨k, hk, Q, r, x, y, eq, entryQ, entryR, hx, hy, lower⟩
    have outer := ZFSet.pair_inj.1 eq
    have left := ZFSet.pair_inj.1 outer.1
    have right := ZFSet.pair_inj.1 outer.2
    rcases left with ⟨rfl, rfl⟩
    rcases right with ⟨rfl, rfl⟩
    exact ⟨rfl, hk, Q, r, entryQ, entryR, hx, hy, lower⟩
  · rintro ⟨rfl, hi, Q, r, entryQ, entryR, hq, ht, lower⟩
    exact ⟨i, hi, Q, r, q, t, rfl, entryQ, entryR, hq, ht, lower⟩

theorem pair_mem_batchAttachmentUpperGraph (I P Qs Fs i q p : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i q) p ∈ batchAttachmentUpperGraph I P Qs Fs ↔
      i ∈ I ∧ p ∈ P ∧ ∃ Q F, ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i F ∈ Fs ∧ q ∈ Q ∧ p ∈ F := by
  rw [mem_batchAttachmentUpperGraph]
  constructor
  · rintro ⟨j, hj, Q, F, x, y, eq, entryQ, entryF, hx, hy, upper⟩
    have outer := ZFSet.pair_inj.1 eq
    have inner := ZFSet.pair_inj.1 outer.1
    rcases inner with ⟨rfl, rfl⟩
    rcases outer.2 with rfl
    exact ⟨hj, hy, Q, F, entryQ, entryF, hx, upper⟩
  · rintro ⟨hi, hp, Q, F, entryQ, entryF, hq, upper⟩
    exact ⟨i, hi, Q, F, q, p, rfl, entryQ, entryF, hq, hp, upper⟩

namespace AttachmentBatchInputs

variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

theorem inside_entry_iff (i j : {i : ZFSet.{u} // i ∈ I}) (q t : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) (ZFSet.pair j.val t) ∈ batchAttachmentInsideGraph I Qs rs ↔
      i = j ∧ q ∈ d.space i ∧ t ∈ d.space i ∧ ZFSet.pair q t ∈ d.rel i := by
  rw [pair_mem_batchAttachmentInsideGraph]
  constructor
  · rintro ⟨same, _, Q, r, entryQ, entryR, hq, ht, lower⟩
    have eqQ : d.space i = Q := d.spaces.value_eq_of_entry i entryQ
    have eqR : d.rel i = r := d.relations.value_eq_of_entry i entryR
    exact ⟨Subtype.ext same, eqQ.symm ▸ hq, eqQ.symm ▸ ht, eqR.symm ▸ lower⟩
  · rintro ⟨rfl, hq, ht, lower⟩
    exact ⟨rfl, i.property, d.space i, d.rel i, d.space_entry i, d.rel_entry i, hq, ht, lower⟩

theorem upper_entry_iff (i : {i : ZFSet.{u} // i ∈ I}) (q p : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) p ∈ batchAttachmentUpperGraph I P Qs Fs ↔
      q ∈ d.space i ∧ p ∈ P ∧ p ∈ d.filter i := by
  rw [pair_mem_batchAttachmentUpperGraph]
  constructor
  · rintro ⟨_, hp, Q, F, entryQ, entryF, hq, upper⟩
    have eqQ : d.space i = Q := d.spaces.value_eq_of_entry i entryQ
    have eqF : d.filter i = F := d.filters.value_eq_of_entry i entryF
    exact ⟨eqQ.symm ▸ hq, hp, eqF.symm ▸ upper⟩
  · rintro ⟨hq, hp, upper⟩
    exact ⟨i.property, hp, d.space i, d.filter i, d.space_entry i, d.filter_entry i, hq, upper⟩

end AttachmentBatchInputs

end



namespace AttachmentBatchInputs

universe u
variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

noncomputable def freshCode (q : d.templates.Fresh) : ZFSet.{u} :=
  ZFSet.pair q.1.val q.2.val.val

theorem freshCode_mem (q : d.templates.Fresh) :
    d.freshCode q ∈ indexedAttachmentFresh I Qs rs As :=
  (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry q.1) (d.rel_entry q.1) (d.anchor_entry q.1)).2
      ((mem_freshPart _ _ _ _).2 ⟨q.2.val.property, q.2.property⟩)

theorem freshCode_injective : Function.Injective d.freshCode := by
  rintro ⟨i, q⟩ ⟨j, t⟩ equal
  have parts := ZFSet.pair_inj.1 equal
  have same : i = j := Subtype.ext parts.1
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext (Subtype.ext parts.2))

theorem freshCode_surjective : ∀ z ∈ indexedAttachmentFresh I Qs rs As,
    ∃ q : d.templates.Fresh, d.freshCode q = z := by
  intro z hz
  obtain ⟨i, hi, q, equal, _⟩ := (mem_indexedAttachmentFresh I Qs rs As z).1 hz
  subst z
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have fresh := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry j) (d.rel_entry j) (d.anchor_entry j)).1 hz
  have parts := (mem_freshPart _ _ _ q).1 fresh
  exact ⟨⟨j, ⟨⟨q, parts.1⟩, parts.2⟩⟩, rfl⟩

theorem freshCode_shadow_entry (q : d.templates.Fresh) :
    ZFSet.pair (d.freshCode q) (d.templates.shadow q).val ∈
      batchAttachmentShadowGraph I P Qs μs As Es := by
  apply (d.batch_shadow_entry_iff q.1 q.2.val.val _).2
  exact (d.fiber q.1).shadow_entry ⟨(), q.2⟩

theorem freshCode_shadow_value (q : d.templates.Fresh) (s : ZFSet.{u})
    (entry : ZFSet.pair (d.freshCode q) s ∈ batchAttachmentShadowGraph I P Qs μs As Es) :
    s = (d.templates.shadow q).val := by
  have domain := indexedAttachmentFresh_subset I Qs rs As (d.freshCode_mem q)
  obtain ⟨v, _, unique⟩ := d.batch_shadow_function.2 (d.freshCode q) domain
  exact (unique s entry).trans (unique _ (d.freshCode_shadow_entry q)).symm

theorem freshCode_inside_iff (q t : d.templates.Fresh) :
    ZFSet.pair (d.freshCode q) (d.freshCode t) ∈ batchAttachmentInsideGraph I Qs rs ↔
      d.templates.Inside q t := by
  rcases q with ⟨i, q⟩
  rcases t with ⟨j, t⟩
  change ZFSet.pair (ZFSet.pair i.val q.val.val) (ZFSet.pair j.val t.val.val) ∈
    batchAttachmentInsideGraph I Qs rs ↔ _
  rw [d.inside_entry_iff]
  constructor
  · rintro ⟨same, _, _, lower⟩
    cases same
    exact ⟨rfl, lower⟩
  · rintro ⟨same, lower⟩
    cases same
    exact ⟨rfl, q.val.property, t.val.property, lower⟩

theorem freshCode_upper_iff (q : d.templates.Fresh) (p : {p : ZFSet.{u} // p ∈ P}) :
    ZFSet.pair (d.freshCode q) p.val ∈ batchAttachmentUpperGraph I P Qs Fs ↔
      d.templates.upper q.1 p := by
  change ZFSet.pair (ZFSet.pair q.1.val q.2.val.val) p.val ∈
    batchAttachmentUpperGraph I P Qs Fs ↔ _
  rw [d.upper_entry_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨q.2.val.property, p.property, h⟩⟩

noncomputable def coding :
    CodedTemplateAttachment d.oldOrder d.templates
      (indexedAttachmentFresh I Qs rs As) (batchAttachmentInsideGraph I Qs rs)
      (batchAttachmentShadowGraph I P Qs μs As Es) (batchAttachmentUpperGraph I P Qs Fs) where
  freshCode := d.freshCode
  fresh_mem := d.freshCode_mem
  fresh_injective := d.freshCode_injective
  fresh_surjective := d.freshCode_surjective
  shadow_entry := d.freshCode_shadow_entry
  shadow_value := d.freshCode_shadow_value
  inside_iff := d.freshCode_inside_iff
  upper_iff := d.freshCode_upper_iff

noncomputable abbrev batchCarrier := d.coding.carrier
noncomputable abbrev batchOrder := d.coding.order
noncomputable abbrev batchMeetGraph := canonicalMeetGraph d.batchCarrier d.batchOrder

theorem batch_meetOrder : MeetOrderCode d.batchCarrier d.batchOrder d.batchMeetGraph :=
  d.coding.meetOrder

end AttachmentBatchInputs




universe u

namespace BoundedFormula

open SetFormula

def pairOfPairsFormula {n} (z a b c d : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (exMem z.succ.succ (exMem 0
    (.conj (orderedPairFormula 2 a.succ.succ.succ.succ b.succ.succ.succ.succ)
      (.conj (orderedPairFormula 0 c.succ.succ.succ.succ d.succ.succ.succ.succ)
        (orderedPairFormula z.succ.succ.succ.succ 2 0))))))

theorem truth_pairOfPairsFormula {n} (z a b c d : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (pairOfPairsFormula z a b c d) env ↔
      env z = ZFSet.pair (ZFSet.pair (env a) (env b)) (ZFSet.pair (env c) (env d)) := by
  simp only [pairOfPairsFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ u ∈ env z, ∃ x ∈ u, ∃ v ∈ env z, ∃ y ∈ v,
    x = ZFSet.pair (env a) (env b) ∧ y = ZFSet.pair (env c) (env d) ∧ env z = ZFSet.pair x y) ↔ _
  constructor
  · rintro ⟨_, _, x, _, _, _, y, _, rfl, rfl, eq⟩
    exact eq
  · intro eq
    refine ⟨{ZFSet.pair (env a) (env b)}, ?_, ZFSet.pair (env a) (env b),
      ZFSet.mem_singleton.2 rfl, {ZFSet.pair (env a) (env b), ZFSet.pair (env c) (env d)},
      ?_, ZFSet.pair (env c) (env d), ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl, eq⟩
    · rw [eq]
      exact ZFSet.mem_pair.2 (Or.inl rfl)
    · rw [eq]
      exact ZFSet.mem_pair.2 (Or.inr rfl)

def batchAttachmentInsideEntryFormula {n} (z i qs rs qb rb : Fin n) : BoundedFormula n :=
  exMem i (exMem qb.succ (exMem rb.succ.succ (exMem 1 (exMem 2
    (.conj (pairOfPairsFormula z.succ.succ.succ.succ.succ 4 1 4 0)
      (.conj (pairMembershipFormula 4 3 qs.succ.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 4 2 rs.succ.succ.succ.succ.succ)
          (pairMembershipFormula 1 0 2))))))))

theorem truth_batchAttachmentInsideEntryFormula {n} (z i qs rs qb rb : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (batchAttachmentInsideEntryFormula z i qs rs qb rb) env ↔
      ∃ j ∈ env i, ∃ Q ∈ env qb, ∃ r ∈ env rb, ∃ q ∈ Q, ∃ t ∈ Q,
        env z = ZFSet.pair (ZFSet.pair j q) (ZFSet.pair j t) ∧
          ZFSet.pair j Q ∈ env qs ∧ ZFSet.pair j r ∈ env rs ∧ ZFSet.pair q t ∈ r := by
  simp only [batchAttachmentInsideEntryFormula, truth_exMem, Truth,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

def batchAttachmentUpperEntryFormula {n} (z i p qs fs qb fb : Fin n) : BoundedFormula n :=
  exMem i (exMem qb.succ (exMem fb.succ.succ (exMem 1
    (exMem p.succ.succ.succ.succ
      (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ 4 1 0)
        (.conj (pairMembershipFormula 4 3 qs.succ.succ.succ.succ.succ)
          (.conj (pairMembershipFormula 4 2 fs.succ.succ.succ.succ.succ) (.mem 0 2))))))))

theorem truth_batchAttachmentUpperEntryFormula {n} (z i p qs fs qb fb : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (batchAttachmentUpperEntryFormula z i p qs fs qb fb) env ↔
      ∃ j ∈ env i, ∃ Q ∈ env qb, ∃ F ∈ env fb, ∃ q ∈ Q, ∃ v ∈ env p,
        env z = ZFSet.pair (ZFSet.pair j q) v ∧
          ZFSet.pair j Q ∈ env qs ∧ ZFSet.pair j F ∈ env fs ∧ v ∈ F := by
  simp only [batchAttachmentUpperEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem batchAttachmentInsideGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I Qs rs : ZFSet.{u}} (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) :
    batchAttachmentInsideGraph I Qs rs ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have rBound := M.union_mem unions (M.union_mem unions hrs)
  have domain := M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs
  let params := extend I (extend Qs (extend rs
    (extend (ZFSet.sUnion (ZFSet.sUnion Qs)) (extend (ZFSet.sUnion (ZFSet.sUnion rs)) Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.batchAttachmentInsideEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hQs (Fin.cases hrs (Fin.cases qBound
      (Fin.cases rBound (fun j => Fin.elim0 j))))))
    (M.prod_mem pairing unions powers separation domain domain)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.batchAttachmentInsideEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (indexedAttachmentDomain I Qs) (indexedAttachmentDomain I Qs)) =
      batchAttachmentInsideGraph I Qs rs := by
    apply ZFSet.ext
    intro z
    rw [batchAttachmentInsideGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchAttachmentInsideEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem batchAttachmentUpperGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs Fs : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hFs : Fs ∈ M.sets) : batchAttachmentUpperGraph I P Qs Fs ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have fBound := M.union_mem unions (M.union_mem unions hFs)
  have domain := M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs
  let params := extend I (extend P (extend Qs (extend Fs
    (extend (ZFSet.sUnion (ZFSet.sUnion Qs)) (extend (ZFSet.sUnion (ZFSet.sUnion Fs)) Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.batchAttachmentUpperEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hI (Fin.cases hP (Fin.cases hQs (Fin.cases hFs (Fin.cases qBound
      (Fin.cases fBound (fun j => Fin.elim0 j)))))))
    (M.prod_mem pairing unions powers separation domain hP)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.batchAttachmentUpperEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod (indexedAttachmentDomain I Qs) P) = batchAttachmentUpperGraph I P Qs Fs := by
    apply ZFSet.ext
    intro z
    rw [batchAttachmentUpperGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchAttachmentUpperEntryFormula 0 1 2 3 4 5 6 _)
  exact eq ▸ selected

end TransitiveGround


end PartitionPilot.Forcing

end OAI
