import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageFromCodes

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

noncomputable def attachmentIdeal (Q rQ a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun q => ZFSet.pair q a ∈ rQ) Q

noncomputable def freshPart (Q rQ a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun q => ZFSet.pair q a ∉ rQ) Q

theorem mem_attachmentIdeal (Q rQ a q : ZFSet.{u}) :
    q ∈ attachmentIdeal Q rQ a ↔ q ∈ Q ∧ ZFSet.pair q a ∈ rQ :=
  ZFSet.mem_sep

theorem mem_freshPart (Q rQ a q : ZFSet.{u}) :
    q ∈ freshPart Q rQ a ↔ q ∈ Q ∧ ZFSet.pair q a ∉ rQ :=
  ZFSet.mem_sep

theorem attachmentIdeal_union_freshPart (Q rQ a : ZFSet.{u}) :
    attachmentIdeal Q rQ a ∪ freshPart Q rQ a = Q := by
  classical
  apply ZFSet.ext
  intro q
  simp only [ZFSet.mem_union, mem_attachmentIdeal, mem_freshPart]
  exact ⟨fun h => h.elim And.left And.left, fun h =>
    (Classical.em (ZFSet.pair q a ∈ rQ)).elim
      (fun rel => Or.inl ⟨h, rel⟩) (fun rel => Or.inr ⟨h, rel⟩)⟩

theorem attachmentIdeal_not_freshPart {Q rQ a q : ZFSet.{u}}
    (hq : q ∈ attachmentIdeal Q rQ a) : q ∉ freshPart Q rQ a := by
  intro fresh
  exact ((mem_freshPart Q rQ a q).1 fresh).2 ((mem_attachmentIdeal Q rQ a q).1 hq).2

noncomputable def attachmentShadowGraph (Q P μQ ell a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ q ∈ Q, ∃ p ∈ P, z = ZFSet.pair q p ∧
    ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μQ ∧ ZFSet.pair c p ∈ ell)
    (ZFSet.prod Q P)

theorem mem_attachmentShadowGraph (Q P μQ ell a z : ZFSet.{u}) :
    z ∈ attachmentShadowGraph Q P μQ ell a ↔
      ∃ q ∈ Q, ∃ p ∈ P, z = ZFSet.pair q p ∧
        ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μQ ∧ ZFSet.pair c p ∈ ell := by
  rw [attachmentShadowGraph, ZFSet.mem_sep]
  exact ⟨And.right, fun h => ⟨by
    obtain ⟨q, hq, p, hp, rfl, _⟩ := h
    exact ZFSet.pair_mem_prod.2 ⟨hq, hp⟩, h⟩⟩

theorem pair_mem_attachmentShadowGraph (Q P μQ ell a q p : ZFSet.{u}) :
    ZFSet.pair q p ∈ attachmentShadowGraph Q P μQ ell a ↔
      q ∈ Q ∧ p ∈ P ∧
        ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μQ ∧ ZFSet.pair c p ∈ ell := by
  rw [mem_attachmentShadowGraph]
  constructor
  · rintro ⟨q', hq, p', hp, equal, c, hc, meet, image⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hq, hp, c, hc, meet, image⟩
  · rintro ⟨hq, hp, c, hc, meet, image⟩
    exact ⟨q, hq, p, hp, rfl, c, hc, meet, image⟩

theorem meet_entry_in_attachmentIdeal {Q rQ μQ a q c : ZFSet.{u}}
    (meet : MeetOrderCode Q rQ μQ)
    (entry : ZFSet.pair (ZFSet.pair q a) c ∈ μQ) :
    c ∈ attachmentIdeal Q rQ a :=
  (mem_attachmentIdeal Q rQ a c).2
    ⟨(ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2, meet.lower_right q a c entry⟩

theorem meet_entry_eq_of_attachmentIdeal {Q rQ μQ a q c : ZFSet.{u}}
    (meet : MeetOrderCode Q rQ μQ) (hq : q ∈ attachmentIdeal Q rQ a)
    (entry : ZFSet.pair (ZFSet.pair q a) c ∈ μQ) : c = q := by
  have inIdeal := (mem_attachmentIdeal Q rQ a q).1 hq
  have hc := (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2
  exact meet.order.antisymm c hc q inIdeal.1 (meet.lower_left q a c entry)
    (meet.greatest q a c q inIdeal.1 entry (meet.order.refl q inIdeal.1) inIdeal.2)

theorem attachmentShadowGraph_function {Q P rQ μQ ell a : ZFSet.{u}}
    (meet : MeetOrderCode Q rQ μQ) (ha : a ∈ Q)
    (ellFunc : ZFSet.IsFunc (attachmentIdeal Q rQ a) P ell) :
    ZFSet.IsFunc Q P (attachmentShadowGraph Q P μQ ell a) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro q hq
  obtain ⟨c, entry, meetUnique⟩ := meet.operation.2 (ZFSet.pair q a)
    (ZFSet.pair_mem_prod.2 ⟨hq, ha⟩)
  have hc := meet_entry_in_attachmentIdeal meet entry
  obtain ⟨p, image, imageUnique⟩ := ellFunc.2 c hc
  have hp := (ZFSet.pair_mem_prod.1 (ellFunc.1 image)).2
  refine ⟨p, (pair_mem_attachmentShadowGraph Q P μQ ell a q p).2
    ⟨hq, hp, c, ((mem_attachmentIdeal Q rQ a c).1 hc).1, entry, image⟩, ?_⟩
  intro p' shadow
  obtain ⟨_, _, c', _, entry', image'⟩ :=
    (pair_mem_attachmentShadowGraph Q P μQ ell a q p').1 shadow
  have equal := meetUnique c' entry'
  subst c'
  exact imageUnique p' image'

theorem attachmentShadowGraph_on_ideal {Q P rQ μQ ell a q p : ZFSet.{u}}
    (meet : MeetOrderCode Q rQ μQ) (ha : a ∈ Q)
    (ellFunc : ZFSet.IsFunc (attachmentIdeal Q rQ a) P ell)
    (hq : q ∈ attachmentIdeal Q rQ a) :
    ZFSet.pair q p ∈ attachmentShadowGraph Q P μQ ell a ↔ ZFSet.pair q p ∈ ell := by
  constructor
  · intro shadow
    obtain ⟨_, _, c, _, entry, image⟩ :=
      (pair_mem_attachmentShadowGraph Q P μQ ell a q p).1 shadow
    exact meet_entry_eq_of_attachmentIdeal meet hq entry ▸ image
  · intro image
    have qQ := ((mem_attachmentIdeal Q rQ a q).1 hq).1
    obtain ⟨c, entry, _⟩ := meet.operation.2 (ZFSet.pair q a)
      (ZFSet.pair_mem_prod.2 ⟨qQ, ha⟩)
    have equal := meet_entry_eq_of_attachmentIdeal meet hq entry
    subst c
    exact (pair_mem_attachmentShadowGraph Q P μQ ell a q p).2
      ⟨qQ, (ZFSet.pair_mem_prod.1 (ellFunc.1 image)).2, q, qQ, entry, image⟩

def familyPointBound (Qs : ZFSet.{u}) : ZFSet.{u} := ⋃₀ ⋃₀ ⋃₀ Qs

theorem mem_familyPointBound_of_entry {Qs i Q q : ZFSet.{u}}
    (entry : ZFSet.pair i Q ∈ Qs) (hq : q ∈ Q) : q ∈ familyPointBound Qs :=
  ZFSet.mem_sUnion.2 ⟨Q, pair_second_mem_doubleUnion entry, hq⟩

noncomputable def indexedAttachmentDomain (I Qs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ Q ∈ ⋃₀ ⋃₀ Qs, ∃ q ∈ Q,
    ZFSet.pair i Q ∈ Qs ∧ z = ZFSet.pair i q)
    (ZFSet.prod I (familyPointBound Qs))

noncomputable def indexedAttachmentFresh (I Qs rs anchors : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ Q ∈ ⋃₀ ⋃₀ Qs, ∃ r ∈ ⋃₀ ⋃₀ rs,
    ∃ a ∈ ⋃₀ ⋃₀ anchors, ∃ q ∈ Q,
      ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧ ZFSet.pair i a ∈ anchors ∧
      z = ZFSet.pair i q ∧ ZFSet.pair q a ∉ r)
    (indexedAttachmentDomain I Qs)

theorem indexedAttachmentDomain_subset (I Qs : ZFSet.{u}) :
    indexedAttachmentDomain I Qs ⊆ ZFSet.prod I (familyPointBound Qs) :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem indexedAttachmentFresh_subset (I Qs rs anchors : ZFSet.{u}) :
    indexedAttachmentFresh I Qs rs anchors ⊆ indexedAttachmentDomain I Qs :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_indexedAttachmentDomain (I Qs z : ZFSet.{u}) :
    z ∈ indexedAttachmentDomain I Qs ↔
      ∃ i ∈ I, ∃ q, z = ZFSet.pair i q ∧ ∃ Q, ZFSet.pair i Q ∈ Qs ∧ q ∈ Q := by
  constructor
  · intro hz
    obtain ⟨i, hi, Q, _, q, hq, entry, equal⟩ := (ZFSet.mem_sep.1 hz).2
    exact ⟨i, hi, q, equal, Q, entry, hq⟩
  · rintro ⟨i, hi, q, rfl, Q, entry, hq⟩
    exact ZFSet.mem_sep.2
      ⟨ZFSet.pair_mem_prod.2 ⟨hi, mem_familyPointBound_of_entry entry hq⟩,
        i, hi, Q, pair_second_mem_doubleUnion entry, q, hq, entry, rfl⟩

theorem pair_mem_indexedAttachmentDomain (I Qs i q : ZFSet.{u}) :
    ZFSet.pair i q ∈ indexedAttachmentDomain I Qs ↔
      i ∈ I ∧ ∃ Q, ZFSet.pair i Q ∈ Qs ∧ q ∈ Q := by
  rw [mem_indexedAttachmentDomain]
  constructor
  · rintro ⟨j, hj, p, equal, Q, entry, hq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, Q, entry, hq⟩
  · rintro ⟨hi, Q, entry, hq⟩
    exact ⟨i, hi, q, rfl, Q, entry, hq⟩

theorem mem_indexedAttachmentFresh (I Qs rs anchors z : ZFSet.{u}) :
    z ∈ indexedAttachmentFresh I Qs rs anchors ↔
      ∃ i ∈ I, ∃ q, z = ZFSet.pair i q ∧ ∃ Q r a,
        ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧ ZFSet.pair i a ∈ anchors ∧
        q ∈ Q ∧ ZFSet.pair q a ∉ r := by
  constructor
  · intro hz
    obtain ⟨i, hi, Q, _, r, _, a, _, q, hq, entryQ, entryR, entryA, equal, fresh⟩ :=
      (ZFSet.mem_sep.1 hz).2
    exact ⟨i, hi, q, equal, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩
  · rintro ⟨i, hi, q, rfl, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩
    exact ZFSet.mem_sep.2
      ⟨(pair_mem_indexedAttachmentDomain I Qs i q).2 ⟨hi, Q, entryQ, hq⟩,
        i, hi, Q, pair_second_mem_doubleUnion entryQ, r, pair_second_mem_doubleUnion entryR,
        a, pair_second_mem_doubleUnion entryA, q, hq, entryQ, entryR, entryA, rfl, fresh⟩

theorem pair_mem_indexedAttachmentFresh (I Qs rs anchors i q : ZFSet.{u}) :
    ZFSet.pair i q ∈ indexedAttachmentFresh I Qs rs anchors ↔
      i ∈ I ∧ ∃ Q r a, ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧
        ZFSet.pair i a ∈ anchors ∧ q ∈ Q ∧ ZFSet.pair q a ∉ r := by
  rw [mem_indexedAttachmentFresh]
  constructor
  · rintro ⟨j, hj, p, equal, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩
  · rintro ⟨hi, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩
    exact ⟨i, hi, q, rfl, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩

theorem pair_mem_indexedAttachmentDomain_of_entry {I Qs i q Q : ZFSet.{u}}
    (family : FunctionGraphOn I Qs) (entry : ZFSet.pair i Q ∈ Qs) :
    ZFSet.pair i q ∈ indexedAttachmentDomain I Qs ↔ q ∈ Q := by
  rw [pair_mem_indexedAttachmentDomain]
  constructor
  · rintro ⟨_, R, other, hq⟩
    exact family.unique other entry ▸ hq
  · intro hq
    exact ⟨family.pair_source entry, Q, entry, hq⟩

theorem pair_mem_indexedAttachmentFresh_of_entries
    {I Qs rs anchors i q Q r a : ZFSet.{u}}
    (spaces : FunctionGraphOn I Qs) (orders : FunctionGraphOn I rs)
    (points : FunctionGraphOn I anchors) (entryQ : ZFSet.pair i Q ∈ Qs)
    (entryR : ZFSet.pair i r ∈ rs) (entryA : ZFSet.pair i a ∈ anchors) :
    ZFSet.pair i q ∈ indexedAttachmentFresh I Qs rs anchors ↔ q ∈ freshPart Q r a := by
  rw [pair_mem_indexedAttachmentFresh, mem_freshPart]
  constructor
  · rintro ⟨_, Q', r', a', otherQ, otherR, otherA, hq, fresh⟩
    have equalQ := spaces.unique otherQ entryQ
    have equalR := orders.unique otherR entryR
    have equalA := points.unique otherA entryA
    subst Q'
    subst r'
    subst a'
    exact ⟨hq, fresh⟩
  · rintro ⟨hq, fresh⟩
    exact ⟨spaces.pair_source entryQ, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩

end PartitionPilot.Forcing

end OAI
