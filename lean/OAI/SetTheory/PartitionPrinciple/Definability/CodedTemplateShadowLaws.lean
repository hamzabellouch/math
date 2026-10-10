import OAI.SetTheory.PartitionPrinciple.Definability.BatchAttachmentRealization

namespace OAI

section

namespace PartitionPilot.Forcing.CodedTemplateAttachment
universe u v w
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

theorem old_lower_iff (p : {p : ZFSet.{u} // p ∈ P}) (q : b.Fresh) :
    ZFSet.pair p.val (d.encode (.inr q)) ∈ d.order ↔
      ZFSet.pair p.val (b.shadow q).val ∈ r :=
  d.le_encode (.inl p) (.inr q)

theorem old_upper_iff (q : b.Fresh) (p : {p : ZFSet.{u} // p ∈ P}) :
    ZFSet.pair (d.encode (.inr q)) p.val ∈ d.order ↔ b.upper q.1 p :=
  d.le_encode (.inr q) (.inl p)

theorem cross_lower_iff (q t : b.Fresh) (different : q.1 ≠ t.1) :
    ZFSet.pair (d.encode (.inr q)) (d.encode (.inr t)) ∈ d.order ↔
      b.upper q.1 (b.shadow t) :=
  (d.le_encode (.inr q) (.inr t)).trans (b.cross_le_iff q t different)

theorem encoded_shadow_meet (q : b.Fresh) (p : {p : ZFSet.{u} // p ∈ P})
    (notAbove : ZFSet.pair (d.encode (.inr q)) p.val ∉ d.order) :
    ZFSet.pair (ZFSet.pair (d.encode (.inr q)) p.val)
      (old.toMeetOrder.meet (b.shadow q) p).val ∈ d.meetGraph := by
  have eq := b.shadow_meet_eq q p (fun lower => notAbove ((d.le_encode _ _).2 lower))
  have result := d.encoded_meet_entry (.inr q) (.inl p)
  rw [eq] at result
  exact result

theorem encoded_cross_meet (q t : b.Fresh) (different : q.1 ≠ t.1)
    (notQT : ZFSet.pair (d.encode (.inr q)) (d.encode (.inr t)) ∉ d.order)
    (notTQ : ZFSet.pair (d.encode (.inr t)) (d.encode (.inr q)) ∉ d.order) :
    ZFSet.pair (ZFSet.pair (d.encode (.inr q)) (d.encode (.inr t)))
      (old.toMeetOrder.meet (b.shadow q) (b.shadow t)).val ∈ d.meetGraph := by
  have eq := b.cross_meet_eq q t different
    (fun lower => notQT ((d.le_encode _ _).2 lower))
    (fun lower => notTQ ((d.le_encode _ _).2 lower))
  have result := d.encoded_meet_entry (.inr q) (.inr t)
  rw [eq] at result
  exact result

theorem greatest_preserved {T : ZFSet.{u}} (hT : T ∈ P)
    (greatest : ∀ p ∈ P, ZFSet.pair p T ∈ r) :
    ∀ z ∈ d.carrier, ZFSet.pair z T ∈ d.order := by
  intro z hz
  obtain ⟨x, rfl⟩ := d.encode_surjective z hz
  exact (d.le_encode x (.inl ⟨T, hT⟩)).2
    (b.greatest_preserved ⟨T, hT⟩ (fun p => greatest p.val p.property) x)

theorem least_preserved {zero : ZFSet.{u}} (hzero : zero ∈ P)
    (least : ∀ p ∈ P, ZFSet.pair zero p ∈ r) :
    ∀ z ∈ d.carrier, ZFSet.pair zero z ∈ d.order := by
  intro z hz
  obtain ⟨x, rfl⟩ := d.encode_surjective z hz
  exact (d.le_encode (.inl ⟨zero, hzero⟩) x).2
    (b.least_preserved ⟨zero, hzero⟩ (fun p => least p.val p.property) x)

end PartitionPilot.Forcing.CodedTemplateAttachment

end

end OAI
