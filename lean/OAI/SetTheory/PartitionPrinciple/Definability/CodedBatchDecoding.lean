import OAI.SetTheory.PartitionPrinciple.Definability.BatchAttachmentRealization

namespace OAI

section

namespace PartitionPilot.Forcing.CodedTemplateAttachment

open Compression.RecursiveMaps
universe u v w
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ}
variable {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

noncomputable def decode (x : {x : ZFSet.{u} // x ∈ d.carrier}) : {p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh :=
  Classical.choose (d.encode_surjective x.val x.property)

theorem encode_decode (x : {x : ZFSet.{u} // x ∈ d.carrier}) : d.encode (d.decode x) = x.val :=
  Classical.choose_spec (d.encode_surjective x.val x.property)

theorem decode_encode (x : {p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh) : d.decode ⟨d.encode x, d.encode_mem x⟩ = x :=
  d.encode_injective (d.encode_decode _)

noncomputable def encodingIso : Compression.MeetIso b.extension d.meetOrder.toMeetOrder :=
  isoOfOrder (fun x => ⟨d.encode x, d.encode_mem x⟩) d.decode d.decode_encode
    (fun x => Subtype.ext (d.encode_decode x)) d.le_encode

noncomputable def decodingIso : Compression.MeetIso d.meetOrder.toMeetOrder b.extension :=
  inverseIso d.encodingIso

theorem encodingIso_value (x : {p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh) :
    (d.encodingIso.toFun x).val = d.encode x := rfl

theorem decodingIso_encode (x : {x : ZFSet.{u} // x ∈ d.carrier}) :
    d.encode (d.decodingIso.toFun x) = x.val := d.encode_decode x

end PartitionPilot.Forcing.CodedTemplateAttachment

end

end OAI
