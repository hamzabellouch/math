import OAI.SetTheory.PartitionPrinciple.Geometry.SeparationTileCodes

namespace OAI

section

namespace PartitionPilot.Forcing.CodedPrincipalTile
open Compression.RecursiveMaps
universe u
variable {P Q rP rQ μP μQ ell : ZFSet.{u}}
variable {old : MeetOrderCode P rP μP} {right : MeetOrderCode Q rQ μQ}
variable {g : PrincipalAmalgamation.Input old.toMeetOrder right.toMeetOrder}
variable (d : CodedPrincipalTile old right g ell)

noncomputable def decode (x : {x : ZFSet.{u} // x ∈ d.carrier}) : g.Node :=
  Classical.choose (d.encode_surjective x.val x.property)

theorem encode_decode (x : {x : ZFSet.{u} // x ∈ d.carrier}) : d.encode (d.decode x) = x.val :=
  Classical.choose_spec (d.encode_surjective x.val x.property)

theorem decode_encode (x : g.Node) : d.decode ⟨d.encode x, d.encode_mem x⟩ = x :=
  d.encode_injective (d.encode_decode _)

noncomputable def encodingIso : Compression.MeetIso g.order d.meetOrder.toMeetOrder :=
  isoOfOrder (fun x => ⟨d.encode x, d.encode_mem x⟩) d.decode d.decode_encode
    (fun x => Subtype.ext (d.encode_decode x)) d.le_encode

noncomputable def decodingIso : Compression.MeetIso d.meetOrder.toMeetOrder g.order :=
  inverseIso d.encodingIso

theorem encodingIso_value (x : g.Node) :
    (d.encodingIso.toFun x).val = d.encode x := rfl

theorem decodingIso_encode (x : {x : ZFSet.{u} // x ∈ d.carrier}) :
    d.encode (d.decodingIso.toFun x) = x.val := d.encode_decode x

theorem vertex_cover (z : ZFSet.{u}) (hz : z ∈ d.carrier) :
    (∃ p ∈ P, ZFSet.pair p z ∈ attachmentOldEmbeddingGraph P) ∨
    ∃ q ∈ Q, ZFSet.pair q z ∈ attachmentTemplateEmbeddingGraph P Q rQ ell g.rightAnchor.val := by
  obtain ⟨x, rfl⟩ := d.encode_surjective z hz
  rcases g.cover x with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · exact Or.inl ⟨p.val, p.property, (pair_mem_attachmentOldEmbeddingGraph _ _ _).2 ⟨p.property, rfl⟩⟩
  · exact Or.inr ⟨q.val, q.property, d.template_entry q⟩

theorem cross_meet_entry (p : {p : ZFSet.{u} // p ∈ P})
    (q : {q : ZFSet.{u} // q ∈ Q}) :
    ZFSet.pair (ZFSet.pair p.val (d.encode (g.right.toFun q)))
      (old.toMeetOrder.meet p (g.shadow q)).val ∈ d.meetGraph := by
  have entry := d.encoded_meet_entry (g.left.toFun p) (g.right.toFun q)
  rw [g.cross_meet] at entry
  exact entry

theorem old_graph_ideal {p z : ZFSet.{u}} (hp : p ∈ P) (hz : z ∈ d.carrier)
    (lower : ZFSet.pair z p ∈ d.order) :
    ∃ x ∈ P, ZFSet.pair x z ∈ attachmentOldEmbeddingGraph P := by
  obtain ⟨x, rfl⟩ := d.encode_surjective z hz
  obtain ⟨q, rfl⟩ := d.old_ideal ⟨p, hp⟩ x lower
  exact ⟨q.val, q.property, (pair_mem_attachmentOldEmbeddingGraph _ _ _).2 ⟨q.property, rfl⟩⟩

theorem template_graph_ideal {q y z : ZFSet.{u}}
    (entry : ZFSet.pair q y ∈ attachmentTemplateEmbeddingGraph P Q rQ ell g.rightAnchor.val)
    (hz : z ∈ d.carrier) (lower : ZFSet.pair z y ∈ d.order) :
    ∃ x ∈ Q, ZFSet.pair x z ∈ attachmentTemplateEmbeddingGraph P Q rQ ell g.rightAnchor.val := by
  have hq := (ZFSet.pair_mem_prod.1 ((attachmentTemplateEmbeddingGraph_isFunc d.base_function).1 entry)).1
  have eq := (d.template_entry_iff ⟨q, hq⟩ y).1 entry
  rw [eq] at lower
  obtain ⟨x, rfl⟩ := d.encode_surjective z hz
  obtain ⟨p, rfl⟩ := d.template_ideal ⟨q, hq⟩ x lower
  exact ⟨p.val, p.property, d.template_entry p⟩

end PartitionPilot.Forcing.CodedPrincipalTile

end

end OAI
