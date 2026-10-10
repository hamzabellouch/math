import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionExternalTileOverlaps

namespace OAI

section

namespace PartitionPilot.Forcing
open Compression Compression.RecursiveMaps SetFormula
universe u
variable {P r μ f : ZFSet.{u}}

noncomputable def compressionTileIso (old : MeetOrderCode P r μ)
    (embedding : MeetEmbeddingCode P P r r μ μ f) (K : {x : ZFSet.{u} // x ∈ P})
    (range : ∀ z, (∃ x ∈ P, ZFSet.pair x z ∈ f) ↔ z ∈ P ∧ ZFSet.pair z K.val ∈ r) :
    MeetIso old.toMeetOrder (Attachment.idealOrder old.toMeetOrder K) := by
  apply isoOntoIdeal old.toMeetOrder (embedding.toMeetEmbedding old old) K
  · intro x
    exact ((range _).1 ⟨x.val, x.property, embedding.value_entry x⟩).2
  · intro z hz
    obtain ⟨x, hx, entry⟩ := (range z.val).2 ⟨z.property, hz⟩
    exact ⟨⟨x, hx⟩, (embedding.toMeetEmbedding_eq_iff old old ⟨x, hx⟩ z).2 entry⟩

theorem compressionTileCoding (old : MeetOrderCode P r μ)
    (embedding : MeetEmbeddingCode P P r r μ μ f)
    (T K : {x : ZFSet.{u} // x ∈ P}) (top : ∀ x, old.toMeetOrder.le x T)
    (range : ∀ z, (∃ x ∈ P, ZFSet.pair x z ∈ f) ↔ z ∈ P ∧ ZFSet.pair z K.val ∈ r) :
    CodedPrincipalTile old old
      (BinaryTiles.compression old.toMeetOrder T K top (compressionTileIso old embedding K range)) f where
  base_function := by
    have ideal : attachmentIdeal P r T.val = P := by
      apply ZFSet.ext
      intro x
      rw [mem_attachmentIdeal]
      exact ⟨And.left, fun hx => ⟨hx, top ⟨x, hx⟩⟩⟩
    change ZFSet.IsFunc (attachmentIdeal P r T.val) P f
    rw [ideal]
    exact embedding.injection.function
  base_entry x := embedding.value_entry x.val

theorem freshPart_of_top {T : ZFSet.{u}} (top : ∀ x ∈ P, ZFSet.pair x T ∈ r) :
    freshPart P r T = ∅ := by
  apply ZFSet.ext
  intro x
  rw [mem_freshPart]
  exact ⟨fun h => False.elim (h.2 (top x h.1)), fun h => False.elim (ZFSet.notMem_empty x h)⟩

theorem singleAttachmentOrder_empty (old : PartialOrderCode P r) (shadow : ZFSet.{u}) :
    singleAttachmentOrder P ∅ r r shadow ∅ = r := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (singleAttachmentOrder_shape _ _ _ _ _ _ hz)
    have cases := ((pair_mem_singleAttachmentOrder _ _ _ _ _ _ _ _).1 hz).2.2
    rcases cases with h | h | h | h
    · exact h.2.2
    · obtain ⟨_, q, hq, _⟩ := h
      exact False.elim (ZFSet.notMem_empty q hq)
    · exact False.elim (ZFSet.notMem_empty y h.2)
    · obtain ⟨q, hq, _⟩ := h
      exact False.elim (ZFSet.notMem_empty q hq)
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (old.relation hz)
    exact (pair_mem_singleAttachmentOrder _ _ _ _ _ _ _ _).2
      ⟨old_mem_taggedExtension hx, old_mem_taggedExtension hy, Or.inl ⟨hx, hy, hz⟩⟩

theorem compressionTile_exact_codes (old : MeetOrderCode P r μ)
    (embedding : MeetEmbeddingCode P P r r μ μ f)
    (T K : {x : ZFSet.{u} // x ∈ P}) (top : ∀ x, old.toMeetOrder.le x T)
    (range : ∀ z, (∃ x ∈ P, ZFSet.pair x z ∈ f) ↔ z ∈ P ∧ ZFSet.pair z K.val ∈ r) :
    let d := compressionTileCoding old embedding T K top range
    d.carrier = P ∧ d.order = r ∧ d.meetGraph = μ ∧
      attachmentTemplateEmbeddingGraph P P r f T.val = f := by
  have empty := freshPart_of_top (fun x hx => top ⟨x, hx⟩)
  have carrier : taggedExtension P (freshPart P r T.val) = P := by
    rw [empty]
    apply ZFSet.ext
    intro x
    rw [mem_taggedExtension]
    exact ⟨fun h => h.elim id (fun ⟨q, hq, _⟩ => False.elim (ZFSet.notMem_empty q hq)), Or.inl⟩
  have order : singleAttachmentOrder P (freshPart P r T.val) r r
      (attachmentShadowGraph P P μ f T.val) ∅ = r := by
    rw [empty]
    exact singleAttachmentOrder_empty old.order _
  refine ⟨carrier, order, ?_, ?_⟩
  · change canonicalMeetGraph (taggedExtension P (freshPart P r T.val))
      (singleAttachmentOrder P (freshPart P r T.val) r r (attachmentShadowGraph P P μ f T.val) ∅) = μ
    rw [carrier, order]
    exact old.eq_canonicalMeetGraph.symm
  · apply ZFSet.ext
    intro z
    rw [mem_attachmentTemplateEmbeddingGraph, empty]
    exact ⟨fun h => h.elim id (fun ⟨q, hq, _⟩ => False.elim (ZFSet.notMem_empty q hq)), Or.inl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem compressionTile_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (old : MeetOrderCode P r μ) (embedding : MeetEmbeddingCode P P r r μ μ f)
    (T K : {x : ZFSet.{u} // x ∈ P}) (top : ∀ x, old.toMeetOrder.le x T)
    (range : ∀ z, (∃ x ∈ P, ZFSet.pair x z ∈ f) ↔ z ∈ P ∧ ZFSet.pair z K.val ∈ r)
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hf : f ∈ M.sets) :
    let d := compressionTileCoding old embedding T K top range
    d.carrier ∈ M.sets ∧ d.order ∈ M.sets ∧ d.meetGraph ∈ M.sets ∧
      attachmentOldEmbeddingGraph P ∈ M.sets ∧
      attachmentTemplateEmbeddingGraph P P r f T.val ∈ M.sets :=
  (compressionTileCoding old embedding T K top range).ground_codes M
    pairing unions powers separation hP hP hr hr hμ hf

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open Compression Compression.RecursiveMaps SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

theorem requested_compression_map {i f k : ZFSet.{u}}
    (map : ZFSet.pair (ZFSet.pair (natSetCode 0) i) f ∈ completion.externalMaps)
    (cap : ZFSet.pair (ZFSet.pair (natSetCode 0) i) k ∈ completion.externalCaps) :
    f ∈ M.sets ∧ k ∈ completion.algebra.union.fields 0 ∧
      MeetEmbeddingCode (completion.algebra.union.fields 0) (completion.algebra.union.fields 0)
        (completion.algebra.union.fields 1) (completion.algebra.union.fields 1)
        (completion.algebra.union.fields 2) (completion.algebra.union.fields 2) f ∧
      ∀ x, (∃ y ∈ completion.algebra.union.fields 0, ZFSet.pair y x ∈ f) ↔
        x ∈ completion.algebra.union.fields 0 ∧ ZFSet.pair x k ∈ completion.algebra.union.fields 1 := by
  have entry := ((completion.external_fields_entries i f k).1).1 map
  have capEntry := ((completion.external_fields_entries i f k).2).1 cap
  have hPair := M.transitive completion.algebra.ground entry
  have hf := M.transitive (M.transitive hPair (ZFSet.mem_pair.2 (Or.inr rfl)))
    (ZFSet.mem_pair.2 (Or.inr rfl))
  exact ⟨hf, (ZFSet.pair_mem_prod.1 (completion.caps_function.1 capEntry)).2,
    completion.external_fields_range map cap⟩

theorem requested_compression_tile
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {i f k : ZFSet.{u}}
    (map : ZFSet.pair (ZFSet.pair (natSetCode 0) i) f ∈ completion.externalMaps)
    (cap : ZFSet.pair (ZFSet.pair (natSetCode 0) i) k ∈ completion.externalCaps) :
    let U := completion.algebra.union.fields 0
    let order := completion.algebra.union.meet.toMeetOrder
    ∃ hk : k ∈ U, ∃ iso : MeetIso order (Attachment.idealOrder order ⟨k, hk⟩),
      ∃ d : CodedPrincipalTile completion.algebra.union.meet completion.algebra.union.meet
        (BinaryTiles.compression order ⟨τ, completion.top_mem⟩ ⟨k, hk⟩
          (fun x => completion.top x.val x.property) iso) f,
        d.carrier = U ∧ d.order = completion.algebra.union.fields 1 ∧
        d.meetGraph = completion.algebra.union.fields 2 ∧
        attachmentTemplateEmbeddingGraph U U (completion.algebra.union.fields 1) f τ = f ∧
        d.carrier ∈ M.sets ∧ d.order ∈ M.sets ∧ d.meetGraph ∈ M.sets ∧
        attachmentOldEmbeddingGraph U ∈ M.sets ∧ f ∈ M.sets := by
  dsimp only
  obtain ⟨hf, hk, embedding, range⟩ := completion.requested_compression_map map cap
  let topPoint : {x : ZFSet.{u} // x ∈ completion.algebra.union.fields 0} := ⟨τ, completion.top_mem⟩
  let capPoint : {x : ZFSet.{u} // x ∈ completion.algebra.union.fields 0} := ⟨k, hk⟩
  have top : ∀ x, completion.algebra.union.meet.toMeetOrder.le x topPoint :=
    fun x => completion.top x.val x.property
  let iso := compressionTileIso completion.algebra.union.meet embedding capPoint range
  let d := compressionTileCoding completion.algebra.union.meet embedding topPoint capPoint top range
  have exactCodes := compressionTile_exact_codes completion.algebra.union.meet embedding topPoint capPoint top range
  have grounds := M.compressionTile_ground pairing unions powers separation completion.algebra.union.meet
    embedding topPoint capPoint top range (completion.algebra.union.ground 0)
    (completion.algebra.union.ground 1) (completion.algebra.union.ground 2) hf
  exact ⟨hk, iso, d, exactCodes.1, exactCodes.2.1, exactCodes.2.2.1, exactCodes.2.2.2,
    grounds.1, grounds.2.1, grounds.2.2.1, grounds.2.2.2.1, hf⟩

end PartitionPilot.Forcing.GroundCompressionCompletion

end

end OAI
