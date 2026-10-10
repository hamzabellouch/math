import OAI.SetTheory.PartitionPrinciple.Definability.BatchGraphSetFormulas
import OAI.SetTheory.PartitionPrinciple.Definability.CodedTemplateShadowLaws

namespace OAI

namespace PartitionPilot.Forcing.CodedTemplateAttachment
universe u v w
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

theorem encoded_embedding_order_iff {A r μ graph : ZFSet.{u}}
    (source : MeetOrderCode A r μ)
    (embedding : MeetEmbedding source.toMeetOrder b.extension)
    (function : ZFSet.IsFunc A d.carrier graph)
    (entries : ∀ x : {x : ZFSet.{u} // x ∈ A},
      ZFSet.pair x.val (d.encode (embedding.toFun x)) ∈ graph)
    {x y x' y' : ZFSet.{u}} (hx : ZFSet.pair x x' ∈ graph) (hy : ZFSet.pair y y' ∈ graph) :
    ZFSet.pair x' y' ∈ d.order ↔ ZFSet.pair x y ∈ r := by
  have hxA := (ZFSet.pair_mem_prod.1 (function.1 hx)).1
  have hyA := (ZFSet.pair_mem_prod.1 (function.1 hy)).1
  obtain ⟨w, _, uniqueX⟩ := function.2 x hxA
  obtain ⟨v, _, uniqueY⟩ := function.2 y hyA
  have eqX := (uniqueX x' hx).trans (uniqueX _ (entries ⟨x, hxA⟩)).symm
  have eqY := (uniqueY y' hy).trans (uniqueY _ (entries ⟨y, hyA⟩)).symm
  rw [eqX, eqY, d.le_encode]
  exact embedding.le_iff ⟨x, hxA⟩ ⟨y, hyA⟩

theorem encoded_embedding_code {A r μ graph : ZFSet.{u}}
    (source : MeetOrderCode A r μ)
    (embedding : MeetEmbedding source.toMeetOrder b.extension)
    (function : ZFSet.IsFunc A d.carrier graph)
    (entries : ∀ x : {x : ZFSet.{u} // x ∈ A},
      ZFSet.pair x.val (d.encode (embedding.toFun x)) ∈ graph) :
    MeetEmbeddingCode A d.carrier r d.order μ d.meetGraph graph := by
  refine ⟨⟨function, ?_⟩, ?_, ?_⟩
  · intro x y z hx hy
    have xA := (ZFSet.pair_mem_prod.1 (function.1 hx)).1
    have yA := (ZFSet.pair_mem_prod.1 (function.1 hy)).1
    have zL := (ZFSet.pair_mem_prod.1 (function.1 hx)).2
    have refl := d.partialOrder.refl z zL
    exact source.order.antisymm x xA y yA
      ((d.encoded_embedding_order_iff source embedding function entries hx hy).1 refl)
      ((d.encoded_embedding_order_iff source embedding function entries hy hx).1 refl)
  · intro x y x' y' lower hx hy
    exact (d.encoded_embedding_order_iff source embedding function entries hx hy).2 lower
  · intro x y z x' y' z' meet hx hy hz
    have hxA := (ZFSet.pair_mem_prod.1 (function.1 hx)).1
    have hyA := (ZFSet.pair_mem_prod.1 (function.1 hy)).1
    have hzA := (ZFSet.pair_mem_prod.1 (function.1 hz)).1
    let X : {x : ZFSet.{u} // x ∈ A} := ⟨x, hxA⟩
    let Y : {y : ZFSet.{u} // y ∈ A} := ⟨y, hyA⟩
    let Z : {z : ZFSet.{u} // z ∈ A} := ⟨z, hzA⟩
    have image_eq (t : {t : ZFSet.{u} // t ∈ A}) (v : ZFSet.{u})
        (entry : ZFSet.pair t.val v ∈ graph) : v = d.encode (embedding.toFun t) := by
      obtain ⟨w, _, unique⟩ := function.2 t.val t.property
      exact (unique v entry).trans (unique _ (entries t)).symm
    have meet_eq : source.toMeetOrder.meet X Y = Z := by
      apply Subtype.ext
      obtain ⟨w, _, unique⟩ := source.operation.2 (ZFSet.pair x y)
        (ZFSet.pair_mem_prod.2 ⟨hxA, hyA⟩)
      exact (unique _ (source.toMeetOrder_meet_entry X Y)).trans (unique z meet).symm
    have mapped : embedding.toFun Z =
        b.extension.meet (embedding.toFun X) (embedding.toFun Y) := by
      rw [← meet_eq]
      exact embedding.map_meet X Y
    rw [image_eq X x' hx, image_eq Y y' hy, image_eq Z z' hz, mapped]
    exact d.encoded_meet_entry (embedding.toFun X) (embedding.toFun Y)

theorem old_embedding_code :
    MeetEmbeddingCode P d.carrier r d.order μ d.meetGraph (attachmentOldEmbeddingGraph P) := by
  apply d.encoded_embedding_code old b.oldEmbedding
    (attachmentOldEmbeddingGraph_isFunc P N)
  intro p
  exact (pair_mem_attachmentOldEmbeddingGraph P p.val p.val).2 ⟨p.property, rfl⟩

end PartitionPilot.Forcing.CodedTemplateAttachment

namespace PartitionPilot.Forcing.AttachmentBatchInputs

universe u
variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
include d

theorem batch_template_graph_entry (i : {i : ZFSet.{u} // i ∈ I})
    (q : {q : ZFSet.{u} // q ∈ d.space i}) :
    ZFSet.pair q.val (d.coding.encode (d.templates.represent i q)) ∈
      batchTemplateGraph I P Qs rs As Es i.val := by
  classical
  apply (pair_mem_batchTemplateGraph I P Qs rs As Es i.val q.val _).2
  apply (d.batch_template_entry_iff i q.val _).2
  by_cases below : (d.fiber i).templateOrder.toMeetOrder.le q
      ⟨d.anchor i, (d.fiber i).anchor_mem⟩
  · rw [d.templates.represent_old i q below]
    exact Or.inl ((d.fiber i).baseMap_entry ⟨q, below⟩)
  · rw [d.templates.represent_new i q below]
    exact Or.inr ⟨(mem_freshPart _ _ _ _).2 ⟨q.property, below⟩, rfl⟩

theorem batch_template_graph_entry_iff (i : {i : ZFSet.{u} // i ∈ I})
    (q : {q : ZFSet.{u} // q ∈ d.space i}) (y : ZFSet.{u}) :
    ZFSet.pair q.val y ∈ batchTemplateGraph I P Qs rs As Es i.val ↔
      y = d.coding.encode (d.templates.represent i q) := by
  constructor
  · intro entry
    obtain ⟨v, _, unique⟩ := (d.batch_template_fiber_function i).2 q.val q.property
    exact (unique y entry).trans (unique _ (d.batch_template_graph_entry i q)).symm
  · intro equal
    exact equal.symm ▸ d.batch_template_graph_entry i q

theorem batch_template_embedding_code (i : {i : ZFSet.{u} // i ∈ I}) :
    MeetEmbeddingCode (d.space i) d.batchCarrier (d.rel i) d.batchOrder
      (d.meet i) d.batchMeetGraph (batchTemplateGraph I P Qs rs As Es i.val) :=
  d.coding.encoded_embedding_code (d.fiber i).templateOrder (d.templates.templateEmbedding i)
    (d.batch_template_fiber_function i) (d.batch_template_graph_entry i)

theorem batch_template_order_iff (i : {i : ZFSet.{u} // i ∈ I})
    {x y x' y' : ZFSet.{u}}
    (hx : ZFSet.pair x x' ∈ batchTemplateGraph I P Qs rs As Es i.val)
    (hy : ZFSet.pair y y' ∈ batchTemplateGraph I P Qs rs As Es i.val) :
    ZFSet.pair x' y' ∈ d.batchOrder ↔ ZFSet.pair x y ∈ d.rel i :=
  d.coding.encoded_embedding_order_iff (d.fiber i).templateOrder (d.templates.templateEmbedding i)
    (d.batch_template_fiber_function i) (d.batch_template_graph_entry i) hx hy

theorem batch_template_old_agreement (i : {i : ZFSet.{u} // i ∈ I})
    {q p : ZFSet.{u}} (entry : ZFSet.pair q p ∈ d.embed i) :
    ZFSet.pair q p ∈ batchTemplateGraph I P Qs rs As Es i.val ∧
      ZFSet.pair p p ∈ attachmentOldEmbeddingGraph P := by
  have shape := ZFSet.pair_mem_prod.1 ((d.fiber i).base_function.1 entry)
  exact ⟨(pair_mem_batchTemplateGraph I P Qs rs As Es i.val q p).2
    ((d.batch_template_entry_iff i q p).2 (Or.inl entry)),
    (pair_mem_attachmentOldEmbeddingGraph P p p).2 ⟨shape.2, rfl⟩⟩

end PartitionPilot.Forcing.AttachmentBatchInputs

namespace PartitionPilot.Forcing.AttachmentBatchInputs
universe u
variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

noncomputable def batchFreshNode (i : {i : ZFSet.{u} // i ∈ I}) {q : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i)) : d.templates.Fresh :=
  ⟨i, ⟨⟨q, ((mem_freshPart _ _ _ q).1 hq).1⟩, ((mem_freshPart _ _ _ q).1 hq).2⟩⟩

theorem batch_old_lower_iff (i : {i : ZFSet.{u} // i ∈ I}) {q s p : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i)) (hp : p ∈ P)
    (hs : ZFSet.pair (ZFSet.pair i.val q) s ∈ batchAttachmentShadowGraph I P Qs μs As Es) :
    ZFSet.pair p (ZFSet.pair P (ZFSet.pair i.val q)) ∈ d.batchOrder ↔ ZFSet.pair p s ∈ rP := by
  have eq := d.coding.shadow_value (d.batchFreshNode i hq) s hs
  rw [eq]
  exact d.coding.old_lower_iff ⟨p, hp⟩ (d.batchFreshNode i hq)

theorem batch_old_upper_iff (i : {i : ZFSet.{u} // i ∈ I}) {q p : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i)) (hp : p ∈ P) :
    ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q)) p ∈ d.batchOrder ↔ p ∈ d.filter i :=
  d.coding.old_upper_iff (d.batchFreshNode i hq) ⟨p, hp⟩

theorem batch_cross_lower_iff (i j : {i : ZFSet.{u} // i ∈ I}) {q t s : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i))
    (ht : t ∈ freshPart (d.space j) (d.rel j) (d.anchor j)) (different : i ≠ j)
    (hs : ZFSet.pair (ZFSet.pair j.val t) s ∈ batchAttachmentShadowGraph I P Qs μs As Es) :
    ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q)) (ZFSet.pair P (ZFSet.pair j.val t)) ∈
      d.batchOrder ↔ s ∈ d.filter i := by
  have eq := d.coding.shadow_value (d.batchFreshNode j ht) s hs
  rw [eq]
  exact d.coding.cross_lower_iff (d.batchFreshNode i hq) (d.batchFreshNode j ht) different

theorem batch_shadow_meet_code (i : {i : ZFSet.{u} // i ∈ I}) {q p s v : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i)) (hp : p ∈ P)
    (hs : ZFSet.pair (ZFSet.pair i.val q) s ∈ batchAttachmentShadowGraph I P Qs μs As Es)
    (oldMeet : ZFSet.pair (ZFSet.pair s p) v ∈ μP)
    (notAbove : ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q)) p ∉ d.batchOrder) :
    ZFSet.pair (ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q)) p) v ∈ d.batchMeetGraph := by
  let x := d.batchFreshNode i hq
  let y : {p : ZFSet.{u} // p ∈ P} := ⟨p, hp⟩
  have sameShadow := d.coding.shadow_value x s hs
  obtain ⟨m, _, unique⟩ := d.oldOrder.operation.2
    (ZFSet.pair (d.templates.shadow x).val p)
    (ZFSet.pair_mem_prod.2 ⟨(d.templates.shadow x).property, hp⟩)
  have sameMeet : v = (d.oldOrder.toMeetOrder.meet (d.templates.shadow x) y).val :=
    (unique v (sameShadow ▸ oldMeet)).trans
      (unique _ (d.oldOrder.toMeetOrder_meet_entry (d.templates.shadow x) y)).symm
  exact sameMeet.symm ▸ d.coding.encoded_shadow_meet x y notAbove

theorem batch_cross_meet_code (i j : {i : ZFSet.{u} // i ∈ I}) {q t s z v : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i))
    (ht : t ∈ freshPart (d.space j) (d.rel j) (d.anchor j)) (different : i ≠ j)
    (hs : ZFSet.pair (ZFSet.pair i.val q) s ∈ batchAttachmentShadowGraph I P Qs μs As Es)
    (hz : ZFSet.pair (ZFSet.pair j.val t) z ∈ batchAttachmentShadowGraph I P Qs μs As Es)
    (oldMeet : ZFSet.pair (ZFSet.pair s z) v ∈ μP)
    (notQT : ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q))
      (ZFSet.pair P (ZFSet.pair j.val t)) ∉ d.batchOrder)
    (notTQ : ZFSet.pair (ZFSet.pair P (ZFSet.pair j.val t))
      (ZFSet.pair P (ZFSet.pair i.val q)) ∉ d.batchOrder) :
    ZFSet.pair (ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q))
      (ZFSet.pair P (ZFSet.pair j.val t))) v ∈ d.batchMeetGraph := by
  let x := d.batchFreshNode i hq
  let y := d.batchFreshNode j ht
  have sameS := d.coding.shadow_value x s hs
  have sameZ := d.coding.shadow_value y z hz
  obtain ⟨m, _, unique⟩ := d.oldOrder.operation.2
    (ZFSet.pair (d.templates.shadow x).val (d.templates.shadow y).val)
    (ZFSet.pair_mem_prod.2 ⟨(d.templates.shadow x).property, (d.templates.shadow y).property⟩)
  have sameMeet : v = (d.oldOrder.toMeetOrder.meet (d.templates.shadow x) (d.templates.shadow y)).val :=
    (unique v (sameS ▸ sameZ ▸ oldMeet)).trans
      (unique _ (d.oldOrder.toMeetOrder_meet_entry (d.templates.shadow x) (d.templates.shadow y))).symm
  exact sameMeet.symm ▸ d.coding.encoded_cross_meet x y different notQT notTQ

end PartitionPilot.Forcing.AttachmentBatchInputs

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem batchAttachment_ground_codes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (hP : P ∈ M.sets) (hrP : rP ∈ M.sets) (hI : I ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets) :
    d.batchCarrier ∈ M.sets ∧ d.batchOrder ∈ M.sets ∧ d.batchMeetGraph ∈ M.sets ∧
      batchAttachmentShadowGraph I P Qs μs As Es ∈ M.sets ∧
      batchAttachmentTemplateGraph I P Qs rs As Es ∈ M.sets ∧
      attachmentOldEmbeddingGraph P ∈ M.sets := by
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  have inside := M.batchAttachmentInsideGraph_mem pairing unions powers separation hI hQs hrs
  have shadow := M.batchAttachmentShadowGraph_mem pairing unions powers separation hI hP hQs hμs hAs hEs
  have upper := M.batchAttachmentUpperGraph_mem pairing unions powers separation hI hP hQs hFs
  have order := M.codedAttachmentOrder_mem pairing unions powers separation hP hN hrP inside shadow upper
  exact ⟨hL, order, M.canonicalMeetGraph_mem pairing unions powers separation hL order,
    shadow, M.batchAttachmentTemplateGraph_mem pairing unions powers separation hI hP hQs hrs hAs hEs,
    M.attachmentOldEmbeddingGraph_mem pairing unions powers separation hP⟩

theorem exists_batchAttachment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (hP : P ∈ M.sets) (hrP : rP ∈ M.sets) (hI : I ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets)
    (_hSs : Ss ∈ M.sets) :
    ∃ L ∈ M.sets, ∃ r ∈ M.sets, ∃ μ ∈ M.sets, ∃ shadow ∈ M.sets,
      ∃ representation ∈ M.sets, ∃ oldMap ∈ M.sets,
      L = taggedExtension P (indexedAttachmentFresh I Qs rs As) ∧
      r = codedAttachmentOrder P (indexedAttachmentFresh I Qs rs As) rP
        (batchAttachmentInsideGraph I Qs rs) shadow (batchAttachmentUpperGraph I P Qs Fs) ∧
      μ = canonicalMeetGraph L r ∧
      shadow = batchAttachmentShadowGraph I P Qs μs As Es ∧
      representation = batchAttachmentTemplateGraph I P Qs rs As Es ∧
      oldMap = attachmentOldEmbeddingGraph P ∧
      MeetOrderCode L r μ ∧
      ZFSet.IsFunc (indexedAttachmentDomain I Qs) P shadow ∧
      ZFSet.IsFunc (indexedAttachmentDomain I Qs) L representation ∧
      MeetEmbeddingCode P L rP r μP μ oldMap ∧
      (∀ p ∈ P, ZFSet.pair p p ∈ oldMap) ∧
      (∀ i : {i : ZFSet.{u} // i ∈ I},
        batchTemplateGraph I P Qs rs As Es i.val ∈ M.sets ∧
        MeetEmbeddingCode (d.space i) L (d.rel i) r (d.meet i) μ
          (batchTemplateGraph I P Qs rs As Es i.val)) := by
  obtain ⟨hL, hr, hμ, hs, ht, ho⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation d hP hrP hI hQs hrs hμs hAs hEs hFs
  refine ⟨d.batchCarrier, hL, d.batchOrder, hr, d.batchMeetGraph, hμ,
    batchAttachmentShadowGraph I P Qs μs As Es, hs,
    batchAttachmentTemplateGraph I P Qs rs As Es, ht,
    attachmentOldEmbeddingGraph P, ho, rfl, rfl, rfl, rfl, rfl, rfl,
    d.batch_meetOrder, d.batch_shadow_function, d.batch_template_function,
    d.coding.old_embedding_code,
    (fun p hp => (pair_mem_attachmentOldEmbeddingGraph P p p).2 ⟨hp, rfl⟩), ?_⟩
  intro i
  exact ⟨M.batchTemplateGraph_mem pairing unions powers separation
    hI hP hQs hrs hAs hEs (M.transitive hI i.property), d.batch_template_embedding_code i⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
