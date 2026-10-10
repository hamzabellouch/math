import OAI.SetTheory.PartitionPrinciple.Definability.BatchAttachmentRealization
import OAI.SetTheory.PartitionPrinciple.Forcing.TaskTransportCodes

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem literalTask_fresh_iff {I P R U Labels r a c base s F label q : ZFSet.{u}}
    (ha : a ∈ P) (hc : c ∈ P) (hb : base ∈ R) (hs : s ∈ P)
    (hF : F ∈ U) (hl : label ∈ Labels) :
    ZFSet.pair (literalTaskCode a c base s F label) q ∈
      indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
        (literalTaskSourceGraph I P R U Labels) ↔
      literalTaskCode a c base s F label ∈ I ∧ q ∈ P ∧ ZFSet.pair q a ∉ r := by
  rw [pair_mem_indexedAttachmentFresh]
  constructor
  · rintro ⟨hi, Q, r', a', eQ, er, ea, hq, fresh⟩
    obtain rfl := ((pair_mem_constantFamilyGraph I P _ Q).1 eQ).2
    obtain rfl := ((pair_mem_constantFamilyGraph I r _ r').1 er).2
    obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 ea).2
    exact ⟨hi, hq, fresh⟩
  · rintro ⟨hi, hq, fresh⟩
    exact ⟨hi, P, r, a, (pair_mem_constantFamilyGraph I P _ P).2 ⟨hi, rfl⟩,
      (pair_mem_constantFamilyGraph I r _ r).2 ⟨hi, rfl⟩,
      (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).2 ⟨hi, rfl⟩, hq, fresh⟩

theorem literalTask_shadow_iff {I P R U Labels μ a c base s F label q x : ZFSet.{u}}
    (ha : a ∈ P) (hc : c ∈ P) (hb : base ∈ R) (hs : s ∈ P)
    (hF : F ∈ U) (hl : label ∈ Labels) :
    ZFSet.pair (ZFSet.pair (literalTaskCode a c base s F label) q) x ∈
      batchAttachmentShadowGraph I P (constantFamilyGraph I P) (constantFamilyGraph I μ)
        (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) ↔
      literalTaskCode a c base s F label ∈ I ∧
        ZFSet.pair q x ∈ attachmentShadowGraph P P μ base a := by
  rw [pair_mem_batchAttachmentShadowGraph]
  constructor
  · rintro ⟨hi, Q, μ', a', base', eQ, eμ, ea, eb, entry⟩
    obtain rfl := ((pair_mem_constantFamilyGraph I P _ Q).1 eQ).2
    obtain rfl := ((pair_mem_constantFamilyGraph I μ _ μ').1 eμ).2
    obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 ea).2
    obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 2).1 eb).2
    exact ⟨hi, entry⟩
  · rintro ⟨hi, entry⟩
    exact ⟨hi, P, μ, a, base,
      (pair_mem_constantFamilyGraph I P _ P).2 ⟨hi, rfl⟩,
      (pair_mem_constantFamilyGraph I μ _ μ).2 ⟨hi, rfl⟩,
      (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).2 ⟨hi, rfl⟩,
      (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 2).2 ⟨hi, rfl⟩, entry⟩

theorem literalTask_upper_iff {I P R U Labels a c base s F label q x : ZFSet.{u}}
    (ha : a ∈ P) (hc : c ∈ P) (hb : base ∈ R) (hs : s ∈ P)
    (hF : F ∈ U) (hl : label ∈ Labels) :
    ZFSet.pair (ZFSet.pair (literalTaskCode a c base s F label) q) x ∈
      batchAttachmentUpperGraph I P (constantFamilyGraph I P)
        (literalTaskFilterGraph I P R U Labels) ↔
      literalTaskCode a c base s F label ∈ I ∧ q ∈ P ∧ x ∈ P ∧ x ∈ F := by
  rw [pair_mem_batchAttachmentUpperGraph]
  constructor
  · rintro ⟨hi, hx, Q, F', eQ, eF, hq, upper⟩
    obtain rfl := ((pair_mem_constantFamilyGraph I P _ Q).1 eQ).2
    obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 4).1 eF).2
    exact ⟨hi, hq, hx, upper⟩
  · rintro ⟨hi, hq, hx, upper⟩
    exact ⟨hi, hx, P, F, (pair_mem_constantFamilyGraph I P _ P).2 ⟨hi, rfl⟩,
      (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 4).2 ⟨hi, rfl⟩, hq, upper⟩

theorem constantTask_inside_iff (I P r t q s v : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair t q) (ZFSet.pair s v) ∈
      batchAttachmentInsideGraph I (constantFamilyGraph I P) (constantFamilyGraph I r) ↔
      t = s ∧ t ∈ I ∧ q ∈ P ∧ v ∈ P ∧ ZFSet.pair q v ∈ r := by
  rw [pair_mem_batchAttachmentInsideGraph]
  constructor
  · rintro ⟨equal, ht, Q, r', eQ, er, hq, hv, lower⟩
    obtain rfl := ((pair_mem_constantFamilyGraph I P t Q).1 eQ).2
    obtain rfl := ((pair_mem_constantFamilyGraph I r t r').1 er).2
    exact ⟨equal, ht, hq, hv, lower⟩
  · rintro ⟨equal, ht, hq, hv, lower⟩
    exact ⟨equal, ht, P, r, (pair_mem_constantFamilyGraph I P t P).2 ⟨ht, rfl⟩,
      (pair_mem_constantFamilyGraph I r t r).2 ⟨ht, rfl⟩, hq, hv, lower⟩

namespace TaskTransportCode

variable {I P R U Labels A g t t' : ZFSet.{u}}
variable (transport : TaskTransportCode P R U Labels A g t t')
include transport

theorem source_eq {a a' : ZFSet.{u}}
    (first : ZFSet.pair t a ∈ literalTaskSourceGraph I P R U Labels)
    (second : ZFSet.pair t' a' ∈ literalTaskSourceGraph I P R U Labels) : a = a' := by
  obtain ⟨b, hb, c, hc, base, hbase, s, hs, F, hF, label, hl,
    c', hc', base', hbase', s', hs', F', hF', rfl, rfl, _⟩ := transport
  have left := ((literalTaskFieldGraph_entry_iff hb hc hbase hs hF hl 0).1 first).2
  have right := ((literalTaskFieldGraph_entry_iff hb hc' hbase' hs' hF' hl 0).1 second).2
  exact left.trans right.symm

theorem label_eq {label label' : ZFSet.{u}}
    (first : ZFSet.pair t label ∈ literalTaskLabelGraph I P R U Labels)
    (second : ZFSet.pair t' label' ∈ literalTaskLabelGraph I P R U Labels) : label = label' := by
  obtain ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, l, hl,
    c', hc', base', hbase', s', hs', F', hF', rfl, rfl, _⟩ := transport
  have left := ((literalTaskFieldGraph_entry_iff ha hc hbase hs hF hl 5).1 first).2
  have right := ((literalTaskFieldGraph_entry_iff ha hc' hbase' hs' hF' hl 5).1 second).2
  exact left.trans right.symm

theorem base_eq {base base' : ZFSet.{u}}
    (first : ZFSet.pair t base ∈ literalTaskBaseGraph I P R U Labels)
    (second : ZFSet.pair t' base' ∈ literalTaskBaseGraph I P R U Labels) :
    base' = actionPostcompose P A g base := by
  obtain ⟨a, ha, c, hc, b, hb, s, hs, F, hF, label, hl,
    c', hc', b', hb', s', hs', F', hF', rfl, rfl, _, _, equal, _⟩ := transport
  have left := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 2).1 first).2
  have right := ((literalTaskFieldGraph_entry_iff ha hc' hb' hs' hF' hl 2).1 second).2
  exact right.trans (equal.trans (congrArg (actionPostcompose P A g) left.symm))

theorem filter_eq {F F' : ZFSet.{u}}
    (first : ZFSet.pair t F ∈ literalTaskFilterGraph I P R U Labels)
    (second : ZFSet.pair t' F' ∈ literalTaskFilterGraph I P R U Labels) :
    F' = actionImage P A g F := by
  obtain ⟨a, ha, c, hc, base, hb, s, hs, J, hJ, label, hl,
    c', hc', base', hb', s', hs', J', hJ', rfl, rfl, _, _, _, equal⟩ := transport
  have left := ((literalTaskFieldGraph_entry_iff ha hc hb hs hJ hl 4).1 first).2
  have right := ((literalTaskFieldGraph_entry_iff ha hc' hb' hs' hJ' hl 4).1 second).2
  exact right.trans (equal.trans (congrArg (actionImage P A g) left.symm))

theorem fresh_iff {r q : ZFSet.{u}} (ht : t ∈ I) (ht' : t' ∈ I) :
    ZFSet.pair t q ∈ indexedAttachmentFresh I (constantFamilyGraph I P)
      (constantFamilyGraph I r) (literalTaskSourceGraph I P R U Labels) ↔
    ZFSet.pair t' q ∈ indexedAttachmentFresh I (constantFamilyGraph I P)
      (constantFamilyGraph I r) (literalTaskSourceGraph I P R U Labels) := by
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F, hF, label, hl,
    c', hc', base', hb', s', hs', F', hF', rfl, rfl, _⟩ := transport
  rw [literalTask_fresh_iff ha hc hb hs hF hl,
    literalTask_fresh_iff ha hc' hb' hs' hF' hl]
  exact and_congr (iff_of_true ht ht') Iff.rfl

theorem shadow_covariant {G m e r μ q x x' : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (ht' : t' ∈ I)
    (shadow : ZFSet.pair (ZFSet.pair t q) x ∈
      batchAttachmentShadowGraph I P (constantFamilyGraph I P) (constantFamilyGraph I μ)
        (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels))
    (acted : ZFSet.pair (ZFSet.pair g x) x' ∈ A) :
    ZFSet.pair (ZFSet.pair t' q) x' ∈
      batchAttachmentShadowGraph I P (constantFamilyGraph I P) (constantFamilyGraph I μ)
        (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) := by
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F, hF, label, hl,
    c', hc', base', hb', s', hs', F', hF', rfl, rfl, _, _, equal, _⟩ := transport
  have old := ((literalTask_shadow_iff ha hc hb hs hF hl).1 shadow).2
  obtain ⟨hq, hx, b, hbp, meet, entry⟩ := (pair_mem_attachmentShadowGraph P P μ base a q x).1 old
  have hx' := (ZFSet.pair_mem_prod.1 (action.function.1 acted)).2
  apply (literalTask_shadow_iff ha hc' hb' hs' hF' hl).2
  refine ⟨ht', (pair_mem_attachmentShadowGraph P P μ base' a q x').2
    ⟨hq, hx', b, hbp, meet, ?_⟩⟩
  rw [equal]
  exact (pair_mem_actionPostcompose P A g base b x').2 ⟨hbp, hx', x, hx, entry, acted⟩

theorem upper_covariant {G m e r q x x' : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (ht' : t' ∈ I)
    (upper : ZFSet.pair (ZFSet.pair t q) x ∈
      batchAttachmentUpperGraph I P (constantFamilyGraph I P) (literalTaskFilterGraph I P R U Labels))
    (acted : ZFSet.pair (ZFSet.pair g x) x' ∈ A) :
    ZFSet.pair (ZFSet.pair t' q) x' ∈
      batchAttachmentUpperGraph I P (constantFamilyGraph I P) (literalTaskFilterGraph I P R U Labels) := by
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F, hF, label, hl,
    c', hc', base', hb', s', hs', F', hF', rfl, rfl, _, _, _, equal⟩ := transport
  obtain ⟨_, hq, _, hxF⟩ := (literalTask_upper_iff ha hc hb hs hF hl).1 upper
  have hx' := (ZFSet.pair_mem_prod.1 (action.function.1 acted)).2
  apply (literalTask_upper_iff ha hc' hb' hs' hF' hl).2
  refine ⟨ht', hq, hx', ?_⟩
  rw [equal]
  exact (mem_actionImage P A g F x').2 ⟨hx', x, hxF, acted⟩

theorem inside_covariant {G m e r s s' q v : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (hg : g ∈ G)
    (second : TaskTransportCode P R U Labels A g s s') (ht' : t' ∈ I)
    (inside : ZFSet.pair (ZFSet.pair t q) (ZFSet.pair s v) ∈
      batchAttachmentInsideGraph I (constantFamilyGraph I P) (constantFamilyGraph I r)) :
    ZFSet.pair (ZFSet.pair t' q) (ZFSet.pair s' v) ∈
      batchAttachmentInsideGraph I (constantFamilyGraph I P) (constantFamilyGraph I r) := by
  obtain ⟨equal, _, hq, hv, lower⟩ := (constantTask_inside_iff I P r t q s v).1 inside
  subst s
  exact (constantTask_inside_iff I P r t' q s' v).2
    ⟨TaskTransportCode.unique action hg transport second, ht', hq, hv, lower⟩

end TaskTransportCode

end PartitionPilot.Forcing

end

end OAI
