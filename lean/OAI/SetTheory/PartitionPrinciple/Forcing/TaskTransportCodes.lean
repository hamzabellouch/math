import OAI.SetTheory.PartitionPrinciple.Definability.CodedFilterImages
import OAI.SetTheory.PartitionPrinciple.Definability.TaskRepresentativeCodes

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem EligibleTaskCode.transport {P G r μ A a c base s F m inv e δ c' s' : ZFSet.{u}}
    (code : EligibleTaskCode P G r μ A a c base s F)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hδ : δ ∈ G)
    (target : ZFSet.pair (ZFSet.pair δ c) c' ∈ A)
    (separator : ZFSet.pair (ZFSet.pair δ s) s' ∈ A) :
    EligibleTaskCode P G r μ A a c' (actionPostcompose P A δ base) s' (actionImage P A δ F) := by
  refine ⟨code.source_mem, (ZFSet.pair_mem_prod.1 (action.function.1 target)).2,
    (ZFSet.pair_mem_prod.1 (action.function.1 separator)).2,
    actionImage_filter group action meet hδ code.filter,
    (action.raw_order_iff group meet.order hδ target separator).2 code.lower,
    fun h => code.strict ((action.raw_order_iff group meet.order hδ separator target).1 h),
    actionImage_lower_bound action code.filter.subset hδ code.separator_mem separator code.upper, ?_⟩
  obtain ⟨g, hg, represented⟩ := code.representative
  obtain ⟨k, product, _⟩ := group.mul_function.2 (ZFSet.pair δ g) (ZFSet.pair_mem_prod.2 ⟨hδ, hg⟩)
  have hk := (ZFSet.pair_mem_prod.1 (group.mul_function.1 product)).2
  exact ⟨k, hk, represented.transport action hg hδ hk product target⟩

def TaskTransportCode (P R U Labels A g t t' : ZFSet.{u}) : Prop :=
  ∃ a ∈ P, ∃ c ∈ P, ∃ base ∈ R, ∃ s ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
    ∃ c' ∈ P, ∃ base' ∈ R, ∃ s' ∈ P, ∃ F' ∈ U,
      t = literalTaskCode a c base s F label ∧
      t' = literalTaskCode a c' base' s' F' label ∧
      ZFSet.pair (ZFSet.pair g c) c' ∈ A ∧ ZFSet.pair (ZFSet.pair g s) s' ∈ A ∧
      base' = actionPostcompose P A g base ∧ F' = actionImage P A g F

theorem TaskTransportCode.unique {G P m e r A R U Labels g t t' t'' : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (hg : g ∈ G)
    (first : TaskTransportCode P R U Labels A g t t')
    (second : TaskTransportCode P R U Labels A g t t'') : t' = t'' := by
  obtain ⟨a, _, c, hc, base, _, s, hs, F, _, label, _, c', _, base', _, s', _, F', _,
    old, new, target, separator, baseEq, filterEq⟩ := first
  obtain ⟨b, _, d, _, ell, _, v, _, J, _, tag, _, d', _, ell', _, v', _, J', _,
    old', new', target', separator', baseEq', filterEq'⟩ := second
  obtain ⟨ha, hd, hell, hv, hJ, htag⟩ := literalTaskCode_inj.1 (old.symm.trans old')
  subst b d ell v J tag
  obtain ⟨w, _, uniqueC⟩ := action.function.2 (ZFSet.pair g c) (ZFSet.pair_mem_prod.2 ⟨hg, hc⟩)
  obtain ⟨v, _, uniqueS⟩ := action.function.2 (ZFSet.pair g s) (ZFSet.pair_mem_prod.2 ⟨hg, hs⟩)
  have hc' := (uniqueC c' target).trans (uniqueC d' target').symm
  have hs' := (uniqueS s' separator).trans (uniqueS v' separator').symm
  rw [new, new', hc', hs', baseEq, baseEq', filterEq, filterEq']

theorem TaskTransportCode.one {G P m e r A R U Labels t : ZFSet.{u}}
    (action : PosetActionCode G P m e r A)
    (shape : ∀ base ∈ R, base ⊆ ZFSet.prod P P) (subsets : ∀ F ∈ U, F ⊆ P)
    (ht : t ∈ literalTaskBound P R U Labels) : TaskTransportCode P R U Labels A e t t := by
  obtain ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel, rfl⟩ :=
    (mem_literalTaskBound P R U Labels t).1 ht
  exact ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel,
    c, hc, base, hbase, s, hs, F, hF, rfl, rfl, action.one c hc, action.one s hs,
    (actionPostcompose_one action (shape base hbase)).symm,
    (actionImage_one action (subsets F hF)).symm⟩

theorem TaskTransportCode.mul {G P m e r A R U Labels g h k t t' t'' : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (subsets : ∀ F ∈ U, F ⊆ P)
    (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m)
    (first : TaskTransportCode P R U Labels A h t t')
    (second : TaskTransportCode P R U Labels A g t' t'') :
    TaskTransportCode P R U Labels A k t t'' := by
  obtain ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel,
    c', hc', base', _, s', hs', F', _, old, middle, target, separator, baseEq, filterEq⟩ := first
  obtain ⟨b, _, d, _, ell, _, v, _, J, _, tag, _,
    d', hd', ell', hell', v', hv', J', hJ', middle', new, target', separator', baseEq', filterEq'⟩ := second
  obtain ⟨ha', hd, hell, hv, hJ, htag⟩ := literalTaskCode_inj.1 (middle.symm.trans middle')
  subst b d ell v J tag
  refine ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel,
    d', hd', ell', hell', v', hv', J', hJ', old, new,
    action.mul g hg h hh k hk c hc c' hc' d' hd' product target target',
    action.mul g hg h hh k hk s hs s' hs' v' hv' product separator separator', ?_, ?_⟩
  · rw [baseEq', baseEq, actionPostcompose_mul action hg hh hk product]
  · rw [filterEq', filterEq, actionImage_mul action (subsets F hF) hg hh hk product]

noncomputable def taskTransportGraph (G I P R U Labels A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ g ∈ G, ∃ t ∈ I, ∃ t' ∈ I,
    z = ZFSet.pair (ZFSet.pair g t) t' ∧ TaskTransportCode P R U Labels A g t t')
    (ZFSet.prod (ZFSet.prod G I) I)

theorem taskTransportGraph_subset (G I P R U Labels A : ZFSet.{u}) :
    taskTransportGraph G I P R U Labels A ⊆ ZFSet.prod (ZFSet.prod G I) I :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem triple_mem_taskTransportGraph (G I P R U Labels A g t t' : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g t) t' ∈ taskTransportGraph G I P R U Labels A ↔
      g ∈ G ∧ t ∈ I ∧ t' ∈ I ∧ TaskTransportCode P R U Labels A g t t' := by
  rw [taskTransportGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, g', hg, s, hs, s', hs', equal, transported⟩
    obtain ⟨pairEq, last⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨first, middle⟩ := ZFSet.pair_inj.1 pairEq
    subst g' s s'
    exact ⟨hg, hs, hs', transported⟩
  · rintro ⟨hg, ht, ht', transported⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, ht⟩, ht'⟩,
      g, hg, t, ht, t', ht', rfl, transported⟩

theorem taskTransportGraph_function {G I P R U Labels A m e r : ZFSet.{u}}
    (action : PosetActionCode G P m e r A)
    (total : ∀ g ∈ G, ∀ t ∈ I, ∃ t' ∈ I, TaskTransportCode P R U Labels A g t t') :
    ZFSet.IsFunc (ZFSet.prod G I) I (taskTransportGraph G I P R U Labels A) := by
  refine ⟨taskTransportGraph_subset G I P R U Labels A, ?_⟩
  intro v hv
  obtain ⟨g, hg, t, ht, rfl⟩ := ZFSet.mem_prod.1 hv
  obtain ⟨t', ht', transported⟩ := total g hg t ht
  refine ⟨t', (triple_mem_taskTransportGraph G I P R U Labels A g t t').2
    ⟨hg, ht, ht', transported⟩, ?_⟩
  intro t'' entry
  have parts := (triple_mem_taskTransportGraph G I P R U Labels A g t t'').1 entry
  exact TaskTransportCode.unique action hg parts.2.2.2 transported

theorem taskTransportGraph_one {G I P R U Labels A m e r : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (he : e ∈ G)
    (shape : ∀ base ∈ R, base ⊆ ZFSet.prod P P) (subsets : ∀ F ∈ U, F ⊆ P)
    (bound : I ⊆ literalTaskBound P R U Labels) :
    ∀ t ∈ I, ZFSet.pair (ZFSet.pair e t) t ∈ taskTransportGraph G I P R U Labels A := by
  intro t ht
  exact (triple_mem_taskTransportGraph G I P R U Labels A e t t).2
    ⟨he, ht, ht, TaskTransportCode.one action shape subsets (bound ht)⟩

theorem taskTransportGraph_mul {G I P R U Labels A m e r : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (subsets : ∀ F ∈ U, F ⊆ P)
    {g h k t t' t'' : ZFSet.{u}} (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m)
    (first : ZFSet.pair (ZFSet.pair h t) t' ∈ taskTransportGraph G I P R U Labels A)
    (second : ZFSet.pair (ZFSet.pair g t') t'' ∈ taskTransportGraph G I P R U Labels A) :
    ZFSet.pair (ZFSet.pair k t) t'' ∈ taskTransportGraph G I P R U Labels A := by
  have parts := (triple_mem_taskTransportGraph G I P R U Labels A h t t').1 first
  have parts' := (triple_mem_taskTransportGraph G I P R U Labels A g t' t'').1 second
  exact (triple_mem_taskTransportGraph G I P R U Labels A k t t'').2
    ⟨hk, parts.2.1, parts'.2.2.1,
      TaskTransportCode.mul action subsets hg hh hk product parts.2.2.2 parts'.2.2.2⟩

end PartitionPilot.Forcing

end

end OAI
