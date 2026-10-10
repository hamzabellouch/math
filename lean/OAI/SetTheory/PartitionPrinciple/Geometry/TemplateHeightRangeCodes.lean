import OAI.SetTheory.PartitionPrinciple.Definability.IntervalSequenceFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundSingleAttachment

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

structure TemplateHeightFamilyInputs
    {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (Vs vrs Hs : ZFSet.{u}) : Prop where
  ranges : FunctionGraphOn I Vs
  orders : FunctionGraphOn I vrs
  heights : FunctionGraphOn I Hs
  linear : ∀ i, StrictLinearOrderCode (ranges.value i) (orders.value i)
  function : ∀ i, ZFSet.IsFunc (d.space i) (ranges.value i) (heights.value i)
  strict : ∀ i x y a b, ZFSet.pair x y ∈ d.rel i → x ≠ y →
    ZFSet.pair x a ∈ heights.value i → ZFSet.pair y b ∈ heights.value i →
      ZFSet.pair a b ∈ orders.value i

noncomputable def componentHeightGraph (I Qs B Hs Cs E C D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => ∃ i ∈ I, ∃ Q ∈ ⋃₀ ⋃₀ Qs, ∃ g ∈ ⋃₀ ⋃₀ Hs, ∃ f ∈ ⋃₀ ⋃₀ E,
    ∃ q ∈ Q, ∃ a ∈ B, ∃ c ∈ C, ∃ z ∈ D,
      w = ZFSet.pair (ZFSet.pair i q) (ZFSet.pair c z) ∧
      ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i g ∈ Hs ∧ ZFSet.pair i f ∈ E ∧
      ZFSet.pair i c ∈ Cs ∧ ZFSet.pair q a ∈ g ∧ ZFSet.pair a z ∈ f)
    (ZFSet.prod (indexedAttachmentDomain I Qs) (ZFSet.prod C D))

theorem componentHeightGraph_shape (I Qs B Hs Cs E C D : ZFSet.{u}) :
    componentHeightGraph I Qs B Hs Cs E C D ⊆
      ZFSet.prod (indexedAttachmentDomain I Qs) (ZFSet.prod C D) :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem pair_mem_componentHeightGraph (I Qs B Hs Cs E C D i q c z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i q) (ZFSet.pair c z) ∈ componentHeightGraph I Qs B Hs Cs E C D ↔
      i ∈ I ∧ c ∈ C ∧ z ∈ D ∧ ∃ Q g f, ZFSet.pair i Q ∈ Qs ∧
        ZFSet.pair i g ∈ Hs ∧ ZFSet.pair i f ∈ E ∧ q ∈ Q ∧ ZFSet.pair i c ∈ Cs ∧
        ∃ a ∈ B, ZFSet.pair q a ∈ g ∧ ZFSet.pair a z ∈ f := by
  constructor
  · intro member
    obtain ⟨j, hj, Q, _, g, _, f, _, u, hu, a, ha, b, hb, v, hv,
      equal, eQ, eg, ef, ec, height, image⟩ := (ZFSet.mem_sep.1 member).2
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 right
    exact ⟨hj, hb, hv, Q, g, f, eQ, eg, ef, hu, ec, a, ha, height, image⟩
  · rintro ⟨hi, hc, hz, Q, g, f, eQ, eg, ef, hq, ec, a, ha, height, image⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain I Qs i q).2 ⟨hi, Q, eQ, hq⟩,
        ZFSet.pair_mem_prod.2 ⟨hc, hz⟩⟩,
      i, hi, Q, pair_second_mem_doubleUnion eQ, g, pair_second_mem_doubleUnion eg,
      f, pair_second_mem_doubleUnion ef, q, hq, a, ha, c, hc, z, hz,
      rfl, eQ, eg, ef, ec, height, image⟩

namespace TemplateHeightFamilyInputs

variable {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs B Cs E C D : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (t : TemplateHeightFamilyInputs d Vs vrs Hs)

theorem componentHeightGraph_entry_iff (embeddings : FunctionGraphOn I E)
    (i : {i : ZFSet.{u} // i ∈ I}) (q c z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) (ZFSet.pair c z) ∈ componentHeightGraph I Qs B Hs Cs E C D ↔
      q ∈ d.space i ∧ c ∈ C ∧ z ∈ D ∧ ZFSet.pair i.val c ∈ Cs ∧
        ∃ a ∈ B, ZFSet.pair q a ∈ t.heights.value i ∧ ZFSet.pair a z ∈ embeddings.value i := by
  rw [pair_mem_componentHeightGraph]
  constructor
  · rintro ⟨_, hc, hz, Q, g, f, eQ, eg, ef, hq, ec, a, ha, height, image⟩
    have eqQ := d.spaces.unique eQ (d.space_entry i)
    have eqg := t.heights.unique eg (t.heights.value_entry i)
    have eqf := embeddings.unique ef (embeddings.value_entry i)
    exact ⟨eqQ ▸ hq, hc, hz, ec, a, ha, eqg ▸ height, eqf ▸ image⟩
  · rintro ⟨hq, hc, hz, ec, a, ha, height, image⟩
    exact ⟨i.property, hc, hz, d.space i, t.heights.value i, embeddings.value i,
      d.space_entry i, t.heights.value_entry i, embeddings.value_entry i,
      hq, ec, a, ha, height, image⟩

theorem componentHeightGraph_function
    (columns : ZFSet.IsFunc I C Cs) (embeddings : FunctionGraphOn I E)
    (maps : ∀ i, ZFSet.IsFunc (t.ranges.value i) D (embeddings.value i))
    (bounds : ∀ i, t.ranges.value i ⊆ B) :
    ZFSet.IsFunc (indexedAttachmentDomain I Qs) (ZFSet.prod C D)
      (componentHeightGraph I Qs B Hs Cs E C D) := by
  refine ⟨componentHeightGraph_shape I Qs B Hs Cs E C D, ?_⟩
  intro x hx
  obtain ⟨i, hi, q, rfl, Q, eQ, hq⟩ := (mem_indexedAttachmentDomain I Qs x).1 hx
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have qQ : q ∈ d.space j := d.spaces.unique eQ (d.space_entry j) ▸ hq
  obtain ⟨a, height, uniqueA⟩ := (t.function j).2 q qQ
  have aV := (ZFSet.pair_mem_prod.1 ((t.function j).1 height)).2
  obtain ⟨z, image, uniqueZ⟩ := (maps j).2 a aV
  have zD := (ZFSet.pair_mem_prod.1 ((maps j).1 image)).2
  obtain ⟨c, column, uniqueC⟩ := columns.2 i hi
  have cC := (ZFSet.pair_mem_prod.1 (columns.1 column)).2
  refine ⟨ZFSet.pair c z, (t.componentHeightGraph_entry_iff embeddings j q c z).2
    ⟨qQ, cC, zD, column, a, bounds j aV, height, image⟩, ?_⟩
  intro y entry
  have shape := ZFSet.pair_mem_prod.1 (componentHeightGraph_shape I Qs B Hs Cs E C D entry)
  obtain ⟨c', _, z', _, rfl⟩ := ZFSet.mem_prod.1 shape.2
  obtain ⟨_, _, _, column', a', _, height', image'⟩ :=
    (t.componentHeightGraph_entry_iff embeddings j q c' z').1 entry
  have equalA := uniqueA a' height'
  exact congrArg₂ ZFSet.pair (uniqueC c' column') (uniqueZ z' (equalA ▸ image'))

end TemplateHeightFamilyInputs

noncomputable def taggedHeightGraph (P N H old fresh : ZFSet.{u}) : ZFSet.{u} :=
  old ∪ ZFSet.sep (fun w => ∃ x ∈ N, ∃ h ∈ H,
    w = ZFSet.pair (ZFSet.pair P x) h ∧ ZFSet.pair x h ∈ fresh)
    (ZFSet.prod (taggedExtension P N) H)

theorem taggedHeightGraph_old_entry {P N H old fresh x h : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair x h ∈ taggedHeightGraph P N H old fresh ↔ ZFSet.pair x h ∈ old := by
  constructor
  · intro member
    rcases ZFSet.mem_union.1 member with member | member
    · exact member
    · obtain ⟨q, _, v, _, equal, _⟩ := (ZFSet.mem_sep.1 member).2
      exact False.elim (pair_tag_not_mem P q ((ZFSet.pair_inj.1 equal).1 ▸ hx))
  · exact fun member => ZFSet.mem_union.2 (Or.inl member)

theorem taggedHeightGraph_fresh_entry {P N H old fresh x h : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P H old) (freshFunction : ZFSet.IsFunc N H fresh) :
    ZFSet.pair (ZFSet.pair P x) h ∈ taggedHeightGraph P N H old fresh ↔
      ZFSet.pair x h ∈ fresh := by
  constructor
  · intro member
    rcases ZFSet.mem_union.1 member with member | member
    · exact False.elim (pair_tag_not_mem P x (ZFSet.pair_mem_prod.1 (oldFunction.1 member)).1)
    · obtain ⟨q, _, v, _, equal, entry⟩ := (ZFSet.mem_sep.1 member).2
      obtain ⟨left, rfl⟩ := ZFSet.pair_inj.1 equal
      exact (ZFSet.pair_inj.1 left).2.symm ▸ entry
  · intro entry
    have shape := ZFSet.pair_mem_prod.1 (freshFunction.1 entry)
    exact ZFSet.mem_union.2 (Or.inr (ZFSet.mem_sep.2
      ⟨ZFSet.pair_mem_prod.2 ⟨pair_mem_taggedExtension.2 shape.1, shape.2⟩,
        x, shape.1, h, shape.2, rfl, entry⟩))

theorem taggedHeightGraph_function {P N H old fresh : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P H old) (freshFunction : ZFSet.IsFunc N H fresh) :
    ZFSet.IsFunc (taggedExtension P N) H (taggedHeightGraph P N H old fresh) := by
  refine ⟨?_, ?_⟩
  · intro w member
    rcases ZFSet.mem_union.1 member with member | member
    · obtain ⟨x, hx, h, hh, rfl⟩ := ZFSet.mem_prod.1 (oldFunction.1 member)
      exact ZFSet.pair_mem_prod.2 ⟨old_mem_taggedExtension hx, hh⟩
    · exact (ZFSet.mem_sep.1 member).1
  · intro x hx
    rcases mem_taggedExtension.1 hx with old | ⟨q, hq, rfl⟩
    · obtain ⟨h, entry, unique⟩ := oldFunction.2 x old
      exact ⟨h, (taggedHeightGraph_old_entry old).2 entry,
        fun y hy => unique y ((taggedHeightGraph_old_entry old).1 hy)⟩
    · obtain ⟨h, entry, unique⟩ := freshFunction.2 q hq
      exact ⟨h, (taggedHeightGraph_fresh_entry oldFunction freshFunction).2 entry,
        fun y hy => unique y ((taggedHeightGraph_fresh_entry oldFunction freshFunction).1 hy)⟩

noncomputable def heightOrderRestriction (R r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod R R) r

theorem pair_mem_heightOrderRestriction (R r a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ heightOrderRestriction R r ↔
      ZFSet.pair a b ∈ r ∧ a ∈ R ∧ b ∈ R := by
  rw [heightOrderRestriction, ZFSet.mem_sep, ZFSet.pair_mem_prod]

theorem heightOrderRestriction_linear {B R r : ZFSet.{u}}
    (linear : StrictLinearOrderCode B r) (subset : R ⊆ B) :
    StrictLinearOrderCode R (heightOrderRestriction R r) := by
  refine ⟨fun _ h => (ZFSet.mem_sep.1 h).2, ?_, ?_, ?_⟩
  · intro a ha entry
    exact linear.irrefl a (subset ha) (ZFSet.mem_sep.1 entry).1
  · intro a b c first second
    obtain ⟨ab, ha, _⟩ := (pair_mem_heightOrderRestriction R r a b).1 first
    obtain ⟨bc, _, hc⟩ := (pair_mem_heightOrderRestriction R r b c).1 second
    exact (pair_mem_heightOrderRestriction R r a c).2 ⟨linear.trans a b c ab bc, ha, hc⟩
  · intro a ha b hb
    rcases linear.compare a (subset ha) b (subset hb) with ab | equal | ba
    · exact Or.inl ((pair_mem_heightOrderRestriction R r a b).2 ⟨ab, ha, hb⟩)
    · exact Or.inr (Or.inl equal)
    · exact Or.inr (Or.inr ((pair_mem_heightOrderRestriction R r b a).2 ⟨ba, hb, ha⟩))

theorem function_on_relationImage {A B h : ZFSet.{u}} (function : ZFSet.IsFunc A B h) :
    ZFSet.IsFunc A (relationImage A B h) h := by
  refine ⟨?_, function.2⟩
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨ha, (mem_relationImage A B h b).2 ⟨hb, a, ha, hz⟩⟩

def heightImageCandidate (Qs Bs Hs i R : ZFSet.{u}) : Prop :=
  ∃ Q ∈ ⋃₀ ⋃₀ Qs, ∃ B ∈ ⋃₀ ⋃₀ Bs, ∃ h ∈ ⋃₀ ⋃₀ Hs,
    ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i B ∈ Bs ∧ ZFSet.pair i h ∈ Hs ∧
      R = relationImage Q B h

def heightOrderCandidate (Rs brs i r : ZFSet.{u}) : Prop :=
  ∃ R ∈ ⋃₀ ⋃₀ Rs, ∃ s ∈ ⋃₀ ⋃₀ brs,
    ZFSet.pair i R ∈ Rs ∧ ZFSet.pair i s ∈ brs ∧ r = heightOrderRestriction R s

noncomputable def heightImageFamily (I W Qs Bs Hs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ R ∈ W,
    z = ZFSet.pair i R ∧ heightImageCandidate Qs Bs Hs i R) (ZFSet.prod I W)

noncomputable def heightOrderFamily (I W Rs brs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ r ∈ W,
    z = ZFSet.pair i r ∧ heightOrderCandidate Rs brs i r) (ZFSet.prod I W)

theorem pair_mem_heightImageFamily (I W Qs Bs Hs i R : ZFSet.{u}) :
    ZFSet.pair i R ∈ heightImageFamily I W Qs Bs Hs ↔
      i ∈ I ∧ R ∈ W ∧ heightImageCandidate Qs Bs Hs i R := by
  rw [heightImageFamily, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hR⟩, j, _, S, _, equal, candidate⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hR, candidate⟩
  · rintro ⟨hi, hR, candidate⟩
    exact ⟨⟨hi, hR⟩, i, hi, R, hR, rfl, candidate⟩

theorem pair_mem_heightOrderFamily (I W Rs brs i r : ZFSet.{u}) :
    ZFSet.pair i r ∈ heightOrderFamily I W Rs brs ↔
      i ∈ I ∧ r ∈ W ∧ heightOrderCandidate Rs brs i r := by
  rw [heightOrderFamily, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hr⟩, j, _, s, _, equal, candidate⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hr, candidate⟩
  · rintro ⟨hi, hr, candidate⟩
    exact ⟨⟨hi, hr⟩, i, hi, r, hr, rfl, candidate⟩

namespace BoundedFormula

open SetFormula

def heightImageEquationFormula {n} (R Q B h : Fin n) : BoundedFormula n :=
  .conj (.allMem R (.conj (.mem 0 B.succ) (imageMemberFormula 0 Q.succ h.succ)))
    (.allMem B (imp (imageMemberFormula 0 Q.succ h.succ) (.mem 0 R.succ)))

theorem truth_heightImageEquationFormula {n} (R Q B h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (heightImageEquationFormula R Q B h) env ↔
      env R = relationImage (env Q) (env B) (env h) := by
  simp only [heightImageEquationFormula, Truth, truth_imp, truth_imageMemberFormula]
  change ((∀ x ∈ env R, x ∈ env B ∧ ∃ q ∈ env Q, ZFSet.pair q x ∈ env h) ∧
    (∀ x ∈ env B, (∃ q ∈ env Q, ZFSet.pair q x ∈ env h) → x ∈ env R)) ↔ _
  constructor
  · rintro ⟨subset, covers⟩
    apply ZFSet.ext
    intro x
    rw [mem_relationImage]
    exact ⟨subset x, fun hx => covers x hx.1 hx.2⟩
  · intro equal
    constructor
    · intro x hx
      exact (mem_relationImage _ _ _ x).1 (equal ▸ hx)
    · intro x hx image
      exact equal.symm ▸ (mem_relationImage _ _ _ x).2 ⟨hx, image⟩

def heightOrderEquationFormula {n} (r R s : Fin n) : BoundedFormula n :=
  .conj (.allMem r (.conj (.mem 0 s.succ) (productElementFormula 0 R.succ R.succ)))
    (.allMem s (imp (productElementFormula 0 R.succ R.succ) (.mem 0 r.succ)))

theorem truth_heightOrderEquationFormula {n} (r R s : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (heightOrderEquationFormula r R s) env ↔
      env r = heightOrderRestriction (env R) (env s) := by
  simp only [heightOrderEquationFormula, Truth, truth_imp, truth_productElementFormula]
  change ((∀ x ∈ env r, x ∈ env s ∧ x ∈ ZFSet.prod (env R) (env R)) ∧
    (∀ x ∈ env s, x ∈ ZFSet.prod (env R) (env R) → x ∈ env r)) ↔ _
  constructor
  · rintro ⟨subset, covers⟩
    apply ZFSet.ext
    intro x
    rw [heightOrderRestriction, ZFSet.mem_sep]
    exact ⟨subset x, fun hx => covers x hx.1 hx.2⟩
  · intro equal
    constructor
    · intro x hx
      have member : x ∈ heightOrderRestriction (env R) (env s) := equal ▸ hx
      exact ZFSet.mem_sep.1 member
    · intro x hx bound
      exact equal.symm ▸ ZFSet.mem_sep.2 ⟨hx, bound⟩

def heightImageCandidateFormula {n} (Qs Bs Hs i R qb bb hb : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ
  exMem qb (exMem bb.succ (exMem hb.succ.succ
    (.conj (pairMembershipFormula (lift i) 2 (lift Qs))
      (.conj (pairMembershipFormula (lift i) 1 (lift Bs))
        (.conj (pairMembershipFormula (lift i) 0 (lift Hs))
          (heightImageEquationFormula (lift R) 2 1 0))))))

theorem truth_heightImageCandidateFormula {n} (Qs Bs Hs i R qb bb hb : Fin n)
    (env : Fin n → ZFSet.{u}) (eqQ : env qb = ⋃₀ ⋃₀ env Qs)
    (eqB : env bb = ⋃₀ ⋃₀ env Bs) (eqH : env hb = ⋃₀ ⋃₀ env Hs) :
    Truth (heightImageCandidateFormula Qs Bs Hs i R qb bb hb) env ↔
      heightImageCandidate (env Qs) (env Bs) (env Hs) (env i) (env R) := by
  simp only [heightImageCandidateFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_heightImageEquationFormula]
  change (∃ Q ∈ env qb, ∃ B ∈ env bb, ∃ h ∈ env hb,
    ZFSet.pair (env i) Q ∈ env Qs ∧ ZFSet.pair (env i) B ∈ env Bs ∧
    ZFSet.pair (env i) h ∈ env Hs ∧ env R = relationImage Q B h) ↔ _
  rw [eqQ, eqB, eqH]
  rfl

def heightOrderCandidateFormula {n} (Rs brs i r rb sb : Fin n) : BoundedFormula n :=
  exMem rb (exMem sb.succ
    (.conj (pairMembershipFormula i.succ.succ 1 Rs.succ.succ)
      (.conj (pairMembershipFormula i.succ.succ 0 brs.succ.succ)
        (heightOrderEquationFormula r.succ.succ 1 0))))

theorem truth_heightOrderCandidateFormula {n} (Rs brs i r rb sb : Fin n)
    (env : Fin n → ZFSet.{u}) (eqR : env rb = ⋃₀ ⋃₀ env Rs)
    (eqS : env sb = ⋃₀ ⋃₀ env brs) :
    Truth (heightOrderCandidateFormula Rs brs i r rb sb) env ↔
      heightOrderCandidate (env Rs) (env brs) (env i) (env r) := by
  simp only [heightOrderCandidateFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_heightOrderEquationFormula]
  change (∃ R ∈ env rb, ∃ s ∈ env sb,
    ZFSet.pair (env i) R ∈ env Rs ∧ ZFSet.pair (env i) s ∈ env brs ∧
    env r = heightOrderRestriction R s) ↔ _
  rw [eqR, eqS]
  rfl

def heightImageFamilyEntryFormula {n} (z I W Qs Bs Hs qb bb hb : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (heightImageCandidateFormula Qs.succ.succ Bs.succ.succ Hs.succ.succ 1 0
      qb.succ.succ bb.succ.succ hb.succ.succ)))

theorem truth_heightImageFamilyEntryFormula {n} (z I W Qs Bs Hs qb bb hb : Fin n)
    (env : Fin n → ZFSet.{u}) (eqQ : env qb = ⋃₀ ⋃₀ env Qs)
    (eqB : env bb = ⋃₀ ⋃₀ env Bs) (eqH : env hb = ⋃₀ ⋃₀ env Hs) :
    Truth (heightImageFamilyEntryFormula z I W Qs Bs Hs qb bb hb) env ↔
      ∃ i ∈ env I, ∃ R ∈ env W, env z = ZFSet.pair i R ∧
        heightImageCandidate (env Qs) (env Bs) (env Hs) i R := by
  simp only [heightImageFamilyEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply exists_congr
  intro R
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_heightImageCandidateFormula Qs.succ.succ Bs.succ.succ
    Hs.succ.succ 1 0 qb.succ.succ bb.succ.succ hb.succ.succ
    (extend R (extend i env)) eqQ eqB eqH)

def heightOrderFamilyEntryFormula {n} (z I W Rs brs rb sb : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (heightOrderCandidateFormula Rs.succ.succ brs.succ.succ 1 0 rb.succ.succ sb.succ.succ)))

theorem truth_heightOrderFamilyEntryFormula {n} (z I W Rs brs rb sb : Fin n)
    (env : Fin n → ZFSet.{u}) (eqR : env rb = ⋃₀ ⋃₀ env Rs)
    (eqS : env sb = ⋃₀ ⋃₀ env brs) :
    Truth (heightOrderFamilyEntryFormula z I W Rs brs rb sb) env ↔
      ∃ i ∈ env I, ∃ r ∈ env W, env z = ZFSet.pair i r ∧
        heightOrderCandidate (env Rs) (env brs) i r := by
  simp only [heightOrderFamilyEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply exists_congr
  intro r
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_heightOrderCandidateFormula Rs.succ.succ brs.succ.succ
    1 0 rb.succ.succ sb.succ.succ (extend r (extend i env)) eqR eqS)

end BoundedFormula

end PartitionPilot.Forcing

end OAI
