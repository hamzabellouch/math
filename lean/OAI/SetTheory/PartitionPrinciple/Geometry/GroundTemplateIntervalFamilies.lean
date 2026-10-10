import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIntervalEmbeddingRelation
import OAI.SetTheory.PartitionPrinciple.Geometry.TemplateHeightRangeCodes

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

namespace BoundedFormula

open SetFormula

def indexedAttachmentDomainEntryFormula {n} (z i qs bound : Fin n) : BoundedFormula n :=
  exMem i (exMem bound.succ (exMem 0
    (.conj (pairMembershipFormula 2 1 qs.succ.succ.succ)
      (orderedPairFormula z.succ.succ.succ 2 0))))

theorem truth_indexedAttachmentDomainEntryFormula {n} (z i qs bound : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedAttachmentDomainEntryFormula z i qs bound) env ↔
      ∃ j ∈ env i, ∃ Q ∈ env bound, ∃ q ∈ Q,
        ZFSet.pair j Q ∈ env qs ∧ env z = ZFSet.pair j q := by
  simp only [indexedAttachmentDomainEntryFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_orderedPairFormula]
  rfl

def indexedAttachmentFreshEntryFormula {n}
    (z i qs rs anchors qBound rBound aBound : Fin n) : BoundedFormula n :=
  exMem i (exMem qBound.succ (exMem rBound.succ.succ
    (exMem aBound.succ.succ.succ (exMem 2
      (.conj (pairMembershipFormula 4 3 qs.succ.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 4 2 rs.succ.succ.succ.succ.succ)
          (.conj (pairMembershipFormula 4 1 anchors.succ.succ.succ.succ.succ)
            (.conj (orderedPairFormula z.succ.succ.succ.succ.succ 4 0)
              (.neg (pairMembershipFormula 0 1 2))))))))))

theorem truth_indexedAttachmentFreshEntryFormula {n}
    (z i qs rs anchors qBound rBound aBound : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (indexedAttachmentFreshEntryFormula z i qs rs anchors qBound rBound aBound) env ↔
      ∃ j ∈ env i, ∃ Q ∈ env qBound, ∃ r ∈ env rBound, ∃ a ∈ env aBound, ∃ q ∈ Q,
        ZFSet.pair j Q ∈ env qs ∧ ZFSet.pair j r ∈ env rs ∧ ZFSet.pair j a ∈ env anchors ∧
        env z = ZFSet.pair j q ∧ ZFSet.pair q a ∉ r := by
  simp only [indexedAttachmentFreshEntryFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_orderedPairFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem familyPointBound_mem (unions : Realize M.sets SetFormula.union Fin.elim0)
    {Qs : ZFSet.{u}} (hQs : Qs ∈ M.sets) : familyPointBound Qs ∈ M.sets :=
  M.union_mem unions (M.union_mem unions (M.union_mem unions hQs))

theorem indexedAttachmentDomain_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I Qs : ZFSet.{u}} (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) :
    indexedAttachmentDomain I Qs ∈ M.sets := by
  have bound := M.union_mem unions (M.union_mem unions hQs)
  let params := extend I (extend Qs (extend (ZFSet.sUnion (ZFSet.sUnion Qs)) Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedAttachmentDomainEntryFormula 0 1 2 3) params
    (Fin.cases hI (Fin.cases hQs (Fin.cases bound (fun j => Fin.elim0 j))))
    (M.prod_mem pairing unions powers separation hI (M.familyPointBound_mem unions hQs))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedAttachmentDomainEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod I (familyPointBound Qs)) = indexedAttachmentDomain I Qs := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedAttachmentDomain, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_indexedAttachmentDomainEntryFormula 0 1 2 3 _)
  exact equal ▸ selected

theorem indexedAttachmentFresh_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I Qs rs anchors : ZFSet.{u}} (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets) (hAnchors : anchors ∈ M.sets) :
    indexedAttachmentFresh I Qs rs anchors ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have rBound := M.union_mem unions (M.union_mem unions hrs)
  have aBound := M.union_mem unions (M.union_mem unions hAnchors)
  let params := extend I (extend Qs (extend rs (extend anchors
    (extend (ZFSet.sUnion (ZFSet.sUnion Qs)) (extend (ZFSet.sUnion (ZFSet.sUnion rs))
      (extend (ZFSet.sUnion (ZFSet.sUnion anchors)) Fin.elim0))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedAttachmentFreshEntryFormula 0 1 2 3 4 5 6 7) params
    (Fin.cases hI (Fin.cases hQs (Fin.cases hrs (Fin.cases hAnchors
      (Fin.cases qBound (Fin.cases rBound (Fin.cases aBound (fun j => Fin.elim0 j))))))))
    (M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedAttachmentFreshEntryFormula 0 1 2 3 4 5 6 7) (extend z params))
      (indexedAttachmentDomain I Qs) = indexedAttachmentFresh I Qs rs anchors := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedAttachmentFresh, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_indexedAttachmentFreshEntryFormula 0 1 2 3 4 5 6 7 _)
  exact equal ▸ selected

end TransitiveGround






noncomputable def batchHeightEndpointRelation
    (I P C D As Es Ss oldH rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z =>
    ∃ i ∈ I, ∃ a ∈ ZFSet.sUnion (ZFSet.sUnion As),
    ∃ ell ∈ ZFSet.sUnion (ZFSet.sUnion Es), ∃ b ∈ P, ∃ e ∈ P,
    ∃ c ∈ C, ∃ lo ∈ D, ∃ hi ∈ D, ∃ d ∈ C, ∃ v ∈ D,
      z = ZFSet.pair i (ZFSet.pair c (ZFSet.pair lo hi)) ∧
      ZFSet.pair i a ∈ As ∧ ZFSet.pair i ell ∈ Es ∧ ZFSet.pair a b ∈ ell ∧
      ZFSet.pair i e ∈ Ss ∧ ZFSet.pair b (ZFSet.pair c lo) ∈ oldH ∧
      ZFSet.pair e (ZFSet.pair d v) ∈ oldH ∧ ZFSet.pair lo hi ∈ rD ∧
      ((c = d ∧ hi = v) ∨ c ∈ d))
    (ZFSet.prod I (ZFSet.prod C (ZFSet.prod D D)))

theorem pair_mem_batchHeightEndpointRelation
    (I P C D As Es Ss oldH rD i c lo hi : ZFSet.{u}) :
    ZFSet.pair i (ZFSet.pair c (ZFSet.pair lo hi)) ∈
      batchHeightEndpointRelation I P C D As Es Ss oldH rD ↔
    i ∈ I ∧ c ∈ C ∧ lo ∈ D ∧ hi ∈ D ∧
      ∃ a ∈ ZFSet.sUnion (ZFSet.sUnion As), ∃ ell ∈ ZFSet.sUnion (ZFSet.sUnion Es),
      ∃ b ∈ P, ∃ e ∈ P, ∃ d ∈ C, ∃ v ∈ D,
      ZFSet.pair i a ∈ As ∧ ZFSet.pair i ell ∈ Es ∧ ZFSet.pair a b ∈ ell ∧
      ZFSet.pair i e ∈ Ss ∧ ZFSet.pair b (ZFSet.pair c lo) ∈ oldH ∧
      ZFSet.pair e (ZFSet.pair d v) ∈ oldH ∧ ZFSet.pair lo hi ∈ rD ∧
      ((c = d ∧ hi = v) ∨ c ∈ d) := by
  rw [batchHeightEndpointRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, a, ha, ell, hell, b, hb, e, he,
      c', hc, lo', hlo, hi', hhi, d, hd, v, hv, equal, rest⟩
    obtain ⟨ij, restEq⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨cc, restEq'⟩ := ZFSet.pair_inj.1 restEq
    obtain ⟨ll, hh⟩ := ZFSet.pair_inj.1 restEq'
    subst j
    subst c'
    subst lo'
    subst hi'
    exact ⟨hj, hc, hlo, hhi, a, ha, ell, hell, b, hb, e, he, d, hd, v, hv, rest⟩
  · rintro ⟨hiI, hc, hlo, hhi, a, ha, ell, hell, b, hb, e, he, d, hd, v, hv, rest⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hiI, ZFSet.pair_mem_prod.2
      ⟨hc, ZFSet.pair_mem_prod.2 ⟨hlo, hhi⟩⟩⟩,
      i, hiI, a, ha, ell, hell, b, hb, e, he, c, hc, lo, hlo, hi, hhi, d, hd, v, hv, rfl, rest⟩

structure BatchHeightEndpointCode
    {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (C D oldH rD Cs los his : ZFSet.{u}) : Prop where
  columns : ZFSet.IsFunc I C Cs
  lows : ZFSet.IsFunc I D los
  highs : ZFSet.IsFunc I D his
  base : ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ c lo,
    ZFSet.pair i.val c ∈ Cs → ZFSet.pair i.val lo ∈ los →
      ZFSet.pair (d.templates.base i).val (ZFSet.pair c lo) ∈ oldH
  gap : ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ lo hi,
    ZFSet.pair i.val lo ∈ los → ZFSet.pair i.val hi ∈ his → ZFSet.pair lo hi ∈ rD
  upper : ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ c hi c' v,
    ZFSet.pair i.val c ∈ Cs → ZFSet.pair i.val hi ∈ his →
      ZFSet.pair (d.separator i) (ZFSet.pair c' v) ∈ oldH →
        (c = c' ∧ hi = v) ∨ c ∈ c'

namespace AttachmentBatchInputs

variable {P rP μP I Qs rs μs As Es Fs Ss C D oldH rD : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

theorem endpoint_base_entry (i : {i : ZFSet.{u} // i ∈ I}) :
    ZFSet.pair (d.anchor i) (d.templates.base i).val ∈ d.embed i :=
  (d.fiber i).baseMap_entry _

include d in
theorem batchHeightEndpointRelation_total
    (old : StrictLexHeightCode P C D rP oldH rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD) :
    ∀ i ∈ I, ∃ t ∈ ZFSet.prod C (ZFSet.prod D D),
      ZFSet.pair i t ∈ batchHeightEndpointRelation I P C D As Es Ss oldH rD := by
  intro i hi
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  obtain ⟨baseHeight, baseEntry, _⟩ := old.function.2 (d.templates.base j).val (d.templates.base j).property
  obtain ⟨c, hc, lo, hlo, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (old.function.1 baseEntry)).2
  obtain ⟨sepHeight, sepEntry, _⟩ := old.function.2 (d.separator j) (d.fiber j).separator_mem
  obtain ⟨c', hc', v, hv, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (old.function.1 sepEntry)).2
  have different : (d.templates.base j).val ≠ d.separator j := by
    intro equal
    have bad := (d.fiber j).separator_not_le_base _ (d.endpoint_base_entry j)
    rw [equal] at bad
    exact bad (d.oldOrder.order.refl _ (d.fiber j).separator_mem)
  have strict := old.strict _ (d.templates.base j).property _ (d.fiber j).separator_mem
    c lo c' v ((d.fiber j).base_le_separator _ (d.endpoint_base_entry j)) different baseEntry sepEntry
  have construct (upper : ZFSet.{u}) (hupper : upper ∈ D) (gap : ZFSet.pair lo upper ∈ rD)
      (rule : (c = c' ∧ upper = v) ∨ c ∈ c') :
      ∃ t ∈ ZFSet.prod C (ZFSet.prod D D),
        ZFSet.pair i t ∈ batchHeightEndpointRelation I P C D As Es Ss oldH rD := by
    refine ⟨ZFSet.pair c (ZFSet.pair lo upper),
      ZFSet.pair_mem_prod.2 ⟨hc, ZFSet.pair_mem_prod.2 ⟨hlo, hupper⟩⟩,
      (pair_mem_batchHeightEndpointRelation _ _ _ _ _ _ _ _ _ _ _ _ _).2 ?_⟩
    exact ⟨hi, hc, hlo, hupper, d.anchor j, d.anchors.value_mem_doubleUnion j,
      d.embed j, d.embeddings.value_mem_doubleUnion j, (d.templates.base j).val,
      (d.templates.base j).property, d.separator j, (d.fiber j).separator_mem, c', hc', v, hv,
      d.anchor_entry j, d.embed_entry j, d.endpoint_base_entry j, d.separator_entry j,
      baseEntry, sepEntry, gap, rule⟩
  rcases strict with smaller | ⟨same, gap⟩
  · obtain ⟨upper, hupper, gap⟩ := above lo hlo
    exact construct upper hupper gap (Or.inr smaller)
  · exact construct v hv gap (Or.inl ⟨same, rfl⟩)

theorem batchHeightEndpointRelation_laws
    (old : StrictLexHeightCode P C D rP oldH rD)
    (i : {i : ZFSet.{u} // i ∈ I}) {c lo hi : ZFSet.{u}}
    (entry : ZFSet.pair i.val (ZFSet.pair c (ZFSet.pair lo hi)) ∈
      batchHeightEndpointRelation I P C D As Es Ss oldH rD) :
    ZFSet.pair (d.templates.base i).val (ZFSet.pair c lo) ∈ oldH ∧
      ZFSet.pair lo hi ∈ rD ∧ ∀ c' v,
      ZFSet.pair (d.separator i) (ZFSet.pair c' v) ∈ oldH →
        (c = c' ∧ hi = v) ∨ c ∈ c' := by
  obtain ⟨_, _, _, _, a, _, ell, _, b, _, e, _, c', _, v, _,
    ia, iell, ab, ie, bH, eH, gap, rule⟩ :=
      (pair_mem_batchHeightEndpointRelation _ _ _ _ _ _ _ _ _ _ _ _ _).1 entry
  have aeq := d.anchors.value_eq_of_entry i ia
  have elleq := d.embeddings.value_eq_of_entry i iell
  have eeq := d.separators.value_eq_of_entry i ie
  change d.anchor i = a at aeq
  change d.embed i = ell at elleq
  change d.separator i = e at eeq
  subst a
  subst ell
  subst e
  have beq := (functionCode_partial (d.fiber i).base_function).unique _ _ _ ab (d.endpoint_base_entry i)
  subst b
  refine ⟨bH, gap, ?_⟩
  intro c'' v' entry'
  have equal := (functionCode_partial old.function).unique _ _ _ eH entry'
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  exact rule

end AttachmentBatchInputs

namespace BatchHeightEndpointCode

theorem interval_upper
    {P rP μP I Qs rs μs As Es Fs Ss C D oldH rD Cs los his : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (endpoints : BatchHeightEndpointCode d C D oldH rD Cs los his)
    (i : {i : ZFSet.{u} // i ∈ I}) {c hi q c' v : ZFSet.{u}}
    (column : ZFSet.pair i.val c ∈ Cs) (upper : ZFSet.pair i.val hi ∈ his)
    (below : ZFSet.pair q hi ∈ rD)
    (separator : ZFSet.pair (d.separator i) (ZFSet.pair c' v) ∈ oldH) :
    c ∈ c' ∨ (c = c' ∧ ZFSet.pair q v ∈ rD) := by
  rcases endpoints.upper i c hi c' v column upper separator with ⟨same, rfl⟩ | smaller
  · exact Or.inr ⟨same, below⟩
  · exact Or.inl smaller

end BatchHeightEndpointCode

end



namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_intervalEmbedding_family
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I As rs los his D rD c : ZFSet.{u}}
    (d : IntervalEmbeddingFamilyInputs I As rs los his D rD)
    (hI : I ∈ M.sets) (hAs : As ∈ M.sets) (hrs : rs ∈ M.sets)
    (hlos : los ∈ M.sets) (hhis : his ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
    (small : ∀ i, M.groundEmbeddable (d.sources.value i) ZFSet.omega) :
    ∃ family ∈ M.sets,
      ZFSet.IsFunc I (M.groundRelations (familyPointBound As) D) family ∧
      ∀ (i : {i : ZFSet.{u} // i ∈ I}) f, ZFSet.pair i.val f ∈ family →
        IntervalEmbeddingCode (d.sources.value i) D (d.orders.value i) rD
          (d.lows.value i) (d.highs.value i) f := by
  let W := M.groundRelations (familyPointBound As) D
  have hW : W ∈ M.sets := M.groundRelations_mem pairing unions powers separation
    (M.familyPointBound_mem unions hAs) hD
  have hR := M.intervalEmbeddingRelation_mem pairing unions powers separation
    hI hW hAs hrs hlos hhis hD hrD
  have total : ∀ i ∈ I, ∃ f ∈ W,
      ZFSet.pair i f ∈ intervalEmbeddingRelation I W As rs los his D rD := by
    intro i hi
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    obtain ⟨f, hf, code⟩ := M.exists_intervalEmbedding
      pairing unions powers separation collection infinite
      (d.sources.value_mem M hAs j) hD (d.orders.value_mem M hrs j) hrD hc
      (d.source_order j) target injection (small j) (d.lower_mem j) (d.upper_mem j) (d.gap j)
    have bound : f ∈ W := (M.mem_groundRelations (familyPointBound As) D f).2
      ⟨hf, d.embedding_subset_bound j code⟩
    exact ⟨f, bound, (pair_mem_intervalEmbeddingRelation I W As rs los his D rD i f).2
      ⟨hi, bound, (d.candidate_iff j f).2 code⟩⟩
  obtain ⟨family, member, function, subset⟩ := M.uniformize_relation
    pairing unions powers separation choice hI hW hR total
  refine ⟨family, member, function, ?_⟩
  intro i f entry
  exact (d.candidate_iff i f).1
    ((pair_mem_intervalEmbeddingRelation I W As rs los his D rD i.val f).1 (subset entry)).2.2

end TransitiveGround




universe u

namespace BoundedFormula

open SetFormula

def endpointRightTripleFormula {n} (z x y w : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (.conj (orderedPairFormula 0 y.succ.succ w.succ.succ)
    (orderedPairFormula z.succ.succ x.succ.succ 0)))

theorem truth_endpointRightTripleFormula {n} (z x y w : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (endpointRightTripleFormula z x y w) env ↔
      env z = ZFSet.pair (env x) (ZFSet.pair (env y) (env w)) := by
  simp only [endpointRightTripleFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ a ∈ env z, ∃ b ∈ a, b = ZFSet.pair (env y) (env w) ∧ env z = ZFSet.pair (env x) b) ↔ _
  constructor
  · rintro ⟨a, _, b, _, rfl, equal⟩
    exact equal
  · intro equal
    refine ⟨{env x, ZFSet.pair (env y) (env w)}, ?_, ZFSet.pair (env y) (env w),
      ZFSet.mem_pair.2 (Or.inr rfl), rfl, equal⟩
    rw [equal]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

def endpointRightMembershipFormula {n} (x y w f : Fin n) : BoundedFormula n :=
  exMem f (endpointRightTripleFormula 0 x.succ y.succ w.succ)

theorem truth_endpointRightMembershipFormula {n} (x y w f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (endpointRightMembershipFormula x y w f) env ↔
      ZFSet.pair (env x) (ZFSet.pair (env y) (env w)) ∈ env f := by
  simp only [endpointRightMembershipFormula, truth_exMem, truth_endpointRightTripleFormula]
  change (∃ a ∈ env f, a = ZFSet.pair (env x) (ZFSet.pair (env y) (env w))) ↔ _
  constructor
  · rintro ⟨a, ha, equal⟩
    exact equal ▸ ha
  · intro ha
    exact ⟨_, ha, rfl⟩

def endpointTupleFormula {n} (z i c lo hi : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (.conj (endpointRightTripleFormula 0 c.succ.succ lo.succ.succ hi.succ.succ)
    (orderedPairFormula z.succ.succ i.succ.succ 0)))

theorem truth_endpointTupleFormula {n} (z i c lo hi : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (endpointTupleFormula z i c lo hi) env ↔
      env z = ZFSet.pair (env i) (ZFSet.pair (env c) (ZFSet.pair (env lo) (env hi))) := by
  simp only [endpointTupleFormula, truth_exMem, Truth, truth_endpointRightTripleFormula,
    truth_orderedPairFormula]
  change (∃ a ∈ env z, ∃ b ∈ a, b = ZFSet.pair (env c) (ZFSet.pair (env lo) (env hi)) ∧
    env z = ZFSet.pair (env i) b) ↔ _
  constructor
  · rintro ⟨a, _, b, _, rfl, equal⟩
    exact equal
  · intro equal
    refine ⟨{env i, ZFSet.pair (env c) (ZFSet.pair (env lo) (env hi))}, ?_,
      ZFSet.pair (env c) (ZFSet.pair (env lo) (env hi)), ZFSet.mem_pair.2 (Or.inr rfl), rfl, equal⟩
    rw [equal]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

def batchHeightEndpointFormula : BoundedFormula 12 :=
  exMem 1 (exMem 11 (exMem 13 (exMem 5 (exMem 6 (exMem 8 (exMem 10 (exMem 11 (exMem 11 (exMem 13
    (.conj (endpointTupleFormula 10 9 4 3 2)
      (.conj (pairMembershipFormula 9 8 15)
        (.conj (pairMembershipFormula 9 7 16)
          (.conj (pairMembershipFormula 8 6 7)
            (.conj (pairMembershipFormula 9 5 17)
              (.conj (endpointRightMembershipFormula 6 4 3 18)
                (.conj (endpointRightMembershipFormula 5 1 0 18)
                  (.conj (pairMembershipFormula 3 2 19)
                    (disj (.conj (.equal 4 1) (.equal 2 0)) (.mem 4 1)))))))))))))))))))

theorem truth_batchHeightEndpointFormula (env : Fin 12 → ZFSet.{u}) :
    Truth batchHeightEndpointFormula env ↔
    ∃ i ∈ env 1, ∃ a ∈ env 10, ∃ ell ∈ env 11, ∃ b ∈ env 2, ∃ e ∈ env 2,
    ∃ c ∈ env 3, ∃ lo ∈ env 4, ∃ hi ∈ env 4, ∃ d ∈ env 3, ∃ v ∈ env 4,
      env 0 = ZFSet.pair i (ZFSet.pair c (ZFSet.pair lo hi)) ∧
      ZFSet.pair i a ∈ env 5 ∧ ZFSet.pair i ell ∈ env 6 ∧ ZFSet.pair a b ∈ ell ∧
      ZFSet.pair i e ∈ env 7 ∧ ZFSet.pair b (ZFSet.pair c lo) ∈ env 8 ∧
      ZFSet.pair e (ZFSet.pair d v) ∈ env 8 ∧ ZFSet.pair lo hi ∈ env 9 ∧
      ((c = d ∧ hi = v) ∨ c ∈ d) := by
  simp only [batchHeightEndpointFormula, truth_exMem, Truth, truth_disj,
    truth_endpointTupleFormula, truth_endpointRightMembershipFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

noncomputable def endpointColumns (I C D f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (ZFSet.prod C (ZFSet.prod D D)) C f (productFirst C (ZFSet.prod D D))

noncomputable def endpointPairs (I C D f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (ZFSet.prod C (ZFSet.prod D D)) (ZFSet.prod D D) f (productSecond C (ZFSet.prod D D))

noncomputable def endpointLows (I C D f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (ZFSet.prod D D) D (endpointPairs I C D f) (productFirst D D)

noncomputable def endpointHighs (I C D f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (ZFSet.prod D D) D (endpointPairs I C D f) (productSecond D D)

theorem endpointProjection_functions {I C D f : ZFSet.{u}}
    (func : ZFSet.IsFunc I (ZFSet.prod C (ZFSet.prod D D)) f) :
    ZFSet.IsFunc I C (endpointColumns I C D f) ∧
      ZFSet.IsFunc I D (endpointLows I C D f) ∧ ZFSet.IsFunc I D (endpointHighs I C D f) := by
  have pairs : ZFSet.IsFunc I (ZFSet.prod D D) (endpointPairs I C D f) :=
    relationCompose_function_of_subset func (productSecond_function C (ZFSet.prod D D)) (fun _ h => h)
  exact ⟨relationCompose_function_of_subset func (productFirst_function C (ZFSet.prod D D)) (fun _ h => h),
    relationCompose_function_of_subset pairs (productFirst_function D D) (fun _ h => h),
    relationCompose_function_of_subset pairs (productSecond_function D D) (fun _ h => h)⟩

theorem endpointProjection_entries {I C D f i c lo hi : ZFSet.{u}}
    (hiI : i ∈ I) (hc : c ∈ C) (hlo : lo ∈ D) (hhi : hi ∈ D)
    (entry : ZFSet.pair i (ZFSet.pair c (ZFSet.pair lo hi)) ∈ f) :
    ZFSet.pair i c ∈ endpointColumns I C D f ∧
      ZFSet.pair i lo ∈ endpointLows I C D f ∧ ZFSet.pair i hi ∈ endpointHighs I C D f := by
  have hpair := ZFSet.pair_mem_prod.2 ⟨hlo, hhi⟩
  have htriple := ZFSet.pair_mem_prod.2 ⟨hc, hpair⟩
  have pairs : ZFSet.pair i (ZFSet.pair lo hi) ∈ endpointPairs I C D f :=
    (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hiI, hpair, _, htriple, entry,
      (mem_productSecond C (ZFSet.prod D D) _).2 ⟨c, hc, _, hpair, rfl⟩⟩
  exact ⟨(pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hiI, hc, _, htriple, entry,
      (mem_productFirst C (ZFSet.prod D D) _).2 ⟨c, hc, _, hpair, rfl⟩⟩,
    (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hiI, hlo, _, hpair, pairs,
      (mem_productFirst D D _).2 ⟨lo, hlo, hi, hhi, rfl⟩⟩,
    (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hiI, hhi, _, hpair, pairs,
      (mem_productSecond D D _).2 ⟨lo, hlo, hi, hhi, rfl⟩⟩⟩

theorem batchHeightEndpointCode_of_selection
    {P rP μP I Qs rs μs As Es Fs Ss C D oldH rD f : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (old : StrictLexHeightCode P C D rP oldH rD)
    (func : ZFSet.IsFunc I (ZFSet.prod C (ZFSet.prod D D)) f)
    (selected : f ⊆ batchHeightEndpointRelation I P C D As Es Ss oldH rD) :
    BatchHeightEndpointCode d C D oldH rD
      (endpointColumns I C D f) (endpointLows I C D f) (endpointHighs I C D f) := by
  obtain ⟨columns, lows, highs⟩ := endpointProjection_functions func
  have atIndex (i : {i : ZFSet.{u} // i ∈ I}) :
      ∃ c lo hi, ZFSet.pair i.val c ∈ endpointColumns I C D f ∧
        ZFSet.pair i.val lo ∈ endpointLows I C D f ∧ ZFSet.pair i.val hi ∈ endpointHighs I C D f ∧
        ZFSet.pair (d.templates.base i).val (ZFSet.pair c lo) ∈ oldH ∧ ZFSet.pair lo hi ∈ rD ∧
        ∀ c' v, ZFSet.pair (d.separator i) (ZFSet.pair c' v) ∈ oldH →
          (c = c' ∧ hi = v) ∨ c ∈ c' := by
    obtain ⟨t, entry, _⟩ := func.2 i.val i.property
    obtain ⟨c, hc, pair, hpair, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (func.1 entry)).2
    obtain ⟨lo, hlo, hi, hhi, rfl⟩ := ZFSet.mem_prod.1 hpair
    obtain ⟨ce, le, he⟩ := endpointProjection_entries i.property hc hlo hhi entry
    exact ⟨c, lo, hi, ce, le, he, d.batchHeightEndpointRelation_laws old i (selected entry)⟩
  refine ⟨columns, lows, highs, ?_, ?_, ?_⟩
  · intro i c lo ce le
    obtain ⟨c', lo', hi, ce', le', _, base, _⟩ := atIndex i
    have ec := (functionCode_partial columns).unique _ _ _ ce' ce
    have el := (functionCode_partial lows).unique _ _ _ le' le
    exact ec ▸ el ▸ base
  · intro i lo hi le he
    obtain ⟨c, lo', hi', _, le', he', _, gap, _⟩ := atIndex i
    have el := (functionCode_partial lows).unique _ _ _ le' le
    have eh := (functionCode_partial highs).unique _ _ _ he' he
    exact el ▸ eh ▸ gap
  · intro i c hi c' v ce he sep
    obtain ⟨c'', lo, hi', ce', _, he', _, _, upper⟩ := atIndex i
    have ec := (functionCode_partial columns).unique _ _ _ ce' ce
    have eh := (functionCode_partial highs).unique _ _ _ he' he
    exact ec ▸ eh ▸ upper c' v sep

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem batchHeightEndpointRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P C D As Es Ss oldH rD : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hOld : oldH ∈ M.sets) (hrD : rD ∈ M.sets) :
    batchHeightEndpointRelation I P C D As Es Ss oldH rD ∈ M.sets := by
  have ha := M.union_mem unions (M.union_mem unions hAs)
  have he := M.union_mem unions (M.union_mem unions hEs)
  let params := extend I (extend P (extend C (extend D (extend As (extend Es (extend Ss
    (extend oldH (extend rD (extend (ZFSet.sUnion (ZFSet.sUnion As))
      (extend (ZFSet.sUnion (ZFSet.sUnion Es)) Fin.elim0))))))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.batchHeightEndpointFormula params
    (Fin.cases hI (Fin.cases hP (Fin.cases hC (Fin.cases hD (Fin.cases hAs (Fin.cases hEs
      (Fin.cases hSs (Fin.cases hOld (Fin.cases hrD (Fin.cases ha (Fin.cases he (fun j => Fin.elim0 j))))))))))))
    (M.prod_mem pairing unions powers separation hI
      (M.prod_mem pairing unions powers separation hC (M.prod_mem pairing unions powers separation hD hD)))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.batchHeightEndpointFormula
      (extend z params)) (ZFSet.prod I (ZFSet.prod C (ZFSet.prod D D))) =
      batchHeightEndpointRelation I P C D As Es Ss oldH rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, batchHeightEndpointRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchHeightEndpointFormula _)
  exact equal ▸ selected

theorem endpointProjections_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I C D f : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hf : f ∈ M.sets) :
    endpointColumns I C D f ∈ M.sets ∧ endpointLows I C D f ∈ M.sets ∧
      endpointHighs I C D f ∈ M.sets := by
  have hDD := M.prod_mem pairing unions powers separation hD hD
  have hT := M.prod_mem pairing unions powers separation hC hDD
  have hPairs : endpointPairs I C D f ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hI hT hDD hf (M.productSecond_mem pairing unions powers separation hC hDD)
  exact ⟨M.relationCompose_mem pairing unions powers separation hI hT hC hf
      (M.productFirst_mem pairing unions powers separation hC hDD),
    M.relationCompose_mem pairing unions powers separation hI hDD hD hPairs
      (M.productFirst_mem pairing unions powers separation hD hD),
    M.relationCompose_mem pairing unions powers separation hI hDD hD hPairs
      (M.productSecond_mem pairing unions powers separation hD hD)⟩

theorem exists_batchHeightEndpoints
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P rP μP I Qs rs μs As Es Fs Ss C D oldH rD : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (old : StrictLexHeightCode P C D rP oldH rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hOld : oldH ∈ M.sets) (hrD : rD ∈ M.sets) :
    ∃ Cs ∈ M.sets, ∃ los ∈ M.sets, ∃ his ∈ M.sets,
      BatchHeightEndpointCode d C D oldH rD Cs los his := by
  have hT := M.prod_mem pairing unions powers separation hC (M.prod_mem pairing unions powers separation hD hD)
  have hRelation := M.batchHeightEndpointRelation_mem pairing unions powers separation
    hI hP hC hD hAs hEs hSs hOld hrD
  obtain ⟨f, hf, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hI hT hRelation (d.batchHeightEndpointRelation_total old above)
  obtain ⟨hc, hl, hh⟩ := M.endpointProjections_mem pairing unions powers separation hI hC hD hf
  exact ⟨endpointColumns I C D f, hc, endpointLows I C D f, hl, endpointHighs I C D f, hh,
    batchHeightEndpointCode_of_selection d old func selected⟩

end TransitiveGround






namespace TemplateHeightFamilyInputs

variable {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D old rD Cs los his : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (t : TemplateHeightFamilyInputs d Vs vrs Hs)

include t in
theorem intervalInputs (e : BatchHeightEndpointCode d C D old rD Cs los his) :
    IntervalEmbeddingFamilyInputs I Vs vrs los his D rD where
  sources := t.ranges
  orders := t.orders
  lows := ⟨D, e.lows⟩
  highs := ⟨D, e.highs⟩
  source_order := t.linear
  lower_mem i := (ZFSet.pair_mem_prod.1 (e.lows.1
    ((show FunctionGraphOn I los from ⟨D, e.lows⟩).value_entry i))).2
  upper_mem i := (ZFSet.pair_mem_prod.1 (e.highs.1
    ((show FunctionGraphOn I his from ⟨D, e.highs⟩).value_entry i))).2
  gap i := e.gap i _ _
    ((show FunctionGraphOn I los from ⟨D, e.lows⟩).value_entry i)
    ((show FunctionGraphOn I his from ⟨D, e.highs⟩).value_entry i)

end TemplateHeightFamilyInputs

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem exists_templateIntervalFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D old rD Cs los his c : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (t : TemplateHeightFamilyInputs d Vs vrs Hs)
    (e : BatchHeightEndpointCode d C D old rD Cs los his)
    (hI : I ∈ M.sets) (hVs : Vs ∈ M.sets) (hvrs : vrs ∈ M.sets)
    (hlos : los ∈ M.sets) (hhis : his ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
    (small : ∀ i, M.groundEmbeddable (t.ranges.value i) ZFSet.omega) :
    ∃ family ∈ M.sets,
      ZFSet.IsFunc I (M.groundRelations (familyPointBound Vs) D) family ∧
      ∀ (i : {i : ZFSet.{u} // i ∈ I}) lo hi f,
        ZFSet.pair i.val lo ∈ los → ZFSet.pair i.val hi ∈ his →
        ZFSet.pair i.val f ∈ family →
        IntervalEmbeddingCode (t.ranges.value i) D (t.orders.value i) rD lo hi f := by
  obtain ⟨family, member, function, valid⟩ := M.exists_intervalEmbedding_family
    pairing unions powers separation collection infinite choice (t.intervalInputs e)
    hI hVs hvrs hlos hhis hD hrD hc target injection small
  refine ⟨family, member, function, ?_⟩
  intro i lo hi f lower upper entry
  have code := valid i f entry
  have sameLo := (t.intervalInputs e).lows.value_eq_of_entry i lower
  have sameHi := (t.intervalInputs e).highs.value_eq_of_entry i upper
  rw [sameLo, sameHi] at code
  exact code

end TransitiveGround


end PartitionPilot.Forcing

end OAI
