import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBatchHeightGraphs
import OAI.SetTheory.PartitionPrinciple.Geometry.HeightColumnBoundLaws
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialCompressionHistory

namespace OAI


namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

noncomputable def lexHeightOrder (C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ c ∈ C, ∃ q ∈ D, ∃ d ∈ C, ∃ v ∈ D,
    z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
      (c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ rD)))
    (ZFSet.prod (ZFSet.prod C D) (ZFSet.prod C D))

theorem mem_lexHeightOrder (C D rD z : ZFSet.{u}) :
    z ∈ lexHeightOrder C D rD ↔
      ∃ c ∈ C, ∃ q ∈ D, ∃ d ∈ C, ∃ v ∈ D,
        z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
          (c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ rD)) := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨c, hc, q, hq, d, hd, v, hv, rfl, lower⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, ZFSet.pair_mem_prod.2 ⟨hd, hv⟩⟩,
      c, hc, q, hq, d, hd, v, hv, rfl, lower⟩

theorem pair_mem_lexHeightOrder (C D rD c q d v : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∈ lexHeightOrder C D rD ↔
      c ∈ C ∧ q ∈ D ∧ d ∈ C ∧ v ∈ D ∧ (c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ rD)) := by
  rw [mem_lexHeightOrder]
  constructor
  · rintro ⟨c', hc, q', hq, d', hd, v', hv, equal, lower⟩
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 right
    exact ⟨hc, hq, hd, hv, lower⟩
  · rintro ⟨hc, hq, hd, hv, lower⟩
    exact ⟨c, hc, q, hq, d, hd, v, hv, rfl, lower⟩

theorem lexHeightOrder_code {C D rD : ZFSet.{u}}
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD) :
    StrictLinearOrderCode (ZFSet.prod C D) (lexHeightOrder C D rD) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_, ?_, ?_⟩
  · intro x hx hxx
    obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 hx
    rcases ((pair_mem_lexHeightOrder C D rD c q c q).1 hxx).2.2.2.2 with less | same
    · exact ZFSet.mem_irrefl c less
    · exact target.irrefl q hq same.2
  · intro x y z hxy hyz
    have xy := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hxy).1
    have yz := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hyz).1
    obtain ⟨c, hc, q, hq, rfl⟩ := ZFSet.mem_prod.1 xy.1
    obtain ⟨d, _, v, _, rfl⟩ := ZFSet.mem_prod.1 xy.2
    obtain ⟨b, hb, w, hw, rfl⟩ := ZFSet.mem_prod.1 yz.2
    have left := ((pair_mem_lexHeightOrder C D rD c q d v).1 hxy).2.2.2.2
    have right := ((pair_mem_lexHeightOrder C D rD d v b w).1 hyz).2.2.2.2
    apply (pair_mem_lexHeightOrder C D rD c q b w).2
    refine ⟨hc, hq, hb, hw, ?_⟩
    rcases left with lower | ⟨same, inside⟩
    · rcases right with lower' | ⟨same', _⟩
      · exact Or.inl (columns.2 b hb d lower' c lower)
      · exact Or.inl (same' ▸ lower)
    · rcases right with lower' | ⟨same', inside'⟩
      · exact Or.inl (same.symm ▸ lower')
      · exact Or.inr ⟨same.trans same', target.trans q v w inside inside'⟩
  · intro x hx y hy
    obtain ⟨c, hc, q, hq, rfl⟩ := ZFSet.mem_prod.1 hx
    obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 hy
    rcases ordinalSetProperty_mem_compare columns hc hd with lower | same | greater
    · exact Or.inl ((pair_mem_lexHeightOrder C D rD c q d v).2 ⟨hc, hq, hd, hv, Or.inl lower⟩)
    · subst d
      rcases target.compare q hq v hv with lower | same | greater
      · exact Or.inl ((pair_mem_lexHeightOrder C D rD c q c v).2
          ⟨hc, hq, hc, hv, Or.inr ⟨rfl, lower⟩⟩)
      · exact Or.inr (Or.inl (congrArg (ZFSet.pair c) same))
      · exact Or.inr (Or.inr ((pair_mem_lexHeightOrder C D rD c v c q).2
          ⟨hc, hv, hc, hq, Or.inr ⟨rfl, greater⟩⟩))
    · exact Or.inr (Or.inr ((pair_mem_lexHeightOrder C D rD d v c q).2
        ⟨hd, hv, hc, hq, Or.inl greater⟩))

namespace StrictLexHeightCode

noncomputable def value {L C D r h rD : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) (x : {a : ZFSet.{u} // a ∈ L}) :
    {y : ZFSet.{u} // y ∈ ZFSet.prod C D} :=
  let function : FunctionGraphOn L h := ⟨ZFSet.prod C D, code.function⟩
  ⟨function.value x, (ZFSet.pair_mem_prod.1 (code.function.1 (function.value_entry x))).2⟩

theorem value_entry {L C D r h rD : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) (x : {a : ZFSet.{u} // a ∈ L}) :
    ZFSet.pair x.val (code.value x).val ∈ h :=
  (show FunctionGraphOn L h from ⟨ZFSet.prod C D, code.function⟩).value_entry x

theorem value_eq_of_entry {L C D r h rD y : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) (x : {a : ZFSet.{u} // a ∈ L})
    (entry : ZFSet.pair x.val y ∈ h) : (code.value x).val = y :=
  (show FunctionGraphOn L h from ⟨ZFSet.prod C D, code.function⟩).value_eq_of_entry x entry

theorem value_pair_iff {L C D r h rD c q : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) (x : {a : ZFSet.{u} // a ∈ L}) :
    (code.value x).val = ZFSet.pair c q ↔ ZFSet.pair x.val (ZFSet.pair c q) ∈ h :=
  ⟨fun equal => equal ▸ code.value_entry x, fun entry => code.value_eq_of_entry x entry⟩

noncomputable def toStrictHeight {L C D r μ h rD : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) (meet : MeetOrderCode L r μ)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD) :
    StrictHeight meet.toMeetOrder (lexHeightOrder_code columns target).toLinearHeightOrder.toHeightOrder where
  value := code.value
  strict x y lower different := by
    have xEntry := code.value_entry x
    have yEntry := code.value_entry y
    obtain ⟨c, hc, q, hq, ex⟩ := ZFSet.mem_prod.1 (code.value x).property
    obtain ⟨d, hd, v, hv, ey⟩ := ZFSet.mem_prod.1 (code.value y).property
    have xHeight : ZFSet.pair x.val (ZFSet.pair c q) ∈ h := ex ▸ xEntry
    have yHeight : ZFSet.pair y.val (ZFSet.pair d v) ∈ h := ey ▸ yEntry
    have lex := code.strict x.val x.property y.val y.property c q d v lower
      (fun equal => different (Subtype.ext equal)) xHeight yHeight
    change ZFSet.pair (code.value x).val (code.value y).val ∈ lexHeightOrder C D rD
    rw [ex, ey]
    exact (pair_mem_lexHeightOrder C D rD c q d v).2 ⟨hc, hq, hd, hv, lex⟩

theorem toStrictHeight_value_entry {L C D r μ h rD : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) (meet : MeetOrderCode L r μ)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD)
    (x : {a : ZFSet.{u} // a ∈ L}) :
    ZFSet.pair x.val ((code.toStrictHeight meet columns target).value x).val ∈ h :=
  code.value_entry x

end StrictLexHeightCode

namespace BoundedFormula

def lexHeightEntryFormula {n} (z C D rD : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  exMem C (exMem D.succ (exMem C.succ.succ (exMem D.succ.succ.succ
    (.conj (pairOfPairsFormula (lift z) 3 2 1 0)
      (disj (.mem 3 1) (.conj (.equal 3 1) (pairMembershipFormula 2 0 (lift rD))))))))

theorem truth_lexHeightEntryFormula {n} (z C D rD : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (lexHeightEntryFormula z C D rD) env ↔
      ∃ c ∈ env C, ∃ q ∈ env D, ∃ d ∈ env C, ∃ v ∈ env D,
        env z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
          (c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ env rD)) := by
  simp only [lexHeightEntryFormula, truth_exMem, Truth, truth_disj,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem lexHeightOrder_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {C D rD : ZFSet.{u}} (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    lexHeightOrder C D rD ∈ M.sets := by
  have carrier := M.prod_mem pairing unions powers separation hC hD
  let params := extend C (extend D (extend rD Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.lexHeightEntryFormula 0 1 2 3) params
    (Fin.cases hC (Fin.cases hD (Fin.cases hrD (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation carrier carrier)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.lexHeightEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod (ZFSet.prod C D) (ZFSet.prod C D)) = lexHeightOrder C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, lexHeightOrder, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_lexHeightEntryFormula 0 1 2 3 _)
  exact equal ▸ selected

end TransitiveGround






namespace BatchHeightEndpointCode

variable {P rP μP I Qs rs μs As Es Fs Ss C D old rD Cs los his : ZFSet.{u}}
  {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
  (e : BatchHeightEndpointCode d C D old rD Cs los his)

noncomputable abbrev column (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} :=
  (show FunctionGraphOn I Cs from ⟨C, e.columns⟩).value i
noncomputable abbrev low (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} :=
  (show FunctionGraphOn I los from ⟨D, e.lows⟩).value i
noncomputable abbrev high (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} :=
  (show FunctionGraphOn I his from ⟨D, e.highs⟩).value i

theorem column_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (e.column i) ∈ Cs :=
  (show FunctionGraphOn I Cs from ⟨C, e.columns⟩).value_entry i
theorem low_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (e.low i) ∈ los :=
  (show FunctionGraphOn I los from ⟨D, e.lows⟩).value_entry i
theorem high_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (e.high i) ∈ his :=
  (show FunctionGraphOn I his from ⟨D, e.highs⟩).value_entry i

end BatchHeightEndpointCode

noncomputable def batchFreshHeightGraph (I Qs rs As Vs Hs Cs E C D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod (indexedAttachmentFresh I Qs rs As) (ZFSet.prod C D))
    (componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D)

noncomputable def batchHeightGraph (P I Qs rs As Vs Hs Cs E C D old : ZFSet.{u}) : ZFSet.{u} :=
  taggedHeightGraph P (indexedAttachmentFresh I Qs rs As) (ZFSet.prod C D) old
    (batchFreshHeightGraph I Qs rs As Vs Hs Cs E C D)

theorem batchHeightGraph_old_entry {P I Qs rs As Vs Hs Cs E C D old x h : ZFSet.{u}}
    (hx : x ∈ P) :
    ZFSet.pair x h ∈ batchHeightGraph P I Qs rs As Vs Hs Cs E C D old ↔ ZFSet.pair x h ∈ old :=
  taggedHeightGraph_old_entry hx

namespace TemplateHeightFamilyInputs

variable {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D rD old Cs los his E : ZFSet.{u}}
  {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
  (t : TemplateHeightFamilyInputs d Vs vrs Hs)
  (e : BatchHeightEndpointCode d C D old rD Cs los his)
  (embeddings : FunctionGraphOn I E)
  (maps : ∀ i, IntervalEmbeddingCode (t.ranges.value i) D (t.orders.value i) rD
    (e.low i) (e.high i) (embeddings.value i))

include t e embeddings maps

theorem batch_component_function :
    ZFSet.IsFunc (indexedAttachmentDomain I Qs) (ZFSet.prod C D)
      (componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D) :=
  t.componentHeightGraph_function e.columns embeddings (fun i => (maps i).injection.function)
    (fun i _ member => mem_familyPointBound_of_entry (t.ranges.value_entry i) member)

theorem batch_fresh_function :
    ZFSet.IsFunc (indexedAttachmentFresh I Qs rs As) (ZFSet.prod C D)
      (batchFreshHeightGraph I Qs rs As Vs Hs Cs E C D) := by
  have full := t.batch_component_function e embeddings maps
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_⟩
  intro x hx
  obtain ⟨y, entry, unique⟩ := full.2 x (indexedAttachmentFresh_subset I Qs rs As hx)
  exact ⟨y, ZFSet.mem_sep.2 ⟨entry, ZFSet.pair_mem_prod.2
    ⟨hx, (ZFSet.pair_mem_prod.1 (full.1 entry)).2⟩⟩,
    fun z hz => unique z (ZFSet.mem_sep.1 hz).1⟩

theorem batch_height_function (oldCode : StrictLexHeightCode P C D rP old rD) :
    ZFSet.IsFunc d.batchCarrier (ZFSet.prod C D)
      (batchHeightGraph P I Qs rs As Vs Hs Cs E C D old) :=
  taggedHeightGraph_function oldCode.function (t.batch_fresh_function e embeddings maps)

noncomputable def componentValue (i : {i : ZFSet.{u} // i ∈ I})
    (q : d.templates.Space i) : {h : ZFSet.{u} // h ∈ ZFSet.prod C D} :=
  let function : FunctionGraphOn (indexedAttachmentDomain I Qs)
      (componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D) :=
    ⟨ZFSet.prod C D, t.batch_component_function e embeddings maps⟩
  let point : {x : ZFSet.{u} // x ∈ indexedAttachmentDomain I Qs} :=
    ⟨ZFSet.pair i.val q.val, (pair_mem_indexedAttachmentDomain I Qs i.val q.val).2
      ⟨i.property, d.space i, d.space_entry i, q.property⟩⟩
  ⟨function.value point, (ZFSet.pair_mem_prod.1
    ((t.batch_component_function e embeddings maps).1 (function.value_entry point))).2⟩

theorem componentValue_entry (i : {i : ZFSet.{u} // i ∈ I}) (q : d.templates.Space i) :
    ZFSet.pair (ZFSet.pair i.val q.val) (t.componentValue e embeddings maps i q).val ∈
      componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D :=
  (show FunctionGraphOn (indexedAttachmentDomain I Qs)
      (componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D) from
    ⟨ZFSet.prod C D, t.batch_component_function e embeddings maps⟩).value_entry _

theorem componentValue_spec (i : {i : ZFSet.{u} // i ∈ I}) (q : d.templates.Space i) :
    ∃ c ∈ C, ∃ z ∈ D, (t.componentValue e embeddings maps i q).val = ZFSet.pair c z ∧
      ZFSet.pair i.val c ∈ Cs ∧ ∃ a ∈ t.ranges.value i,
        ZFSet.pair q.val a ∈ t.heights.value i ∧ ZFSet.pair a z ∈ embeddings.value i := by
  obtain ⟨c, hc, z, hz, equal⟩ := ZFSet.mem_prod.1 (t.componentValue e embeddings maps i q).property
  have entry := equal ▸ t.componentValue_entry e embeddings maps i q
  obtain ⟨_, _, _, column, a, _, height, image⟩ := (t.componentHeightGraph_entry_iff embeddings i q.val c z).1 entry
  exact ⟨c, hc, z, hz, equal, column, a,
    (ZFSet.pair_mem_prod.1 ((t.function i).1 height)).2, height, image⟩

noncomputable def componentStrictHeight (columns : ordinalSetProperty C)
    (target : StrictLinearOrderCode D rD) (i : {i : ZFSet.{u} // i ∈ I}) :
    StrictHeight (d.templates.order i) (lexHeightOrder_code columns target).toLinearHeightOrder.toHeightOrder where
  value := t.componentValue e embeddings maps i
  strict x y lower different := by
    obtain ⟨c, hc, q, hq, ex, colx, a, _, heightx, imagex⟩ := t.componentValue_spec e embeddings maps i x
    obtain ⟨b, hb, z, hz, ey, coly, v, _, heighty, imagey⟩ := t.componentValue_spec e embeddings maps i y
    have same : c = b := (show FunctionGraphOn I Cs from ⟨C, e.columns⟩).unique colx coly
    have strict := t.strict i x.val y.val a v lower (fun equal => different (Subtype.ext equal)) heightx heighty
    have imageStrict := ((maps i).order a v q z imagex imagey).1 strict
    change ZFSet.pair (t.componentValue e embeddings maps i x).val
      (t.componentValue e embeddings maps i y).val ∈ lexHeightOrder C D rD
    rw [ex, ey]
    exact (pair_mem_lexHeightOrder C D rD c q b z).2 ⟨hc, hq, hb, hz, Or.inr ⟨same, imageStrict⟩⟩

theorem component_lower (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD)
    (x : d.templates.Fresh) :
    (lexHeightOrder_code columns target).toLinearHeightOrder.lt
      ((oldCode.toStrictHeight d.oldOrder columns target).value (d.templates.base x.1))
      ((t.componentStrictHeight e embeddings maps columns target x.1).value x.2.val) := by
  obtain ⟨c, hc, z, hz, value, column, a, _, _, image⟩ :=
    t.componentValue_spec e embeddings maps x.1 x.2.val
  have base := e.base x.1 c (e.low x.1) column (e.low_entry x.1)
  have baseValue := oldCode.value_eq_of_entry (d.templates.base x.1) base
  have hlo := (ZFSet.pair_mem_prod.1 (e.lows.1 (e.low_entry x.1))).2
  have lower := ((maps x.1).inside a z image).1
  change ZFSet.pair (oldCode.value (d.templates.base x.1)).val
    (t.componentValue e embeddings maps x.1 x.2.val).val ∈ lexHeightOrder C D rD
  rw [baseValue, value]
  exact (pair_mem_lexHeightOrder C D rD c (e.low x.1) c z).2 ⟨hc, hlo, hc, hz, Or.inr ⟨rfl, lower⟩⟩

theorem component_upper (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD)
    (x : d.templates.Fresh) :
    (lexHeightOrder_code columns target).toLinearHeightOrder.lt
      ((t.componentStrictHeight e embeddings maps columns target x.1).value x.2.val)
      ((oldCode.toStrictHeight d.oldOrder columns target).value (d.templates.separator x.1)) := by
  obtain ⟨c, hc, z, hz, value, column, a, _, _, image⟩ :=
    t.componentValue_spec e embeddings maps x.1 x.2.val
  obtain ⟨b, hb, v, hv, sepValue⟩ := ZFSet.mem_prod.1 (oldCode.value (d.templates.separator x.1)).property
  have sepEntry : ZFSet.pair (d.separator x.1) (ZFSet.pair b v) ∈ old :=
    sepValue ▸ oldCode.value_entry (d.templates.separator x.1)
  have upper := e.interval_upper x.1 column (e.high_entry x.1) ((maps x.1).inside a z image).2 sepEntry
  change ZFSet.pair (t.componentValue e embeddings maps x.1 x.2.val).val
    (oldCode.value (d.templates.separator x.1)).val ∈ lexHeightOrder C D rD
  rw [value, sepValue]
  exact (pair_mem_lexHeightOrder C D rD c z b v).2 ⟨hc, hz, hb, hv, upper⟩

noncomputable def extendedHeight (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD) :
    StrictHeight d.templates.extension (lexHeightOrder_code columns target).toLinearHeightOrder.toHeightOrder :=
  AttachmentHeight.extend d.templates (oldCode.toStrictHeight d.oldOrder columns target)
    (t.componentStrictHeight e embeddings maps columns target)
    (t.component_lower e embeddings maps oldCode columns target)
    (t.component_upper e embeddings maps oldCode columns target)

theorem encoded_height_entry (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD)
    (x : {p : ZFSet.{u} // p ∈ P} ⊕ d.templates.Fresh) :
    ZFSet.pair (d.coding.encode x) ((t.extendedHeight e embeddings maps oldCode columns target).value x).val ∈
      batchHeightGraph P I Qs rs As Vs Hs Cs E C D old := by
  cases x with
  | inl x =>
    exact (batchHeightGraph_old_entry x.property).2 (oldCode.value_entry x)
  | inr x =>
    apply (taggedHeightGraph_fresh_entry oldCode.function (t.batch_fresh_function e embeddings maps)).2
    exact ZFSet.mem_sep.2 ⟨t.componentValue_entry e embeddings maps x.1 x.2.val,
      ZFSet.pair_mem_prod.2 ⟨d.freshCode_mem x, (t.componentValue e embeddings maps x.1 x.2.val).property⟩⟩

theorem batchHeightGraph_strictLex (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD) :
    StrictLexHeightCode d.batchCarrier C D d.batchOrder
      (batchHeightGraph P I Qs rs As Vs Hs Cs E C D old) rD := by
  have function := t.batch_height_function e embeddings maps oldCode
  refine ⟨function, ?_⟩
  intro x hx y hy c q b v lower different first second
  obtain ⟨s, rfl⟩ := d.coding.encode_surjective x hx
  obtain ⟨z, rfl⟩ := d.coding.encode_surjective y hy
  have strict := (t.extendedHeight e embeddings maps oldCode columns target).strict s z
    ((d.coding.le_encode s z).1 lower) (fun same => different (congrArg d.coding.encode same))
  have graph : FunctionGraphOn d.batchCarrier (batchHeightGraph P I Qs rs As Vs Hs Cs E C D old) :=
    ⟨ZFSet.prod C D, function⟩
  have eqs := graph.unique (t.encoded_height_entry e embeddings maps oldCode columns target s) first
  have eqz := graph.unique (t.encoded_height_entry e embeddings maps oldCode columns target z) second
  change ZFSet.pair ((t.extendedHeight e embeddings maps oldCode columns target).value s).val
    ((t.extendedHeight e embeddings maps oldCode columns target).value z).val ∈ lexHeightOrder C D rD at strict
  rw [eqs, eqz] at strict
  exact ((pair_mem_lexHeightOrder C D rD c q b v).1 strict).2.2.2.2

theorem batchHeightGraph_bound_preserved (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD)
    {bound : ZFSet.{u}} (hBound : bound ∈ ZFSet.prod C D)
    (oldBound : ∀ x ∈ P, ∀ h, ZFSet.pair x h ∈ old → h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD) :
    ∀ x ∈ d.batchCarrier, ∀ h,
      ZFSet.pair x h ∈ batchHeightGraph P I Qs rs As Vs Hs Cs E C D old →
        h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD := by
  let R := (lexHeightOrder_code columns target).toLinearHeightOrder.toHeightOrder
  have oldWeak : ∀ x, R.Weak ((oldCode.toStrictHeight d.oldOrder columns target).value x) ⟨bound, hBound⟩ := by
    intro x
    rcases oldBound x.val x.property (oldCode.value x).val (oldCode.value_entry x) with same | less
    · exact Or.inl (Subtype.ext same)
    · exact Or.inr less
  have preserved := AttachmentHeight.bound_preserved d.templates
    (oldCode.toStrictHeight d.oldOrder columns target)
    (t.componentStrictHeight e embeddings maps columns target)
    (t.component_upper e embeddings maps oldCode columns target) ⟨bound, hBound⟩ oldWeak
  intro x hx h entry
  obtain ⟨s, rfl⟩ := d.coding.encode_surjective x hx
  have graph : FunctionGraphOn d.batchCarrier (batchHeightGraph P I Qs rs As Vs Hs Cs E C D old) :=
    ⟨ZFSet.prod C D, t.batch_height_function e embeddings maps oldCode⟩
  have eqs := graph.unique (t.encoded_height_entry e embeddings maps oldCode columns target s) entry
  rcases preserved s with same | less
  · exact Or.inl (eqs.symm.trans (congrArg Subtype.val same))
  · apply Or.inr
    change ZFSet.pair ((t.extendedHeight e embeddings maps oldCode columns target).value s).val bound ∈
      lexHeightOrder C D rD at less
    exact eqs ▸ less

end TemplateHeightFamilyInputs

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

theorem FunctionGraphOn.constant_value {I x : ZFSet.{u}}
    (graph : FunctionGraphOn I (constantFamilyGraph I x)) (i : {i : ZFSet.{u} // i ∈ I}) :
    graph.value i = x :=
  ((pair_mem_constantFamilyGraph I x _ _).1 (graph.value_entry i)).2

theorem StrictLexHeightCode.strict_entry {P C D r old rD x y a b : ZFSet.{u}}
    (code : StrictLexHeightCode P C D r old rD) (lower : ZFSet.pair x y ∈ r)
    (different : x ≠ y) (first : ZFSet.pair x a ∈ old) (second : ZFSet.pair y b ∈ old) :
    ZFSet.pair a b ∈ lexHeightOrder C D rD := by
  have hx := ZFSet.pair_mem_prod.1 (code.function.1 first)
  have hy := ZFSet.pair_mem_prod.1 (code.function.1 second)
  obtain ⟨c, hc, q, hq, rfl⟩ := ZFSet.mem_prod.1 hx.2
  obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 hy.2
  exact (pair_mem_lexHeightOrder C D rD c q d v).2
    ⟨hc, hq, hd, hv, code.strict x hx.1 y hy.1 c q d v lower different first second⟩

namespace AttachmentBatchInputs
variable {P rP μP I Qs rs μs As Es Fs Ss P0 r0 C D old rD : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

theorem constantTemplateHeights
    (spaces : ∀ i, d.space i = P0) (relations : ∀ i, d.rel i = r0)
    (code : StrictLexHeightCode P0 C D r0 old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD) :
    TemplateHeightFamilyInputs d (constantFamilyGraph I (ZFSet.prod C D))
      (constantFamilyGraph I (lexHeightOrder C D rD)) (constantFamilyGraph I old) := by
  have rangeGraph : FunctionGraphOn I (constantFamilyGraph I (ZFSet.prod C D)) :=
    ⟨_, constantFamilyGraph_function I (ZFSet.prod C D)⟩
  have orderGraph : FunctionGraphOn I (constantFamilyGraph I (lexHeightOrder C D rD)) :=
    ⟨_, constantFamilyGraph_function I (lexHeightOrder C D rD)⟩
  have heightGraph : FunctionGraphOn I (constantFamilyGraph I old) :=
    ⟨_, constantFamilyGraph_function I old⟩
  refine {
    ranges := rangeGraph
    orders := orderGraph
    heights := heightGraph
    linear := ?_
    function := ?_
    strict := ?_
  }
  · intro i
    simpa only [FunctionGraphOn.constant_value] using lexHeightOrder_code columns target
  · intro i
    simpa only [FunctionGraphOn.constant_value, spaces i] using code.function
  · intro i x y a b lower different first second
    simp only [FunctionGraphOn.constant_value] at first second ⊢
    exact code.strict_entry (relations i ▸ lower) different first second

end AttachmentBatchInputs






noncomputable def fixedTopHeightGraph (P old b q : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair P (ZFSet.pair b q)) old

theorem pair_mem_fixedTopHeightGraph (P old b q x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ fixedTopHeightGraph P old b q ↔
      (x = P ∧ y = ZFSet.pair b q) ∨ ZFSet.pair x y ∈ old := by
  rw [fixedTopHeightGraph, ZFSet.mem_insert_iff, ZFSet.pair_inj]

theorem fixedTopHeightGraph_old_iff {P old b q x y : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair x y ∈ fixedTopHeightGraph P old b q ↔ ZFSet.pair x y ∈ old := by
  rw [pair_mem_fixedTopHeightGraph]
  exact ⟨fun h => h.elim (fun eq => False.elim (ZFSet.mem_irrefl P (eq.1 ▸ hx))) id,
    Or.inr⟩

theorem fixedTopHeightGraph_top_iff {P C D old b q y : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old) :
    ZFSet.pair P y ∈ fixedTopHeightGraph P old b q ↔ y = ZFSet.pair b q := by
  rw [pair_mem_fixedTopHeightGraph]
  exact ⟨fun h => h.elim And.right (fun h => False.elim
    (ZFSet.mem_irrefl P (ZFSet.pair_mem_prod.1 (function.1 h)).1)),
    fun h => Or.inl ⟨rfl, h⟩⟩

theorem fixedTopHeightGraph_function {P C D old b q : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old) (hb : b ∈ C) (hq : q ∈ D) :
    ZFSet.IsFunc (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | hz
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert P P, ZFSet.pair_mem_prod.2 ⟨hb, hq⟩⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem P hx, hy⟩
  · intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | hx
    · refine ⟨ZFSet.pair b q, ZFSet.mem_insert _ _, ?_⟩
      intro y hy
      exact (fixedTopHeightGraph_top_iff function).1 hy
    · obtain ⟨y, entry, unique⟩ := function.2 x hx
      refine ⟨y, (fixedTopHeightGraph_old_iff hx).2 entry, ?_⟩
      intro z hz
      exact unique z ((fixedTopHeightGraph_old_iff hx).1 hz)

theorem fixedTopHeightGraph_strict {P C D r old rD b q : ZFSet.{u}}
    (code : StrictLexHeightCode P C D r old rD) (order : PartialOrderCode P r)
    (hb : b ∈ C) (hq : q ∈ D)
    (above : ∀ c ∈ heightColumns P C D old, c ∈ b) :
    StrictLexHeightCode (fixedTopCarrier P) C D (fixedTopOrder P r)
      (fixedTopHeightGraph P old b q) rD := by
  refine ⟨fixedTopHeightGraph_function code.function hb hq, ?_⟩
  intro x hx y hy c v d w lower different xEntry yEntry
  rcases ZFSet.mem_union.1 lower with lower | top
  · have bounds := ZFSet.pair_mem_prod.1 (order.relation lower)
    exact code.strict x bounds.1 y bounds.2 c v d w lower different
      ((fixedTopHeightGraph_old_iff bounds.1).1 xEntry)
      ((fixedTopHeightGraph_old_iff bounds.2).1 yEntry)
  · obtain ⟨_, yP⟩ := ZFSet.pair_mem_prod.1 top
    have yEq : y = P := ZFSet.mem_singleton.1 yP
    subst y
    have hxOld : x ∈ P := (ZFSet.mem_insert_iff.1 hx).resolve_left different
    have oldEntry := (fixedTopHeightGraph_old_iff hxOld).1 xEntry
    have eq := ZFSet.pair_inj.1 ((fixedTopHeightGraph_top_iff code.function).1 yEntry)
    rcases eq with ⟨rfl, rfl⟩
    exact Or.inl (above c (mem_heightColumns_of_entry code.function oldEntry))

theorem fixedTopHeightGraph_range {P C D old b q : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old) (hb : b ∈ C) (hq : q ∈ D) :
    relationImage (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q) =
      insert (ZFSet.pair b q) (relationImage P (ZFSet.prod C D) old) := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, ZFSet.mem_insert_iff, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, entry⟩
    rcases (pair_mem_fixedTopHeightGraph P old b q x y).1 entry with ⟨_, eq⟩ | oldEntry
    · exact Or.inl eq
    · exact Or.inr ⟨hy, x, (ZFSet.pair_mem_prod.1 (function.1 oldEntry)).1, oldEntry⟩
  · rintro (rfl | ⟨hy, x, hx, entry⟩)
    · exact ⟨ZFSet.pair_mem_prod.2 ⟨hb, hq⟩, P, ZFSet.mem_insert P P,
        (pair_mem_fixedTopHeightGraph P old b q P _).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨hy, x, ZFSet.mem_insert_of_mem P hx,
        (pair_mem_fixedTopHeightGraph P old b q x y).2 (Or.inr entry)⟩

theorem fixedTopHeightGraph_old_lt_top {P C D old rD b q x y : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old) (hb : b ∈ C) (hq : q ∈ D)
    (above : ∀ c ∈ heightColumns P C D old, c ∈ b) (entry : ZFSet.pair x y ∈ old) :
    ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD := by
  have yShape := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨c, hc, v, hv, rfl⟩ := ZFSet.mem_prod.1 yShape
  exact (pair_mem_lexHeightOrder C D rD c v b q).2
    ⟨hc, hv, hb, hq, Or.inl (above c (mem_heightColumns_of_entry function entry))⟩

theorem fixedTopHeightGraph_bound {P C D old rD b q x y : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old) (hb : b ∈ C) (hq : q ∈ D)
    (above : ∀ c ∈ heightColumns P C D old, c ∈ b)
    (entry : ZFSet.pair x y ∈ fixedTopHeightGraph P old b q) :
    y = ZFSet.pair b q ∨ ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD := by
  rcases (pair_mem_fixedTopHeightGraph P old b q x y).1 entry with newEntry | oldEntry
  · exact Or.inl newEntry.2
  · exact Or.inr (fixedTopHeightGraph_old_lt_top function hb hq above oldEntry)






theorem batchHeightGraph_columns
    {P rP μP I Qs rs μs As Es Fs Ss Vs Hs C D old rD Cs los his E : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (e : BatchHeightEndpointCode d C D old rD Cs los his)
    (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (x c q : ZFSet.{u})
    (entry : ZFSet.pair x (ZFSet.pair c q) ∈
      batchHeightGraph P I Qs rs As Vs Hs Cs E C D old) :
    c ∈ heightColumns P C D old := by
  rcases ZFSet.mem_union.1 entry with oldEntry | freshEntry
  · exact mem_heightColumns_of_entry oldFunction oldEntry
  · obtain ⟨y, hy, h, _, equal, height⟩ := (ZFSet.mem_sep.1 freshEntry).2
    have sameHeight := (ZFSet.pair_inj.1 equal).2
    subst h
    obtain ⟨i, hi, p, equalY, _⟩ := (mem_indexedAttachmentFresh I Qs rs As y).1 hy
    subst y
    have component := (ZFSet.mem_sep.1 height).1
    obtain ⟨_, _, _, Q, g, f, _, _, _, _, column, _⟩ :=
      (pair_mem_componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D i p c q).1 component
    exact mem_heightColumns_of_entry oldFunction
      (e.base ⟨i, hi⟩ c (e.low ⟨i, hi⟩) column (e.low_entry ⟨i, hi⟩))

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem batchFreshHeightGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I Qs rs As Vs Hs Cs E C D : ZFSet.{u}}
    (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hVs : Vs ∈ M.sets) (hHs : Hs ∈ M.sets) (hCs : Cs ∈ M.sets) (hE : E ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    batchFreshHeightGraph I Qs rs As Vs Hs Cs E C D ∈ M.sets :=
  M.injection_restriction_mem separation
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
    (M.prod_mem pairing unions powers separation hC hD)
    (M.componentHeightGraph_mem pairing unions powers separation hI hQs
      (M.familyPointBound_mem unions hVs) hHs hCs hE hC hD)

theorem batchHeightGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P I Qs rs As Vs Hs Cs E C D old : ZFSet.{u}}
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hVs : Vs ∈ M.sets) (hHs : Hs ∈ M.sets)
    (hCs : Cs ∈ M.sets) (hE : E ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hOld : old ∈ M.sets) : batchHeightGraph P I Qs rs As Vs Hs Cs E C D old ∈ M.sets :=
  M.taggedHeightGraph_mem pairing unions powers separation hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
    (M.prod_mem pairing unions powers separation hC hD) hOld
    (M.batchFreshHeightGraph_mem pairing unions powers separation
      hI hQs hrs hAs hVs hHs hCs hE hC hD)

theorem exists_batchHeight
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D old rD c : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (t : TemplateHeightFamilyInputs d Vs vrs Hs)
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hVs : Vs ∈ M.sets) (hvrs : vrs ∈ M.sets) (hHs : Hs ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hOld : old ∈ M.sets) (hc : c ∈ M.sets)
    (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (oldSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega)
    (templateSmall : ∀ i, M.groundEmbeddable (t.ranges.value i) ZFSet.omega) :
    ∃ height ∈ M.sets,
      StrictLexHeightCode d.batchCarrier C D d.batchOrder height rD ∧
      (∀ p ∈ P, ∀ h, ZFSet.pair p h ∈ height ↔ ZFSet.pair p h ∈ old) ∧
      relationImage d.batchCarrier (ZFSet.prod C D) height ∈ M.sets ∧
      M.groundEmbeddable (relationImage d.batchCarrier (ZFSet.prod C D) height) ZFSet.omega ∧
      (∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height → c ∈ heightColumns P C D old) ∧
      ∀ bound ∈ ZFSet.prod C D,
        (∀ p ∈ P, ∀ h, ZFSet.pair p h ∈ old →
          h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD) →
        ∀ x ∈ d.batchCarrier, ∀ h, ZFSet.pair x h ∈ height →
          h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD := by
  obtain ⟨Cs, hCs, los, hlos, his, hhis, endpoints⟩ := M.exists_batchHeightEndpoints
    pairing unions powers separation choice d oldCode above
    hI hP hC hD hAs hEs hSs hOld hrD
  obtain ⟨E, hE, family, valid⟩ := M.exists_templateIntervalFamily
    pairing unions powers separation collection infinite choice t endpoints
    hI hVs hvrs hlos hhis hD hrD hc target coordinateInjection templateSmall
  let embeddings : FunctionGraphOn I E := ⟨M.groundRelations (familyPointBound Vs) D, family⟩
  have maps : ∀ i, IntervalEmbeddingCode (t.ranges.value i) D (t.orders.value i) rD
      (endpoints.low i) (endpoints.high i) (embeddings.value i) := by
    intro i
    exact valid i _ _ _ (endpoints.low_entry i) (endpoints.high_entry i) (embeddings.value_entry i)
  let height := batchHeightGraph P I Qs rs As Vs Hs Cs E C D old
  have hHeight : height ∈ M.sets := M.batchHeightGraph_mem pairing unions powers separation
    hP hI hQs hrs hAs hVs hHs hCs hE hC hD hOld
  have hL : d.batchCarrier ∈ M.sets := M.taggedExtension_mem pairing unions powers separation hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
  have columnLaw : ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height →
      c ∈ heightColumns P C D old := batchHeightGraph_columns endpoints oldCode.function
  obtain ⟨rangeMember, rangeSmall⟩ := M.countable_height_range_of_old_columns
    pairing unions powers separation infinite choice hP hL hC hD hOld hHeight
    oldSmall ⟨c, hc, coordinateInjection⟩ columnLaw
  refine ⟨height, hHeight,
    t.batchHeightGraph_strictLex endpoints embeddings maps oldCode columns target.toStrictLinearOrderCode,
    (fun p hp h => batchHeightGraph_old_entry hp), rangeMember, rangeSmall, columnLaw, ?_⟩
  intro bound hBound oldBound
  exact t.batchHeightGraph_bound_preserved endpoints embeddings maps oldCode columns
    target.toStrictLinearOrderCode hBound oldBound

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)

include pairing unions in
theorem fixedTopHeightGraph_mem {P old b q : ZFSet.{u}}
    (hP : P ∈ M.sets) (hOld : old ∈ M.sets) (hb : b ∈ M.sets) (hq : q ∈ M.sets) :
    fixedTopHeightGraph P old b q ∈ M.sets :=
  M.insert_mem pairing unions
    (M.orderedPair_mem pairing hP (M.orderedPair_mem pairing hb hq)) hOld

include choice in
theorem exists_fixedTopHeight
    {P D r old rD : ZFSet.{u}} (hP : P ∈ M.sets) (hD : D ∈ M.sets)
    (hOld : old ∈ M.sets) (order : PartialOrderCode P r) (nonempty : D.Nonempty)
    (code : StrictLexHeightCode P
      (M.groundOmegaOne pairing unions powers separation collection infinite) D r old rD)
    (small : M.groundEmbeddable (relationImage P (ZFSet.prod
      (M.groundOmegaOne pairing unions powers separation collection infinite) D) old) ZFSet.omega) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ b ∈ C, ∃ q ∈ D, ∃ height ∈ M.sets,
      height = fixedTopHeightGraph P old b q ∧
      (∀ c ∈ heightColumns P C D old, c ∈ b) ∧
      b ∉ heightColumns P C D old ∧
      StrictLexHeightCode (fixedTopCarrier P) C D (fixedTopOrder P r) height rD ∧
      (∀ x ∈ P, ∀ y, ZFSet.pair x y ∈ height ↔ ZFSet.pair x y ∈ old) ∧
      (∀ y, ZFSet.pair P y ∈ height ↔ y = ZFSet.pair b q) ∧
      relationImage (fixedTopCarrier P) (ZFSet.prod C D) height =
        insert (ZFSet.pair b q) (relationImage P (ZFSet.prod C D) old) ∧
      relationImage (fixedTopCarrier P) (ZFSet.prod C D) height ∈ M.sets ∧
      M.groundEmbeddable (relationImage (fixedTopCarrier P) (ZFSet.prod C D) height) ZFSet.omega ∧
      (∀ x y, ZFSet.pair x y ∈ old →
        ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD) ∧
      (∀ x y, ZFSet.pair x y ∈ height →
        y = ZFSet.pair b q ∨ ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD) := by
  let C := M.groundOmegaOne pairing unions powers separation collection infinite
  change ∃ b ∈ C, ∃ q ∈ D, ∃ height ∈ M.sets, _
  have hC : C ∈ M.sets :=
    (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  have hK := M.heightColumns_mem pairing unions powers separation hP hC hD hOld
  have smallK := M.heightColumns_countable pairing unions powers separation infinite choice
    hP hC hD hOld small
  have subset : heightColumns P C D old ⊆ C :=
    fun x hx => ((mem_relationImage _ C _ x).1 hx).1
  obtain ⟨b, hb, above⟩ := M.groundOmegaOne_countable_bound pairing unions powers separation
    collection infinite choice hK subset smallK
  obtain ⟨q, hq⟩ := nonempty
  have hbM := M.transitive hC hb
  have hqM := M.transitive hD hq
  have hPair := M.orderedPair_mem pairing hbM hqM
  have hRange := M.relationImage_mem separation hP
    (M.prod_mem pairing unions powers separation hC hD) hOld
  have rangeEq := fixedTopHeightGraph_range code.function hb hq
  refine ⟨b, hb, q, hq, fixedTopHeightGraph P old b q,
    M.fixedTopHeightGraph_mem pairing unions hP hOld hbM hqM, rfl, above,
    fun h => ZFSet.mem_irrefl b (above b h),
    fixedTopHeightGraph_strict code order hb hq above,
    fun x hx y => fixedTopHeightGraph_old_iff hx,
    fun y => fixedTopHeightGraph_top_iff code.function, rangeEq, ?_, ?_, ?_, ?_⟩
  · rw [rangeEq]
    exact M.insert_mem pairing unions hPair hRange
  · rw [rangeEq]
    exact M.groundEmbeddable_insert pairing unions powers separation infinite hRange hPair small
  · intro x y entry
    exact fixedTopHeightGraph_old_lt_top code.function hb hq above entry
  · intro x y entry
    exact fixedTopHeightGraph_bound code.function hb hq above entry

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_batchHeight_of_countable_ranges
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D old rD c : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (t : TemplateHeightFamilyInputs d Vs vrs Hs)
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hVs : Vs ∈ M.sets) (hvrs : vrs ∈ M.sets) (hHs : Hs ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hOld : old ∈ M.sets) (hc : c ∈ M.sets)
    (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (oldSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega)
    (templateSmall : ∀ i, M.groundEmbeddable
      (relationImage (d.space i) (t.ranges.value i) (t.heights.value i)) ZFSet.omega) :
    ∃ height ∈ M.sets,
      StrictLexHeightCode d.batchCarrier C D d.batchOrder height rD ∧
      (∀ p ∈ P, ∀ h, ZFSet.pair p h ∈ height ↔ ZFSet.pair p h ∈ old) ∧
      relationImage d.batchCarrier (ZFSet.prod C D) height ∈ M.sets ∧
      M.groundEmbeddable (relationImage d.batchCarrier (ZFSet.prod C D) height) ZFSet.omega ∧
      (∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height → c ∈ heightColumns P C D old) ∧
      ∀ bound ∈ ZFSet.prod C D,
        (∀ p ∈ P, ∀ h, ZFSet.pair p h ∈ old →
          h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD) →
        ∀ x ∈ d.batchCarrier, ∀ h, ZFSet.pair x h ∈ height →
          h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD := by
  obtain ⟨Rs, hRs, ors, hors, restricted, rangeEq, _⟩ :=
    M.exists_templateHeightRanges pairing unions powers separation t hI hQs hVs hvrs hHs
  have small : ∀ i, M.groundEmbeddable (restricted.ranges.value i) ZFSet.omega := by
    intro i
    rw [rangeEq i]
    exact templateSmall i
  exact M.exists_batchHeight pairing unions powers separation collection infinite choice d restricted
    hP hI hQs hrs hAs hEs hSs hRs hors hHs hC hD hrD hOld hc oldCode columns target above
    coordinateInjection oldSmall small

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_height_step
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {C D rD c original old : ZFSet.{u}}
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (hOriginal : original ∈ M.sets) (hOld : old ∈ M.sets)
    (originalCode : StrictLexHeightCode P0 C D r0 original rD)
    (oldCode : StrictLexHeightCode state.data.D C D state.data.rD old rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P0 (ZFSet.prod C D) original) ZFSet.omega)
    (oldSmall : M.groundEmbeddable (relationImage state.data.D (ZFSet.prod C D) old) ZFSet.omega) :
    ∃ height ∈ M.sets,
      StrictLexHeightCode state.data.currentCarrier C D state.data.currentOrder height rD ∧
      (∀ x ∈ state.data.D, ∀ y, ZFSet.pair x y ∈ height ↔ ZFSet.pair x y ∈ old) ∧
      relationImage state.data.currentCarrier (ZFSet.prod C D) height ∈ M.sets ∧
      M.groundEmbeddable (relationImage state.data.currentCarrier (ZFSet.prod C D) height) ZFSet.omega ∧
      (∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ height → a ∈ heightColumns state.data.D C D old) ∧
      ∀ bound ∈ ZFSet.prod C D,
        (∀ x ∈ state.data.D, ∀ y, ZFSet.pair x y ∈ old →
          y = bound ∨ ZFSet.pair y bound ∈ lexHeightOrder C D rD) →
        ∀ x ∈ state.data.currentCarrier, ∀ y, ZFSet.pair x y ∈ height →
          y = bound ∨ ZFSet.pair y bound ∈ lexHeightOrder C D rD := by
  have spaces : ∀ i, state.batch.space i = P0 :=
    fun i => ((constant.space_entry_iff _ _).1 (state.batch.space_entry i)).2
  have relations : ∀ i, state.batch.rel i = r0 :=
    fun i => ((constant.relation_entry_iff _ _).1 (state.batch.rel_entry i)).2
  let templates := state.batch.constantTemplateHeights spaces relations originalCode columns
    target.toStrictLinearOrderCode
  have templateSmall : ∀ i, M.groundEmbeddable
      (relationImage (state.batch.space i) (templates.ranges.value i) (templates.heights.value i))
      ZFSet.omega := by
    intro i
    simpa only [FunctionGraphOn.constant_value, spaces i] using originalSmall
  have hValues := M.prod_mem pairing unions powers separation hC hD
  have hOrder := M.lexHeightOrder_mem pairing unions powers separation hC hD hrD
  exact M.exists_batchHeight_of_countable_ranges pairing unions powers separation collection infinite choice
    state.batch templates state.ground.carrier state.ground.indices state.ground.spaces state.ground.relations
    state.ground.anchors state.ground.embeddings state.ground.separators
    (M.constantFamilyGraph_mem pairing unions powers separation state.ground.indices hValues)
    (M.constantFamilyGraph_mem pairing unions powers separation state.ground.indices hOrder)
    (M.constantFamilyGraph_mem pairing unions powers separation state.ground.indices hOriginal)
    hC hD hrD hOld hc oldCode columns target above coordinateInjection oldSmall templateSmall

end PartitionPilot.Forcing.GroundCompressionState

end OAI
