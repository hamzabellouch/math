import OAI.SetTheory.PartitionPrinciple.Definability.GroundTaggedComponentGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.TaggedGrowthLayerFormulas
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundBatchBirths

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem batchTemplateGraph_eq_section (I P Qs rs As Es i : ZFSet.{u}) :
    batchTemplateGraph I P Qs rs As Es i =
      indexedRelationSection (familyPointBound Qs)
        (taggedExtension P (indexedAttachmentFresh I Qs rs As))
        (batchAttachmentTemplateGraph I P Qs rs As Es) i := by
  apply ZFSet.ext
  intro z
  rw [batchTemplateGraph, ZFSet.mem_sep, mem_indexedRelationSection]
  constructor
  · exact fun h => h.2
  · rintro ⟨q, hq, y, hy, rfl, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hq, hy⟩, q, hq, y, hy, rfl, entry⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def batchTemplateFamily (I P Qs rs As Es : ZFSet.{u}) : ZFSet.{u} :=
  M.indexedRelationSections I (familyPointBound Qs)
    (taggedExtension P (indexedAttachmentFresh I Qs rs As))
    (batchAttachmentTemplateGraph I P Qs rs As Es)

noncomputable def batchTemplateFamilyBound (I P Qs rs As : ZFSet.{u}) : ZFSet.{u} :=
  M.groundRelations (familyPointBound Qs)
    (taggedExtension P (indexedAttachmentFresh I Qs rs As))

theorem batchTemplateFamily_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs rs As Es : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) :
    M.batchTemplateFamilyBound I P Qs rs As ∈ M.sets ∧
      M.batchTemplateFamily I P Qs rs As Es ∈ M.sets ∧
      ZFSet.IsFunc I (M.batchTemplateFamilyBound I P Qs rs As)
        (M.batchTemplateFamily I P Qs rs As Es) ∧
      ∀ i e, ZFSet.pair i e ∈ M.batchTemplateFamily I P Qs rs As Es ↔
        i ∈ I ∧ e = batchTemplateGraph I P Qs rs As Es i := by
  have hPoints := M.familyPointBound_mem unions hQs
  have hL := M.taggedExtension_mem pairing unions powers separation hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
  have hGraph := M.batchAttachmentTemplateGraph_mem pairing unions powers separation hI hP hQs hrs hAs hEs
  have spec := M.indexedRelationSections_spec pairing unions powers separation hI hPoints hL hGraph
  refine ⟨M.groundRelations_mem pairing unions powers separation hPoints hL, spec.1, spec.2.1, ?_⟩
  intro i e
  exact (spec.2.2 i e).trans (and_congr Iff.rfl (by rw [batchTemplateGraph_eq_section]))

end TransitiveGround

namespace AttachmentBatchInputs
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

noncomputable abbrev batchIncomingFiber (_d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss) := ZFSet.prod {P} (indexedAttachmentFresh I Qs rs As)
noncomputable abbrev batchIncomingComponents (_d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss) :=
  taggedComponentGraph P I (familyPointBound Qs) (indexedAttachmentFresh I Qs rs As)

theorem batchIncomingFiber_eq {birth stamp : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp) :
    d.batchIncomingFiber = layerBirthFiber d.batchCarrier (d.batchBirth birth stamp) stamp := by
  apply ZFSet.ext
  intro x
  rw [mem_layerBirthFiber]
  constructor
  · intro hx
    exact ⟨ZFSet.mem_union.2 (Or.inr hx), (taggedBirth_stamp_iff earlier).2 hx⟩
  · exact fun hx => (taggedBirth_stamp_iff earlier).1 hx.2

theorem batchIncomingComponents_function :
    ZFSet.IsFunc d.batchIncomingFiber I d.batchIncomingComponents :=
  taggedComponentGraph_function (fun _ hn => indexedAttachmentDomain_subset I Qs
    (indexedAttachmentFresh_subset I Qs rs As hn))

theorem batchIncomingComponents_encode (q : d.templates.Fresh) {i : ZFSet.{u}}
    (entry : ZFSet.pair (d.coding.encode (.inr q)) i ∈ d.batchIncomingComponents) :
    q.1.val = i := by
  obtain ⟨_, z, _, _, equal⟩ := (pair_mem_taggedComponentGraph _ _ _ _ _ _).1 entry
  change ZFSet.pair P (ZFSet.pair q.1.val q.2.val.val) = ZFSet.pair P (ZFSet.pair i z) at equal
  exact (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).2).1

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
variable (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets)

include pairing unions powers separation hP hI hQs hrs hAs in
theorem batchIncomingComponents_ground :
    d.batchIncomingFiber ∈ M.sets ∧ d.batchIncomingComponents ∈ M.sets := by
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs
  have hSingle : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  exact ⟨M.prod_mem pairing unions powers separation hSingle hN,
    M.taggedComponentGraph_mem pairing unions powers separation hP hI
      (M.familyPointBound_mem unions hQs) hN⟩

include pairing unions powers separation hP hI hQs hrs hAs hEs in
theorem batchSeparatedLayerCode
    {HQs Hrs Hμs HTime T birth stamp Indices : ZFSet.{u}}
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (indices : ZFSet.IsFunc I stamp Indices)
    (sourceMatches : ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ s,
      ZFSet.pair i.val s ∈ Indices →
        ZFSet.pair s (d.space i) ∈ HQs ∧ ZFSet.pair s (d.rel i) ∈ Hrs ∧
        ZFSet.pair s (d.meet i) ∈ Hμs) :
    SeparatedLayerCode HQs Hrs Hμs d.batchCarrier d.batchOrder d.batchMeetGraph
      (d.batchBirth birth stamp) stamp I Indices (M.batchTemplateFamily I P Qs rs As Es)
      (M.batchTemplateFamilyBound I P Qs rs As) d.batchIncomingComponents d.batchIncomingFiber := by
  have maps := M.batchTemplateFamily_spec pairing unions powers separation hI hP hQs hrs hAs hEs
  refine ⟨indices, maps.2.2.1, d.batchIncomingFiber_eq earlier,
    d.batchIncomingComponents_function, ?_, ?_, ?_⟩
  · intro i hi s _ e Q R V indexEntry mapEntry spaceEntry orderEntry meetEntry
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    have matching :=  sourceMatches j s indexEntry
    have qeq := historySpaces.unique spaceEntry matching.1
    have req := historyOrders.unique orderEntry matching.2.1
    have veq := historyMeets.unique meetEntry matching.2.2
    have eeq := ((maps.2.2.2 i e).1 mapEntry).2
    subst Q R V e
    exact d.batch_template_embedding_code j
  · intro i hi s _ e Q x hx indexEntry mapEntry spaceEntry componentEntry
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    have qeq := historySpaces.unique spaceEntry (sourceMatches j s indexEntry).1
    have eeq := ((maps.2.2.2 i e).1 mapEntry).2
    subst Q e
    obtain ⟨_, q, _, fresh, rfl⟩ := (pair_mem_taggedComponentGraph _ _ _ _ _ _).1 componentEntry
    have qFresh := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
      (d.space_entry j) (d.rel_entry j) (d.anchor_entry j)).1 fresh
    exact (mem_relationImage _ _ _ _).2 ⟨hx, q, (mem_freshPart _ _ _ _).1 qFresh |>.1,
      (pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).2
        ((d.batch_template_entry_iff j q _).2 (Or.inr ⟨qFresh, rfl⟩))⟩
  · intro x hx y hy i _ j _ componentX componentY different
    obtain ⟨qx, eqx⟩ := d.batchBirth_fresh_cases earlier ((taggedBirth_stamp_iff earlier).2 hx)
    obtain ⟨qy, eqy⟩ := d.batchBirth_fresh_cases earlier ((taggedBirth_stamp_iff earlier).2 hy)
    have first := d.batchIncomingComponents_encode qx (eqx.symm ▸ componentX)
    have second := d.batchIncomingComponents_encode qy (eqy.symm ▸ componentY)
    have neq : qx.1 ≠ qy.1 := fun equal => different
      (first.symm.trans ((congrArg Subtype.val equal).trans second))
    exact eqx ▸ eqy ▸ d.batchBirth_different_components_bridge born earlier qx qy neq

include pairing unions powers separation hP hI hQs hrs hAs hEs in
theorem batchSeparatedWitness
    {HQs Hrs Hμs HTime T birth stamp Indices N : ZFSet.{u}}
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (hIndices : Indices ∈ M.sets) (indices : ZFSet.IsFunc I stamp Indices)
    (sourceMatches : ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ s,
      ZFSet.pair i.val s ∈ Indices →
        ZFSet.pair s (d.space i) ∈ HQs ∧ ZFSet.pair s (d.rel i) ∈ Hrs ∧
        ZFSet.pair s (d.meet i) ∈ Hμs) :
    let z := separatedLayerWitness I Indices (M.batchTemplateFamily I P Qs rs As Es)
      (M.batchTemplateFamilyBound I P Qs rs As) d.batchIncomingComponents d.batchIncomingFiber
    z ∈ M.sets ∧ GrowthLayerWitnessCode HQs Hrs Hμs d.batchCarrier d.batchOrder d.batchMeetGraph
      (d.batchBirth birth stamp) stamp N z := by
  have maps := M.batchTemplateFamily_spec pairing unions powers separation hI hP hQs hrs hAs hEs
  have components := d.batchIncomingComponents_ground pairing unions powers separation hP hI hQs hrs hAs
  exact ⟨M.separatedLayerWitness_mem pairing unions hI hIndices maps.2.1 maps.1 components.2 components.1,
    Or.inr (Or.inr ⟨I, Indices, _, _, _, _, rfl,
      d.batchSeparatedLayerCode pairing unions powers separation hP hI hQs hrs hAs hEs
        historySpaces historyOrders historyMeets born earlier indices sourceMatches⟩)⟩

end AttachmentBatchInputs

namespace AttachmentBatchInputs
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

noncomputable def constantBatchLayerWitness (M : TransitiveGround.{u}) (τ : ZFSet.{u}) : ZFSet.{u} :=
  separatedLayerWitness I (constantFamilyGraph I τ) (M.batchTemplateFamily I P Qs rs As Es)
    (M.batchTemplateFamilyBound I P Qs rs As) d.batchIncomingComponents d.batchIncomingFiber

theorem constantBatchLayerWitness_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets)
    {HQs Hrs Hμs HTime T birth stamp τ P0 r0 μ0 N : ZFSet.{u}}
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (hStamp : stamp ∈ M.sets) (before : τ ∈ stamp)
    (constant : ∀ i, d.space i = P0 ∧ d.rel i = r0 ∧ d.meet i = μ0)
    (source : ZFSet.pair τ P0 ∈ HQs ∧ ZFSet.pair τ r0 ∈ Hrs ∧ ZFSet.pair τ μ0 ∈ Hμs) :
    d.constantBatchLayerWitness M τ ∈ M.sets ∧
      GrowthLayerWitnessCode HQs Hrs Hμs d.batchCarrier d.batchOrder d.batchMeetGraph
        (d.batchBirth birth stamp) stamp N (d.constantBatchLayerWitness M τ) := by
  have indices : ZFSet.IsFunc I stamp (constantFamilyGraph I τ) := by
    refine ⟨?_, (constantFamilyGraph_function I τ).2⟩
    intro z hz
    obtain ⟨i, hi, s, hs, rfl⟩ := ZFSet.mem_prod.1 ((constantFamilyGraph_function I τ).1 hz)
    obtain rfl := ZFSet.mem_singleton.1 hs
    exact ZFSet.pair_mem_prod.2 ⟨hi, before⟩
  apply d.batchSeparatedWitness pairing unions powers separation hP hI hQs hrs hAs hEs
    historySpaces historyOrders historyMeets born earlier
    (M.constantFamilyGraph_mem pairing unions powers separation hI (M.transitive hStamp before)) indices
  intro i s entry
  obtain rfl := ((pair_mem_constantFamilyGraph I τ i.val s).1 entry).2
  simpa only [(constant i).1, (constant i).2.1, (constant i).2.2] using source

end AttachmentBatchInputs
end PartitionPilot.Forcing

end OAI
