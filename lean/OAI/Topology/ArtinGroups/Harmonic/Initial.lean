import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.UnionCarrier
import OAI.Topology.ArtinGroups.Harmonic.InsertOldIso

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

lemma weight_eq_vertex_subsingleton [Subsingleton P] (w:OrderWeights P) (v:P) : w=weightVertex v := by
  apply weight_eq_vertex_of_one
  have he:w.weights.support={v}:=by
    obtain ⟨x,hx⟩:=w.support_nonempty
    have hxv:x=v:=Subsingleton.elim _ _
    subst x
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hx,fun y _=>Subsingleton.elim _ _⟩
  simpa only [Finsupp.sum,he,Finset.sum_singleton] using w.total

variable {r:P→P→Prop} {c:P}
namespace WeightContractionPiece

noncomputable def initial (hc:∀x,¬r x c) : WeightContractionPiece r c where
  carrier:={c}
  root_mem:=Set.mem_singleton c
  down:=by
    intro x y hx hy
    have he:x=c:=Set.mem_singleton_iff.mp hx
    exact (hc y (he ▸ hy)).elim
  hom:={
    toFun p:=p.2
    continuous_toFun:=continuous_snd
    map_zero_left:=fun _=>rfl
    map_one_left:=fun w=>weight_eq_vertex_subsingleton w _ }

variable (wf:WellFounded r) (htotal:∀x y,x≠y → r x y ∨ r y x)

include wf htotal in
lemma missing_minimal (a:WeightContractionPiece r c) (ha:∃x,x∉a.carrier) :
    ∃v,v∉a.carrier ∧ ∀x,x∈a.carrier↔r x v := by
  obtain ⟨v,hv,hm⟩:=wf.has_min a.carrierᶜ ha
  refine ⟨v,hv,?_⟩
  intro x
  constructor
  · intro hx
    have hne:x≠v:=by intro he;exact hv (he ▸ hx)
    rcases htotal x v hne with h|h
    · exact h
    · exact (hv (a.down hx h)).elim
  · intro h
    by_contra hn
    exact hm x hn h

variable (a:WeightContractionPiece r c) (v:P) (hv:v∉a.carrier)
  (heA:∀x,x∈a.carrier↔r x v)
  (hlink:ContractibleSpace (OrderWeights (WeightEarlierLink r v)))

noncomputable def insertLinkContractionPoint : OrderWeights (WeightLink (⟨v,Set.mem_insert v a.carrier⟩:↥(insert v a.carrier))) :=
  let e:=weightHomeomorph (insertLinkIso r (fun x=>wf.irrefl.irrefl x) a.carrier v heA).symm
  e (Classical.choose (@id_nullhomotopic _ _ hlink))

noncomputable def insertLinkContraction :
    ContinuousMap.Homotopy (ContinuousMap.id _)
      (ContinuousMap.const _ (insertLinkContractionPoint wf a v heA hlink)) :=
  transportContraction (weightHomeomorph (insertLinkIso r (fun x=>wf.irrefl.irrefl x) a.carrier v heA).symm)
    (Classical.choose (@id_nullhomotopic _ _ hlink))
    (Classical.choice (Classical.choose_spec (@id_nullhomotopic _ _ hlink)))

noncomputable def successor : WeightContractionPiece r c where
  carrier:=insert v a.carrier
  root_mem:=Set.mem_insert_of_mem v a.root_mem
  down:=by
    intro x y hx hy
    rcases Set.mem_insert_iff.mp hx with hx|hx
    · subst x
      exact Set.mem_insert_of_mem v ((heA y).mpr hy)
    · exact Set.mem_insert_of_mem v (a.down hx hy)
  hom:=by
    let E:=weightInsertContraction a.carrier v hv
      (insertLinkContractionPoint wf a v heA hlink) (insertLinkContraction wf a v heA hlink)
      (weightVertex ⟨c,a.root_mem⟩) a.hom
    refine E.cast rfl ?_
    apply ContinuousMap.ext
    intro w
    exact weightMap_vertex _ _

lemma extends_successor : a.Extends (successor wf a v hv heA hlink) := by
  refine ⟨Set.subset_insert v a.carrier,?_⟩
  intro t w
  change weightMap a.inclusion (a.hom (t,w))=
    weightMap (weightInclusion (insert v a.carrier))
      (weightInsertContraction a.carrier v hv (insertLinkContractionPoint wf a v heA hlink)
        (insertLinkContraction wf a v heA hlink) (weightVertex ⟨c,a.root_mem⟩) a.hom
        (t,weightMap (weightSubset a.carrier (insert v a.carrier) (Set.subset_insert v a.carrier)) w))
  rw [weightInsertContraction_old,weightMap_comp]
  rfl

end WeightContractionPiece

theorem orderWeights_contractible_of_earlier_links (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (c:P) (hc:∀x,¬r x c)
    (hl:∀v,v≠c → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ContractibleSpace (OrderWeights P) := by
  let : Nonempty (WeightContractionPiece r c) := ⟨WeightContractionPiece.initial hc⟩
  obtain ⟨a,ha⟩:=exists_maximal_of_nonempty_chains_bounded
    (r:=@WeightContractionPiece.Extends P _ r c)
    (fun C hc hn=>⟨WeightContractionPiece.union C hc hn,
      fun a ha=>WeightContractionPiece.extends_union C hc hn ha⟩)
    WeightContractionPiece.extends_trans
  have hfull:∀x,x∈a.carrier:=by
    by_contra hn
    have he:∃x,x∉a.carrier:=not_forall.mp hn
    obtain ⟨v,hv,heA⟩:=WeightContractionPiece.missing_minimal wf htotal a he
    have hvc:v≠c:=by intro he;exact hv (he ▸ a.root_mem)
    have hnext:=WeightContractionPiece.extends_successor wf a v hv heA (hl v hvc)
    have hback:=ha _ hnext
    exact hv (hback.choose (Set.mem_insert v a.carrier))
  let e:a.carrier≃oP:={
    toFun:=Subtype.val
    invFun:=fun x=>⟨x,hfull x⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact (contractible_iff_id_nullhomotopic _).mpr
    ⟨weightHomeomorph e (weightVertex ⟨c,a.root_mem⟩),
      ⟨transportContraction (weightHomeomorph e) _ a.hom⟩⟩

end HarmonicArtin

end OAI
