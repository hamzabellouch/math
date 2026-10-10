import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightEarlierLower
import OAI.Topology.ArtinGroups.Realizations.WeightRetractionPiece

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def weightInsertRetract (A:Set P) (v:P) (hv:v∉A)
    (hc:ContractibleSpace (OrderWeights (WeightLink (⟨v,Set.mem_insert v A⟩:↥(insert v A))))) :
    C(OrderWeights ↥(insert v A),OrderWeights A) :=
  let c:=Classical.choose (@id_nullhomotopic _ _ hc)
  let H:=Classical.choice (Classical.choose_spec (@id_nullhomotopic _ _ hc))
  (show C(_,_) from ⟨(weightHomeomorph (insertOldIso A v hv)).symm,
    (weightHomeomorph (insertOldIso A v hv)).symm.continuous⟩).comp (weightVertexRetract _ c H)

lemma weightInsertRetract_old (A:Set P) (v:P) (hv:v∉A)
    (hc:ContractibleSpace (OrderWeights (WeightLink (⟨v,Set.mem_insert v A⟩:↥(insert v A)))))
    (w:OrderWeights A) :
    weightInsertRetract A v hv hc (weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) w)=w := by
  let e:=weightHomeomorph (insertOldIso A v hv)
  have he:weightMap (weightSubset A (insert v A) (Set.subset_insert v A)) w=
      weightOldMap (⟨v,Set.mem_insert v A⟩:↥(insert v A)) (e w):=by
    change _=weightMap (weightOldIncl _) (weightMap (OrderHom.ofClass (insertOldIso A v hv)) w)
    rw [weightMap_comp,insertOldIso_incl]
  rw [he]
  change e.symm (weightVertexRetract _ _ _ (weightOldMap _ (e w)))=w
  rw [weightVertexRetract_old,e.symm_apply_apply]

namespace WeightRetractionPiece
variable {r:P→P→Prop} {A:Set P}

noncomputable def initial (hA:∀{x y},x∈A → r y x → y∈A) : WeightRetractionPiece r A where
  carrier:=A
  base:=Set.Subset.rfl
  down:=hA
  map:=ContinuousMap.id _
  retract:=by intro w; rw [weightSubset_self,weightMap_id];rfl

variable (wf:WellFounded r) (htotal:∀x y,x≠y → r x y ∨ r y x)

include wf htotal in
lemma missing_minimal (a:WeightRetractionPiece r A) (ha:∃x,x∉a.carrier) :
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

variable (a:WeightRetractionPiece r A) (v:P) (hv:v∉a.carrier)
  (heA:∀x,x∈a.carrier↔r x v)
  (hlink:ContractibleSpace (OrderWeights (WeightEarlierLink r v)))

include wf heA hlink in
theorem insertLinkContractible :
    ContractibleSpace (OrderWeights (WeightLink (⟨v,Set.mem_insert v a.carrier⟩:↥(insert v a.carrier)))) :=
  (weightHomeomorph (insertLinkIso r (fun x=>wf.irrefl.irrefl x) a.carrier v heA)).contractibleSpace_iff.mpr hlink

noncomputable def successor : WeightRetractionPiece r A where
  carrier:=insert v a.carrier
  base:=a.base.trans (Set.subset_insert v a.carrier)
  down:=by
    intro x y hx hy
    rcases Set.mem_insert_iff.mp hx with hx|hx
    · subst x
      exact Set.mem_insert_of_mem v ((heA y).mpr hy)
    · exact Set.mem_insert_of_mem v (a.down hx hy)
  map:=a.map.comp (weightInsertRetract a.carrier v hv (insertLinkContractible wf a v heA hlink))
  retract:=by
    intro w
    have he:weightSubset A (insert v a.carrier) (a.base.trans (Set.subset_insert v a.carrier))=
        (weightSubset a.carrier (insert v a.carrier) (Set.subset_insert v a.carrier)).comp
          (weightSubset A a.carrier a.base):=rfl
    rw [he,← weightMap_comp]
    change a.map (weightInsertRetract _ _ _ _ (weightMap _ (weightMap _ w)))=w
    rw [weightInsertRetract_old,a.retract]

lemma extends_successor : a.Extends (successor wf a v hv heA hlink) := by
  refine ⟨Set.subset_insert v a.carrier,?_⟩
  intro w
  change a.map (weightInsertRetract _ _ _ _ (weightMap _ w))=a.map w
  exact congrArg a.map (weightInsertRetract_old a.carrier v hv
    (insertLinkContractible wf a v heA hlink) w)

end WeightRetractionPiece

theorem orderWeights_retract_of_initial (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (A:Set P)
    (hdown:∀{x y},x∈A → r y x → y∈A)
    (hl:∀v,v∉A → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ∃f:C(OrderWeights P,OrderWeights A),∀w:OrderWeights A,f (weightMap (weightInclusion A) w)=w := by
  let :Nonempty (WeightRetractionPiece r A):=⟨WeightRetractionPiece.initial hdown⟩
  obtain ⟨a,ha⟩:=exists_maximal_of_nonempty_chains_bounded
    (r:=@WeightRetractionPiece.Extends P _ r A)
    (fun C hc hn=>⟨WeightRetractionPiece.union C hc hn,
      fun a ha=>WeightRetractionPiece.extends_union C hc hn ha⟩)
    WeightRetractionPiece.extends_trans
  have hfull:∀x,x∈a.carrier:=by
    by_contra hn
    obtain ⟨v,hv,heA⟩:=WeightRetractionPiece.missing_minimal wf htotal a (not_forall.mp hn)
    have hvA:v∉A:=fun h=>hv (a.base h)
    have hnext:=WeightRetractionPiece.extends_successor wf a v hv heA (hl v hvA)
    have hback:=ha _ hnext
    exact hv (hback.choose (Set.mem_insert v a.carrier))
  let e:a.carrier≃oP:={
    toFun:=Subtype.val
    invFun:=fun x=>⟨x,hfull x⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  refine ⟨a.map.comp ⟨(weightHomeomorph e).symm,(weightHomeomorph e).symm.continuous⟩,?_⟩
  intro w
  change a.map (weightMap (e.symm:P→o a.carrier) (weightMap (weightInclusion A) w))=w
  rw [weightMap_comp]
  exact a.retract w

theorem orderWeights_retract_of_lower_fibers (A:Set P) (k:P→ℕ) (N:ℕ)
    (hk:∀x,k x≤N) (hm:StrictMono k)
    (hf:∀v,v∉A → ContractibleSpace (OrderWeights {x:P // x∈A ∧ x<v})) :
    ∃f:C(OrderWeights P,OrderWeights A),∀w:OrderWeights A,f (weightMap (weightInclusion A) w)=w := by
  let d:P→ℕ:=fun x=>N-k x
  let r:=WeightJoinEarlier A d
  have hw:=weightJoinEarlier_wf A d
  apply orderWeights_retract_of_initial r hw (weightJoinEarlier_total A d) A
    (weightJoinEarlier_initial A d)
  intro v hv
  have he:∀x,x<v → (r x v ↔ x∈A):=by
    intro x hx
    constructor
    · intro hr
      by_contra hn
      change WeightJoinEarlier A d x v at hr
      rw [weightJoinEarlier_iff] at hr
      have hlt:=hm hx
      have hb:=hk v
      simp [weightJoinKey,hn,hv,d] at hr
      omega
    · intro ha
      exact weightJoinEarlier_old A d ha hv
  let e:WeightEarlierLower r v ≃o {x:P // x∈A ∧ x<v}:={
    toFun:=fun x=>⟨x.val,(he x.val x.property.2).mp x.property.1,x.property.2⟩
    invFun:=fun x=>⟨x.val,(he x.val x.property.2).mpr x.property.1,x.property.2⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact weightLink_contractible_of_lower r (fun x=>hw.irrefl.irrefl x) v k N hk hm
    ((weightHomeomorph e).contractibleSpace_iff.mpr (hf v hv))

lemma contractible_of_continuous_retract {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (i:C(X,Y)) (r:C(Y,X)) (hr:∀x,r (i x)=x) (h:ContractibleSpace Y) : ContractibleSpace X := by
  obtain ⟨y,⟨H⟩⟩:=@id_nullhomotopic _ _ h
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨r y,⟨?_⟩⟩
  exact {
    toFun:=fun p=>r (H (p.1,i p.2))
    continuous_toFun:=r.continuous.comp (H.continuous.comp (continuous_fst.prodMk (i.continuous.comp continuous_snd)))
    map_zero_left:=fun x=>by rw [H.apply_zero];exact hr x
    map_one_left:=fun x=>by rw [H.apply_one];rfl }

end HarmonicArtin

end OAI
