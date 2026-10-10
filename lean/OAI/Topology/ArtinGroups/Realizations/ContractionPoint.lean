import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Initial

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def contractionToPoint {X:Type*} [TopologicalSpace X]
    (a:X) (H:ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X a)) (b:X) :
    ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.const X b) :=
  H.trans {
    toFun p:=H (σ p.1,b)
    continuous_toFun:=H.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_const)
    map_zero_left:=by intro x;rw [unitInterval.symm_zero,H.apply_one];rfl
    map_one_left:=by intro x;rw [unitInterval.symm_one,H.apply_zero];rfl }

theorem orderWeights_contractible_of_piece (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (c:P) (a0:WeightContractionPiece r c)
    (hl:∀v,v∉a0.carrier → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ContractibleSpace (OrderWeights P) := by
  let X:Type u:={a:WeightContractionPiece r c // a0.Extends a}
  let R:X→X→Prop:=fun a b=>a.val.Extends b.val
  let : Nonempty X := ⟨a0,WeightContractionPiece.extends_refl a0⟩
  have hbound:∀C:Set X,IsChain R C→C.Nonempty→∃ub:X,∀a∈C,R a ub:=by
    intro C hc hn
    let D:Set (WeightContractionPiece r c):=Subtype.val '' C
    have hd:IsChain WeightContractionPiece.Extends D:=by
      rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ hne
      exact hc ha hb (fun he=>hne (congrArg Subtype.val he))
    have hdn:D.Nonempty:=hn.image Subtype.val
    let u:=WeightContractionPiece.union D hd hdn
    have h0:a0.Extends u:=by
      obtain ⟨a,ha⟩:=hn
      exact WeightContractionPiece.extends_trans a.property
        (WeightContractionPiece.extends_union D hd hdn ⟨a,ha,rfl⟩)
    refine ⟨⟨u,h0⟩,?_⟩
    intro a ha
    exact WeightContractionPiece.extends_union D hd hdn ⟨a,ha,rfl⟩
  obtain ⟨a,ha⟩:=exists_maximal_of_nonempty_chains_bounded (r:=R) hbound
    (fun hab hbd=>WeightContractionPiece.extends_trans hab hbd)
  have hfull:∀x,x∈a.val.carrier:=by
    by_contra hn
    obtain ⟨v,hv,heA⟩:=WeightContractionPiece.missing_minimal wf htotal a.val (not_forall.mp hn)
    have hv0:v∉a0.carrier:=fun he=>hv (a.property.choose he)
    let b:=WeightContractionPiece.successor wf a.val v hv heA (hl v hv0)
    have hab:a.val.Extends b:=WeightContractionPiece.extends_successor wf a.val v hv heA (hl v hv0)
    let z:X:=⟨b,WeightContractionPiece.extends_trans a.property hab⟩
    have hback:=ha z hab
    exact hv (hback.choose (Set.mem_insert v a.val.carrier))
  let e:a.val.carrier≃oP:={
    toFun:=Subtype.val
    invFun:=fun x=>⟨x,hfull x⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl
    map_rel_iff':=by intros;rfl }
  exact (contractible_iff_id_nullhomotopic _).mpr
    ⟨weightHomeomorph e (weightVertex ⟨c,a.val.root_mem⟩),
      ⟨transportContraction (weightHomeomorph e) _ a.val.hom⟩⟩

theorem orderWeights_contractible_of_initial (r:P→P→Prop) (wf:WellFounded r)
    (htotal:∀x y,x≠y → r x y ∨ r y x) (A:Set P)
    (hdown:∀{x y},x∈A → r y x → y∈A)
    (hA:ContractibleSpace (OrderWeights A))
    (hl:∀v,v∉A → ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ContractibleSpace (OrderWeights P) := by
  obtain ⟨a,⟨H⟩⟩:=@id_nullhomotopic _ _ hA
  obtain ⟨v,hv⟩:=a.support_nonempty
  let c:P:=v.val

  let H':ContinuousMap.Homotopy (ContinuousMap.id (OrderWeights A))
      (ContinuousMap.const _ (weightVertex v)):=
    contractionToPoint a H (weightVertex v)
  let a0:WeightContractionPiece r c:={
    carrier:=A
    root_mem:=v.property
    down:=hdown
    hom:=H' }
  exact orderWeights_contractible_of_piece r wf htotal c a0 hl

end HarmonicArtin

end OAI
