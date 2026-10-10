import Mathlib
import OAI.Topology.ArtinGroups.Realizations.OrderWeightsContractibleUnique

namespace OAI

namespace HarmonicArtin
open CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {P:Type u} [PartialOrder P]

noncomputable def weightColor {A:Type v} (f:P→A) (w:OrderWeights P) : A :=
  f (Classical.choose w.support_nonempty)

lemma weightColor_eq {A:Type v} (f:P→A) (hf:∀x y,x≤y → f x=f y)
    (w:OrderWeights P) (p:P) (hp:p∈w.weights.support) : weightColor f w=f p := by
  rcases w.chain (Classical.choose w.support_nonempty) (Classical.choose_spec w.support_nonempty) p hp with h|h
  · exact hf _ _ h
  · exact (hf _ _ h).symm

lemma weightColor_continuous {A:Type v} [TopologicalSpace A] (f:P→A)
    (hf:∀x y,x≤y → f x=f y) : Continuous (weightColor f) := by
  rw [orderWeights_continuous_iff]
  intro n x
  have he: (fun z=>weightColor f (orderWeightsOfChain (nerveChain x) z))=
      (fun _ : Convexity.StdSimplex ℝ (Fin (n.len+1))=>f (nerveChain x 0)) := by
    funext z
    let w:=orderWeightsOfChain (nerveChain x) z
    have hp:Classical.choose w.support_nonempty∈(chainWeights (nerveChain x) z).support:=Classical.choose_spec w.support_nonempty
    obtain ⟨j,_,hj⟩:=Finset.mem_image.mp (chainWeights_support (nerveChain x) z hp)
    change f (Classical.choose w.support_nonempty)=_
    rw [←hj]
    exact (hf _ _ ((nerveChain x).monotone (Fin.zero_le j))).symm
  rw [he]
  exact continuous_const

lemma weightColor_vertex {A:Type v} (f:P→A) (hf:∀x y,x≤y → f x=f y) (p:P) :
    weightColor f (weightVertex p)=f p := by
  apply weightColor_eq f hf
  simp [weightVertex]

lemma orderWeights_colors_eq {A:Type v} (h:ContractibleSpace (OrderWeights P))
    (f:P→A) (hf:∀x y,x≤y → f x=f y) (x y:P) : f x=f y := by
  let _ := h
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have he:=PreconnectedSpace.constant (inferInstance:PreconnectedSpace (OrderWeights P))
    (weightColor_continuous f hf) (x:=weightVertex x) (y:=weightVertex y)
  simpa only [weightColor_vertex f hf] using he

variable (r:P→P→Prop) (wf:WellFounded r)

noncomputable def weightSource : P→P :=
  wf.fix (fun v f=>if h:Nonempty (WeightEarlierLink r v) then
    f (Classical.choice h).val (Classical.choice h).property.1 else v)

lemma weightSource_eq (v:P) : weightSource r wf v=
    if h:Nonempty (WeightEarlierLink r v) then
      weightSource r wf (Classical.choice h).val else v := by
  rw [weightSource,WellFounded.fix_eq]

lemma weightSource_of_empty (v:P) (h:¬Nonempty (WeightEarlierLink r v)) :
    weightSource r wf v=v := by rw [weightSource_eq,dite_eq_right h]

lemma weightSource_near (htotal:∀x y,x≠y → r x y ∨ r y x)
    (hl:∀v,Nonempty (WeightEarlierLink r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLink r v))) :
    ∀v x,r x v → (x≤v ∨ v≤x) → weightSource r wf x=weightSource r wf v := by
  intro v
  induction v using wf.induction with
  | h v ih =>
    intro x hx hcomp
    have hn:Nonempty (WeightEarlierLink r v):=⟨⟨x,hx,hcomp⟩⟩
    have hcolor:∀a b:WeightEarlierLink r v,a≤b →
        weightSource r wf a.val=weightSource r wf b.val:=by
      intro a b hab
      by_cases he:a.val=b.val
      · rw [he]
      · rcases htotal a b he with h|h
        · exact ih b b.property.1 a h (Or.inl hab)
        · exact (ih a a.property.1 b h (Or.inr hab)).symm
    rw [weightSource_eq r wf v,dite_eq_left hn]
    exact orderWeights_colors_eq (hl v hn) (fun a=>weightSource r wf a.val) hcolor
      ⟨x,hx,hcomp⟩ (Classical.choice hn)

lemma weightSource_comparable (htotal:∀x y,x≠y → r x y ∨ r y x)
    (hl:∀v,Nonempty (WeightEarlierLink r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLink r v)))
    (x y:P) (h:x≤y) : weightSource r wf x=weightSource r wf y := by
  by_cases he:x=y
  · rw [he]
  · rcases htotal x y he with he|he
    · exact weightSource_near r wf htotal hl y x he (Or.inl h)
    · exact (weightSource_near r wf htotal hl x y he (Or.inr h)).symm

include wf in

theorem orderWeights_contractible_connected [CategoryTheory.IsConnected P]
    (htotal:∀x y,x≠y → r x y ∨ r y x)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (hl:∀v,Nonempty (WeightEarlierLower r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLower r v)))
    (hu:∀v,Nonempty (WeightEarlierUpper r v) →
      ContractibleSpace (OrderWeights (WeightEarlierUpper r v))) :
    ContractibleSpace (OrderWeights P) := by
  have hlink:∀v,Nonempty (WeightEarlierLink r v) →
      ContractibleSpace (OrderWeights (WeightEarlierLink r v)):=by
    intro v hv
    rcases weightLink_nonempty_parts r (fun x=>wf.irrefl.irrefl x) v hv with h|h
    · exact weightLink_contractible_of_lower r (fun x=>wf.irrefl.irrefl x) v k N hk hmono (hl v h)
    · exact weightLink_contractible_of_upper r (fun x=>wf.irrefl.irrefl x) v k N hk hmono (hu v h)
  apply orderWeights_contractible_unique_source r wf htotal k N hk hmono hl hu ?_ inferInstance
  intro x y hx hy
  have he:=CategoryTheory.constant_of_preserves_morphisms (weightSource r wf)
    (fun a b hab=>weightSource_comparable r wf htotal hlink a b (leOfHom hab)) x y
  simpa only [weightSource_of_empty r wf x hx,weightSource_of_empty r wf y hy] using he

end HarmonicArtin

end OAI
