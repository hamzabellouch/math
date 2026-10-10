import Mathlib
import OAI.Topology.ArtinGroups.Realizations.NerveOrderRetractionEquiv
import OAI.Topology.ArtinGroups.Realizations.OrderWeightsContractibleLower

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
universe u

lemma weight_contractible_of_order_retraction {P Q:Type u} [PartialOrder P] [PartialOrder Q]
    (r:P→oQ) (i:Q→oP) (hr:r.comp i=OrderHom.id) (hi:∀p,p ≤ i (r p))
    (h:ContractibleSpace (OrderWeights Q)) : ContractibleSpace (OrderWeights P) := by
  have hQ:ContractibleSpace |nerve Q|:=nerveWeightsHomeomorph.contractibleSpace_iff.mpr h
  have hP:ContractibleSpace |nerve P|:=(nerveOrderRetractionEquiv r i hr hi).contractibleSpace_iff.mpr hQ
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mp hP

variable {J:Type u} (E:J→Type u) [∀j,PartialOrder (E j)] [∀j,OrderTop (E j)]

abbrev ProductBoxSlice (a:J) (b:∀j,E j) := {x:(∀j,E j) // x≤b ∧ x a≠⊤}

noncomputable def productBoxProject (a:J) (b:∀j,E j) :
    ProductBoxSlice E a b →o {t:E a //t≠⊤} where
  toFun x:=⟨x.val a,x.property.2⟩
  monotone':=fun _ _ h=>h a

noncomputable def productBoxSection (a:J) (b:∀j,E j) (hb:b a=⊤) :
    {t:E a //t≠⊤} →o ProductBoxSlice E a b where
  toFun t:=⟨Function.update b a t.val,by
    constructor
    · intro j
      by_cases h:j=a
      · subst j;simp [hb]
      · simp [Function.update_of_ne h]
    · simpa using t.property⟩
  monotone':=by
    intro x y h j
    by_cases he:j=a
    · subst j;simpa using h
    · simp [Function.update_of_ne he]

lemma productBox_contractible (a:J) (b:∀j,E j) (hb:b a=⊤)
    (h:ContractibleSpace (OrderWeights {t:E a //t≠⊤})) :
    ContractibleSpace (OrderWeights (ProductBoxSlice E a b)) := by
  apply weight_contractible_of_order_retraction (productBoxProject E a b) (productBoxSection E a b hb)
  · apply OrderHom.ext;funext x;apply Subtype.ext;change Function.update b a x.val a=x.val;simp
  · intro x j
    change x.val j ≤ Function.update b a (x.val a) j
    by_cases he:j=a
    · subst j;simp
    · simpa [Function.update_of_ne he] using x.property.1 j
  · exact h

abbrev ProductBoundary := {x:(∀j,E j) //x≠⊤}

noncomputable def productBoundarySliceIso (a:J) :
    {x:ProductBoundary E //x.val a≠⊤} ≃o ProductBoxSlice E a (⊤:∀j,E j) where
  toFun x:=⟨x.val.val,le_top,x.property⟩
  invFun x:=⟨⟨x.val,by intro he;exact x.property.2 (congrFun he a)⟩,x.property.2⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def productBoundaryFiberIso (a:J) (v:ProductBoundary E) (hv:v.val a=⊤) :
    {x:ProductBoundary E //x.val a≠⊤ ∧ x<v} ≃o ProductBoxSlice E a v.val where
  toFun x:=⟨x.val.val,x.property.2.le,x.property.1⟩
  invFun x:=⟨⟨x.val,by intro he;exact x.property.2 (congrFun he a)⟩,x.property.2,by
    apply lt_of_le_of_ne x.property.1
    intro he
    exact x.property.2 ((congrFun he a).trans hv)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

theorem productBoundary_contractible (k:ProductBoundary E→ℕ) (N:ℕ)
    (hk:∀x,k x≤N) (hm:StrictMono k) (a:J)
    (h:ContractibleSpace (OrderWeights {t:E a //t≠⊤})) :
    ContractibleSpace (OrderWeights (ProductBoundary E)) := by
  apply orderWeights_contractible_of_lower_fibers {x |x.val a≠⊤} k N hk hm
  · exact (weightHomeomorph (productBoundarySliceIso E a)).contractibleSpace_iff.mpr
      (productBox_contractible E a ⊤ rfl h)
  · intro v hv
    have he:v.val a=⊤:=not_not.mp hv
    exact (weightHomeomorph (productBoundaryFiberIso E a v he)).contractibleSpace_iff.mpr
      (productBox_contractible E a v.val he h)

end HarmonicArtin

end OAI
