import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProductBoxSlice

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {A B:Type u} [PartialOrder A] [PartialOrder B] [OrderTop A] [OrderTop B]

abbrev BinaryProductBoundary (A B:Type u) [PartialOrder A] [PartialOrder B] [OrderTop A] [OrderTop B] :=
  {x:A×B //x≠⊤}

abbrev BinaryProductBox (b:A×B) := {x:A×B //x≤b ∧ x.1≠⊤}

omit [OrderTop B] in
lemma binaryProductBox_contractible (b:A×B) (hb:b.1=⊤)
    (h:ContractibleSpace (OrderWeights {a:A //a≠⊤})) :
    ContractibleSpace (OrderWeights (BinaryProductBox b)) := by
  let r : BinaryProductBox b →o {a:A //a≠⊤} :=
    { toFun := fun x=>⟨x.val.1,x.property.2⟩
      monotone' := fun _ _ h=>h.1 }
  let i : {a:A //a≠⊤} →o BinaryProductBox b :=
    { toFun := fun a=>⟨(a.val,b.2),⟨by simpa only [hb] using (le_top:a.val≤⊤),le_rfl⟩,a.property⟩
      monotone' := fun _ _ h=>⟨h,le_rfl⟩ }
  apply weight_contractible_of_order_retraction r i rfl ?_ h
  intro x
  exact ⟨le_rfl,x.property.1.2⟩

noncomputable def binaryBoundarySliceIso :
    {x:BinaryProductBoundary A B //x.val.1≠⊤} ≃o BinaryProductBox (⊤:A×B) where
  toFun x:=⟨x.val.val,le_top,x.property⟩
  invFun x:=⟨⟨x.val,by intro he;exact x.property.2 (congrArg Prod.fst he)⟩,x.property.2⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def binaryBoundaryFiberIso (v:BinaryProductBoundary A B) (hv:v.val.1=⊤) :
    {x:BinaryProductBoundary A B //x.val.1≠⊤ ∧ x<v} ≃o BinaryProductBox v.val where
  toFun x:=⟨x.val.val,x.property.2.le,x.property.1⟩
  invFun x:=⟨⟨x.val,by intro he;exact x.property.2 (congrArg Prod.fst he)⟩,x.property.2,by
    apply lt_of_le_of_ne x.property.1
    intro he
    exact x.property.2 ((congrArg Prod.fst he).trans hv)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

theorem binaryProductBoundary_contractible (k:BinaryProductBoundary A B→ℕ) (N:ℕ)
    (hk:∀x,k x≤N) (hm:StrictMono k)
    (h:ContractibleSpace (OrderWeights {a:A //a≠⊤})) :
    ContractibleSpace (OrderWeights (BinaryProductBoundary A B)) := by
  apply orderWeights_contractible_of_lower_fibers {x |x.val.1≠⊤} k N hk hm
  · exact (weightHomeomorph binaryBoundarySliceIso).contractibleSpace_iff.mpr
      (binaryProductBox_contractible (⊤:A×B) rfl h)
  · intro v hv
    have he:v.val.1=⊤:=not_not.mp hv
    exact (weightHomeomorph (binaryBoundaryFiberIso v he)).contractibleSpace_iff.mpr
      (binaryProductBox_contractible v.val he h)

end HarmonicArtin

end OAI
