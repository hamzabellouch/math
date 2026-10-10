import Mathlib
import OAI.Topology.ArtinGroups.Realizations.DeligneRankBound

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma sourceResidue_lower_weights_contractible {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0)
    (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (sourceFrameFamily M x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hX:Nonempty (WeightEarlierLower (SourceResidueEarlier M strict P q) X)) :
    ContractibleSpace (OrderWeights (WeightEarlierLower (SourceResidueEarlier M strict P q) X)) := by
  let e:=sourceResidueEarlierLowerIso M X hh
  have hsmall:Nonempty (SourceResidue M true X q):=
    (hX.map e).map (sourceResidueLowerProjection M X.property)
  have :=sourceStrictResidue_contractible M X q (sourceCosetRepresentative M X)
    (sourceCosetRepresentative_mem M X) (sourceResidue_lower_boundary M X.property x hx hb) hsmall
  have hc:= (sourceResidueLowerEquiv M X.property).contractibleSpace
  exact (weightHomeomorph e).contractibleSpace_iff.mpr
    (nerveWeightsHomeomorph.contractibleSpace_iff.mp hc)

noncomputable def sourceResidueZeroLowerIso {P:Deligne M} {q:ℤ}
    (X:SourceResidue M false P q) (hh:sourceResidueHeight M P X q=0) :
    WeightEarlierLower (SourceResidueEarlier M false P q) X ≃o SourceResidue M false X q where
  toFun Y:=⟨Y.val.val,(sourceResidue_zero_lower_iff M X.property hh Y.property.2).mp Y.val.property⟩
  invFun Y:=⟨⟨Y.val,sourceResidueAllowed_closed_trans M X.property Y.property⟩,
    sourceResidueEarlier_lower_zero M X _ Y.property.1 hh,Y.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

lemma sourceResidueZeroUpper_empty {P:Deligne M} {q:ℤ}
    (X:SourceResidue M false P q) (hh:sourceResidueHeight M P X q=0) :
    ¬Nonempty (WeightEarlierUpper (SourceResidueEarlier M false P q) X) := by
  rintro ⟨Y⟩
  exact sourceResidueEarlier_upper_zero M X Y.val Y.property.2 hh Y.property.1

lemma sourceResidue_special_boundary {P:Deligne M} {q:ℤ}
    (I:Set S) (hPI:P.val.1⊆I) (x:Artin M)
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q) :
    ∀H,ClassCapOn Q (sourceFrameFamily M x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q := by
  intro H
  apply ClassCapOn.mono Q (hE H)
  intro α hα
  refine ⟨closedNeighborhood_mono Q ?_ hα.1,?_⟩
  · change Set.range (unfoldedInclusion M P.val.1) ⊆ _
    rw [unfoldedInclusion_range]
    exact fun _ h=>(Set.image_mono hPI) h
  · simpa only [←unfoldedInclusion_range] using hα.2

end HarmonicArtin

end OAI
