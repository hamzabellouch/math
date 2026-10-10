import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedStrictResidue
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueHeightZero
import Mathlib
import OAI.Topology.ArtinGroups.Realizations.DeligneRankBound

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma pointedResidue_lower_weights_contractible {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0)
    (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hX:Nonempty (WeightEarlierLower (PointedResidueEarlier M f strict P q) X)) :
    ContractibleSpace (OrderWeights (WeightEarlierLower (PointedResidueEarlier M f strict P q) X)) := by
  let e:=pointedResidueEarlierLowerIso M f X hh
  have hsmall:Nonempty (PointedResidue M f true X q):=
    (hX.map e).map (pointedResidueLowerProjection M f X.property)
  have :=pointedStrictResidue_contractible M f X q (sourceCosetRepresentative M X)
    (sourceCosetRepresentative_mem M X) (pointedResidue_lower_boundary M f X.property x hx hb) hsmall
  have hc:= (pointedResidueLowerEquiv M f X.property).contractibleSpace
  exact (weightHomeomorph e).contractibleSpace_iff.mpr
    (nerveWeightsHomeomorph.contractibleSpace_iff.mp hc)

noncomputable def pointedResidueZeroLowerIso {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f false P q) (hh:pointedResidueHeight M f P X q=0) :
    WeightEarlierLower (PointedResidueEarlier M f false P q) X ≃o PointedResidue M f false X q where
  toFun Y:=⟨Y.val.val,(pointedResidue_zero_lower_iff M f X.property hh Y.property.2).mp Y.val.property⟩
  invFun Y:=⟨⟨Y.val,pointedResidueAllowed_closed_trans M f X.property Y.property⟩,
    pointedResidueEarlier_lower_zero M f X _ Y.property.1 hh,Y.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

lemma pointedResidueZeroUpper_empty {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f false P q) (hh:pointedResidueHeight M f P X q=0) :
    ¬Nonempty (WeightEarlierUpper (PointedResidueEarlier M f false P q) X) := by
  rintro ⟨Y⟩
  exact pointedResidueEarlier_upper_zero M f X Y.val Y.property.2 hh Y.property.1

lemma pointedResidue_special_boundary {P:Deligne M} {q:ℤ}
    (I:Set S) (hPI:P.val.1⊆I) (x:Artin M)
    (hE:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q) :
    ∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q := by
  intro H
  apply ClassCapOn.mono Q (hE H)
  intro α hα
  refine ⟨closedNeighborhood_mono Q ?_ hα.1,?_⟩
  · change Set.range (unfoldedInclusion M P.val.1) ⊆ _
    rw [unfoldedInclusion_range]
    exact fun _ h=>(Set.image_mono hPI) h
  · simpa only [←unfoldedInclusion_range] using hα.2

end HarmonicArtin.ParabolicIntersections

end OAI
