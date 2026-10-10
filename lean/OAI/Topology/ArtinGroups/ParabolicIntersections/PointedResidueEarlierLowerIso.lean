import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueAllowed
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetExteriorCap
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueActive
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueEarlierLower
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueRank
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Harmonic.ResidueEarlierLowerIso
import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightEarlierLower
import OAI.Topology.ArtinGroups.Harmonic.ResidueEarlierLower
import OAI.Topology.ArtinGroups.Harmonic.ResidueActive
import OAI.Topology.ArtinGroups.Harmonic.ResidueRank

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma pointedResidueEarlier_total (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:PointedResidue M f strict P q) (h:X≠Y) :
    PointedResidueEarlier M f strict P q X Y ∨ PointedResidueEarlier M f strict P q Y X := by
  exact lt_or_gt_of_ne (fun he=>h (pointedResidueKey_injective M f strict P q he))

noncomputable def pointedResidueEarlierLowerIso {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0) :
    WeightEarlierLower (PointedResidueEarlier M f strict P q) X ≃o
      PointedResidueEarlierLower M f strict P X q where
  toFun Y:=⟨Y.val.val,Y.val.property,Y.property.2,
    (pointedResidueEarlier_lower_negative M f X Y.val Y.property.2 hh).mp Y.property.1⟩
  invFun Y:=⟨⟨Y.val,Y.property.1⟩,
    (pointedResidueEarlier_lower_negative M f X ⟨Y.val,Y.property.1⟩ Y.property.2.1 hh).mpr Y.property.2.2,
    Y.property.2.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def pointedResidueEarlierUpperIso {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0) :
    WeightEarlierUpper (PointedResidueEarlier M f strict P q) X ≃o
      PointedResidueEarlierUpper M f P X q where
  toFun Y:=⟨Y.val.val,Y.property.2,Y.val.property.1,
    (pointedResidueEarlier_upper_negative M f X Y.val Y.property.2 hh).mp Y.property.1⟩
  invFun Y:=⟨⟨Y.val,pointedResidueAllowed_upper M f X.property Y.property.1.le Y.property.2.1⟩,
    (pointedResidueEarlier_upper_negative M f X _ Y.property.1 hh).mpr Y.property.2.2,Y.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

lemma pointedResidue_lower_boundary {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:PointedResidueAllowed M f strict P X q) (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q) :
    ∀H,ClassCapOn Q (pointedFamily M f (sourceCosetRepresentative M X) H)
      (closedNeighborhood Q (U X.val.1)\U X.val.1) q := by
  have h':=pointedResidue_exterior_cap M f hX x (sourceCosetRepresentative M X) hx
    (sourceCosetRepresentative_mem M X) (closedNeighborhood Q (U P.val.1))
    (by simpa only [←unfoldedInclusion_range] using hb)
  intro H
  apply ClassCapOn.mono Q (h' H)
  intro α hα
  refine ⟨closedNeighborhood_mono Q (unfoldedInclusion_range_mono M hX.1.le.1) hα.1,?_⟩
  simpa only [←unfoldedInclusion_range] using hα.2

lemma pointedResidue_upper_weights_contractible {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0)
    (hn:Nonempty (WeightEarlierUpper (PointedResidueEarlier M f strict P q) X)) :
    ContractibleSpace (OrderWeights (WeightEarlierUpper (PointedResidueEarlier M f strict P q) X)) := by
  let e:=pointedResidueEarlierUpperIso M f X hh
  have hc:=pointedResidueEarlierUpper_contractible M f X.property.1.le hh (hn.map e)
  have hw:ContractibleSpace (OrderWeights (PointedResidueEarlierUpper M f P X q)):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp hc
  exact (weightHomeomorph e).contractibleSpace_iff.mpr hw

lemma pointedResidue_emptyLink_upper {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0)
    (hn:¬Nonempty (WeightEarlierLink (PointedResidueEarlier M f strict P q) X)) :
    ¬Nonempty (PointedResidueEarlierUpper M f P X q) := by
  intro h
  obtain ⟨Y⟩:=h.map (pointedResidueEarlierUpperIso M f X hh).symm
  exact hn ⟨Y.val,Y.property.1,Or.inr Y.property.2.le⟩

lemma pointedResidue_emptyLink_lower {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:PointedResidue M f strict P q) (hh:pointedResidueHeight M f P X q<0)
    (hn:¬Nonempty (WeightEarlierLink (PointedResidueEarlier M f strict P q) X)) :
    ¬Nonempty (PointedResidue M f true X q) := by
  intro h
  obtain ⟨Y⟩:=h.map (pointedResidueLowerInclusion M f X.property)
  let Z:=(pointedResidueEarlierLowerIso M f X hh).symm Y
  exact hn ⟨Z.val,Z.property.1,Or.inl Z.property.2.le⟩

end HarmonicArtin.ParabolicIntersections

end OAI
