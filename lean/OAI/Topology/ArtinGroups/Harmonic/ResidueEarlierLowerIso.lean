import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightEarlierLower
import OAI.Topology.ArtinGroups.Harmonic.ResidueEarlierLower
import OAI.Topology.ArtinGroups.Harmonic.ResidueActive
import OAI.Topology.ArtinGroups.Harmonic.ResidueRank

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

lemma sourceResidueEarlier_total (strict:Bool) (P:Deligne M) (q:ℤ)
    (X Y:SourceResidue M strict P q) (h:X≠Y) :
    SourceResidueEarlier M strict P q X Y ∨ SourceResidueEarlier M strict P q Y X := by
  exact lt_or_gt_of_ne (fun he=>h (sourceResidueKey_injective M strict P q he))

noncomputable def sourceResidueEarlierLowerIso {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0) :
    WeightEarlierLower (SourceResidueEarlier M strict P q) X ≃o
      SourceResidueEarlierLower M strict P X q where
  toFun Y:=⟨Y.val.val,Y.val.property,Y.property.2,
    (sourceResidueEarlier_lower_negative M X Y.val Y.property.2 hh).mp Y.property.1⟩
  invFun Y:=⟨⟨Y.val,Y.property.1⟩,
    (sourceResidueEarlier_lower_negative M X ⟨Y.val,Y.property.1⟩ Y.property.2.1 hh).mpr Y.property.2.2,
    Y.property.2.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def sourceResidueEarlierUpperIso {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0) :
    WeightEarlierUpper (SourceResidueEarlier M strict P q) X ≃o
      SourceResidueEarlierUpper M P X q where
  toFun Y:=⟨Y.val.val,Y.property.2,Y.val.property.1,
    (sourceResidueEarlier_upper_negative M X Y.val Y.property.2 hh).mp Y.property.1⟩
  invFun Y:=⟨⟨Y.val,sourceResidueAllowed_upper M X.property Y.property.1.le Y.property.2.1⟩,
    (sourceResidueEarlier_upper_negative M X _ Y.property.1 hh).mpr Y.property.2.2,Y.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

lemma sourceResidue_lower_boundary {strict:Bool} {P X:Deligne M} {q:ℤ}
    (hX:SourceResidueAllowed M strict P X q) (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (sourceFrameFamily M x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q) :
    ∀H,ClassCapOn Q (sourceFrameFamily M (sourceCosetRepresentative M X) H)
      (closedNeighborhood Q (U X.val.1)\U X.val.1) q := by
  have h':=sourceResidue_exterior_cap M hX x (sourceCosetRepresentative M X) hx
    (sourceCosetRepresentative_mem M X) (closedNeighborhood Q (U P.val.1))
    (by simpa only [←unfoldedInclusion_range] using hb)
  intro H
  apply ClassCapOn.mono Q (h' H)
  intro α hα
  refine ⟨closedNeighborhood_mono Q (unfoldedInclusion_range_mono M hX.1.le.1) hα.1,?_⟩
  simpa only [←unfoldedInclusion_range] using hα.2

lemma sourceResidue_upper_weights_contractible {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0)
    (hn:Nonempty (WeightEarlierUpper (SourceResidueEarlier M strict P q) X)) :
    ContractibleSpace (OrderWeights (WeightEarlierUpper (SourceResidueEarlier M strict P q) X)) := by
  let e:=sourceResidueEarlierUpperIso M X hh
  have hc:=sourceResidueEarlierUpper_contractible M X.property.1.le hh (hn.map e)
  have hw:ContractibleSpace (OrderWeights (SourceResidueEarlierUpper M P X q)):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp hc
  exact (weightHomeomorph e).contractibleSpace_iff.mpr hw

lemma sourceResidue_emptyLink_upper {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0)
    (hn:¬Nonempty (WeightEarlierLink (SourceResidueEarlier M strict P q) X)) :
    ¬Nonempty (SourceResidueEarlierUpper M P X q) := by
  intro h
  obtain ⟨Y⟩:=h.map (sourceResidueEarlierUpperIso M X hh).symm
  exact hn ⟨Y.val,Y.property.1,Or.inr Y.property.2.le⟩

lemma sourceResidue_emptyLink_lower {strict:Bool} {P:Deligne M} {q:ℤ}
    (X:SourceResidue M strict P q) (hh:sourceResidueHeight M P X q<0)
    (hn:¬Nonempty (WeightEarlierLink (SourceResidueEarlier M strict P q) X)) :
    ¬Nonempty (SourceResidue M true X q) := by
  intro h
  obtain ⟨Y⟩:=h.map (sourceResidueLowerInclusion M X.property)
  let Z:=(sourceResidueEarlierLowerIso M X hh).symm Y
  exact hn ⟨Z.val,Z.property.1,Or.inl Z.property.2.le⟩

end HarmonicArtin

end OAI
