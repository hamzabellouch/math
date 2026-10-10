import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueAllowed
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueEarlierLower
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueRank
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueEarlierLowerIso
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueActiveEmpty
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Realizations.DeligneRankBound
import Mathlib
import OAI.Topology.ArtinGroups.Realizations.OrderWeightsContractibleUnique
import OAI.Topology.ArtinGroups.Harmonic.ResidueActiveEmpty
import OAI.Topology.ArtinGroups.Harmonic.ResidueEarlierLowerIso

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

private theorem pointedStrictResidue_rank (n:ℕ) : ∀(P:Deligne M),P.val.1.ncard=n →
    ∀(q:ℤ) (x:Artin M),x∈P.val.2 →
    (∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q) →
    Nonempty (PointedResidue M f true P q) →
    ContractibleSpace (OrderWeights (PointedResidue M f true P q)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hn q x hx hb hne
    let r:=PointedResidueEarlier M f true P q
    have hl:∀X:PointedResidue M f true P q,Nonempty (WeightEarlierLower r X) →
        ContractibleSpace (OrderWeights (WeightEarlierLower r X)):=by
      intro X hX
      have hh:=pointedResidueHeight_strict M f X.property
      let e:=pointedResidueEarlierLowerIso M f X hh
      have hsmall:Nonempty (PointedResidue M f true X q):=
        (hX.map e).map (pointedResidueLowerProjection M f X.property)
      have hrank:X.val.val.1.ncard<n:=by
        rw [←hn]
        exact sourceDeligne_rank_strictMono M X.property.1
      have hcont:=ih X.val.val.1.ncard hrank X.val rfl q (sourceCosetRepresentative M X)
        (sourceCosetRepresentative_mem M X) (pointedResidue_lower_boundary M f X.property x hx hb) hsmall
      have hnerve:ContractibleSpace |CategoryTheory.nerve (PointedResidue M f true X q)|:=
        nerveWeightsHomeomorph.contractibleSpace_iff.mpr hcont
      have hlarge:ContractibleSpace |CategoryTheory.nerve (PointedResidueEarlierLower M f true P X q)|:=by
        let :=hnerve
        exact (pointedResidueLowerEquiv M f X.property).contractibleSpace
      have hw:ContractibleSpace (OrderWeights (PointedResidueEarlierLower M f true P X q)):=
        nerveWeightsHomeomorph.contractibleSpace_iff.mp hlarge
      exact (weightHomeomorph e).contractibleSpace_iff.mpr hw
    apply orderWeights_contractible_unique_source r (pointedResidueEarlier_wellFounded M f true P q)
      (pointedResidueEarlier_total M f true P q) (fun X=>X.val.val.1.ncard) (Fintype.card S)
      (fun X=>sourceDeligne_rank_bound M X) (by intro X Y h;exact sourceDeligne_rank_strictMono M h)
      hl (fun X hX=>pointedResidue_upper_weights_contractible M f X (pointedResidueHeight_strict M f X.property) hX)
      ?_ hne
    intro X Y hX hY
    apply Subtype.ext
    have hhX:=pointedResidueHeight_strict M f X.property
    have hhY:=pointedResidueHeight_strict M f Y.property
    exact pointedResidue_negative_pointeds_unique M f X.property Y.property x hx hb hhX hhY
      (pointedResidue_emptyLink_upper M f X hhX hX) (pointedResidue_emptyLink_upper M f Y hhY hY)
      (pointedResidue_emptyLink_lower M f X hhX hX) (pointedResidue_emptyLink_lower M f Y hhY hY)

theorem pointedStrictResidue_contractible (P:Deligne M) (q:ℤ) (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hne:Nonempty (PointedResidue M f true P q)) :
    ContractibleSpace |CategoryTheory.nerve (PointedResidue M f true P q)| :=
  nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    (pointedStrictResidue_rank M f P.val.1.ncard P rfl q x hx hb hne)

theorem pointedStrictResidue_empty_or_contractible (P:Deligne M) (q:ℤ) (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (pointedFamily M f x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q) :
    IsEmpty (PointedResidue M f true P q) ∨
      ContractibleSpace |CategoryTheory.nerve (PointedResidue M f true P q)| := by
  by_cases h:Nonempty (PointedResidue M f true P q)
  · exact Or.inr (pointedStrictResidue_contractible M f P q x hx hb h)
  · exact Or.inl (not_nonempty_iff.mp h)

end HarmonicArtin.ParabolicIntersections

end OAI
