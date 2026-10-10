import Mathlib
import OAI.Topology.ArtinGroups.Realizations.OrderWeightsContractibleUnique
import OAI.Topology.ArtinGroups.Harmonic.ResidueActiveEmpty
import OAI.Topology.ArtinGroups.Harmonic.ResidueEarlierLowerIso

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)
local notation "U" => fun J:Set S=>Set.range (unfoldedInclusion M J)

omit [LinearOrder S] in
lemma sourceDeligne_rank_bound (X:Deligne M) : X.val.1.ncard≤Fintype.card S := by
  simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card X.val.1
omit [LinearOrder S] in
lemma sourceDeligne_rank_strictMono : StrictMono (fun X:Deligne M=>X.val.1.ncard) := by
  intro X Y h
  exact Set.ncard_lt_ncard (deligne_lt_type M h) (Set.toFinite _)

private theorem strictResidue_rank (n:ℕ) : ∀(P:Deligne M),P.val.1.ncard=n →
    ∀(q:ℤ) (x:Artin M),x∈P.val.2 →
    (∀H,ClassCapOn Q (sourceFrameFamily M x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q) →
    Nonempty (SourceResidue M true P q) →
    ContractibleSpace (OrderWeights (SourceResidue M true P q)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hn q x hx hb hne
    let r:=SourceResidueEarlier M true P q
    have hl:∀X:SourceResidue M true P q,Nonempty (WeightEarlierLower r X) →
        ContractibleSpace (OrderWeights (WeightEarlierLower r X)):=by
      intro X hX
      have hh:=sourceResidueHeight_strict M X.property
      let e:=sourceResidueEarlierLowerIso M X hh
      have hsmall:Nonempty (SourceResidue M true X q):=
        (hX.map e).map (sourceResidueLowerProjection M X.property)
      have hrank:X.val.val.1.ncard<n:=by
        rw [←hn]
        exact sourceDeligne_rank_strictMono M X.property.1
      have hcont:=ih X.val.val.1.ncard hrank X.val rfl q (sourceCosetRepresentative M X)
        (sourceCosetRepresentative_mem M X) (sourceResidue_lower_boundary M X.property x hx hb) hsmall
      have hnerve:ContractibleSpace |CategoryTheory.nerve (SourceResidue M true X q)|:=
        nerveWeightsHomeomorph.contractibleSpace_iff.mpr hcont
      have hlarge:ContractibleSpace |CategoryTheory.nerve (SourceResidueEarlierLower M true P X q)|:=by
        let :=hnerve
        exact (sourceResidueLowerEquiv M X.property).contractibleSpace
      have hw:ContractibleSpace (OrderWeights (SourceResidueEarlierLower M true P X q)):=
        nerveWeightsHomeomorph.contractibleSpace_iff.mp hlarge
      exact (weightHomeomorph e).contractibleSpace_iff.mpr hw
    apply orderWeights_contractible_unique_source r (sourceResidueEarlier_wellFounded M true P q)
      (sourceResidueEarlier_total M true P q) (fun X=>X.val.val.1.ncard) (Fintype.card S)
      (fun X=>sourceDeligne_rank_bound M X) (by intro X Y h;exact sourceDeligne_rank_strictMono M h)
      hl (fun X hX=>sourceResidue_upper_weights_contractible M X (sourceResidueHeight_strict M X.property) hX)
      ?_ hne
    intro X Y hX hY
    apply Subtype.ext
    have hhX:=sourceResidueHeight_strict M X.property
    have hhY:=sourceResidueHeight_strict M Y.property
    exact sourceResidue_negative_sources_unique M X.property Y.property x hx hb hhX hhY
      (sourceResidue_emptyLink_upper M X hhX hX) (sourceResidue_emptyLink_upper M Y hhY hY)
      (sourceResidue_emptyLink_lower M X hhX hX) (sourceResidue_emptyLink_lower M Y hhY hY)

theorem sourceStrictResidue_contractible (P:Deligne M) (q:ℤ) (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (sourceFrameFamily M x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q)
    (hne:Nonempty (SourceResidue M true P q)) :
    ContractibleSpace |CategoryTheory.nerve (SourceResidue M true P q)| :=
  nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    (strictResidue_rank M P.val.1.ncard P rfl q x hx hb hne)

theorem sourceStrictResidue_empty_or_contractible (P:Deligne M) (q:ℤ) (x:Artin M) (hx:x∈P.val.2)
    (hb:∀H,ClassCapOn Q (sourceFrameFamily M x H) (closedNeighborhood Q (U P.val.1)\U P.val.1) q) :
    IsEmpty (SourceResidue M true P q) ∨
      ContractibleSpace |CategoryTheory.nerve (SourceResidue M true P q)| := by
  by_cases h:Nonempty (SourceResidue M true P q)
  · exact Or.inr (sourceStrictResidue_contractible M P q x hx hb h)
  · exact Or.inl (not_nonempty_iff.mp h)

end HarmonicArtin

end OAI
