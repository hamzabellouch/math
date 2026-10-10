import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ResidueZeroLowerIso

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory _root_.Matrix _root_.OAI.Matrix
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

private theorem specialResidue_rank (n:ℕ) : ∀(P:Deligne M),P.val.1.ncard=n →
    ∀(x:Artin M),x∈P.val.2 → ∀(I:Set S),I.Nonempty → P.val.1⊆I → ∀(q:ℤ),0<q →
    ∀(c:S⊕Unit→ℝ),(∀v,0≤c v) → (∀v,v∉Sum.inl '' I→c v=0) →
    (∀v,v∈Sum.inl '' I→0<c v) → (∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0) →
    (∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q) →
    (∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M x q v=c v) →
    ContractibleSpace (OrderWeights (SourceResidue M false P q)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hn x hx I hI hPI q hq c hc hcSupp hcPos hcNull hE hdata
    let r:=SourceResidueEarlier M false P q
    have hb:=sourceResidue_special_boundary M I hPI x hE
    have hzcont:∀(X:SourceResidue M false P q),sourceResidueHeight M P X q=0 →
        ContractibleSpace (OrderWeights (SourceResidue M false X q)):=by
      intro X hh
      have hrank:X.val.val.1.ncard<n:=by
        rw [←hn]
        exact sourceDeligne_rank_strictMono M X.property.1
      exact ih X.val.val.1.ncard hrank X.val rfl (sourceCosetRepresentative M X)
        (sourceCosetRepresentative_mem M X) I hI (X.property.1.le.1.trans hPI) q hq c hc hcSupp hcPos hcNull
        (sourceResidue_exterior_cap M X.property x (sourceCosetRepresentative M X) hx
          (sourceCosetRepresentative_mem M X) _ hE)
        (sourceResidue_zero_exterior M X.property hh x (sourceCosetRepresentative M X) hx
          (sourceCosetRepresentative_mem M X) I hPI c hcNull hdata)
    have hneg:∀(X:SourceResidue M false P q),¬Nonempty (WeightEarlierLink r X) →
        sourceResidueHeight M P X q<0:=by
      intro X hX
      rcases lt_or_eq_of_le (sourceResidueHeight_nonpos M X.property) with hh|hh
      · exact hh
      · exfalso
        obtain ⟨Y,hy,hYa⟩:=sourceResidue_zero_ne_lower M P X x hx I hI hPI q hq c hc hcSupp hcPos hcNull hE hdata X.property hh
        exact hX ⟨⟨Y,hYa⟩,sourceResidueEarlier_lower_zero M X _ hy hh,Or.inl hy.le⟩
    apply orderWeights_contractible_unique_source r (sourceResidueEarlier_wellFounded M false P q)
      (sourceResidueEarlier_total M false P q) (fun X=>X.val.val.1.ncard) (Fintype.card S)
      (fun X=>sourceDeligne_rank_bound M X) (by intro X Y h;exact sourceDeligne_rank_strictMono M h)
      ?_ ?_ ?_ (sourceClosedResidue_nonempty M P x hx I hI hPI q hq c hc hcSupp hcPos hcNull hE hdata)
    · intro X hX
      rcases lt_or_eq_of_le (sourceResidueHeight_nonpos M X.property) with hh|hh
      · exact sourceResidue_lower_weights_contractible M X hh x hx hb hX
      · exact (weightHomeomorph (sourceResidueZeroLowerIso M X hh)).contractibleSpace_iff.mpr (hzcont X hh)
    · intro X hX
      rcases lt_or_eq_of_le (sourceResidueHeight_nonpos M X.property) with hh|hh
      · exact sourceResidue_upper_weights_contractible M X hh hX
      · exact False.elim (sourceResidueZeroUpper_empty M X hh hX)
    · intro X Y hX hY
      have hhX:=hneg X hX
      have hhY:=hneg Y hY
      apply Subtype.ext
      exact sourceResidue_negative_sources_unique M X.property Y.property x hx hb hhX hhY
        (sourceResidue_emptyLink_upper M X hhX hX) (sourceResidue_emptyLink_upper M Y hhY hY)
        (sourceResidue_emptyLink_lower M X hhX hX) (sourceResidue_emptyLink_lower M Y hhY hY)

theorem sourceSpecialResidue_contractible (P:Deligne M) (x:Artin M) (hx:x∈P.val.2)
    (I:Set S) (hI:I.Nonempty) (hPI:P.val.1⊆I) (q:ℤ) (hq:0<q)
    (c:S⊕Unit→ℝ) (hc:∀v,0≤c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0<c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→sourceMultiplicity M x q v=c v) :
    ContractibleSpace |nerve (SourceResidue M false P q)| :=
  nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    (specialResidue_rank M P.val.1.ncard P rfl x hx I hI hPI q hq c hc hcSupp hcPos hcNull hE hdata)

end HarmonicArtin

end OAI
