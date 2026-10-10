import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueZeroLower
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedStrictResidue
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueHeightZero
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ResidueZeroLowerIso

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory _root_.Matrix _root_.OAI.Matrix
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

private theorem pointedSpecialResidue_rank (n:ℕ) : ∀(P:Deligne M),P.val.1.ncard=n →
    ∀(x:Artin M),x∈P.val.2 → x∈artinParabolic M {f}ᶜ →
    ∀(I:Set S),I.Nonempty → f∉I → P.val.1⊆I → ∀(q:ℤ),
    ∀(c:S⊕Unit→ℝ),(∀v,0≤c v) → (∀v,v∉Sum.inl '' I→c v=0) →
    (∀v,v∈Sum.inl '' I→0<c v) → (∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0) →
    (∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q) →
    (∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→pointedMultiplicity M f x q v=c v) →
    ContractibleSpace (OrderWeights (PointedResidue M f false P q)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hn x hx hxA I hI hf hPI q c hc hcSupp hcPos hcNull hE hdata
    let r:=PointedResidueEarlier M f false P q
    have hb:=pointedResidue_special_boundary M f I hPI x hE
    have hzcont:∀(X:PointedResidue M f false P q),pointedResidueHeight M f P X q=0 →
        ContractibleSpace (OrderWeights (PointedResidue M f false X q)):=by
      intro X hh
      have hrank:X.val.val.1.ncard<n:=by
        rw [←hn]
        exact sourceDeligne_rank_strictMono M X.property.1
      exact ih X.val.val.1.ncard hrank X.val rfl (sourceCosetRepresentative M X)
        (sourceCosetRepresentative_mem M X)
        (pointedCoset_avoids_frame M f P x (sourceCosetRepresentative M X) hx
          (X.property.1.le.2 (sourceCosetRepresentative_mem M X)) I hPI hf hxA)
        I hI hf (X.property.1.le.1.trans hPI) q c hc hcSupp hcPos hcNull
        (pointedResidue_exterior_cap M f X.property x (sourceCosetRepresentative M X) hx
          (sourceCosetRepresentative_mem M X) _ hE)
        (pointedResidue_zero_exterior M f X.property hh x (sourceCosetRepresentative M X) hx
          (sourceCosetRepresentative_mem M X) I hPI c hcNull hdata)
    have hneg:∀(X:PointedResidue M f false P q),¬Nonempty (WeightEarlierLink r X) →
        pointedResidueHeight M f P X q<0:=by
      intro X hX
      rcases lt_or_eq_of_le (pointedResidueHeight_nonpos M f X.property) with hh|hh
      · exact hh
      · exfalso
        obtain ⟨Y,hy,hYa⟩:=pointedResidue_zero_ne_lower M f P X x hx hxA I hI hf hPI q c hc hcSupp hcPos hcNull hE hdata X.property hh
        exact hX ⟨⟨Y,hYa⟩,pointedResidueEarlier_lower_zero M f X _ hy hh,Or.inl hy.le⟩
    apply orderWeights_contractible_unique_source r (pointedResidueEarlier_wellFounded M f false P q)
      (pointedResidueEarlier_total M f false P q) (fun X=>X.val.val.1.ncard) (Fintype.card S)
      (fun X=>sourceDeligne_rank_bound M X) (by intro X Y h;exact sourceDeligne_rank_strictMono M h)
      ?_ ?_ ?_ (pointedClosedResidue_nonempty M f P x hx hxA I hI hf hPI q c hc hcSupp hcPos hcNull hE hdata)
    · intro X hX
      rcases lt_or_eq_of_le (pointedResidueHeight_nonpos M f X.property) with hh|hh
      · exact pointedResidue_lower_weights_contractible M f X hh x hx hb hX
      · exact (weightHomeomorph (pointedResidueZeroLowerIso M f X hh)).contractibleSpace_iff.mpr (hzcont X hh)
    · intro X hX
      rcases lt_or_eq_of_le (pointedResidueHeight_nonpos M f X.property) with hh|hh
      · exact pointedResidue_upper_weights_contractible M f X hh hX
      · exact False.elim (pointedResidueZeroUpper_empty M f X hh hX)
    · intro X Y hX hY
      have hhX:=hneg X hX
      have hhY:=hneg Y hY
      apply Subtype.ext
      exact pointedResidue_negative_pointeds_unique M f X.property Y.property x hx hb hhX hhY
        (pointedResidue_emptyLink_upper M f X hhX hX) (pointedResidue_emptyLink_upper M f Y hhY hY)
        (pointedResidue_emptyLink_lower M f X hhX hX) (pointedResidue_emptyLink_lower M f Y hhY hY)

theorem pointedSpecialResidue_contractible (P:Deligne M) (x:Artin M) (hx:x∈P.val.2) (hxA:x∈artinParabolic M {f}ᶜ)
    (I:Set S) (hI:I.Nonempty) (hf:f∉I) (hPI:P.val.1⊆I) (q:ℤ)
    (c:S⊕Unit→ℝ) (hc:∀v,0≤c v) (hcSupp:∀v,v∉Sum.inl '' I→c v=0)
    (hcPos:∀v,v∈Sum.inl '' I→0<c v)
    (hcNull:∀v,v∈Sum.inl '' I→(framedCartan M *ᵥ c) v=0)
    (hE:∀H,ClassCapOn Q (pointedFamily M f x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \fusionColorRegion m (Sum.inl '' P.val.1)) q)
    (hdata:∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' P.val.1) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→pointedMultiplicity M f x q v=c v) :
    ContractibleSpace |nerve (PointedResidue M f false P q)| :=
  nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    (pointedSpecialResidue_rank M f P.val.1.ncard P rfl x hx hxA I hI hf hPI q c hc hcSupp hcPos hcNull hE hdata)

end HarmonicArtin.ParabolicIntersections

end OAI
