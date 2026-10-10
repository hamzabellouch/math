import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.EarlierLower
import OAI.Topology.ArtinGroups.Realizations.NerveOrderRetractionEquiv

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

abbrev SourceAllEligibleLower (P:Deligne M) :=
  {Q:Deligne M // Q<P ∧ ∀i∈P.val.1,i∉Q.val.1→SourceEligible M P Q i}

noncomputable def sourceAllEligibleInclusion (P:Deligne M) :
    SourceAllEligibleLower M P →o SourceEarlierLower M P where
  toFun Q:=⟨Q.val,Q.property.1,sourceLower_eligible_earlier M Q.property.1 Q.property.2⟩
  monotone':=fun _ _ h=>h

noncomputable def sourceAllEligibleProjection (P:Deligne M) :
    SourceEarlierLower M P →o SourceAllEligibleLower M P where
  toFun Q:=⟨sourceLowerClose M P Q,(sourceLowerClose_mem M Q.property.1 Q.property.2).1,
    sourceLowerClose_all_eligible M Q.property.1.le⟩
  monotone':=fun _ R h=>sourceLowerClose_monotone M h R.property.1.le

lemma sourceAllEligible_retract (P:Deligne M) :
    (sourceAllEligibleProjection M P).comp (sourceAllEligibleInclusion M P)=OrderHom.id := by
  apply OrderHom.ext
  funext Q
  apply Subtype.ext
  exact sourceLowerClose_eq_of_all M Q.property.2 Q.property.1.le

noncomputable def sourceEarlierLower_equiv_allEligible (P:Deligne M) :
    ContinuousMap.HomotopyEquiv |nerve (SourceEarlierLower M P)| |nerve (SourceAllEligibleLower M P)| :=
  nerveOrderRetractionEquiv (sourceAllEligibleProjection M P) (sourceAllEligibleInclusion M P)
    (sourceAllEligible_retract M P) (le_sourceLowerRetraction M P)

end HarmonicArtin

end OAI
