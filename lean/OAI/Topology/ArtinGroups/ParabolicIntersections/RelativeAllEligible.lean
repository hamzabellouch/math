import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeLowerRetraction
import OAI.Topology.ArtinGroups.Realizations.NerveOrderRetractionEquiv

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open Simplicial CategoryTheory
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

abbrev RelativeAllEligibleLower (P:Deligne M) :=
  {Q:Deligne M // Q<P ∧ ∀i∈P.val.1,i∉Q.val.1→RelativeEligible M f U cutoff P Q i}

noncomputable def relativeAllEligibleInclusion (P:Deligne M) :
    RelativeAllEligibleLower M f U cutoff P →o RelativeDescendingLower M f U cutoff P where
  toFun Q:=⟨Q.val,Q.property.1,relativeLower_eligible_descending M f U cutoff Q.property.1 Q.property.2⟩
  monotone':=fun _ _ h=>h

noncomputable def relativeAllEligibleProjection (P:Deligne M) :
    RelativeDescendingLower M f U cutoff P →o RelativeAllEligibleLower M f U cutoff P where
  toFun Q:=⟨relativeLowerClose M f U cutoff P Q,(relativeLowerClose_mem M f U cutoff Q.property.1 Q.property.2).1,
    relativeLowerClose_all_eligible M f U cutoff Q.property.1.le⟩
  monotone':=fun _ R h=>relativeLowerClose_monotone M f U cutoff h R.property.1.le

lemma relativeAllEligible_retract (P:Deligne M) :
    (relativeAllEligibleProjection M f U cutoff P).comp (relativeAllEligibleInclusion M f U cutoff P)=OrderHom.id := by
  apply OrderHom.ext
  funext Q
  apply Subtype.ext
  exact relativeLowerClose_eq_of_all M f U cutoff Q.property.2 Q.property.1.le

noncomputable def relativeEarlierLower_equiv_allEligible (P:Deligne M) :
    ContinuousMap.HomotopyEquiv |nerve (RelativeDescendingLower M f U cutoff P)| |nerve (RelativeAllEligibleLower M f U cutoff P)| :=
  nerveOrderRetractionEquiv (relativeAllEligibleProjection M f U cutoff P) (relativeAllEligibleInclusion M f U cutoff P)
    (relativeAllEligible_retract M f U cutoff P) (le_relativeLowerRetraction M f U cutoff P)


end HarmonicArtin.ParabolicIntersections

end OAI
