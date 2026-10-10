import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistModern
import OAI.Topology.ArtinGroups.Complexes.LayerSocleDimensionLayer
import OAI.Topology.ArtinGroups.Complexes.HighConeRetainedPure

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem classPositiveTwist_unshifted_layer (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (α:V) (ht:∀ c,classLayerTopDimension Q (q-1) α c x=0) :
    classLayer Q q (classPositiveTwist Q α x)=
      classLayer Q q (classPositiveTwist Q α (classLayer Q q x)) := by
  let E:=(minimalClassModel Q x).complex
  have hE:E.IsMinimal Q:=minimalClassModel_minimal Q x
  have hx:classOfComplex Q E=x:=minimalClassModel_class Q x
  let L:=lowerTruncation Q E hE q
  have hL:L.IsMinimal Q:=lowerTruncation_minimal Q E hE q
  have hl:classLayer Q (q-1) (classOfComplex Q L)=classLayer Q (q-1) x := by
    exact (classLayer_lowerTruncation_le Q E hE (q-1) q (by omega)).trans
      (congrArg (classLayer Q (q-1)) hx)
  have htL:∀ c,coefficientTopDual Q (L.pureLayer Q hL (q-1)) α c=⊥ := by
    intro c
    exact Submodule.finrank_eq_zero.mp
      ((classLayerTopDimension_minimal Q L hL (q-1) α c).symm.trans
        ((classLayerTopDimension_congr_layer Q (q-1) hl α c).trans (ht c)))
  have hh:=positiveLayer_top Q L hL q (fun i=>i.property) α htL
  have hp:=positiveLayer_lowerTruncation Q E hE q α
  change classLayer Q q (classPositiveTwist Q α (classOfComplex Q L))=
    classLayer Q q (classPositiveTwist Q α (classOfComplex Q E)) at hp
  rw [classLayer_lowerTruncation_le Q E hE q q le_rfl,hx] at hh
  rw [hx] at hp
  exact hp.symm.trans hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
