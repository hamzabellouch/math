import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistModern
import OAI.Topology.ArtinGroups.Harmonic.PositiveWord
import OAI.Topology.ArtinGroups.Harmonic.FusionColorWord

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] {K:Type*} [Field K]
  (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "hdiag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd
local notation "T" => fusionPacketPerm m d hd hdiag (K:=K)

lemma sourceBottomWord_nil (J:Set S) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    sourceBottomWord M J q [] x=classLayer Q q x := by
  simp only [sourceBottomWord,sourcePositiveWord,List.map_nil,wordArtin,
    List.prod_nil,map_one,Equiv.Perm.one_apply]

lemma sourceBottomWord_cons (J:Set S) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hx:ClassLowerBound Q q x) (j:J) (w:List J) :
    sourceBottomWord M J q (j::w) x=
      classLayer Q q (T (.inl j) (sourceBottomWord M J q w x)) := by
  unfold sourceBottomWord
  rw [sourcePositiveWord_cons]
  have h:=positiveWord_bottom_layer Q (fusionColorWord m (.inl (j:S)))
    (sourcePositiveWord M J w x) q (sourcePositiveWord_lowerBound M J w x q hx)
  have hc (y:FiniteHomotopyClass Q (K:=K)) :
      positiveWordAction Q (fusionColorWord m (.inl (j:S))) y=T (.inl j) y := by
    convert fusionColorWord_action m d hd hdiag (.inl (j:S)) y using 1
    congr 9
    exact Subsingleton.elim _ _
  rw [hc,hc] at h
  exact h

end HarmonicArtin

end OAI
