import Mathlib
import OAI.Topology.ArtinGroups.Functors.Placement
import OAI.Topology.ArtinGroups.Functors.ReversibleQuiverMap
import OAI.Topology.ArtinGroups.Complexes.LowerTruncation

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
attribute [local instance] Classical.decEq Classical.propDecidable
open Zigzag Zigzag.BasedComplex

universe u
variable {V A W B:Type u} {K:Type*} {Q:ReversibleQuiver V A} {R:ReversibleQuiver W B}
  (e:Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I:Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] [DecidableEq I] in
lemma complex_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    e.complex (lowerTruncation Q E hE d)=lowerTruncation R (e.complex E) (e.complex_minimal hE) d := rfl

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] in
lemma classMap_lowerTruncation (x:FiniteHomotopyClass Q (K:=K)) (d:ℤ) :
    e.classMap (classLowerTruncation Q d x)=classLowerTruncation R d (e.classMap x) := by
  let E:=(minimalClassModel Q x).complex
  have hE:=minimalClassModel_minimal Q x
  have hx:classOfComplex Q E=x:=minimalClassModel_class Q x
  rw [← hx,classMap_complex,classLowerTruncation_minimal Q E hE d,
    classLowerTruncation_minimal R (e.complex E) (e.complex_minimal hE) d,
    classMap_complex,e.complex_lowerTruncation]
  rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
