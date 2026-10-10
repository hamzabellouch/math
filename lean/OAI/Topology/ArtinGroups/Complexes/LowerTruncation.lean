import Mathlib
import OAI.Topology.ArtinGroups.Complexes.UpperBound
import OAI.Topology.ArtinGroups.Complexes.DownClosed
import OAI.Topology.ArtinGroups.Complexes.LowMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def classLowerTruncation (d:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    FiniteHomotopyClass Q (K:=K) :=
  classOfComplex Q (lowerTruncation Q (minimalClassModel Q x).complex (minimalClassModel_minimal Q x) d)

omit [Fintype V] [DecidableEq A] in
lemma classLowerTruncation_minimal (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    classLowerTruncation Q d (classOfComplex Q E)=classOfComplex Q (lowerTruncation Q E hE d) :=
  classOfComplex_eq Q ((minimalClassModelEquivalence Q E).lowerTruncation Q
    (minimalClassModel_minimal Q _) hE d)

omit [Fintype V] [DecidableEq A] in
lemma classLowerTruncation_cap (d:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    ClassUpperBound Q d (classLowerTruncation Q d x) :=
  classUpperBound_of_representative Q _ (fun i=>i.property)

omit [Fintype V] [DecidableEq A] in
lemma classLowerTruncation_floor (d a:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hx:ClassLowerBound Q a x) : ClassLowerBound Q a (classLowerTruncation Q d x) :=
  classLowerBound_of_representative Q _ (fun i=>hx i)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
