import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseMatrix
import OAI.Topology.ArtinGroups.Complexes.Cone

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J L:Type u} [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

omit [Fintype V] [DecidableEq A] in
theorem classLayer_eq_of_cone_equivalence (f:Map Q E F)
    (D:BasedComplex Q (K:=K) L) (e:HomotopyEquivalence Q (f.cone Q) D)
    (q:ℤ) (hD:∀ j,(D.placement j).level≠q-1 ∧ (D.placement j).level≠q) :
    classLayer Q q (classOfComplex Q E)=classLayer Q q (classOfComplex Q F) := by
  let E₀:=minimalClassModel Q (classOfComplex Q E)
  let F₀:=minimalClassModel Q (classOfComplex Q F)
  let a:HomotopyEquivalence Q E₀.complex E:=minimalClassModelEquivalence Q E
  let b:HomotopyEquivalence Q F F₀.complex:=(minimalClassModelEquivalence Q F).symm Q
  let h:=a.forward.comp Q f
  let g:=h.comp Q b.forward
  let c:HomotopyEquivalence Q (g.cone Q) D:=
    (((b.coneTarget Q h).symm Q).trans Q (a.coneSource Q f)).trans Q e
  have hh:=classLayer_eq_of_cone_gap Q g
    (minimalClassModel_minimal Q (classOfComplex Q E))
    (minimalClassModel_minimal Q (classOfComplex Q F)) D c q hD
  have he:classOfComplex Q E₀.complex=classOfComplex Q E:=minimalClassModel_class Q _
  have hf:classOfComplex Q F₀.complex=classOfComplex Q F:=minimalClassModel_class Q _
  exact (congrArg (classLayer Q q) he).symm.trans
    (hh.trans (congrArg (classLayer Q q) hf))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
