import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModel
import OAI.Topology.ArtinGroups.Complexes.CoefficientTopDual
import OAI.Topology.ArtinGroups.Complexes.BasedComplexComplex
import OAI.Topology.ArtinGroups.Complexes.Refl
import OAI.Topology.ArtinGroups.Complexes.PureSupportedCycles

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def minimalClassModelEquivalence (E : BasedComplex Q (K := K) I) :
    HomotopyEquivalence Q (minimalClassModel Q (classOfComplex Q E)).complex E :=
  Classical.choice (Quotient.exact (minimalClassModel_class Q (classOfComplex Q E)))

noncomputable def classLayer (d : ℤ) (x : FiniteHomotopyClass Q (K := K)) :
    FiniteHomotopyClass Q (K := K) :=
  classOfComplex Q ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) d)

omit [Fintype V] [DecidableEq A] in
lemma classLayer_minimal (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q) (d : ℤ) :
    classLayer Q d (classOfComplex Q E) = classOfComplex Q (E.pureLayer Q hE d) :=
  classOfComplex_eq Q (((minimalClassModelEquivalence Q E).pureLayer Q
    (minimalClassModel_minimal Q _) hE d).toHomotopyEquivalence Q)

noncomputable def classLayerSocleDimension (d : ℤ) (α : V) (c : ℤ)
    (x : FiniteHomotopyClass Q (K := K)) : ℕ :=
  Module.finrank K (coefficientSocle Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) d) α c)

noncomputable def classLayerTopDimension (d : ℤ) (α : V) (c : ℤ)
    (x : FiniteHomotopyClass Q (K := K)) : ℕ :=
  Module.finrank K (coefficientTopDual Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) d) α c)

lemma classLayerSocleDimension_minimal (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (d : ℤ) (α : V) (c : ℤ) :
    classLayerSocleDimension Q d α c (classOfComplex Q E) =
      Module.finrank K (coefficientSocle Q (E.pureLayer Q hE d) α c) :=
  (((minimalClassModelEquivalence Q E).pureLayer Q
    (minimalClassModel_minimal Q _) hE d).coefficientSocle Q
    (fun i => i.property) (fun j => j.property) α c).finrank_eq

lemma classLayerTopDimension_minimal (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (d : ℤ) (α : V) (c : ℤ) :
    classLayerTopDimension Q d α c (classOfComplex Q E) =
      Module.finrank K (coefficientTopDual Q (E.pureLayer Q hE d) α c) :=
  (((minimalClassModelEquivalence Q E).pureLayer Q
    (minimalClassModel_minimal Q _) hE d).coefficientTopDual Q
    (fun i => i.property) (fun j => j.property) α c).finrank_eq

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
