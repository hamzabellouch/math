import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Level
import OAI.Topology.ArtinGroups.Quivers.Reduction

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]

noncomputable def generatorArray (E : BasedComplex Q (K := K) I) :
    GeneratorPlacement V →₀ ℕ := ∑ i, Finsupp.single (E.placement i) 1

lemma generatorArray_apply (E : BasedComplex Q (K := K) I) (a : GeneratorPlacement V) :
    E.generatorArray Q a = E.multiplicity Q a := by
  classical
  simp only [generatorArray, Finsupp.finsetSum_apply, Finsupp.single_apply,
    multiplicity, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.sum_boole, Nat.cast_id]

noncomputable def levelArray (E : BasedComplex Q (K := K) I) : V × ℤ →₀ ℕ :=
  (E.generatorArray Q).mapDomain (fun a => (a.color, a.level))

lemma levelArray_eq_sum (E : BasedComplex Q (K := K) I) :
    E.levelArray Q = ∑ i, Finsupp.single ((E.placement i).color, (E.placement i).level) 1 := by
  simp only [levelArray, generatorArray, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]

lemma levelArray_apply (E : BasedComplex Q (K := K) I) (v : V) (d : ℤ) :
    E.levelArray Q (v, d) = Nat.card {i : I //
      (E.placement i).color = v ∧ (E.placement i).level = d} := by
  classical
  simp only [levelArray_eq_sum, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Prod.mk.injEq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.sum_boole, Nat.cast_id]

variable [DecidableEq I] [DecidableEq J]

lemma generatorArray_eq_of_minimal_homotopyEquivalence
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q E F) :
    E.generatorArray Q = F.generatorArray Q := by
  ext a
  simp only [generatorArray_apply]
  exact multiplicity_eq_of_minimal_homotopyEquivalence Q E F hE hF e a

lemma levelArray_eq_of_minimal_homotopyEquivalence
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (e : HomotopyEquivalence Q E F) :
    E.levelArray Q = F.levelArray Q := by
  unfold levelArray
  rw [generatorArray_eq_of_minimal_homotopyEquivalence Q E F hE hF e]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
