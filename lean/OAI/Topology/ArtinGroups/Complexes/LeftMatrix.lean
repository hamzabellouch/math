import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PureHomSpaceHomogeneous

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]

lemma coefficientMap_row_support {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F)
    (hf : CoefficientMatrix Q f.matrix) (U : Set V)
    (hF : ∀ j, (F.placement j).color ∈ U) (i : I) (j : J)
    (hi : (E.placement i).color ∉ U) : f.matrix i j = 0 := by
  apply Zigzag.ext
  · funext w
    change (f.matrix i j).vertex w = 0
    by_contra hw
    have he := (reduction_support Q f.entries f.degree i j w hw).1
    exact hi (he ▸ hF j)
  · exact (hf i j).1
  · exact (hf i j).2

lemma pureMap_coefficient {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) (q : ℤ)
    (hE : ∀ i, (E.placement i).level = q) (hF : ∀ j, (F.placement j).level = q) :
    CoefficientMatrix Q f.matrix :=
  pure_homSpace_coefficient Q E F hE hF (by omega) ⟨f.entries, f.degree⟩

omit [Fintype L] in
lemma pureMap_mul_support {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) (q : ℤ)
    (hE : ∀ i, (E.placement i).level = q) (hF : ∀ j, (F.placement j).level = q)
    (U : Set V) (hU : ∀ j, (F.placement j).color ∈ U)
    (g : Matrix J L (Q.Zigzag K)) (i : I) (j : L)
    (hi : (E.placement i).color ∉ U) : (f.matrix * g) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro t _
  rw [coefficientMap_row_support Q f (pureMap_coefficient Q f q hE hF) U hU i t hi,
    MulZeroClass.zero_mul]

noncomputable def leftMatrix (a : Matrix I J (Q.Zigzag K)) :
    Matrix J L (Q.Zigzag K) →ₗ[K] Matrix I L (Q.Zigzag K) where
  toFun f := a * f
  map_add' _ _ := Matrix.mul_add _ _ _
  map_smul' _ _ := Matrix.mul_smul _ _ _

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
