import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomDimensionDual

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A) [DecidableEq (ProbeVertex V)]

lemma probeClassHomDimension_generatorArray_flexible
    (x:FiniteHomotopyClass (probeQuiver Q) (K:=K)) (α:V) (b:Bool)
    (ha:∀i,((minimalClassModel (probeQuiver Q) x).complex.placement i).color≠.inr (α,b)) (n v:ℤ) :
    classHomDimension (probeQuiver Q) n v (initialClass (probeQuiver Q) (.inr (α,b))) x=
      classGeneratorArray (probeQuiver Q) x ⟨.inl α,n,v-1⟩ := by
  cases Subsingleton.elim (inferInstance : DecidableEq (ProbeVertex V))
    (@instDecidableEqSum V (V×Bool) (Classical.decEq V)
      (@instDecidableEqProd V Bool (Classical.decEq V) inferInstance))
  exact probeClassHomDimension_generatorArray Q x α b ha n v

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
