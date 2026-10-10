import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Complexes.Refl

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J L N : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N]
  {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}

omit [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N] in
lemma Map.reindexCone_eq (f : Map Q E F) (e : L ≃ I) (d : N ≃ J) :
    (f.cone Q).reindex Q (Equiv.sumCongr e d) = (f.reindex Q e d).cone Q := by
  apply ext_placement_differential
  · funext i
    rcases i with i|i <;> rfl
  · apply Matrix.ext
    intro i j
    rcases i with i|i <;> rcases j with j|j <;> rfl

noncomputable def Map.reindexConeIsomorphism (f : Map Q E F) (e : L ≃ I) (d : N ≃ J) :
    ChainIsomorphism Q (f.cone Q) ((f.reindex Q e d).cone Q) := by
  rw [← f.reindexCone_eq Q e d]
  exact reindexChainIsomorphism Q (f.cone Q) (Equiv.sumCongr e d)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
