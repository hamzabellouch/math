import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.AltList
import OAI.Topology.ArtinGroups.Coxeter.OrdinaryCoxeterMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange

universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn : ∀ a,Q.source a≠Q.target a)

lemma ordinaryTwist_braid (α β : V) :
    ((altList α β (ordinaryCoxeterMatrix Q α β)).map (classTwistPerm Q (K:=K) hn)).prod=
      ((altList β α (ordinaryCoxeterMatrix Q α β)).map (classTwistPerm Q hn)).prod := by
  by_cases he : α=β
  · subst β; rfl
  by_cases ho : OrthogonalVertices Q α β
  · rw [ordinaryCoxeterMatrix_orthogonal Q ho]
    simpa only [altList_succ,altList_zero,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      _root_.mul_one] using classTwistPerm_orthogonal Q hn ho
  by_cases ha : Nonempty (SimpleEdge Q α β)
  · obtain ⟨edge⟩ := ha
    rw [ordinaryCoxeterMatrix_adjacent Q edge]
    simpa only [altList_succ,altList_zero,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      _root_.mul_one,_root_.mul_assoc] using classTwistPerm_adjacent Q hn edge
  · have hzero : ordinaryCoxeterMatrix Q α β=0 := by simp [ordinaryCoxeterMatrix,he,ho,ha]
    rw [hzero]
    rfl

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
