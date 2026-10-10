import Mathlib
import OAI.Topology.ArtinGroups.Functors.Path
import OAI.Topology.ArtinGroups.Functors.Placement
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Quivers.Iso

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

variable {V A W B K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I J : Type*}

def testIndex (p : I → GeneratorPlacement V) (α:V) :
    TestIndex Q p α ≃ TestIndex R (e.placement ∘ p) (e.vertex α) :=
  Equiv.sigmaCongrRight fun i => e.cornerPath α (p i).color

omit [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B] in
lemma test_placement (p:I → GeneratorPlacement V) (α:V) (i:TestIndex Q p α) :
    testPlacement R (e.placement ∘ p) (e.vertex α) (e.testIndex p α i) =
      e.placement (testPlacement Q p α i) := by
  change GeneratorPlacement.mk _ _ (_ + Path.length (e.path i.2.val)) = _
  rw [e.path_length]
  rfl

lemma test_matrix (p:I → GeneratorPlacement V) (q:J → GeneratorPlacement V) (α:V)
    (M:Matrix I J (Q.Zigzag K)) (i:TestIndex Q p α) (j:TestIndex Q q α) :
    testMatrix R (e.placement ∘ p) (e.placement ∘ q) (e.vertex α) (e.matrix M)
      (e.testIndex p α i) (e.testIndex q α j) = testMatrix Q p q α M i j := by
  change pathCoordinates R (pathBasis R (e.path i.2.val) * e.zigzagLinear (M i.1 j.1))
    (e.path j.2.val) = _
  rw [← e.path_basis,← e.zigzagLinear_mul,e.path_coordinates]
  rfl

lemma test_transform (p:I → GeneratorPlacement V) (q:J → GeneratorPlacement V) (α:V)
    (M:Matrix I J (Q.Zigzag K)) (i:TestIndex Q p α) (j:TestIndex Q q α) :
    testTransform R (e.placement ∘ p) (e.placement ∘ q) (e.vertex α) (e.matrix M)
      (e.testIndex p α i) (e.testIndex q α j) =
      e.zigzagLinear (testTransform Q p q α M i j) := by
  unfold testTransform scalarCornerMatrix
  rw [e.test_matrix,← e.zigzag_vertexId,map_smul]

lemma evaluation_matrix (p:I → GeneratorPlacement V) (α:V)
    (i:TestIndex Q p α) (j:I) :
    evaluationMatrix R (e.placement ∘ p) (e.vertex α) (K := K) (e.testIndex p α i) j =
      e.zigzagLinear (evaluationMatrix Q p α i j) := by
  classical
  change (if i.1=j then pathBasis R (e.path i.2.val) else 0) = _
  unfold evaluationMatrix
  split_ifs
  · exact (e.path_basis i.2.val).symm
  · exact (map_zero e.zigzagLinear).symm

variable [Fintype I]

lemma positiveTwist_transport (E:BasedComplex Q (K := K) I) (α:V) :
    ((e.complex E).positiveTwist R (e.vertex α)).reindex R
      ((e.testIndex E.placement α).sumCongr (Equiv.refl I)) =
      e.complex (E.positiveTwist Q α) := by
  apply ext_placement_differential R
  · funext i
    rcases i with i|i
    · change GeneratorPlacement.mk _ _ (_ + Path.length (e.path i.2.val)) = _
      rw [e.path_length]
      rfl
    · rfl
  · apply Matrix.ext
    intro i j
    rcases i with i|i <;> rcases j with j|j
    · change -(testTransform R (e.placement ∘ E.placement) (e.placement ∘ E.placement)
          (e.vertex α) (e.matrix E.differential) (e.testIndex E.placement α i)
          (e.testIndex E.placement α j)) = e.zigzagLinear (-testTransform Q _ _ _ _ i j)
      rw [e.test_transform,map_neg]
    · exact e.evaluation_matrix E.placement α i j
    · exact (map_zero e.zigzagLinear).symm
    · rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
