import Mathlib
import OAI.Topology.ArtinGroups.Functors.Path2

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)]
  {I J:Type*}
local notation "R" => probeQuiver Q

noncomputable def testIndex (p : I → GeneratorPlacement V) (α:V) :
    TestIndex Q p α ≃ TestIndex R (placement ∘ p) (Sum.inl α) :=
  Equiv.sigmaCongrRight fun i => cornerPath Q α (p i).color

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [DecidableEq (ProbeVertex V)] [DecidableEq (ProbeArrow V A)] in
lemma test_placement (p:I → GeneratorPlacement V) (α:V) (i:TestIndex Q p α) :
    testPlacement R (placement ∘ p) (Sum.inl α) (testIndex Q p α i) =
      placement (testPlacement Q p α i) := by
  change GeneratorPlacement.mk _ _ (_ + Path.length (path i.2.val)) = _
  rw [path_length]
  rfl

lemma test_matrix (p:I → GeneratorPlacement V) (q:J → GeneratorPlacement V) (α:V)
    (M:Matrix I J (Q.Zigzag K)) (i:TestIndex Q p α) (j:TestIndex Q q α) :
    testMatrix R (placement ∘ p) (placement ∘ q) (Sum.inl α) (matrix Q M)
      (testIndex Q p α i) (testIndex Q q α j) = testMatrix Q p q α M i j := by
  change pathCoordinates R (pathBasis R (path i.2.val) * zigzagLinear Q (M i.1 j.1))
    (path j.2.val) = _
  rw [← path_basis Q,← zigzagLinear_mul Q,path_coordinates Q]
  rfl

lemma test_transform (p:I → GeneratorPlacement V) (q:J → GeneratorPlacement V) (α:V)
    (M:Matrix I J (Q.Zigzag K)) (i:TestIndex Q p α) (j:TestIndex Q q α) :
    testTransform R (placement ∘ p) (placement ∘ q) (Sum.inl α) (matrix Q M)
      (testIndex Q p α i) (testIndex Q q α j) =
      zigzagLinear Q (testTransform Q p q α M i j) := by
  unfold testTransform scalarCornerMatrix
  rw [test_matrix Q,← zigzag_vertexId Q,map_smul]

lemma evaluation_matrix (p:I → GeneratorPlacement V) (α:V)
    (i:TestIndex Q p α) (j:I) :
    evaluationMatrix R (placement ∘ p) (Sum.inl α) (K := K) (testIndex Q p α i) j =
      zigzagLinear Q (evaluationMatrix Q p α i j) := by
  classical
  change (if i.1=j then pathBasis R (path i.2.val) else 0) = _
  unfold evaluationMatrix
  split_ifs
  · exact (path_basis Q i.2.val).symm
  · exact (map_zero (zigzagLinear Q)).symm

variable [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma positiveTwist_transport (E:BasedComplex Q (K := K) I) (α:V) :
    ((complex Q E).positiveTwist R (Sum.inl α)).reindex R
      ((testIndex Q E.placement α).sumCongr (Equiv.refl I)) =
      complex Q (E.positiveTwist Q α) := by
  apply ext_placement_differential R
  · funext i
    rcases i with i|i
    · change GeneratorPlacement.mk _ _ (_ + Path.length (path i.2.val)) = _
      rw [path_length]
      rfl
    · rfl
  · apply Matrix.ext
    intro i j
    rcases i with i|i <;> rcases j with j|j
    · change -(testTransform R (placement ∘ E.placement) (placement ∘ E.placement)
          (Sum.inl α) (matrix Q E.differential) (testIndex Q E.placement α i)
          (testIndex Q E.placement α j)) = zigzagLinear Q (-testTransform Q _ _ _ _ i j)
      rw [test_transform Q,map_neg]
    · exact evaluation_matrix Q E.placement α i j
    · exact (map_zero (zigzagLinear Q)).symm
    · rfl

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
