import Mathlib
import OAI.RepresentationTheory.TensorSquares.Triangular
import OAI.RepresentationTheory.TensorSquares.Candidate
import OAI.RepresentationTheory.TensorSquares.Transpose
import OAI.RepresentationTheory.Saxl.Model

namespace OAI

/-! The prescribed self-conjugate candidate and its tensor-square support. -/

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquares

theorem candidate_with_transpose_support (n : ℕ) (hM : 9 ≤ largestIndex n) :
    ∃ hL : (candidate (largestIndex n) (remainderPairs n)).card = n,
      (candidate (largestIndex n) (remainderPairs n)).transpose =
        candidate (largestIndex n) (remainderPairs n) ∧
      ∀ (nu : YoungDiagram) (hnu : nu.card = n),
        (0 < Saxl.kronecker
          (Saxl.canonicalTableau (candidate (largestIndex n) (remainderPairs n)) hL)
          (Saxl.canonicalTableau (candidate (largestIndex n) (remainderPairs n)) hL)
          (Saxl.canonicalTableau nu hnu)) ↔
        (0 < Saxl.kronecker
          (Saxl.canonicalTableau (candidate (largestIndex n) (remainderPairs n)) hL)
          (Saxl.canonicalTableau (candidate (largestIndex n) (remainderPairs n)) hL)
          (Saxl.canonicalTableau nu.transpose ((Saxl.transpose_card nu).trans hnu))) := by
  obtain ⟨hcard, hself⟩ := candidate_size_and_self_conjugacy n hM
  refine ⟨hcard, hself, ?_⟩
  intro nu hnu
  exact transpose_support_of_self_conjugate _ hcard hself nu hnu

end UniversalTensorSquares

end

end OAI
