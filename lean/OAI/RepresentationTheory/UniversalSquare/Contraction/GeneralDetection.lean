import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.RepeatedColumns

namespace OAI

/-! General Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma wordMap_pair_transpose {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (x : WordSpace n d) (y : WordSpace n e) :
    dotProduct (wordMap L x) y = dotProduct x (wordMap (fun b a => L a b) y) := by
  classical
  change (∑ b, (∑ a, x a * ∏ i, L (a i) (b i)) * y b) =
    ∑ a, x a * ∑ b, y b * ∏ i, L (a i) (b i)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem specht_to_cyclic_of_pair {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (L : Fin (μ.colLen 0) → Fin d → ℂ)
    (u : WordSpace n d)
    (h : dotProduct (wordMap L (polytabloid t)) u ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, F ≠ 0 := by
  let pr := subrepProject (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
  let F : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) :=
    pr.comp ((wordMap (fun b a => L a b)).comp (subrepInclusion _))
  apply specht_map_back_of_nonzero _ t F
  intro hz
  have hp := subrepProject_pair (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
    (wordMap (fun b a => L a b) u) ⟨polytabloid t, mem_cyclic _ _⟩
  have he : pr (wordMap (fun b a => L a b) u) = 0 :=
    congrArg (fun H : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) =>
      H ⟨u, mem_cyclic _ _⟩) hz
  rw [he] at hp
  change dotProduct (0 : WordSpace n (μ.colLen 0)) (polytabloid t) =
    dotProduct (wordMap (fun b a => L a b) u) (polytabloid t) at hp
  rw [zero_dotProduct] at hp
  rw [wordMap_pair_transpose, dotProduct_comm]
    at h
  exact h hp.symm

end Saxl
end
end

end OAI
