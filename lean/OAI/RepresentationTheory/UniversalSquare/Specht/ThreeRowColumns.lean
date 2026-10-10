import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.ThreeRowGenerator

namespace OAI

/-! Three Row Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

def pairCoords : Fin 6 → Fin 3 × Fin 3 := ![(0,0),(1,1),(0,1),(1,0),(0,2),(2,0)]

def pairLetters : Fin 6 → Fin 9 := fun a => finProdFinEquiv (pairCoords a)

lemma pairLetters_output (a : Fin 6) : output (d := 3) (e := 3) (pairLetters a) ∈ Set.Icc 1 3 := by
  fin_cases a <;> decide

lemma restrict_square {n : ℕ} (v : WordSpace n 3) (w : Fin n → Fin 6) :
    restrictLetters pairLetters (wordTensor n 3 3 (v ⊗ₜ[ℂ] v)) w =
      v (fun i => (pairCoords (w i)).1) * v (fun i => (pairCoords (w i)).2) := by
  change wordTensor n 3 3 (v ⊗ₜ[ℂ] v) (pairLetters ∘ w) = _
  rw [wordTensor_tmul]
  have hleft : splitLeft (d:=3) (e:=3) (pairLetters ∘ w) =
      fun i => (pairCoords (w i)).1 := by
    funext i
    exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (pairCoords (w i)))
  have hright : splitRight (d:=3) (e:=3) (pairLetters ∘ w) =
      fun i => (pairCoords (w i)).2 := by
    funext i
    exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (pairCoords (w i)))
  rw [hleft,hright]

lemma restrict_projected {n : ℕ} (v : WordSpace n 9) :
    restrictLetters pairLetters (invariantCoordinateProjection (inOutputs (d := 3) (e := 3) (Set.Icc 1 3))
      (inOutputs_invariant (d := 3) (e := 3) (Set.Icc 1 3)) v) = restrictLetters pairLetters v := by
  classical
  funext w
  change (if inOutputs (d := 3) (e := 3) (Set.Icc 1 3) (pairLetters ∘ w) then v (pairLetters ∘ w) else 0) = _
  exact ite_eq_left (fun i => pairLetters_output (w i))

lemma perm_three_sum {R : Type*} [AddCommMonoid R] (f : Equiv.Perm (Fin 3) → R) :
    ∑ g, f g = f 1 + f (Equiv.swap 0 1) + f (Equiv.swap 0 2) +
      f (Equiv.swap 1 2) + f (Equiv.swap 0 1 * Equiv.swap 1 2) +
      f (Equiv.swap 1 2 * Equiv.swap 0 1) := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by decide +kernel
  rw [h]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  ac_rfl

lemma symmetricTriple_expansion : symmetricTriple =
    Pi.single ![4,5,1] 1 + Pi.single ![5,4,1] 1 + Pi.single ![1,5,4] 1 +
    Pi.single ![4,1,5] 1 + Pi.single ![5,1,4] 1 + Pi.single ![1,4,5] 1 := by
  rw [symmetricTriple,perm_three_sum]
  have h₀ : tripleColors ∘ (1 : Equiv.Perm (Fin 3)) = ![4,5,1] := rfl
  have h₁ : tripleColors ∘ Equiv.swap 0 1 = ![5,4,1] := by decide
  have h₂ : tripleColors ∘ Equiv.swap 0 2 = ![1,5,4] := by decide
  have h₃ : tripleColors ∘ Equiv.swap 1 2 = ![4,1,5] := by decide
  have h₄ : tripleColors ∘ ((Equiv.swap 0 1 * Equiv.swap 1 2) : Equiv.Perm (Fin 3)) = ![5,1,4] := by decide
  have h₅ : tripleColors ∘ ((Equiv.swap 1 2 * Equiv.swap 0 1) : Equiv.Perm (Fin 3)) = ![1,4,5] := by decide
  rw [h₀,h₁,h₂,h₃,h₄,h₅]

def sixSquare {n : ℕ} (v : WordSpace n 3) : WordSpace n 6 :=
  restrictLetters pairLetters (wordTensor n 3 3 (v ⊗ₜ[ℂ] v))

lemma sixSquare_apply {n : ℕ} (v : WordSpace n 3) (w : Fin n → Fin 6) :
    sixSquare v w =
      v (fun i => (pairCoords (w i)).1) * v (fun i => (pairCoords (w i)).2) :=
  restrict_square v w

lemma sixSquare_product {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a 3) (u : WordSpace b 3) :
    sixSquare (positionProduct e v u) = positionProduct e (sixSquare v) (sixSquare u) := by
  funext w
  simp only [sixSquare_apply, positionProduct]
  exact mul_mul_mul_comm _ _ _ _

lemma sixSquare_pair (w : Fin 2 → Fin 6) :
    sixSquare (wedge 2 (standard 3)) w = sixPairForm (w 0) (w 1) := by
  rw [sixSquare_apply,wedge_apply_det,wedge_apply_det]
  simp only [Matrix.det_fin_two,Matrix.of_apply]
  generalize w 0 = a
  generalize w 1 = b
  fin_cases a <;> fin_cases b <;> norm_num [standard,pairCoords,sixPairForm]

lemma word_three_eq_iff {d : ℕ} (w : Fin 3 → Fin d) (a b c : Fin d) :
    w = ![a,b,c] ↔ w 0 = a ∧ w 1 = b ∧ w 2 = c := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl,rfl⟩
  · rintro ⟨ha,hb,hc⟩
    funext i
    fin_cases i <;> assumption

lemma sixSquare_triple (w : Fin 3 → Fin 6) :
    sixSquare (wedge 3 (standard 3)) w = -symmetricTriple w := by
  rw [sixSquare_apply,wedge_apply_det,wedge_apply_det,symmetricTriple_expansion]
  simp only [Matrix.det_fin_three,Matrix.of_apply,Pi.add_apply,Pi.single_apply,word_three_eq_iff]
  generalize w 0 = a
  generalize w 1 = b
  generalize w 2 = c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [standard,pairCoords,Fin.ext_iff]

end Saxl.ThreeRow
end
end

end OAI
