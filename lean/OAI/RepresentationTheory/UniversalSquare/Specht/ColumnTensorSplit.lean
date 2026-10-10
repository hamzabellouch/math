import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.FlagColumns

namespace OAI

/-! Column Tensor Split. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.FlagColumns

def splitCons {a b A B n : ℕ} (e : Fin n ≃ Fin A ⊕ Fin B) :
    Fin ((a + b) + n) ≃ Fin (a + A) ⊕ Fin (b + B) :=
  (finSumFinEquiv.symm.trans ((finSumFinEquiv.symm).sumCongr e)).trans
    ((Equiv.sumSumSumComm (Fin a) (Fin b) (Fin A) (Fin B)).trans
      (finSumFinEquiv.sumCongr finSumFinEquiv))

lemma splitCons_left_first {a b A B n : ℕ} (e : Fin n ≃ Fin A ⊕ Fin B) (i : Fin a) :
    (splitCons (a := a) (b := b) e).symm (Sum.inl (Fin.castAdd A i)) =
      Fin.castAdd n (Fin.castAdd b i) := by
  simp [splitCons, Equiv.sumCongr_symm]

lemma splitCons_right_first {a b A B n : ℕ} (e : Fin n ≃ Fin A ⊕ Fin B) (i : Fin b) :
    (splitCons (a := a) (b := b) e).symm (Sum.inr (Fin.castAdd B i)) =
      Fin.castAdd n (Fin.natAdd a i) := by
  simp [splitCons, Equiv.sumCongr_symm]

lemma splitCons_left_rest {a b A B n : ℕ} (e : Fin n ≃ Fin A ⊕ Fin B) (i : Fin A) :
    (splitCons (a := a) (b := b) e).symm (Sum.inl (Fin.natAdd a i)) =
      Fin.natAdd (a+b) (e.symm (Sum.inl i)) := by
  simp [splitCons, Equiv.sumCongr_symm]

lemma splitCons_right_rest {a b A B n : ℕ} (e : Fin n ≃ Fin A ⊕ Fin B) (i : Fin B) :
    (splitCons (a := a) (b := b) e).symm (Sum.inr (Fin.natAdd b i)) =
      Fin.natAdd (a+b) (e.symm (Sum.inr i)) := by
  simp [splitCons, Equiv.sumCongr_symm]

def splitPositions : (ps : List (ℕ × ℕ)) →
    Fin (ps.map (fun p => p.1 + p.2)).sum ≃
      Fin (ps.map Prod.fst).sum ⊕ Fin (ps.map Prod.snd).sum
  | [] => show Fin 0 ≃ Fin 0 ⊕ Fin 0 from Equiv.equivOfIsEmpty _ _
  | (_,_)::ps => splitCons (splitPositions ps)

lemma splitPositions_left_first (a b : ℕ) (ps : List (ℕ × ℕ)) (i : Fin a) :
    (splitPositions ((a,b)::ps)).symm (Sum.inl (Fin.castAdd (ps.map Prod.fst).sum i)) =
      Fin.castAdd (ps.map (fun p => p.1+p.2)).sum (Fin.castAdd b i) := by
  exact splitCons_left_first (splitPositions ps) i

lemma splitPositions_right_first (a b : ℕ) (ps : List (ℕ × ℕ)) (i : Fin b) :
    (splitPositions ((a,b)::ps)).symm (Sum.inr (Fin.castAdd (ps.map Prod.snd).sum i)) =
      Fin.castAdd (ps.map (fun p => p.1+p.2)).sum (Fin.natAdd a i) := by
  exact splitCons_right_first (splitPositions ps) i

lemma splitPositions_left_rest (a b : ℕ) (ps : List (ℕ × ℕ))
    (i : Fin (ps.map Prod.fst).sum) :
    (splitPositions ((a,b)::ps)).symm (Sum.inl (Fin.natAdd a i)) =
      Fin.natAdd (a+b) ((splitPositions ps).symm (Sum.inl i)) := by
  exact splitCons_left_rest (splitPositions ps) i

lemma splitPositions_right_rest (a b : ℕ) (ps : List (ℕ × ℕ))
    (i : Fin (ps.map Prod.snd).sum) :
    (splitPositions ((a,b)::ps)).symm (Sum.inr (Fin.natAdd b i)) =
      Fin.natAdd (a+b) ((splitPositions ps).symm (Sum.inr i)) := by
  exact splitCons_right_rest (splitPositions ps) i

theorem tensorList_split {d : ℕ}
    (v : ∀ p : ℕ × ℕ, WordSpace p.1 d) (u : ∀ p : ℕ × ℕ, WordSpace p.2 d)
    (ps : List (ℕ × ℕ)) :
    positionProduct (splitPositions ps) (tensorList Prod.fst v ps) (tensorList Prod.snd u ps) =
      tensorList (fun p => p.1+p.2)
        (fun p => positionProduct finSumFinEquiv.symm (v p) (u p)) ps := by
  induction ps with
  | nil => funext w; change (1:ℂ)*1=1; ring
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    funext w
    have hll : leftWord finSumFinEquiv.symm (leftWord (splitPositions ((a,b)::ps)) w) =
        leftWord finSumFinEquiv.symm (leftWord finSumFinEquiv.symm w) := by
      funext i
      change w ((splitPositions ((a,b)::ps)).symm (Sum.inl (Fin.castAdd _ i))) =
        w (Fin.castAdd _ (Fin.castAdd _ i))
      erw [splitPositions_left_first]
      rfl
    have hrl : leftWord finSumFinEquiv.symm (rightWord (splitPositions ((a,b)::ps)) w) =
        rightWord finSumFinEquiv.symm (leftWord finSumFinEquiv.symm w) := by
      funext i
      change w ((splitPositions ((a,b)::ps)).symm (Sum.inr (Fin.castAdd _ i))) =
        w (Fin.castAdd _ (Fin.natAdd _ i))
      erw [splitPositions_right_first]
      rfl
    have hlr : rightWord finSumFinEquiv.symm (leftWord (splitPositions ((a,b)::ps)) w) =
        leftWord (splitPositions ps) (rightWord finSumFinEquiv.symm w) := by
      funext i
      change w ((splitPositions ((a,b)::ps)).symm (Sum.inl (Fin.natAdd _ i))) =
        w (Fin.natAdd _ ((splitPositions ps).symm (Sum.inl i)))
      erw [splitPositions_left_rest]
      rfl
    have hrr : rightWord finSumFinEquiv.symm (rightWord (splitPositions ((a,b)::ps)) w) =
        rightWord (splitPositions ps) (rightWord finSumFinEquiv.symm w) := by
      funext i
      change w ((splitPositions ((a,b)::ps)).symm (Sum.inr (Fin.natAdd _ i))) =
        w (Fin.natAdd _ ((splitPositions ps).symm (Sum.inr i)))
      erw [splitPositions_right_rest]
      rfl
    change ((v (a,b) _) * tensorList Prod.fst v ps _) *
      ((u (a,b) _) * tensorList Prod.snd u ps _) =
        ((v (a,b) _) * (u (a,b) _)) * _
    erw [hll,hrl,hlr,hrr, ← ih]
    change (_ * _) * (_ * _) = (_ * _) * (_ * _)
    exact mul_mul_mul_comm _ _ _ _

lemma blocks_eq_tensorList {α : Type*} (k : α → ℕ) {d : ℕ}
    (N : ℕ → Fin d → ℂ) (as : List α) :
    blocks (as.map k) N = tensorList k (fun a => wedge (k a) N) as := by
  induction as with
  | nil => exact blocks_nil N
  | cons a as ih => exact (blocks_cons (k a) (as.map k) N).trans (by rw [ih]; rfl)

end Saxl.FlagColumns
end
end

end OAI
