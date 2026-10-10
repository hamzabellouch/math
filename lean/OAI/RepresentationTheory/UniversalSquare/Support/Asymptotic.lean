import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceFour
import OAI.RepresentationTheory.UniversalSquare.Capacity.CapacityDichotomy

namespace OAI

/-! Asymptotic. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma remainderPairs_bound (n : ℕ) : 2*remainderPairs n ≤ 3*staircaseIndex n+4 := by
  rcases Nat.mod_two_eq_zero_or_one (staircaseIndex n) with he | ho
  · exact remainderPairs_bound_even n he
  · have h := remainderPairs_bound_odd n ho
    omega

lemma fixedCandidate_half_bound (n : ℕ) (hM : 9 ≤ staircaseIndex n) :
    remainderPairs n / 2 ≤ staircaseIndex n-2 := by
  have h := remainderPairs_bound n
  omega

lemma canonical_square_pos_congr {n N : ℕ} {lam Lam μ : YoungDiagram}
    (he : n = N) (hlam : lam = Lam) (hc : lam.card = n) (hC : Lam.card = N)
    (hμ : μ.card = n) (hμ' : μ.card = N) :
    (0 < kronecker (canonicalTableau lam hc) (canonicalTableau lam hc) (canonicalTableau μ hμ)) ↔
      (0 < kronecker (canonicalTableau Lam hC) (canonicalTableau Lam hC) (canonicalTableau μ hμ')) := by
  subst N
  subst Lam
  rfl

theorem fixedCandidate_nonexceptional_pos (n : ℕ) (hn : 64 < n)
    (hexc : ¬ exceptionalPair (staircaseIndex n) (remainderPairs n))
    (μ : YoungDiagram) (hμ : μ.card = n) :
    0 < kronecker (canonicalTableau (fixedCandidate n)
      (fixedCandidate_card n (by have := (fixedCandidate_large_degree n hn).1; omega)))
      (canonicalTableau (fixedCandidate n)
        (fixedCandidate_card n (by have := (fixedCandidate_large_degree n hn).1; omega)))
      (canonicalTableau μ hμ) := by
  have hM := (fixedCandidate_large_degree n hn).1
  by_cases hr : remainderPairs n = 0
  · have he : n = staircaseIndex n * (staircaseIndex n+1)/2 := by
      have h := degree_eq n
      rw [hr,staircase_card] at h
      omega
    apply (canonical_square_pos_congr he
      (fixedCandidate_eq_staircase_of_remainder_zero n hr) _
      (staircase_card (staircaseIndex n)) hμ (hμ.trans he)).mpr
    exact saxl_kronecker_pos (staircaseIndex n) (by omega) μ (hμ.trans he)
  · rcases fixed_degree_capacity_dichotomy n hn (by omega) hexc μ hμ with
      h | h | h | h
    · exact balance_kronecker_pos hM (fixedCandidate_half_bound n hM) (by omega)
        _ μ _ h
    · exact balance_kronecker_pos_or_transpose hM (fixedCandidate_half_bound n hM)
        (by omega) _ μ hμ (Or.inr h)
    · exact fixedCandidate_band_pos n (by omega) μ hμ h
    · apply (fixedCandidate_support_transpose n (by omega) μ hμ).mpr
      exact fixedCandidate_band_pos n (by omega) μ.transpose ((transpose_card μ).trans hμ) h

universe u

theorem universal_tensor_square_nonexceptional (n : ℕ) (hn : 64 < n)
    (hexc : ¬ exceptionalPair (staircaseIndex n) (remainderPairs n)) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  have hM := (fixedCandidate_large_degree n hn).1
  refine ⟨fixedCandidate n,fixedCandidate_card n (by omega),
    fixedCandidate_nonexceptional_pos n hn hexc,?_⟩
  exact irreducibles_of_kronecker_pos _ _ (fixedCandidate_nonexceptional_pos n hn hexc)

lemma exceptional_degree_le (n : ℕ)
    (hexc : exceptionalPair (staircaseIndex n) (remainderPairs n)) : n ≤ 151 := by
  have he := degree_eq n
  rw [staircase_card] at he
  unfold exceptionalPair at hexc
  rcases hexc with ⟨hM,hr⟩ | ⟨hM,hr⟩ | ⟨hM,hr⟩ <;> rw [hM] at he <;> norm_num at he <;> omega

theorem universal_tensor_square_large (n : ℕ) (hn : 152 ≤ n) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  apply universal_tensor_square_nonexceptional n (by omega)
  intro hexc
  have := exceptional_degree_le n hexc
  omega

end UniversalTensorSquare
end
end

end OAI
