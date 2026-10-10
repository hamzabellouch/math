import Mathlib
import OAI.RepresentationTheory.Saxl.Main

namespace OAI

/-! Extensions. -/

section

noncomputable section
open scoped TensorProduct

namespace UniversalTensorSquare

universe u

theorem irreducibles_of_kronecker_pos {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hpos : ∀ (ν : YoungDiagram) (hν : ν.card = n),
      0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
        (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) :
    Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
      (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
      ∃ F : Representation.IntertwiningMap ρ
        ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
          (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
        Function.Injective F := by
  refine ⟨Saxl.specht_irreducible _, ?_⟩
  intro V _ _ _ ρ _
  obtain ⟨p, ⟨e⟩⟩ := Saxl.irreducible_equiv_specht ρ
  obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp
    (hpos (Saxl.partitionDiagram p) (Saxl.partitionDiagram_card p))
  let := Saxl.specht_irreducible (Saxl.canonicalTableau (Saxl.partitionDiagram p)
    (Saxl.partitionDiagram_card p))
  have hs := Representation.IsIrreducible.injective_or_eq_zero
    (W := Saxl.Specht (Saxl.canonicalTableau lam hlam) ⊗[ℂ]
      Saxl.Specht (Saxl.canonicalTableau lam hlam)) f
  have hi : Function.Injective f := hs.resolve_right hf
  exact ⟨f.comp e.toIntertwiningMap, hi.comp e.injective⟩

theorem universal_tensor_square_triangular (m : ℕ) (hm : 1 ≤ m) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = m * (m + 1) / 2),
      (∀ (ν : YoungDiagram) (hν : ν.card = m * (m + 1) / 2),
        0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
          (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin (m * (m + 1) / 2))) V)
        [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
            (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
          Function.Injective F := by
  refine ⟨Saxl.staircase m, Saxl.staircase_card m, Saxl.saxl_kronecker_pos m hm, ?_⟩
  exact irreducibles_of_kronecker_pos _ _ (Saxl.saxl_kronecker_pos m hm)

def staircaseIndex (n : ℕ) : ℕ :=
  Nat.findGreatest (fun M => (Saxl.staircase M).card ≤ n ∧
    (Saxl.staircase M).card % 2 = n % 2) n

lemma index_le_staircase_card (M : ℕ) : M ≤ (Saxl.staircase M).card := by
  cases M with
  | zero => simp
  | succ M => rw [Saxl.staircase_card_succ]; omega

lemma staircaseIndex_spec (n : ℕ) :
    (Saxl.staircase (staircaseIndex n)).card ≤ n ∧
    (Saxl.staircase (staircaseIndex n)).card % 2 = n % 2 := by
  unfold staircaseIndex
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · apply Nat.findGreatest_spec (P := fun M => (Saxl.staircase M).card ≤ n ∧
      (Saxl.staircase M).card % 2 = n % 2) (m := 0) (Nat.zero_le n)
    simp [he]
  · apply Nat.findGreatest_spec (P := fun M => (Saxl.staircase M).card ≤ n ∧
      (Saxl.staircase M).card % 2 = n % 2) (m := 1) (n := n) (by omega)
    simp only [Saxl.staircase_card]
    norm_num
    omega

lemma le_staircaseIndex (n M : ℕ) (hle : (Saxl.staircase M).card ≤ n)
    (hpar : (Saxl.staircase M).card % 2 = n % 2) : M ≤ staircaseIndex n := by
  apply Nat.le_findGreatest ((index_le_staircase_card M).trans hle)
  exact ⟨hle, hpar⟩

def remainderPairs (n : ℕ) : ℕ := (n - (Saxl.staircase (staircaseIndex n)).card) / 2

lemma degree_eq (n : ℕ) :
    (Saxl.staircase (staircaseIndex n)).card + 2 * remainderPairs n = n := by
  have h := staircaseIndex_spec n
  unfold remainderPairs
  omega

lemma remainderPairs_bound_odd (n : ℕ) (hodd : staircaseIndex n % 2 = 1) :
    2 * remainderPairs n ≤ staircaseIndex n - 1 := by
  have hs := staircaseIndex_spec n
  have hd := degree_eq n
  have hpar : (Saxl.staircase (staircaseIndex n + 1)).card % 2 = n % 2 := by
    rw [Saxl.staircase_card_succ]
    omega
  have hlt : n < (Saxl.staircase (staircaseIndex n + 1)).card := by
    by_contra hh
    have := le_staircaseIndex n (staircaseIndex n + 1) (by omega) hpar
    omega
  rw [Saxl.staircase_card_succ] at hlt
  omega

lemma remainderPairs_bound_even (n : ℕ) (heven : staircaseIndex n % 2 = 0) :
    2 * remainderPairs n ≤ 3 * staircaseIndex n + 4 := by
  have hs := staircaseIndex_spec n
  have hd := degree_eq n
  have hsucc : (Saxl.staircase (staircaseIndex n + 3)).card =
      (Saxl.staircase (staircaseIndex n)).card + 3 * staircaseIndex n + 6 := by
    have h1 := Saxl.staircase_card_succ (staircaseIndex n)
    have h2 : (Saxl.staircase (staircaseIndex n + 2)).card =
        (Saxl.staircase (staircaseIndex n + 1)).card + (staircaseIndex n + 2) := by
      simpa [Nat.add_assoc] using Saxl.staircase_card_succ (staircaseIndex n + 1)
    have h3 : (Saxl.staircase (staircaseIndex n + 3)).card =
        (Saxl.staircase (staircaseIndex n + 2)).card + (staircaseIndex n + 3) := by
      simpa [Nat.add_assoc] using Saxl.staircase_card_succ (staircaseIndex n + 2)
    omega
  have hpar : (Saxl.staircase (staircaseIndex n + 3)).card % 2 = n % 2 := by
    rw [hsucc]
    omega
  have hlt : n < (Saxl.staircase (staircaseIndex n + 3)).card := by
    by_contra hh
    have := le_staircaseIndex n (staircaseIndex n + 3) (by omega) hpar
    omega
  rw [hsucc] at hlt
  omega

lemma degree_le_64_of_small_index (n : ℕ) (hM : staircaseIndex n < 9) : n ≤ 64 := by
  by_contra hn
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have h11 : 11 ≤ staircaseIndex n := by
      apply le_staircaseIndex
      · norm_num [Saxl.staircase_card]
        omega
      · norm_num [Saxl.staircase_card, he]
    omega
  · have h9 : 9 ≤ staircaseIndex n := by
      apply le_staircaseIndex
      · norm_num [Saxl.staircase_card]
        omega
      · norm_num [Saxl.staircase_card, ho]
    omega

end UniversalTensorSquare

namespace Saxl.Path

theorem odd_path_support (r : ℕ) (μ : YoungDiagram)
    (t : Tableau (2*r+1) μ) (hμ : μ.colLen 0 ≤ 4) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r+1) 4) (bandWord r)).toRepresentation, f ≠ 0 := by
  have hn : μ.transpose.rowLens.sum = 2*r+1 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr ((Columns.columnTableau μ).trans t.symm)
  obtain ⟨s, hs⟩ := fourRow_tableau_noncancellation (2*r+1) μ hn hμ
  let L : Fin (μ.colLen 0) → Fin 4 → ℂ := fun i a =>
    Band.conjugation (Band.basis i.val) (parts a).1 (parts a).2
  apply hom_to_cyclic_of_pair L (spechtSub t)
    ⟨polytabloid s, polytabloid_mem_all t s⟩ (bandWord r) (bandWord_real r)
  intro h
  rw [chainFunctional_endpoint] at hs
  exact hs (by change (-1 : ℂ)^r * dotProduct (wordMap L (polytabloid s)) (bandWord r) = 0
               rw [h, mul_zero])

end Saxl.Path
end
end

end OAI
