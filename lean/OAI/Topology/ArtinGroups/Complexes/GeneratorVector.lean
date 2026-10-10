import Mathlib
import OAI.Topology.ArtinGroups.Complexes.EqualColorPair

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def generatorVector (E : BasedComplex Q (K := K) I) : V → ℝ :=
  fun α => Nat.card {i : I // (E.placement i).color = α}

noncomputable def unfoldedCartan : Matrix V V ℝ := fun α β =>
  (if α = β then 2 else 0) - Nat.card {a : A // Q.source a = α ∧ Q.target a = β}

omit [Fintype V] [DecidableEq A] in
lemma generatorVector_sum (E : BasedComplex Q (K := K) I) (α : V) :
    generatorVector Q E α = ∑ i, if (E.placement i).color = α then (1 : ℝ) else 0 := by
  classical
  simp only [generatorVector, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole]

omit [DecidableEq A] in
lemma sum_generatorVector (E : BasedComplex Q (K := K) I) (f : V → ℝ) :
    ∑ α, generatorVector Q E α * f α = ∑ i, f (E.placement i).color := by
  classical
  simp only [generatorVector_sum, Finset.sum_mul, ite_mul, _root_.one_mul, MulZeroClass.zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [Fintype V] [DecidableEq A] in
lemma equalColorPair_card (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :
    (Nat.card (EqualColorPair Q E F) : ℝ) =
      ∑ i, ∑ j, if (E.placement i).color = (F.placement j).color then (1 : ℝ) else 0 := by
  classical
  simp only [EqualColorPair, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole,
    Fintype.sum_prod_type]

omit [Fintype V] [DecidableEq A] in
lemma arrowPair_card (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :
    (Nat.card (ArrowPair Q E F) : ℝ) =
      ∑ i, ∑ j, (Nat.card {a : A // Q.source a = (E.placement i).color ∧
        Q.target a = (F.placement j).color} : ℝ) := by
  classical
  simp only [ArrowPair, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole,
    Fintype.sum_prod_type]

omit [DecidableEq A] in
lemma generator_cartan_pairing (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) :
    (generatorVector Q E) ⬝ᵥ ((unfoldedCartan Q).mulVec (generatorVector Q F)) =
      2 * (Nat.card (EqualColorPair Q E F) : ℝ) - Nat.card (ArrowPair Q E F) := by
  classical
  rw [dotProduct, sum_generatorVector]
  simp only [Matrix.mulVec, dotProduct]
  have hs (i : I) :
      ∑ α, unfoldedCartan Q (E.placement i).color α * generatorVector Q F α =
        ∑ j, unfoldedCartan Q (E.placement i).color (F.placement j).color := by
    simpa only [_root_.mul_comm] using
      sum_generatorVector Q F (fun α => unfoldedCartan Q (E.placement i).color α)
  simp_rw [hs, unfoldedCartan]
  rw [equalColorPair_card, arrowPair_card]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> norm_num

lemma pure_cartan_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) :
    (generatorVector Q E) ⬝ᵥ ((unfoldedCartan Q).mulVec (generatorVector Q F)) =
      (totalHomDimension Q E F (k-l) : ℝ) - totalHomDimension Q E F (k-l+1) +
        totalHomDimension Q F E (l-k) := by
  rw [generator_cartan_pairing]
  have hh := pure_generator_euler Q E F hE hF
  have hh' : (2 : ℝ) * Nat.card (EqualColorPair Q E F) + totalHomDimension Q E F (k-l+1) =
      Nat.card (ArrowPair Q E F) + totalHomDimension Q E F (k-l) +
        totalHomDimension Q F E (l-k) := by exact_mod_cast hh
  linarith

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
