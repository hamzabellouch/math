import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshNilpotence
import OAI.Topology.ArtinGroups.Complexes.ScalarKernel

namespace OAI

/-! The path-algebra relations satisfied by actual minimal differentials. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A)
  [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

noncomputable def arrowMatrix (E : BasedComplex Q (K := ℂ) I) (a : A) : Matrix I I ℂ :=
  fun i j => (E.differential i j).arrow a

omit [Fintype V] in
lemma differential_arrow_left_support (E : BasedComplex Q (K := ℂ) I) (i j : I) (a : A)
    (h : (E.placement i).color ≠ Q.source a) : (E.differential i j).arrow a = 0 := by
  have hh := congrArg (fun z : Q.Zigzag ℂ => z.arrow a) (E.entries.1 i j)
  simpa only [arrow_mul, Pi.add_apply, leftScale, rightScale, arrow_vertexId, Pi.zero_apply,
    MulZeroClass.zero_mul, add_zero, vertexId_eval, ite_eq_right h.symm,
    MulZeroClass.zero_mul] using hh.symm

omit [Fintype V] in
lemma arrowMatrix_noncomposable (E : BasedComplex Q (K := ℂ) I) (a b : A)
    (hab : Q.target a ≠ Q.source b) : arrowMatrix Q E a * arrowMatrix Q E b = 0 := by
  ext i j
  apply Finset.sum_eq_zero
  intro k _
  change (E.differential i k).arrow a * (E.differential k j).arrow b = 0
  by_cases hk : (E.placement k).color = Q.target a
  · rw [differential_arrow_left_support Q E k j b (by rwa [hk]), MulZeroClass.mul_zero]
  · rw [differential_arrow_right_support Q E i k a hk, MulZeroClass.zero_mul]

omit [Fintype V] in
lemma arrowMatrix_outside (E : BasedComplex Q (K := ℂ) I) (U : Set V)
    (hU : ∀ i, (E.placement i).color ∈ U) (a : A)
    (ha : Q.source a ∉ U ∨ Q.target a ∉ U) : arrowMatrix Q E a = 0 := by
  ext i j
  rcases ha with ha | ha
  · exact differential_arrow_left_support Q E i j a (fun he => ha (he ▸ hU i))
  · exact differential_arrow_right_support Q E i j a (fun he => ha (he ▸ hU j))

omit [Fintype V] in
/-- The mesh relation is precisely the token coefficient of `d²=0`;
minimality eliminates the other two terms in that coefficient. -/
lemma arrowMatrix_mesh (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q) (v : V) :
    (∑ a, if Q.source a = v then arrowMatrix Q E a * arrowMatrix Q E (Q.reverse a) else 0) = 0 := by
  ext i j
  have hs := congrArg (fun D : Matrix I I (Q.Zigzag ℂ) => (D i j).token v) E.square_zero
  have hv (i j : I) : (E.differential i j).vertex v = 0 := congrFun (hE i j) v
  simp only [Matrix.mul_apply, token_sum, Finset.sum_apply, token_mul, Pi.add_apply,
    Pi.mul_apply, hv, MulZeroClass.zero_mul, MulZeroClass.mul_zero, zero_add, backtrack,
    Matrix.zero_apply, token_zero, Pi.zero_apply] at hs
  have hentry (a : A) :
      (if Q.source a = v then arrowMatrix Q E a * arrowMatrix Q E (Q.reverse a) else 0) i j =
      if Q.source a = v then
        (∑ k, (E.differential i k).arrow a * (E.differential k j).arrow (Q.reverse a)) else 0 := by
    by_cases ha : Q.source a = v
    · simp only [ha, ite_true, Matrix.mul_apply, arrowMatrix]
    · simp only [ha, ite_false, Matrix.zero_apply]
  rw [Matrix.sum_apply]
  simp only [hentry, Matrix.zero_apply]
  calc
    _ = ∑ a, ∑ k, if Q.source a = v then
        (E.differential i k).arrow a * (E.differential k j).arrow (Q.reverse a) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp only [Finset.sum_const_zero]
    _ = ∑ k, ∑ a, if Q.source a = v then
        (E.differential i k).arrow a * (E.differential k j).arrow (Q.reverse a) else 0 :=
      Finset.sum_comm
    _ = 0 := hs

omit [Fintype V] in
/-- The published abstract mesh input applies to the coefficient maps of
any actual minimal complex supported in the given colors. -/
theorem coefficient_paths_nilpotent (U : Set V) (hmesh : MeshNilpotent Q U)
    (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q)
    (hU : ∀ i, (E.placement i).color ∈ U) :
    ∃ N : ℕ, 0 < N ∧ ∀ w : List A, w.length = N → (w.map (arrowMatrix Q E)).prod = 0 :=
  meshNilpotent_evaluate Q hmesh (arrowMatrix Q E)
    (arrowMatrix_outside Q E U hU) (arrowMatrix_noncomposable Q E)
    (fun v _ => arrowMatrix_mesh Q E hE v)

omit [Fintype V] in
/-- Truncating to a cochain interval gives a complex. No differential can
leave and re-enter the interval because it increases cochain degree by one. -/
lemma cochain_interval_restrict (E : BasedComplex Q (K := ℂ) I) (l r : ℤ) :
    ∀ i ∈ {i | l ≤ (E.placement i).cochain ∧ (E.placement i).cochain ≤ r},
    ∀ j ∈ {j | l ≤ (E.placement j).cochain ∧ (E.placement j).cochain ≤ r},
    ∀ k ∉ {k | l ≤ (E.placement k).cochain ∧ (E.placement k).cochain ≤ r},
      E.differential i k * E.differential k j = 0 := by
  intro i hi j hj k hk
  change l ≤ (E.placement i).cochain ∧ (E.placement i).cochain ≤ r at hi
  change l ≤ (E.placement j).cochain ∧ (E.placement j).cochain ≤ r at hj
  by_cases hik : E.differential i k = 0
  · rw [hik, Zigzag.zero_mul]
  by_cases hkj : E.differential k j = 0
  · rw [hkj, Zigzag.mul_zero]
  have hci : (E.placement k).cochain = (E.placement i).cochain + 1 := by
    by_contra hn
    exact hik ((E.degree i k).1 hn)
  have hcj : (E.placement j).cochain = (E.placement k).cochain + 1 := by
    by_contra hn
    exact hkj ((E.degree k j).1 hn)
  exact (hk ⟨by omega, by omega⟩).elim

noncomputable def cochainInterval (E : BasedComplex Q (K := ℂ) I) (l r : ℤ) :
    BasedComplex Q (K := ℂ) {i | l ≤ (E.placement i).cochain ∧ (E.placement i).cochain ≤ r} :=
  E.restrict Q _ (cochain_interval_restrict Q E l r)

omit [Fintype V] in
/-- Lemma 7.1 in its interval form. The fixed exponent works for every
minimal complex and every interval; coefficient maps may vary with placement. -/
theorem interval_coefficient_paths_nilpotent (U : Set V) (hmesh : MeshNilpotent Q U) :
    ∃ N : ℕ, 0 < N ∧ ∀ (I : Type) [Fintype I]
      (E : BasedComplex Q (K := ℂ) I), E.IsMinimal Q → ∀ l r : ℤ,
      (∀ i, l ≤ (E.placement i).cochain → (E.placement i).cochain ≤ r →
        (E.placement i).color ∈ U) →
      ∀ w : List A, w.length = N →
        (w.map (arrowMatrix Q (cochainInterval Q E l r))).prod = 0 := by
  obtain ⟨N, hN, hwords⟩ := hmesh
  refine ⟨N, hN, ?_⟩
  intro J _ E hE l r hU w hw
  let F := cochainInterval Q E l r
  have hF : F.IsMinimal Q := restrict_minimal Q E hE _ _
  have hf : ∀ i, (F.placement i).color ∈ U := fun i => hU i.val i.property.1 i.property.2
  exact mesh_word_evaluate Q (arrowMatrix Q F) (arrowMatrix_outside Q F U hf)
    (arrowMatrix_noncomposable Q F) (fun v _ => arrowMatrix_mesh Q F hF v) w (hwords w hw)

end HarmonicArtin.ParabolicIntersections

end OAI
