import OAI.RingTheory.DirectFiniteness.PrescribedFields

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17

noncomputable section
open scoped BigOperators
open Module
namespace KaplanskyCounterexample.FiniteGeometry

def curve {F : Type u_1} [Field F] (m : ℕ) (ξ : F) : Fin m → F := fun j => ξ ^ j.val

lemma curve_relation {F : Type u_2} [Field F] {k m : ℕ}
    (hk : k ≤ m) {ξ : Fin k → F} (hξ : Function.Injective ξ) (a : Fin k → F)
    (h : ∑ i, a i • curve m (ξ i) = 0) : a = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hξ
  intro j
  have hj := congrFun h (Fin.castLE hk j)
  simpa [curve, Finset.sum_apply, Pi.smul_apply] using hj

lemma curve_linearIndependent {F : Type u_3} [Field F] {k m : ℕ}
    (hk : k ≤ m) {ξ : Fin k → F} (hξ : Function.Injective ξ) :
    LinearIndependent F (fun i => curve m (ξ i)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  exact congrFun (curve_relation hk hξ a ha)

/-- The one-dimensional extension-field line, viewed over the ground field. -/
def curveMap {Q : Type u_4} {F : Type u_5} [Field Q] [Field F] [Algebra Q F]
    (m : ℕ) (ξ : F) : F →ₗ[Q] (Fin m → F) where
  toFun a := a • curve m ξ
  map_add' a b := add_smul _ _ _
  map_smul' c a := by
    ext j
    simp [Pi.smul_apply, Algebra.smul_def, mul_assoc]

lemma curveMap_injective {Q : Type u_6} {F : Type u_7} [Field Q] [Field F] [Algebra Q F]
    {m : ℕ} (hm : 0 < m) (ξ : F) : Function.Injective (curveMap (Q := Q) m ξ) := by
  intro a b hab
  have := congrFun hab ⟨0, hm⟩
  simpa [curveMap, curve] using this

/-- Any at most m of the extension-field lines have direct sum over Q.
Each chosen Q-subspace can subsequently be taken inside its own line. -/
lemma curveMap_direct {Q : Type u_8} {F : Type u_9} [Field Q] [Field F] [Algebra Q F]
    {k m : ℕ} (hk : k ≤ m) {ξ : Fin k → F} (hξ : Function.Injective ξ)
    (x : Fin k → (Fin m → F))
    (hx : ∀ i, x i ∈ (curveMap (Q := Q) m (ξ i)).range)
    (hsum : ∑ i, x i = 0) : ∀ i, x i = 0 := by
  choose a ha using hx
  have hrel : ∑ i, a i • curve m (ξ i) = 0 := by simpa [← ha, curveMap] using hsum
  have hz := curve_relation hk hξ a hrel
  intro i
  rw [← ha i]
  simp [hz]

/-- Select any required ground-field dimension inside a curve line. -/
lemma exists_subspace_in_curve {Q : Type u_10} {F : Type u_11} [Field Q] [Field F] [Algebra Q F]
    [FiniteDimensional Q F] {m : ℕ} (hm : 0 < m) (ξ : F)
    (d : ℕ) (hd : d ≤ finrank Q F) :
    ∃ P : Submodule Q (Fin m → F), finrank Q P = d ∧
      P ≤ (curveMap (Q := Q) m ξ).range := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := Q) (M := F) hd
  let g := curveMap (Q := Q) m ξ
  have hg : Function.Injective g := curveMap_injective hm ξ
  refine ⟨Submodule.span Q (Set.range (g ∘ f)), ?_, ?_⟩
  · have hgf := hf.map' g (LinearMap.ker_eq_bot.mpr hg)
    simpa using finrank_span_eq_card hgf
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, rfl⟩

/-- Direct sum for distinct selections of at most m members of a family. -/
def ShortDirect {Q : Type u_12} {A : Type u_13} {ι : Type u_14} [Field Q] [AddCommGroup A] [Module Q A]
    (m : ℕ) (P : ι → Submodule Q A) : Prop :=
  ∀ (k : ℕ), k ≤ m → ∀ j : Fin k → ι, Function.Injective j →
    ∀ x : Fin k → A, (∀ i, x i ∈ P (j i)) → (∑ i, x i) = 0 → ∀ i, x i = 0

/-- The Vandermonde construction of all the required direction spaces. -/
theorem exists_shortDirect_subspaces {Q : Type u_15} {F : Type u_16} {ι : Type u_17} [Field Q] [Field F] [Algebra Q F]
    [FiniteDimensional Q F] [Fintype F] [Fintype ι]
    {m : ℕ} (hm : 0 < m) (d : ι → ℕ) (hd : ∀ i, d i ≤ finrank Q F)
    (hcard : Fintype.card ι ≤ Fintype.card F) :
    ∃ P : ι → Submodule Q (Fin m → F),
      (∀ i, finrank Q (P i) = d i) ∧ ShortDirect m P := by
  obtain ⟨ξ⟩ := (Function.Embedding.nonempty_iff_card_le).mpr hcard
  choose P hPdim hPle using fun i => exists_subspace_in_curve hm (ξ i) (d i) (hd i)
  refine ⟨P, hPdim, ?_⟩
  intro k hk j hj x hx hsum
  exact curveMap_direct hk (ξ.injective.comp hj) x (fun i => hPle _ (hx i)) hsum

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
