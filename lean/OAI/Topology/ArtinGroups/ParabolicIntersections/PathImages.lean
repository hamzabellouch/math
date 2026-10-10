import Mathlib

namespace OAI

/-! Iterated images of the arrow coefficient maps. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A I : Type} [Fintype I] [DecidableEq I] (B : A → Matrix I I ℂ)

noncomputable def pathImages (n : ℕ) : Submodule ℂ (I → ℂ) :=
  Submodule.span ℂ {x | ∃ w : List A, w.length = n ∧
    ∃ y : I → ℂ, Matrix.vecMul y (w.map B).prod = x}

lemma mem_pathImages_zero (x : I → ℂ) : x ∈ pathImages B 0 := by
  apply Submodule.subset_span
  exact ⟨[], rfl, x, Matrix.vecMul_one x⟩

lemma pathImages_step {n : ℕ} {x : I → ℂ} (hx : x ∈ pathImages B n) (a : A) :
    Matrix.vecMul x (B a) ∈ pathImages B (n+1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, y, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨w ++ [a], by simp only [List.length_append, List.length_singleton, hw], y, ?_⟩
    simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      Matrix.vecMul_vecMul]
  | zero =>
    rw [Matrix.zero_vecMul]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.add_vecMul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Matrix.smul_vecMul]
    exact Submodule.smul_mem _ c hx

lemma pathImages_eq_bot (n : ℕ)
    (hz : ∀ w : List A, w.length = n → (w.map B).prod = 0) : pathImages B n = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨w, hw, y, rfl⟩
  rw [hz w hw, Matrix.vecMul_zero]
  exact Submodule.zero_mem _

/-- An arbitrary supported vector belongs to a subspace as soon as all
its occupied coordinate vectors do. -/
lemma supported_mem_of_single {P : Submodule ℂ (I → ℂ)} (x : I → ℂ)
    (h : ∀ i, x i ≠ 0 → Pi.single i (1 : ℂ) ∈ P) : x ∈ P := by
  have he : x = ∑ i : I, x i • Pi.single i (1 : ℂ) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp
  rw [he]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : x i = 0
  · rw [hi, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (h i hi)

/-- Iterating incoming spanning equations lands in the image of paths of
length `n`. The lower bound on the placement prevents leaving the range
where the spanning equations hold. -/
theorem incoming_spanning_pathImages (degree : I → ℤ) (lower : ℤ)
    (hspan : ∀ i, lower < degree i → ∃ y : A → (I → ℂ),
      (∀ a j, y a j ≠ 0 → degree j = degree i - 1) ∧
      (∃ t : Finset A, Pi.single i (1 : ℂ) = ∑ a ∈ t, Matrix.vecMul (y a) (B a))) :
    ∀ n : ℕ, ∀ i, lower + n ≤ degree i → Pi.single i (1 : ℂ) ∈ pathImages B n := by
  intro n
  induction n with
  | zero => exact fun i _ => mem_pathImages_zero B _
  | succ n ih =>
    intro i hi
    obtain ⟨y, hy, t, he⟩ := hspan i (by omega)
    rw [he]
    apply Submodule.sum_mem
    intro a _
    apply pathImages_step B
    apply supported_mem_of_single
    intro j hj
    apply ih
    have := hy a j hj
    omega

end HarmonicArtin.ParabolicIntersections

end OAI
