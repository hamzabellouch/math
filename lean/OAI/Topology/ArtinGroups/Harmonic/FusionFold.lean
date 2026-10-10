import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetVertex
import OAI.Topology.ArtinGroups.Harmonic.FusionLabel

namespace OAI

namespace HarmonicArtin
open Matrix
open scoped Matrix BigOperators

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ)

noncomputable def fusionFold (p : V → ℝ) : V × FusionLabel m → ℝ :=
  fun α => fusionWeight m α.2 * p α.1

noncomputable def fusionUnfoldedCartan (d : V → V → FusionEdge E) :
    Matrix (V × FusionLabel m) (V × FusionLabel m) ℝ :=
  Matrix.diagonal (fun _ => (2 : ℝ)) -
    Matrix.of (fun (α β : V × FusionLabel m) => ((d α.1 β.1).multiplicity m α.2 β.2 : ℝ))

noncomputable def fusionFoldedCartan (d : V → V → FusionEdge E) : Matrix V V ℝ :=
  Matrix.diagonal (fun _ => (2 : ℝ)) - Matrix.of (fun s t => (d s t).dimension m)

lemma fusion_intertwining (hm : ∀ e, 2 ≤ m e) (d : V → V → FusionEdge E) (p : V → ℝ) :
    fusionUnfoldedCartan m d *ᵥ fusionFold m p =
      fusionFold m (fusionFoldedCartan m d *ᵥ p) := by
  funext α
  simp only [fusionUnfoldedCartan, Matrix.sub_mulVec, Matrix.mulVec_diagonal,
    Pi.sub_apply, fusionFold, fusionFoldedCartan]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.of_apply, fusionFold]
  have hs (s : V) : (∑ L : FusionLabel m,
      ((d α.1 s).multiplicity m α.2 L : ℝ) * (fusionWeight m L * p s)) =
      (d α.1 s).dimension m * fusionWeight m α.2 * p s := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, FusionEdge.dimension_identity m hm]
  simp_rw [hs]
  simp only [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro s _
    ring

omit [Fintype V] in
lemma fusionUnfoldedCartan_symm (d : V → V → FusionEdge E)
    (hd : ∀ s t, d s t = d t s) (α β : V × FusionLabel m) :
    fusionUnfoldedCartan m d α β = fusionUnfoldedCartan m d β α := by
  classical
  simp only [fusionUnfoldedCartan, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply]
  rw [hd α.1 β.1, FusionEdge.multiplicity_symm]
  simp only [eq_comm]

omit [Fintype V] in
lemma fusionUnfoldedCartan_off (d : V → V → FusionEdge E)
    (α β : V × FusionLabel m) (h : α ≠ β) :
    fusionUnfoldedCartan m d α β ≤ 0 := by
  simp only [fusionUnfoldedCartan, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply, ite_eq_right h, zero_sub]
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

noncomputable def fusionD0 : ℝ := ∑ L : FusionLabel m, (fusionWeight m L)^2

lemma fusion_pairing (hm : ∀ e, 2 ≤ m e) (d : V → V → FusionEdge E) (p q : V → ℝ) :
    fusionFold m p ⬝ᵥ (fusionUnfoldedCartan m d *ᵥ fusionFold m q) =
      fusionD0 m * (p ⬝ᵥ (fusionFoldedCartan m d *ᵥ q)) := by
  rw [fusion_intertwining m hm]
  simp only [dotProduct, Fintype.sum_prod_type, fusionFold, fusionD0, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro L _
  ring

omit [Fintype V] [DecidableEq V] in
lemma fusionD0_pos (hm : ∀ e, 2 ≤ m e) : 0 < fusionD0 m := by
  let L : FusionLabel m := fun e => ⟨0, by have := hm e; omega⟩
  apply Finset.sum_pos'
  · intro L _; exact sq_nonneg _
  · exact ⟨L, Finset.mem_univ L, sq_pos_of_pos (fusionWeight_pos m hm L)⟩

lemma harmonic_posDef_of_strict_rows {ι : Type*} [Fintype ι]
    (C : Matrix ι ι ℝ) (hSym : ∀ i j, C i j = C j i)
    (hOff : ∀ i j, i ≠ j → C i j ≤ 0)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) (hCv : ∀ i, 0 < (C *ᵥ v) i) : C.PosDef := by
  classical
  have hHerm : C.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j; exact hSym j i
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  simp only [star_trivial]
  let w : ι → ℝ := fun i => x i / v i
  have hxw : x = v*w := by
    funext i
    exact (mul_div_cancel₀ (x i) (ne_of_gt (hv i))).symm
  have he : 0 ≤ (1/2 : ℝ) * ∑ i, ∑ j, (-C i j * v i * v j) * (w i-w j)^2 := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i=j
    · subst j; simp
    · exact mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr (hOff i j hij)) (hv i).le)
        (hv j).le) (sq_nonneg _)
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    apply hx
    funext i
    exact not_ne_iff.mp (fun hi => hn ⟨i,hi⟩)
  have hsum : 0 < ∑ i, v i*(C *ᵥ v) i*(w i)^2 := by
    apply Finset.sum_pos'
    · intro j _; exact mul_nonneg (mul_pos (hv j) (hCv j)).le (sq_nonneg _)
    · refine ⟨i, Finset.mem_univ i, mul_pos (mul_pos (hv i) (hCv i)) ?_⟩
      exact sq_pos_of_ne_zero (div_ne_zero hi (ne_of_gt (hv i)))
  rw [hxw, harmonic_scaled_form C hSym]
  linarith

lemma fusion_positive_definite (hm : ∀ e, 2 ≤ m e) (d : V → V → FusionEdge E)
    (hd : ∀ s t, d s t = d t s)
    (hOff : ∀ s t, s ≠ t → fusionFoldedCartan m d s t ≤ 0)
    (hC : (fusionFoldedCartan m d).PosDef) : (fusionUnfoldedCartan m d).PosDef := by
  let C := fusionFoldedCartan m d
  let v : V → ℝ := C⁻¹ *ᵥ (fun _ => 1)
  have hv : ∀ s, 0 < v s := by
    intro s
    change 0 < ∑ t, C⁻¹ s t * 1
    apply Finset.sum_pos'
    · intro t _; exact mul_nonneg (harmonic_inverse_nonneg C hC hOff s t) (by norm_num)
    · exact ⟨s, Finset.mem_univ s, mul_pos hC.inv.diag_pos (by norm_num)⟩
  apply harmonic_posDef_of_strict_rows (fusionUnfoldedCartan m d)
    (fusionUnfoldedCartan_symm m d hd) (fusionUnfoldedCartan_off m d)
    (fusionFold m v)
  · intro α; exact mul_pos (fusionWeight_pos m hm α.2) (hv α.1)
  · rw [fusion_intertwining m hm d, show C *ᵥ v = (fun _ => 1) from harmonic_solve C hC _]
    intro α
    simpa only [fusionFold, mul_one] using fusionWeight_pos m hm α.2

end HarmonicArtin

end OAI
