import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.ControlledMatrices
import OAI.Topology.CoarseAssembly.FiberEmbedding

namespace OAI

/-! # Controlled block matrices on the spatial vertex module

The bounded block-matrix construction is transported through the explicit
Hilbert-sum equivalence. Its vertex entries are the entries of the original
blocks, which allows propagation and local compactness to be checked there.
-/

noncomputable section

namespace CoarseAssembly

variable {I : Type*} {Q : I → Type*} {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

@[simp] theorem flattenOperator_apply
    (A : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2)
    (x : lp (fun _ : Sigma Q => H) 2) (i : I) (q : Q i) :
    flattenOperator A x ⟨i, q⟩ = A (unflattenVector x) i q := rfl

theorem flattenOperator_norm_le
    (A : lp (fun i => lp (fun _ : Q i => H) 2) 2 →L[ℂ]
      lp (fun i => lp (fun _ : Q i => H) 2) 2) : ‖flattenOperator A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  change ‖flattenEquiv (A ((flattenEquiv (Q := Q) (H := H)).symm x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    A.le_opNorm ((flattenEquiv (Q := Q) (H := H)).symm x)

variable [DecidableEq I] [∀ i, DecidableEq (Q i)]

omit [NormedSpace ℂ H] in
theorem rowVector_single_same (i : I) (q : Q i) (h : H) :
    rowVector (lp.single 2 ⟨i, q⟩ h) i = lp.single 2 q h := by
  apply lp.ext
  funext r
  change lp.single (E := fun _ : Sigma Q => H) 2 ⟨i, q⟩ h ⟨i, r⟩ =
    lp.single (E := fun _ : Q i => H) 2 q h r
  by_cases hr : r = q
  · subst r; simp
  · have hn : (⟨i, r⟩ : Sigma Q) ≠ ⟨i, q⟩ := by
      intro he
      cases he
      exact hr rfl
    simp [hr, hn]

omit [NormedSpace ℂ H] in
theorem rowVector_single_ne {i j : I} (hji : j ≠ i) (q : Q i) (h : H) :
    rowVector (lp.single 2 ⟨i, q⟩ h) j = 0 := by
  apply lp.ext
  funext r
  have hn : (⟨j, r⟩ : Sigma Q) ≠ ⟨i, q⟩ := fun he => hji (congrArg Sigma.fst he)
  change lp.single (E := fun _ : Sigma Q => H) 2 ⟨i, q⟩ h ⟨j, r⟩ = 0
  exact lp.single_apply_ne (E := fun _ : Sigma Q => H) 2 ⟨i, q⟩ h hn

section Matrix

variable (rows cols : I → Finset I) (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j)
variable (B : ∀ i j, lp (fun _ : Q j => H) 2 →L[ℂ] lp (fun _ : Q i => H) 2)
variable (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
variable (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
variable (hB : ∀ i j, j ∈ rows i → ‖B i j‖ ≤ C)

def spatialBlocks : lp (fun _ : Sigma Q => H) 2 →L[ℂ] lp (fun _ : Sigma Q => H) 2 :=
  flattenOperator (controlledMatrix rows cols hdual B N C hC hr hc hB)

omit [∀ i, DecidableEq (Q i)] in
theorem spatialBlocks_norm_le : ‖spatialBlocks rows cols hdual B N C hC hr hc hB‖ ≤
    (N : ℝ) * C :=
  (flattenOperator_norm_le _).trans (controlledMatrix_norm_le rows cols hdual B N C hC hr hc hB)

omit [∀ i, DecidableEq (Q i)] in
@[simp] theorem spatialBlocks_apply (x : lp (fun _ : Sigma Q => H) 2) (i : I) (q : Q i) :
    spatialBlocks rows cols hdual B N C hC hr hc hB x ⟨i, q⟩ =
      (∑ j ∈ rows i, B i j (rowVector x j)) q := rfl

theorem spatialBlocks_single (i j : I) (q : Q i) (r : Q j) (h : H) :
    spatialBlocks rows cols hdual B N C hC hr hc hB (lp.single 2 ⟨j, r⟩ h) ⟨i, q⟩ =
      if j ∈ rows i then B i j (lp.single 2 r h) q else 0 := by
  rw [spatialBlocks_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply]
  by_cases hj : j ∈ rows i
  · rw [ite_eq_left hj, Finset.sum_eq_single j]
    · rw [rowVector_single_same]
    · intro k hk hkj
      rw [rowVector_single_ne hkj, map_zero]
      rfl
    · exact fun hn => (hn hj).elim
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≠ j := fun h => hj (h ▸ hk)
    rw [rowVector_single_ne hkj, map_zero]
    rfl

end Matrix

end CoarseAssembly

end

end OAI
