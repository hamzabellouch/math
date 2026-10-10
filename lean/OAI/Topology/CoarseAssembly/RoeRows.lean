import OAI.Topology.CoarseAssembly.RoeCalculus

namespace OAI

/-! # Reconstruction from finite operator rows

Finite propagation and finite metric balls make every row finite. The
finite-row formula extends to arbitrary Hilbert-sum vectors by density of
the single-coordinate subspaces.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem operator_ext_entries {T S : Operator X H}
    (h : ∀ x y, entry T x y = entry S x y) : T = S := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro y
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext x
  exact DFunLike.congr_fun (h x y) v

theorem entry_norm_le (T : Operator X H) (x y : X) : ‖entry T x y‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro h
  have hsingle : ‖(lp.single 2 y h : Module X H)‖ = ‖h‖ :=
    lp.norm_single (E := fun _ : X => H) (by norm_num : (0 : ENNReal) < 2) y h
  have hop := T.le_opNorm (lp.single 2 y h : Module X H)
  rw [hsingle] at hop
  exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (T (lp.single 2 y h)) x).trans hop

theorem finite_row_apply (T : Operator X H) (x : X) (s : Finset X)
    (hs : ∀ y, y ∉ s → entry T x y = 0) (v : Module X H) :
    T v x = ∑ y ∈ s, entry T x y (v y) := by
  have heq : (coordinate x).comp T =
      ∑ y ∈ s, (entry T x y).comp (coordinate y) := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
    intro y
    apply ContinuousLinearMap.ext
    intro z
    change entry T x y z = _
    simp only [ContinuousLinearMap.comp_apply, sum_apply,
      coordinate_apply, lp.singleContinuousLinearMap_apply]
    by_cases hy : y ∈ s
    · rw [Finset.sum_eq_single y]
      · simp
      · intro b hb hby
        simp [Ne.symm hby]
      · exact fun h => (h hy).elim
    · rw [hs y hy]
      simp only [zero_apply]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have hby : b ≠ y := fun h => hy (h ▸ hb)
      simp [hby]
  simpa only [ContinuousLinearMap.comp_apply, sum_apply, coordinate_apply] using
    DFunLike.congr_fun heq v

end CoarseAssembly.DiscreteRoe

end

end OAI
