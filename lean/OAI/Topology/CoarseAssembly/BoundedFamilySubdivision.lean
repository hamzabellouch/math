import OAI.Topology.CoarseAssembly.BoundedFamilyHomotopy
import OAI.Topology.CoarseAssembly.HomotopySubdivision
import OAI.Topology.CoarseAssembly.ControlledBoundaryNearby

namespace OAI

/-! # Component-dependent subdivisions with uniformly close sampled Roe operators -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

namespace BoundedFamilyHomotopy

def samplingTolerance (h : BoundedFamilyHomotopy Q r) (i : ℕ) : ℝ :=
  1 / (8 * (1 + (4 * h.bound + 2) * Fintype.card (Q i)))

omit [∀ i, DecidableEq (Q i)] in
theorem samplingTolerance_pos (h : BoundedFamilyHomotopy Q r) (i : ℕ) :
    0 < h.samplingTolerance i := by
  have hb : 0 ≤ h.bound := zero_le_one.trans h.one_le_bound
  unfold samplingTolerance
  positivity

omit [∀ i, DecidableEq (Q i)] in
theorem samplingTolerance_estimate (h : BoundedFamilyHomotopy Q r) (i : ℕ) :
    h.samplingTolerance i + (4 * h.bound + 2) *
      ((Fintype.card (Q i) : ℝ) * h.samplingTolerance i) = 1 / 8 := by
  have hb : 0 ≤ h.bound := zero_le_one.trans h.one_le_bound
  have hd : 0 < 1 + (4 * h.bound + 2) * (Fintype.card (Q i) : ℝ) := by positivity
  unfold samplingTolerance
  field_simp

omit [∀ i, DecidableEq (Q i)] in
theorem exists_small_subdivision (h : BoundedFamilyHomotopy Q r) :
    ∃ (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval),
      (∀ i, τ i 0 = start) ∧ (∀ i, τ i (N i + 1) = finish) ∧
      ∀ i j, j < N i + 1 →
        ‖(h.homotopy i).operator (τ i (j + 1)) - (h.homotopy i).operator (τ i j)‖ ≤
          h.samplingTolerance i ∧
        ∀ x, ‖(h.homotopy i).representation (τ i (j + 1)) (sqrtCoordinate r x) -
          (h.homotopy i).representation (τ i j) (sqrtCoordinate r x)‖ ≤ h.samplingTolerance i := by
  choose K hK hstep using fun i => exists_rips_homotopy_subdivision r (h.homotopy i)
    (h.samplingTolerance i) (h.samplingTolerance_pos i)
  refine ⟨(fun i => K i - 1), (fun i => intervalGrid (K i) (hK i)), ?_, ?_, ?_⟩
  · intro i
    exact intervalGrid_start _ _
  · intro i
    have hk := hK i
    have hi : K i - 1 + 1 = K i := by omega
    dsimp only
    rw [hi]
    exact intervalGrid_finish _ _
  · intro i j hj
    apply hstep i j
    dsimp only at hj
    have hk := hK i
    omega

structure SmallSubdivision (h : BoundedFamilyHomotopy Q r) where
  count : ℕ → ℕ
  time : ℕ → ℕ → Interval
  at_start : ∀ i, time i 0 = start
  at_finish : ∀ i, time i (count i + 1) = finish
  step : ∀ i j, j < count i + 1 →
    ‖(h.homotopy i).operator (time i (j + 1)) - (h.homotopy i).operator (time i j)‖ ≤
      h.samplingTolerance i ∧
    ∀ x, ‖(h.homotopy i).representation (time i (j + 1)) (sqrtCoordinate r x) -
      (h.homotopy i).representation (time i j) (sqrtCoordinate r x)‖ ≤ h.samplingTolerance i

def smallSubdivision (h : BoundedFamilyHomotopy Q r) : SmallSubdivision h := by
  let N := Classical.choose h.exists_small_subdivision
  have hN := Classical.choose_spec h.exists_small_subdivision
  let τ := Classical.choose hN
  have ht := Classical.choose_spec hN
  exact ⟨N, τ, ht.1, ht.2.1, ht.2.2⟩

theorem sampled_boundary_eq (h : BoundedFamilyHomotopy Q r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (o : ∀ i, Q i) (hr : 0 ≤ r) (N : ℕ → ℕ) (τ : ℕ → ℕ → Interval)
    (hstep : ∀ i j, j < N i + 1 →
      ‖(h.homotopy i).operator (τ i (j + 1)) - (h.homotopy i).operator (τ i j)‖ ≤
        h.samplingTolerance i ∧
      ∀ x, ‖(h.homotopy i).representation (τ i (j + 1)) (sqrtCoordinate r x) -
        (h.homotopy i).representation (τ i j) (sqrtCoordinate r x)‖ ≤ h.samplingTolerance i) :
    (h.sample χ (fun i => N i + 1) τ).boundary o hr =
      (h.sample χ (fun i => N i + 1) (fun i j => τ i (j + 1))).boundary o hr := by
  apply ControlledCycleFamily.boundary_eq_of_ample_nearby _ _ o hr (1 / 8)
    (by norm_num) (by norm_num)
  intro i
  exact (sampledFiniteSum_ample_sub_norm_le r (h.homotopy i) (χ i) (N i + 1)
    (fun j => τ i (j + 1)) (τ i) h.bound h.one_le_bound (fun t => h.norm_le t i)
    (fun t => h.unital t i) (h.samplingTolerance i) (h.samplingTolerance_pos i).le
    (fun j hj => (hstep i j hj).1) (fun x j hj => (hstep i j hj).2 x)).trans
    (h.samplingTolerance_estimate i).le

end BoundedFamilyHomotopy

end CoarseAssembly.Rips

end

end OAI
