import OAI.Topology.CoarseAssembly.SpatialBlocks
import OAI.Topology.CoarseAssembly.RoeRows

namespace OAI

/-! # The controlled lift and its exact compression

The lift is constructed as a bounded block matrix. Its scalar coefficient
condition proves local compactness, while preservation of constant-fiber
vectors proves the compression identity. These are explicit construction
conditions, not published hypotheses for the main result.
-/

noncomputable section

namespace CoarseAssembly

open DiscreteRoe

variable {I : Type*} {Q : I → Type*} {H : Type*}
variable [DecidableEq I] [∀ i, DecidableEq (Q i)]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fiberBlockEntry {i j : I}
    (B : lp (fun _ : Q j => H) 2 →L[ℂ] lp (fun _ : Q i => H) 2)
    (q : Q i) (r : Q j) : H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : Q i => H) 2 q).comp
    (B.comp (lp.singleContinuousLinearMap ℂ (fun _ : Q j => H) 2 r))

variable (rows cols : I → Finset I) (hdual : ∀ i j, j ∈ rows i ↔ i ∈ cols j)
variable (B : ∀ i j, lp (fun _ : Q j => H) 2 →L[ℂ] lp (fun _ : Q i => H) 2)
variable (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
variable (hr : ∀ i, (rows i).card ≤ N) (hc : ∀ i, (cols i).card ≤ N)
variable (hB : ∀ i j, j ∈ rows i → ‖B i j‖ ≤ C)

local notation "Aₗ" => spatialBlocks rows cols hdual B N C hC hr hc hB

omit [CompleteSpace H] in
theorem spatialBlocks_entry (i j : I) (q : Q i) (r : Q j) :
    entry Aₗ ⟨i, q⟩ ⟨j, r⟩ = if j ∈ rows i then fiberBlockEntry (B i j) q r else 0 := by
  apply ContinuousLinearMap.ext
  intro h
  rw [entry_apply]
  rw [spatialBlocks_single]
  split_ifs <;> rfl

section Metric

variable [PseudoMetricSpace I] [PseudoMetricSpace (Sigma Q)]

theorem spatialBlocks_generator (T : Operator I H) (hT : Generator T)
    (s : ℝ) (hs : 0 ≤ s)
    (hprop : ∀ i j, j ∈ rows i → ∀ q r, s < dist (⟨i, q⟩ : Sigma Q) ⟨j, r⟩ →
      fiberBlockEntry (B i j) q r = 0)
    (hscalar : ∀ i j, j ∈ rows i → ∀ q r, ∃ c : ℂ,
      fiberBlockEntry (B i j) q r = c • entry T i j) : Generator Aₗ := by
  refine ⟨⟨s, hs, ?_⟩, ?_, ?_⟩
  · intro x y hxy
    rcases x with ⟨i, q⟩
    rcases y with ⟨j, r⟩
    rw [spatialBlocks_entry]
    split_ifs with hij
    · exact hprop i j hij q r hxy
    · rfl
  · intro x y
    rcases x with ⟨i, q⟩
    rcases y with ⟨j, r⟩
    rw [spatialBlocks_entry]
    split_ifs with hij
    · obtain ⟨c, hcoeff⟩ := hscalar i j hij q r
      rw [hcoeff]
      exact (hT.2.1 i j).smul c
    · exact isCompactOperator_zero
  · intro x y
    rcases x with ⟨i, q⟩
    rcases y with ⟨j, r⟩
    rw [entry_star, spatialBlocks_entry]
    split_ifs with hji
    · obtain ⟨c, hcoeff⟩ := hscalar j i hji r q
      rw [hcoeff, star_smul]
      have hcompact := hT.2.2 i j
      rw [entry_star] at hcompact
      exact hcompact.smul (star c)
    · rw [star_zero]
      exact isCompactOperator_zero

end Metric

section Constants

variable [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)]

omit [∀ i, DecidableEq (Q i)] [CompleteSpace H] in
theorem spatialBlocks_intertwines (T : Operator I H)
    (houtside : ∀ i j, j ∉ rows i → entry T i j = 0)
    (hconstant : ∀ i j, j ∈ rows i → ∀ h : H,
      B i j (fiberConstant (Q j) h) = fiberConstant (Q i) (entry T i j h)) :
    (Aₗ).comp (fiberEmbedding Q).toContinuousLinearMap =
      (fiberEmbedding Q).toContinuousLinearMap.comp T := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext y
  rcases y with ⟨i, q⟩
  change Aₗ (fiberEmbedding Q x) ⟨i, q⟩ = fiberEmbedding Q (T x) ⟨i, q⟩
  rw [spatialBlocks_apply]
  have heq : (∑ j ∈ rows i, B i j (rowVector (fiberEmbedding Q x) j)) =
      fiberConstant (Q i) (∑ j ∈ rows i, entry T i j (x j)) := by
    calc
      _ = ∑ j ∈ rows i, fiberConstant (Q i) (entry T i j (x j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hconstant i j hj (x j)
      _ = _ := (map_sum (fiberConstantIsometry (Q i)).toLinearMap _ _).symm
  rw [heq, ← finite_row_apply T i (rows i) (houtside i) x]
  rfl

omit [∀ i, DecidableEq (Q i)] in
theorem spatialBlocks_compression (T : Operator I H)
    (houtside : ∀ i j, j ∉ rows i → entry T i j = 0)
    (hconstant : ∀ i j, j ∈ rows i → ∀ h : H,
      B i j (fiberConstant (Q j) h) = fiberConstant (Q i) (entry T i j h)) :
    fiberProjection Q * Aₗ * fiberProjection Q = operatorConjugation (fiberEmbedding Q) T := by
  have heq := spatialBlocks_intertwines rows cols hdual B N C hC hr hc hB T houtside hconstant
  apply ContinuousLinearMap.ext
  intro x
  have hx := DFunLike.congr_fun heq ((fiberEmbedding Q).toContinuousLinearMap.adjoint x)
  change Aₗ (fiberEmbedding Q ((fiberEmbedding Q).toContinuousLinearMap.adjoint x)) =
    fiberEmbedding Q (T ((fiberEmbedding Q).toContinuousLinearMap.adjoint x)) at hx
  change fiberEmbedding Q ((fiberEmbedding Q).toContinuousLinearMap.adjoint
      (Aₗ (fiberEmbedding Q ((fiberEmbedding Q).toContinuousLinearMap.adjoint x)))) = _
  rw [hx, adjoint_apply_isometry]
  rfl

end Constants

end CoarseAssembly

end

end OAI
