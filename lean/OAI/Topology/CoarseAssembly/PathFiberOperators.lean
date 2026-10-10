import OAI.Topology.CoarseAssembly.GraphFiberOperators
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace OAI

/-! # Composing the concrete fiber transports

Every base walk gives a contraction preserving normalized constants.
A nonzero matrix coefficient comes with an actual lifted walk of the same
length, which is the propagation estimate needed by the transfer criterion.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

section FiniteMatrices

variable {Q R T : Type*} [Fintype Q] [Fintype R] [Fintype T]
variable [DecidableEq Q] [DecidableEq R] [DecidableEq T]

theorem scalarFiber_expansion (x : lp (fun _ : Q => ℂ) 2) :
    x = ∑ q : Q, (x q) • lp.single 2 q (1 : ℂ) := by
  apply lp.ext
  funext r
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, smul_eq_mul]
  simp [Pi.single_apply, mul_ite]

omit [Fintype R] [DecidableEq R] in
theorem scalarFiber_apply_sum
    (A : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (x : lp (fun _ : Q => ℂ) 2) (r : R) :
    A x r = ∑ q : Q, x q * A (lp.single 2 q 1) r := by
  conv_lhs => rw [scalarFiber_expansion x]
  simp only [map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

omit [Fintype Q] [Fintype T] [DecidableEq T] in
theorem scalarFiber_comp_nonzero
    (A : lp (fun _ : Q => ℂ) 2 →L[ℂ] lp (fun _ : R => ℂ) 2)
    (B : lp (fun _ : R => ℂ) 2 →L[ℂ] lp (fun _ : T => ℂ) 2)
    (q : Q) (t : T) (h : (B.comp A) (lp.single 2 q 1) t ≠ 0) :
    ∃ r : R, A (lp.single 2 q 1) r ≠ 0 ∧ B (lp.single 2 r 1) t ≠ 0 := by
  classical
  by_contra! hn
  apply h
  rw [ContinuousLinearMap.comp_apply, scalarFiber_apply_sum]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : A (lp.single 2 q 1) r = 0
  · rw [hr, zero_mul]
  · rw [hn r hr, mul_zero]

end FiniteMatrices

/-- The concrete edge maps compose without any loss in the propagation
bound. This includes the length-zero identity case. -/
theorem exists_base_walk_operator (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} {u v : Disc j} (p : (discGraph j).Walk u v) :
    ∃ O : lp (fun _ : Quotient (discDepth j u) => ℂ) 2 →L[ℂ]
        lp (fun _ : Quotient (discDepth j v) => ℂ) 2,
      ‖O‖ ≤ 1 ∧ O (fiberConstant (Quotient (discDepth j u)) (1 : ℂ)) =
        fiberConstant (Quotient (discDepth j v)) 1 ∧
      ∀ q z, O (lp.single 2 q 1) z ≠ 0 →
        ∃ w : (fiberedGraph S t j).Walk ⟨u, q⟩ ⟨v, z⟩, w.length = p.length := by
  classical
  induction p with
  | @nil u =>
    refine ⟨ContinuousLinearMap.id ℂ _, ContinuousLinearMap.norm_id_le, rfl, ?_⟩
    intro q z hn
    have hz : z = q := by
      by_contra hne
      apply hn
      exact lp.single_apply_ne 2 q 1 hne
    subst z
    exact ⟨.nil, rfl⟩
  | @cons u v w huv p ih =>
    obtain ⟨A, hA, hAc, hAs⟩ := exists_base_edge_operator S t huv
    obtain ⟨B, hB, hBc, hBs⟩ := ih
    refine ⟨B.comp A, ?_, ?_, ?_⟩
    · exact (ContinuousLinearMap.opNorm_comp_le B A).trans
        ((mul_le_mul hB hA (norm_nonneg A) zero_le_one).trans_eq (one_mul 1))
    · rw [ContinuousLinearMap.comp_apply, hAc, hBc]
    · intro q z hn
      obtain ⟨r, hAr, hBr⟩ := scalarFiber_comp_nonzero A B q z hn
      have he : (fiberedGraph S t j).Adj ⟨u, q⟩ ⟨v, r⟩ := by
        by_contra he
        exact hAr (hAs q r he)
      obtain ⟨p', hp'⟩ := hBs r z hBr
      exact ⟨.cons he p', by simp only [SimpleGraph.Walk.length_cons, hp']⟩

/-- A shortest base walk provides the desired controlled contraction for
any prescribed finite graph-distance bound. -/
theorem exists_bounded_base_operator (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} {u v : Disc j} {R : ℕ} (hR : (discGraph j).edist u v ≤ R) :
    ∃ O : lp (fun _ : Quotient (discDepth j u) => ℂ) 2 →L[ℂ]
        lp (fun _ : Quotient (discDepth j v) => ℂ) 2,
      ‖O‖ ≤ 1 ∧ O (fiberConstant (Quotient (discDepth j u)) (1 : ℂ)) =
        fiberConstant (Quotient (discDepth j v)) 1 ∧
      ∀ q z, R < (fiberedGraph S t j).edist ⟨u, q⟩ ⟨v, z⟩ →
        O (lp.single 2 q 1) z = 0 := by
  obtain ⟨p, hp⟩ := (discGraph j).exists_walk_of_edist_ne_top
    (ne_of_lt (lt_of_le_of_lt hR (by simp)))
  obtain ⟨O, hO, hOc, hOs⟩ := exists_base_walk_operator S t p
  refine ⟨O, hO, hOc, ?_⟩
  intro q z hdist
  by_contra hn
  obtain ⟨w, hw⟩ := hOs q z hn
  have hle := w.edist_le
  rw [hw, hp] at hle
  exact (not_lt_of_ge (hle.trans hR)) hdist

end CoarseAssembly

end

end OAI
