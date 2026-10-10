import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Crossing

namespace OAI

namespace HarmonicArtin.GraphConnection
variable {J : Type*} [Fintype J] [DecidableEq J]
  (N : J → J → Prop) [DecidableRel N]

omit [DecidableEq J] in
theorem eigenvector_proportional [Nonempty J]
    (hconn : ∀ a b, Relation.ReflTransGen N a b)
    (μ : J → ℝ) (hμ : ∀ a, 0 < μ a) (δ : ℝ)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a)
    (v : J → ℝ) (hv : ∀ a, ∑ b ∈ neighbors N a, v b = δ * v a) :
    ∃ r : ℝ, ∀ a, v a = r * μ a := by
  classical
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image Finset.univ (fun a => v a / μ a)
    Finset.univ_nonempty
  let r := v a / μ a
  let z (b : J) := r * μ b - v b
  have hz : ∀ b, 0 ≤ z b := by
    intro b
    have h := (div_le_iff₀ (hμ b)).mp (hmax b (Finset.mem_univ _))
    exact sub_nonneg.mpr h
  have hzPF (b : J) : ∑ c ∈ neighbors N b, z c = δ * z b := by
    simp only [z,Finset.sum_sub_distrib,← Finset.mul_sum,hPF,hv]
    ring
  have hza : z a = 0 := by
    dsimp only [z,r]
    rw [div_mul_cancel₀ _ (ne_of_gt (hμ a)),sub_self]
  have hstep {b c : J} (hb : z b=0) (hbc : N b c) : z c=0 := by
    have hs : ∑ d ∈ neighbors N b, z d=0 := by rw [hzPF,hb,mul_zero]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => hz d)).mp hs c
      ((mem_neighbors N b c).mpr hbc)
  have hzero (b : J) : z b=0 := by
    have hp := hconn a b
    induction hp with
    | refl => exact hza
    | tail hp hbc ih => exact hstep ih hbc
  refine ⟨r,fun b => ?_⟩
  exact (sub_eq_zero.mp (hzero b)).symm

omit [DecidableEq J] in
theorem nonnegative_eigenvector_proportional [Nonempty J]
    (hconn : ∀ a b, Relation.ReflTransGen N a b)
    (μ : J → ℝ) (hμ : ∀ a, 0 < μ a) (δ : ℝ)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a)
    (v : J → ℝ) (hv : ∀ a, ∑ b ∈ neighbors N a, v b = δ * v a)
    (hnonneg : ∀ a, 0 ≤ v a) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ a, v a = r * μ a := by
  obtain ⟨r,hr⟩ := eigenvector_proportional N hconn μ hμ δ hPF v hv
  refine ⟨r,?_,hr⟩
  let a : J := Classical.choice inferInstance
  exact nonneg_of_mul_nonneg_right (by rw [mul_comm,← hr]; exact hnonneg a) (hμ a)

end HarmonicArtin.GraphConnection

end OAI
