import Mathlib
import OAI.Topology.ArtinGroups.Quivers.SmulMul

namespace OAI

namespace HarmonicArtin.GraphConnection

variable {J K : Type*} [Fintype J] [DecidableEq J] [Field K]

def crossing (μ : J → K) (A : K) (a b c d : J) : K :=
  (if a = d then A * (μ c / μ a) else 0) + (if b = c then A⁻¹ else 0)

variable (N : J → J → Prop) [DecidableRel N]

def neighbors (a : J) : Finset J := Finset.univ.filter (N a)

omit [DecidableEq J] in
@[simp] lemma mem_neighbors (a b : J) : b ∈ neighbors N a ↔ N a b := by
  simp [neighbors]

theorem crossing_square (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2 + A⁻¹^2 + δ = 0)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a)
    (a a' b c : J) (hba : N b a) (hba' : N b a') (hca : N c a)
    (hca' : N c a') :
    (∑ d ∈ neighbors N b ∩ neighbors N c,
      crossing μ A a b c d * crossing μ A b a' d c) =
      if a = a' then μ c / μ a else 0 := by
  classical
  by_cases hbc : b = c
  · subst c
    rw [Finset.inter_self]
    have ha : a ∈ neighbors N b := (mem_neighbors _ _ _).2 hba
    have ha' : a' ∈ neighbors N b := (mem_neighbors _ _ _).2 hba'
    have hexp (d : J) : crossing μ A a b b d * crossing μ A b a' d b =
        (if a = d then A^2 else 0) +
        (if a = d ∧ a' = d then μ b / μ a else 0) +
        μ d / μ b + (if a' = d then A⁻¹^2 else 0) := by
      unfold crossing
      simp only [ite_true]
      by_cases ha : a = d <;> by_cases ha' : a' = d <;>
        simp only [ha, ha', ite_true, ite_false, and_self, true_and, false_and]
      all_goals subst_vars
      all_goals field_simp [hA, hμ]
      all_goals ring
    simp_rw [hexp, Finset.sum_add_distrib]
    have hs1 : (∑ d ∈ neighbors N b, if a = d then A^2 else 0) = A^2 := by
      simpa only [eq_comm] using Finset.sum_ite_eq' (neighbors N b) a (fun _ => A^2)
        |>.trans (ite_eq_left ha)
    have hs4 : (∑ d ∈ neighbors N b, if a' = d then A⁻¹^2 else 0) = A⁻¹^2 := by
      simpa only [eq_comm] using Finset.sum_ite_eq' (neighbors N b) a' (fun _ => A⁻¹^2)
        |>.trans (ite_eq_left ha')
    have hs2 : (∑ d ∈ neighbors N b, if a = d ∧ a' = d then μ b / μ a else 0) =
        if a = a' then μ b / μ a else 0 := by
      by_cases haa : a = a'
      · subst a'
        simp only [and_self, ite_true]
        simpa only [eq_comm] using Finset.sum_ite_eq' (neighbors N b) a (fun _ => μ b / μ a)
          |>.trans (ite_eq_left ha)
      · rw [ite_eq_right haa]
        apply Finset.sum_eq_zero
        intro d hd
        exact ite_eq_right (fun equalities => haa (equalities.1.trans equalities.2.symm))
    have hs3 : (∑ d ∈ neighbors N b, μ d / μ b) = δ := by
      rw [← Finset.sum_div, hPF, mul_div_cancel_right₀ _ (hμ b)]
    rw [hs1,hs2,hs3,hs4]
    linear_combination hroot
  · have ha : a ∈ neighbors N b ∩ neighbors N c := by simp [hba,hca]
    have hexp (d : J) : crossing μ A a b c d * crossing μ A b a' d c =
        if a = d ∧ a' = d then μ c / μ a else 0 := by
      unfold crossing
      simp only [hbc, ite_false, add_zero, zero_add]
      by_cases ha : a = d <;> by_cases ha' : a' = d <;>
        simp only [ha,ha',ite_true,ite_false,and_self,true_and,false_and]
      all_goals field_simp [hA, hμ]
      all_goals ring
    simp_rw [hexp]
    by_cases haa : a = a'
    · subst a'
      simp only [and_self,ite_true]
      simpa only [eq_comm] using Finset.sum_ite_eq' (neighbors N b ∩ neighbors N c) a
        (fun _ => μ c / μ a) |>.trans (ite_eq_left ha)
    · rw [ite_eq_right haa]
      apply Finset.sum_eq_zero
      intro d hd
      exact ite_eq_right (fun equalities => haa (equalities.1.trans equalities.2.symm))

lemma exists_crossing_parameter (δ : ℂ) :
    ∃ A : ℂ, A ≠ 0 ∧ A^2 + A⁻¹^2 + δ = 0 := by
  obtain ⟨D, hD⟩ := IsAlgClosed.exists_pow_nat_eq (δ^2-4) (by decide : 0 < 2)
  let z := (-δ+D)/2
  have hz : z^2+δ*z+1=0 := by
    dsimp [z]
    linear_combination (1/4 : ℂ) * hD
  have hn : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  obtain ⟨A, hA⟩ := IsAlgClosed.exists_pow_nat_eq z (by decide : 0 < 2)
  have hAn : A ≠ 0 := by intro h; apply hn; rw [← hA,h]; norm_num
  refine ⟨A,hAn,?_⟩
  have hpoly : A^4+δ*A^2+1=0 := by
    rw [show A^4=(A^2)^2 by ring, hA]
    exact hz
  apply (mul_right_cancel₀ (pow_ne_zero 2 hAn))
  field_simp [hAn]
  linear_combination hpoly

def cupCap (μ : J → K) (a : J) :
    Matrix {b // N a b} {b // N a b} K := fun _ column => μ column / μ a

omit [DecidableEq J] in
lemma cupCap_square {vertex : J} (μ : J → K) (hμ : μ vertex ≠ 0) (δ : K)
    (hPF : ∑ b ∈ neighbors N vertex, μ b = δ * μ vertex) :
    cupCap N μ vertex * cupCap N μ vertex = δ • cupCap N μ vertex := by
  classical
  have hs : (∑ b : {b // N vertex b}, μ b) = δ * μ vertex := by
    rw [← hPF]
    exact (Finset.sum_subtype (neighbors N vertex) (fun neighbor =>
      mem_neighbors N vertex neighbor)
      (fun b => μ b)).symm
  ext b c
  simp only [cupCap, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [div_mul_div_comm]
  rw [← Finset.sum_div, ← Finset.sum_mul, hs]
  field_simp [hμ]

lemma crossing_matrix_inverse {vertex : J} (μ : J → K) (hμ : μ vertex ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∑ b ∈ neighbors N vertex, μ b = δ * μ vertex) :
    (A⁻¹ • (1 : Matrix {b // N vertex b} {b // N vertex b} K) + A • cupCap N μ vertex) *
      (A • 1 + A⁻¹ • cupCap N μ vertex) = 1 ∧
    (A • (1 : Matrix {b // N vertex b} {b // N vertex b} K) + A⁻¹ • cupCap N μ vertex) *
      (A⁻¹ • 1 + A • cupCap N μ vertex) = 1 := by
  have hCC := cupCap_square N μ hμ δ hPF
  constructor <;>
    simp only [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,
      smul_smul,hCC,inv_mul_cancel₀ hA,mul_inv_cancel₀ hA,one_smul]
  all_goals
    simp only [← mul_assoc,inv_mul_cancel₀ hA,mul_inv_cancel₀ hA,one_mul]
    match_scalars <;> first | (solve | ring) | linear_combination hroot

end HarmonicArtin.GraphConnection

end OAI
