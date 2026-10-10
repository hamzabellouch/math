import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.InverseParabolicMinimum
import OAI.Topology.ArtinGroups.Coxeter.RightParabolicDecomposition
import OAI.Topology.ArtinGroups.Geometry.RootCoeffAltExtension

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.propDecidable Classical.decEq
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

theorem root_nonneg_of_ascent (w : W) (s : S)
    (hs : cs.length (w*cs.simple s)=cs.length w+1) :
    ∀ k, 0 ≤ representation cs w (Pi.single s 1) k := by
  suffices H : ∀ n : ℕ, ∀ w : W, cs.length w=n → ∀ s : S,
      cs.length (w*cs.simple s)=cs.length w+1 →
      ∀ k, 0 ≤ representation cs w (Pi.single s 1) k from H _ w rfl s hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn s hs
    by_cases hw : w=1
    · subst w
      intro k
      simp only [map_one]
      change 0 ≤ (Pi.single s (1 : ℝ) : S → ℝ) k
      by_cases hks : k=s <;> simp [hks]
    · obtain ⟨j,hj⟩ := exists_right_descent cs hw
      have hsj : s≠j := by intro he; subst j; omega
      let J : Set S := {s,j}
      obtain ⟨v,a,ha,hv,he,hl⟩ := exists_right_parabolic_decomposition cs J w
      have hsJ : s ∈ J := by simp [J]
      have hjJ : j ∈ J := by simp [J]
      have haone : a≠1 := by
        intro h
        have hmin := hv (cs.simple j) (simple_mem_parabolic cs J hjJ)
        rw [h,mul_one] at he
        rw [← he] at hmin
        omega
      have halen : 0 < cs.length a := by
        exact Nat.pos_of_ne_zero (fun h => haone (cs.length_eq_zero_iff.mp h))
      have hvlt : cs.length v < n := by omega
      have hvas : cs.length (v*cs.simple s)=cs.length v+1 := by
        have hmin := hv (cs.simple s) (simple_mem_parabolic cs J hsJ)
        rcases cs.length_mul_simple v s with h | h <;> omega
      have hvaj : cs.length (v*cs.simple j)=cs.length v+1 := by
        have hmin := hv (cs.simple j) (simple_mem_parabolic cs J hjJ)
        rcases cs.length_mul_simple v j with h | h <;> omega
      have hposS := ih (cs.length v) hvlt v rfl s hvas
      have hposJ := ih (cs.length v) hvlt v rfl j hvaj
      have has : cs.length (a*cs.simple s)=cs.length a+1 := by
        have hmul := length_mul_of_right_minimum cs J v hv (a*cs.simple s)
          ((parabolic cs J).mul_mem ha (simple_mem_parabolic cs J hsJ))
        have hwprod : w*cs.simple s=v*(a*cs.simple s) := by rw [he,mul_assoc]
        rw [← hwprod] at hmul
        omega
      obtain ⟨x,y,hx,hy,hroot⟩ := pair_ascent_root_coeff cs s j hsj a ha has
      intro k
      rw [he,map_mul,LinearEquiv.mul_apply,hroot,map_add,map_smul,map_smul]
      exact add_nonneg (mul_nonneg hx (hposS k)) (mul_nonneg hy (hposJ k))

lemma geometric_root_ne_zero (w : W) (s : S) :
    representation cs w (Pi.single s 1) ≠ 0 := by
  intro h
  have hb : (Pi.single s (1 : ℝ) : S → ℝ) = 0 :=
    (representation cs w).map_eq_zero_iff.mp h
  have := congrFun hb s
  simp at this

theorem root_nonpos_of_descent (w : W) (s : S)
    (hs : cs.length (w*cs.simple s)+1=cs.length w) :
    ∀ k, representation cs w (Pi.single s 1) k ≤ 0 := by
  have has : cs.length ((w*cs.simple s)*cs.simple s)=cs.length (w*cs.simple s)+1 := by
    rw [cs.simple_mul_simple_cancel_right]
    omega
  have hpos := root_nonneg_of_ascent cs (w*cs.simple s) s has
  rw [map_mul] at hpos
  simp only [LinearEquiv.mul_apply,representation_simple,simpleReflection_basis_self,map_neg,
    Pi.neg_apply,neg_nonneg] at hpos
  exact hpos

theorem root_nonneg_iff_ascent (w : W) (s : S) :
    (∀ k, 0 ≤ representation cs w (Pi.single s 1) k) ↔
      cs.length (w*cs.simple s)=cs.length w+1 := by
  constructor
  · intro h
    rcases cs.length_mul_simple w s with hlen | hlen
    · exact hlen
    · have hn := root_nonpos_of_descent cs w s hlen
      have hz : representation cs w (Pi.single s 1)=0 :=
        funext (fun k => le_antisymm (hn k) (h k))
      exact (geometric_root_ne_zero cs w s hz).elim
  · exact root_nonneg_of_ascent cs w s

theorem representation_map_eq_one (w : W) (hw : representation cs w=1) : w=1 := by
  by_contra h
  obtain ⟨s,hs⟩ := exists_right_descent cs h
  have hn := root_nonpos_of_descent cs w s hs s
  rw [hw] at hn
  norm_num at hn

end HarmonicArtin.Geometric

end OAI
