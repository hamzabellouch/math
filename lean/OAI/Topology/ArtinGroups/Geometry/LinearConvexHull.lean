import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin.Geometric
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma linear_le_on_convexHull (f : E →ₗ[ℝ] ℝ) (s : Set E) (b : ℝ)
    (h : ∀ x ∈ s, f x ≤ b) : ∀ x ∈ convexHull ℝ s, f x ≤ b := by
  apply convexHull_min (t := {x | f x ≤ b}) h
  intro x hx y hy a c ha hc hac
  change f x ≤ b at hx
  change f y ≤ b at hy
  change f (a • x + c • y) ≤ b
  rw [map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  calc
    a * f x + c * f y ≤ a*b+c*b := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hc)
    _ = b := by rw [←add_mul,hac,one_mul]

lemma convexHull_supporting_level (f : E →ₗ[ℝ] ℝ) (s : Set E) (b : ℝ)
    (h : ∀ x ∈ s, f x ≤ b) :
    {x | x ∈ convexHull ℝ s ∧ f x = b} = convexHull ℝ {x | x ∈ s ∧ f x = b} := by
  have H : ∀ x ∈ convexHull ℝ s, f x ≤ b ∧
      (f x = b → x ∈ convexHull ℝ {x | x ∈ s ∧ f x = b}) := by
    apply convexHull_min (t := {x | f x ≤ b ∧ (f x = b → x ∈ convexHull ℝ {x | x ∈ s ∧ f x = b})})
    · intro x hx
      exact ⟨h x hx,fun he => subset_convexHull ℝ _ ⟨hx,he⟩⟩
    · intro x hx y hy a c ha hc hac
      change f x ≤ b ∧ (f x = b → x ∈ convexHull ℝ {x | x ∈ s ∧ f x = b}) at hx
      change f y ≤ b ∧ (f y = b → y ∈ convexHull ℝ {x | x ∈ s ∧ f x = b}) at hy
      change f (a • x + c • y) ≤ b ∧ _
      have he : f (a • x + c • y) = a * f x + c * f y := by
        simp only [map_add,map_smul,smul_eq_mul]
      have h1 : a * f x ≤ a*b := mul_le_mul_of_nonneg_left hx.1 ha
      have h2 : c * f y ≤ c*b := mul_le_mul_of_nonneg_left hy.1 hc
      have hab : a*b+c*b = b := by rw [←add_mul,hac,one_mul]
      refine ⟨by rw [he]; linarith,?_⟩
      intro hh
      by_cases ha0 : a = 0
      · have hc1 : c = 1 := by linarith
        simpa only [ha0,hc1,zero_smul,one_smul,zero_add] using
          hy.2 (by simpa only [ha0,hc1,zero_smul,one_smul,zero_add] using hh)
      by_cases hc0 : c = 0
      · have ha1 : a = 1 := by linarith
        simpa only [ha1,hc0,zero_smul,one_smul,add_zero] using
          hx.2 (by simpa only [ha1,hc0,zero_smul,one_smul,add_zero] using hh)
      rw [he] at hh
      have hx' : f x = b := mul_left_cancel₀ ha0 (by linarith : a*f x = a*b)
      have hy' : f y = b := mul_left_cancel₀ hc0 (by linarith : c*f y = c*b)
      exact (convex_convexHull ℝ _ ) (hx.2 hx') (hy.2 hy') ha hc hac
  apply Set.Subset.antisymm
  · intro x hx; exact (H x hx.1).2 hx.2
  · apply convexHull_min
    · intro x hx; exact ⟨subset_convexHull ℝ _ hx.1,hx.2⟩
    · intro x hx y hy a c ha hc hac
      refine ⟨(convex_convexHull ℝ s) hx.1 hy.1 ha hc hac,?_⟩
      simp only [map_add,map_smul,smul_eq_mul,hx.2,hy.2]
      rw [← add_mul,hac,one_mul]

lemma finite_average_le {V : Type*} [Fintype V] [Nonempty V]
    (z : V → E) (f : E →ₗ[ℝ] ℝ) (b : ℝ) (h : ∀ v, f (z v) ≤ b) :
    f ((Fintype.card V : ℝ)⁻¹ • ∑ v,z v) ≤ b := by
  rw [map_smul,map_sum]
  simp only [smul_eq_mul]
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => h v)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  exact (inv_mul_le_iff₀ hn).mpr hs

lemma finite_average_eq_iff {V : Type*} [Fintype V] [Nonempty V]
    (z : V → E) (f : E →ₗ[ℝ] ℝ) (b : ℝ) (h : ∀ v, f (z v) ≤ b) :
    f ((Fintype.card V : ℝ)⁻¹ • ∑ v,z v) = b ↔ ∀ v,f (z v) = b := by
  rw [map_smul,map_sum]
  simp only [smul_eq_mul]
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  rw [←div_eq_inv_mul,div_eq_iff hn.ne']
  have hb : b * (Fintype.card V : ℝ) = ∑ v : V,b := by simp [mul_comm]
  rw [hb]
  exact (Finset.sum_eq_sum_iff_of_le (fun v _ => h v)).trans (by simp)

lemma finite_average_mem {V : Type*} [Fintype V] [Nonempty V] (z : V → E) :
    (Fintype.card V : ℝ)⁻¹ • ∑ v,z v ∈ convexHull ℝ (Set.range z) := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply mem_convexHull_of_exists_fintype (fun _ : V => (Fintype.card V : ℝ)⁻¹) z
  · intro v; positivity
  · simp [hn]
  · intro v; exact Set.mem_range_self v
  · rw [Finset.smul_sum]

end HarmonicArtin.Geometric

end OAI
