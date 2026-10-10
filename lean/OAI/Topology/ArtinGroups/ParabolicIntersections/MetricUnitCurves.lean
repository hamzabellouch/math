import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.Linarith

namespace OAI

/-! Concatenation of unit-speed curves and realization of distance. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
variable {X : Type} [MetricSpace X]

def HasCurve (x y : X) (L : ℝ) : Prop :=
  ∃ f : ℝ → X,(∀ s t,dist (f s) (f t) ≤ |s-t|) ∧ f 0=x ∧ f L=y

lemma curve_const (x : X) : HasCurve x x 0 :=
  ⟨fun _ => x,fun _ _ => by simp,rfl,rfl⟩

lemma curve_subsegment (f : ℝ → X) (hf : ∀ s t,dist (f s) (f t) ≤ |s-t|)
    (a b : ℝ) : HasCurve (f a) (f b) |a-b| := by
  by_cases hab : a ≤ b
  · refine ⟨fun t => f (a+t),?_,by simp,?_⟩
    · intro s t
      simpa only [add_sub_add_left_eq_sub] using hf (a+s) (a+t)
    · apply congrArg f
      rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
  · refine ⟨fun t => f (a-t),?_,by simp,?_⟩
    · intro s t
      have he : (a-s)-(a-t)=t-s := by ring
      simpa only [he,abs_sub_comm t s] using hf (a-s) (a-t)
    · apply congrArg f
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hab))]
      ring

lemma curve_reverse {x y : X} {L : ℝ} (hc : HasCurve x y L) : HasCurve y x L := by
  obtain ⟨f,hf,hx,hy⟩ := hc
  refine ⟨fun t => f (L-t),?_,by simpa using hy,by simpa using hx⟩
  intro s t
  have he : (L-s)-(L-t)=t-s := by ring
  simpa only [he,abs_sub_comm t s] using hf (L-s) (L-t)

lemma curve_concat {x y z : X} {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hc : HasCurve x y L) (hd : HasCurve y z K) : HasCurve x z (L+K) := by
  obtain ⟨f,hf,hx,hy⟩ := hc
  obtain ⟨g,hg,hy',hz⟩ := hd
  let F (t : ℝ) := if t ≤ L then f t else g (t-L)
  have hbound (s t : ℝ) (hst : s ≤ t) : dist (F s) (F t) ≤ |s-t| := by
    by_cases hs : s ≤ L <;> by_cases ht : t ≤ L
    · simpa only [F,ite_eq_left hs,ite_eq_left ht] using hf s t
    · have hm : dist (f s) (g (t-L)) ≤ dist (f s) (f L)+dist (g 0) (g (t-L)) := by
        rw [hy,hy']
        exact dist_triangle (f s) y (g (t-L))
      have h₁ := hf s L
      have h₂ := hg 0 (t-L)
      rw [abs_of_nonpos (sub_nonpos.mpr hs)] at h₁
      rw [abs_of_nonpos (by linarith : 0-(t-L) ≤ 0)] at h₂
      simp only [F,ite_eq_left hs,ite_eq_right ht]
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      linarith
    · exact False.elim (hs (hst.trans ht))
    · have he : (s-L)-(t-L)=s-t := by ring
      simpa only [F,ite_eq_right hs,ite_eq_right ht,he] using hg (s-L) (t-L)
  refine ⟨F,?_,?_,?_⟩
  · intro s t
    rcases le_total s t with h|h
    · exact hbound s t h
    · simpa only [dist_comm,abs_sub_comm] using hbound t s h
  · simpa only [F,ite_eq_left hL] using hx
  · by_cases hK' : K=0
    · subst K
      have he : y=z := hy'.symm.trans hz
      simpa only [add_zero,F,ite_eq_left le_rfl,he] using hy
    · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK')
      have hLK : ¬L+K ≤ L := by linarith
      simpa only [F,ite_eq_right hLK,add_sub_cancel_left] using hz

/-- A unit-speed curve whose length is the endpoint distance is a geodesic. -/
lemma curve_realizes_distance {x y : X} (hc : HasCurve x y (dist x y)) :
    ∃ γ : Set.Icc (0 : ℝ) (dist x y) → X, Isometry γ ∧
      γ ⟨0,le_rfl,dist_nonneg⟩=x ∧ γ ⟨dist x y,dist_nonneg,le_rfl⟩=y := by
  obtain ⟨f,hf,hx,hy⟩ := hc
  refine ⟨fun t => f t,?_,hx,hy⟩
  apply isometry_iff_dist_eq.mpr
  intro a b
  change dist (f a) (f b)=|(a : ℝ)-b|
  apply le_antisymm (hf a b)
  have lower (a b : Set.Icc (0 : ℝ) (dist x y)) (hab : (a : ℝ) ≤ b) :
      |(a : ℝ)-b| ≤ dist (f a) (f b) := by
    have h₁ := hf 0 a
    have h₂ := hf b (dist x y)
    rw [hx,abs_of_nonpos (by linarith [a.property.1] : 0-(a : ℝ) ≤ 0)] at h₁
    rw [hy,abs_of_nonpos (sub_nonpos.mpr b.property.2)] at h₂
    have h₃ := dist_triangle x (f a) y
    have h₄ := dist_triangle (f a) (f b) y
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith
  rcases le_total (a : ℝ) b with h|h
  · exact lower a b h
  · simpa only [dist_comm,abs_sub_comm] using lower b a h

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
