import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphRealizationSpace
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeShortcutHyperbolic

namespace OAI

/-! Hyperbolicity passes from graph vertices to the unit-interval realization. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
variable {V : Type} (H : SimpleGraph V) (hH : H.Connected)

noncomputable def product (o x y : Space H hH) : ℝ := (dist o x+dist o y-dist x y)/2

lemma dist_change {X : Type} [MetricSpace X] {x y x' y' : X}
    (hx : dist x x' ≤ 1) (hy : dist y y' ≤ 1) :
    dist x y ≤ dist x' y'+2 ∧ dist x' y' ≤ dist x y+2 := by
  have h₁ := dist_triangle x x' y
  have h₂ := dist_triangle x' y' y
  have h₃ := dist_triangle x' x y'
  have h₄ := dist_triangle x y y'
  rw [dist_comm y' y] at h₂
  rw [dist_comm x' x] at h₃
  constructor <;> linarith

lemma product_close {o x y : Space H hH} {a b c : V}
    (ho : dist o (vertex H hH a) ≤ 1) (hx : dist x (vertex H hH b) ≤ 1)
    (hy : dist y (vertex H hH c) ≤ 1) :
    product H hH o x y ≤ graphProduct H a b c+3 ∧
      graphProduct H a b c ≤ product H hH o x y+3 := by
  have h₁ := dist_change ho hx
  have h₂ := dist_change ho hy
  have h₃ := dist_change hx hy
  rw [dist_vertex] at h₁ h₂ h₃
  unfold product graphProduct
  constructor <;> linarith

theorem realization_hyperbolic (δ : ℝ)
    (hδ : ∀ o x y z,min (graphProduct H o x y) (graphProduct H o y z) ≤ graphProduct H o x z+δ)
    (o x y z : Space H hH) :
    min (product H hH o x y) (product H hH o y z) ≤ product H hH o x z+(δ+6) := by
  obtain ⟨a,ha⟩ := exists_near_vertex H hH o
  obtain ⟨b,hb⟩ := exists_near_vertex H hH x
  obtain ⟨c,hc⟩ := exists_near_vertex H hH y
  obtain ⟨d,hd⟩ := exists_near_vertex H hH z
  have h₁ := product_close H hH ha hb hc
  have h₂ := product_close H hH ha hc hd
  have h₃ := product_close H hH ha hb hd
  have hm := min_le_min h₁.1 h₂.1
  rw [min_add_add_right] at hm
  have hh := hδ a b c d
  linarith

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
