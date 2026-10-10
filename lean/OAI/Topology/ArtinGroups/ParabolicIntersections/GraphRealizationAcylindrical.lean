import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphRealizationAction
import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphRealizationHyperbolic

namespace OAI

/-! Acylindricity passes from graph vertices to their unit-interval realization. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
variable {G V : Type} [Group G] [MulAction G V]
variable (H : SimpleGraph V) (hA : PreservesAdj (G := G) H) (hH : H.Connected)

lemma vertex_displacement_le (g : G) (x : Space H hH) (v : V)
    (hv : dist x (vertex H hH v) ≤ 1) (r : ℕ) :
    let _ := action H hA hH
    dist x (g • x) ≤ r →
    (H.dist v (g • v) : ℝ) ≤ r+2 := by
  let _ := action H hA hH
  change dist x (g • x) ≤ (r : ℝ) → _
  intro hg
  have h₁ := dist_triangle (vertex H hH v) x (g • vertex H hH v)
  have h₂ := dist_triangle x (g • x) (g • vertex H hH v)
  rw [dist_comm (vertex H hH v) x] at h₁
  rw [(action_isometric H hA hH g).dist_eq] at h₂
  have he : dist (vertex H hH v) (g • vertex H hH v)=(H.dist v (g • v) : ℝ) := by
    change dist (vertex H hH v) (act H hA hH g (vertex H hH v))= _
    rw [act_vertex,dist_vertex]
  rw [he] at h₁
  linarith

theorem acylindricity_transfer (r R N : ℕ)
    (hcount : ∀ v w : V,R ≤ H.dist v w →
      {g : G | H.dist v (g • v) ≤ r+2 ∧ H.dist w (g • w) ≤ r+2}.Finite ∧
      {g : G | H.dist v (g • v) ≤ r+2 ∧ H.dist w (g • w) ≤ r+2}.ncard ≤ N)
    (x y : Space H hH) (hxy : (R : ℝ)+2 ≤ dist x y) :
    let _ := action H hA hH
    {g : G | dist x (g • x) ≤ r ∧ dist y (g • y) ≤ r}.Finite ∧
      {g : G | dist x (g • x) ≤ r ∧ dist y (g • y) ≤ r}.ncard ≤ N := by
  let _ := action H hA hH
  obtain ⟨v,hv⟩ := exists_near_vertex H hH x
  obtain ⟨w,hw⟩ := exists_near_vertex H hH y
  have hdist : R ≤ H.dist v w := by
    have h := (dist_change hv hw).1
    rw [dist_vertex] at h
    have h' : (R : ℝ) ≤ H.dist v w := by linarith
    exact_mod_cast h'
  obtain ⟨hfin,hcard⟩ := hcount v w hdist
  have hsub : {g : G | dist x (g • x) ≤ r ∧ dist y (g • y) ≤ r} ⊆
      {g : G | H.dist v (g • v) ≤ r+2 ∧ H.dist w (g • w) ≤ r+2} := by
    intro g hg
    constructor
    · have h := vertex_displacement_le H hA hH g x v hv r hg.1
      exact_mod_cast h
    · have h := vertex_displacement_le H hA hH g y w hw r hg.2
      exact_mod_cast h
  exact ⟨hfin.subset hsub,(Set.ncard_le_ncard hsub hfin).trans hcard⟩

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
