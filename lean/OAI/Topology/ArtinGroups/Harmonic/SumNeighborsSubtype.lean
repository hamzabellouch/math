import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Crossing

namespace OAI

namespace HarmonicArtin.GraphConnection
variable {J : Type*} [Fintype J]
  (N : J → J → Prop) [DecidableRel N]

lemma sum_neighbors_subtype {R : Type*} [AddCommMonoid R] (a : J) (f : J → R) :
    ∑ b ∈ neighbors N a, f b = ∑ b : {b // N a b}, f b :=
  Finset.sum_subtype (neighbors N a) (mem_neighbors N a) f

lemma sum_neighbors_subtype_left (hN : ∀ ⦃left right⦄, N left right → N right left)
    {R : Type*} [AddCommMonoid R] (a : J) (f : J → R) :
    ∑ b ∈ neighbors N a, f b = ∑ b : {b // N b a}, f b :=
  Finset.sum_subtype (neighbors N a)
    (fun b => (mem_neighbors N a b).trans ⟨fun h => hN h, fun h => hN h⟩) f

lemma weighted_intertwiner (hN : ∀ ⦃left right⦄, N left right → N right left)
    (ρ : J → ℝ) (θ : ℝ)
    (hρ : ∀ a, ∑ b ∈ neighbors N a, ρ b = θ * ρ a)
    (D : J → J → ℕ)
    (hD : ∀ i j, (∑ b : {b // N b j}, D i b) = ∑ a : {a // N i a}, D a j)
    (j : J) :
    ∑ b ∈ neighbors N j, (∑ i, ρ i * (D i b : ℝ)) =
      θ * (∑ i, ρ i * (D i j : ℝ)) := by
  have hd (i j : J) : ∑ b ∈ neighbors N j, (D i b : ℝ) =
      ∑ a ∈ neighbors N i, (D a j : ℝ) := by
    rw [sum_neighbors_subtype_left N hN,sum_neighbors_subtype N]
    exact_mod_cast hD i j
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,hd]
  simp_rw [Finset.mul_sum,neighbors,Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, (∑ i ∈ neighbors N a, ρ i) * (D a j : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      simp only [neighbors,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      have he : N i a ↔ N a i := ⟨fun h => hN h,fun h => hN h⟩
      simp only [he]
    _ = _ := by simp_rw [hρ]; apply Finset.sum_congr rfl; intros; ring

end HarmonicArtin.GraphConnection

end OAI
