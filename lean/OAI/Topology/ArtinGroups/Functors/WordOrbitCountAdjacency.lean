import Mathlib
import OAI.Topology.ArtinGroups.Functors.LevelGeneratorEquiv
import OAI.Topology.ArtinGroups.Functors.SignedPacketPerm
import OAI.Topology.ArtinGroups.Harmonic.EigenvectorProportional
import OAI.Topology.ArtinGroups.Harmonic.SumNeighborsSubtype

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (hn : ∀ b, Q.source b ≠ Q.target b)
  (orient : B → Bool) (μ : J → K) (A : K)
  (ho : ∀ b, orient (Q.reverse b) = !(orient b))
  (hμ : ∀ a, μ a ≠ 0) (δ : K)
  (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
  (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "O" => (fun (w : List (V × Bool)) (s : V) (a : J) =>
  wordPacketPerm Q step hstep N hN hn w (initialClass U (K := K) (s,a)))

include ho hμ hA hroot hPF

lemma wordOrbit_count_adjacency (w : List (V × Bool)) (s v : V) (d : ℤ) (i j : J) :
    (∑ a : {a // N a j}, classLevelArray U (O w s i) ((v,a),d)) =
      ∑ a : {a // N i a}, classLevelArray U (O w s a) ((v,j),d) := by
  rw [← classLevelArray_label Q step hstep N hN orient μ A ho hμ δ hA hroot hPF]
  rw [classLabel_wordOrbit Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF,
    classLevelArray_sum]
  simp

variable [Nonempty J]
  (hconn : ∀ a b, Relation.ReflTransGen N a b)
  (ρ : J → ℝ) (hρ : ∀ a, 0 < ρ a) (θ : ℝ)
  (hρPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, ρ b = θ * ρ a)

include hconn hρ hρPF

theorem wordOrbit_count_proportional (w : List (V × Bool)) (s v : V) (d : ℤ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ j,
      (∑ i, ρ i * (classLevelArray U (O w s i) ((v,j),d) : ℝ)) = r * ρ j := by
  apply GraphConnection.nonnegative_eigenvector_proportional N hconn ρ hρ θ hρPF
  · exact GraphConnection.weighted_intertwiner N hN ρ θ hρPF _
      (wordOrbit_count_adjacency Q step hstep N hN hn orient μ A ho hμ δ hA hroot hPF w s v d)
  · intro j
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (le_of_lt (hρ i)) (Nat.cast_nonneg _)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
