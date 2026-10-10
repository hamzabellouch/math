import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Path
import OAI.Topology.ArtinGroups.Harmonic.LeftSector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor

variable {V B J K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃left right⦄, N left right → N right left)
  [Fintype J] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)

local notation "U" => Q.stringQuiver step hstep N hN

def pathMarked : Path V B → Bool
  | .inl _ => false
  | .inr (.inl e) => step e
  | .inr (.inr _) => false

abbrev PathLeft (p : Path V B) (b c : J) :=
  GraphConnection.LeftSector N (pathMarked step p) b c
abbrev PathRight (p : Path V B) (b c : J) :=
  GraphConnection.RightSector N (pathMarked step p) b c

def pathScalar (p : Path V B) (b c : J) : K :=
  match p with
  | .inl _ => 1
  | .inr (.inl e) => if orient e then μ c / μ b else 1
  | .inr (.inr _) => μ c / μ b

omit [Fintype J] [DecidableEq J] in
lemma pathScalar_ne_zero (hμ : ∀ a, μ a ≠ 0) (p : Path V B) (b c : J) :
    pathScalar orient μ p b c ≠ 0 := by
  rcases p with v|e|v
  · exact one_ne_zero
  · simp only [pathScalar]; split
    · exact div_ne_zero (hμ c) (hμ b)
    · exact one_ne_zero
  · exact div_ne_zero (hμ c) (hμ b)

def pathSwitch (p : Path V B) (b c : J) : Matrix (PathLeft step N p b c) (PathRight step N p b c) K :=
  GraphConnection.sectorSwitch N μ A b c (pathScalar orient μ p b c) (pathMarked step p)

def pathUnswitch (p : Path V B) (b c : J) : Matrix (PathRight step N p b c) (PathLeft step N p b c) K :=
  GraphConnection.sectorUnswitch N μ A b c (pathScalar orient μ p b c) (pathMarked step p)

include hN in
lemma pathSwitch_inverse (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : Path V B) (b c : J) :
    pathSwitch step N orient μ A p b c * pathUnswitch step N orient μ A p b c = 1 :=
  GraphConnection.sector_inverse N hN μ hμ δ A hA hroot hPF b c
    (pathScalar orient μ p b c) (pathScalar_ne_zero orient μ hμ p b c) (pathMarked step p)

include hN in
lemma pathUnswitch_inverse (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
    (p : Path V B) (b c : J) :
    pathUnswitch step N orient μ A p b c * pathSwitch step N orient μ A p b c = 1 := by
  classical
  exact (Matrix.mul_eq_one_comm_of_equiv (GraphConnection.sectorEquiv N hN (pathMarked step p) b c)).mp
    (pathSwitch_inverse step N hN orient μ A hμ δ hA hroot hPF p b c)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
