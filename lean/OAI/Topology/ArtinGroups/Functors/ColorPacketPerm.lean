import Mathlib
import OAI.Topology.ArtinGroups.Complexes.BasedComplexComplex
import OAI.Topology.ArtinGroups.Functors.PacketTwistComparison

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

omit [Fintype V] [Fintype B] [Fintype J] [DecidableEq V] [DecidableEq B]
  [DecidableEq J] [DecidableRel N] in
lemma string_loopless (hn : ∀ b, Q.source b ≠ Q.target b) :
    ∀ a, (U).source a ≠ (U).target a := by
  intro a ha
  exact hn a.base (congrArg Prod.fst ha)

omit [Fintype V] [Fintype B] [Fintype J] [DecidableEq V] [DecidableEq B]
  [DecidableEq J] [DecidableRel N] in
lemma color_orthogonal (hn : ∀ b, Q.source b ≠ Q.target b) (v:V) :
    Pairwise (fun a b : J => Zigzag.OrthogonalVertices U (v,a) (v,b)) := by
  intro a b hab
  refine ⟨fun he => hab (congrArg Prod.snd he),fun p hp hq => ?_⟩
  exact hn p.base ((congrArg Prod.fst hp).trans (congrArg Prod.fst hq).symm)

noncomputable def colorPacketPerm (hn : ∀ b, Q.source b ≠ Q.target b) (v:V) :
    Equiv.Perm (FiniteHomotopyClass U (K := K)) :=
  classPacketPerm U (string_loopless Q step hstep N hN hn) (fun a:J => (v,a))
    (color_orthogonal Q step hstep N hN hn v)

lemma colorPacketPerm_apply (hn : ∀ b, Q.source b ≠ Q.target b) (v:V)
    (E : FiniteModel U (K := K)) :
    colorPacketPerm Q step hstep N hN (K := K) hn v
      (Quotient.mk (finiteHomotopySetoid U) E) =
      classOfComplex U (E.complex.packetTwist U (fun a:J => (v,a))) :=
  classPacketPerm_apply U _ _ _ E

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

noncomputable def classLabelFunctor : FiniteHomotopyClass U (K := K) → FiniteHomotopyClass U (K := K) :=
  Quotient.map (fun E => FiniteModel.ofComplex U (C E.complex)) (by
    intro E F ⟨e⟩
    exact ⟨homotopyEquivalence Q step hstep N hN orient μ A ho hμ δ hA hroot hPF e⟩)

local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

lemma classLabel_packet (hn : ∀ b, Q.source b ≠ Q.target b) (v:V)
    (x : FiniteHomotopyClass U (K := K)) :
    F (colorPacketPerm Q step hstep N hN hn v x) =
      colorPacketPerm Q step hstep N hN hn v (F x) := by
  induction x using Quotient.inductionOn with | _ E =>
    rw [colorPacketPerm_apply]
    change classOfComplex U (C (E.complex.packetTwist U (fun a:J => (v,a)))) =
      colorPacketPerm Q step hstep N hN hn v
        (Quotient.mk (finiteHomotopySetoid U) (FiniteModel.ofComplex U (C E.complex)))
    rw [colorPacketPerm_apply]
    exact classOfComplex_eq U
      ((packetTwistComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E.complex v).toHomotopyEquivalence U)

lemma classLabel_packet_inverse (hn : ∀ b, Q.source b ≠ Q.target b) (v:V)
    (x : FiniteHomotopyClass U (K := K)) :
    F ((colorPacketPerm Q step hstep N hN hn v).symm x) =
      (colorPacketPerm Q step hstep N hN hn v).symm (F x) := by
  let π := colorPacketPerm Q step hstep N hN (K := K) hn v
  apply π.injective
  change π (F (π.symm x)) = π (π.symm (F x))
  rw [π.apply_symm_apply,← classLabel_packet Q step hstep N hN orient μ A ho hμ δ hA hroot hPF hn v,
    π.apply_symm_apply]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
