import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PacketPermReindex
import OAI.Topology.ArtinGroups.Functors.SeedEquiv

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

noncomputable def signedPacketPerm (a : V × Bool) :
    Equiv.Perm (FiniteHomotopyClass U (K := K)) :=
  if a.2 then colorPacketPerm Q step hstep N hN hn a.1
  else (colorPacketPerm Q step hstep N hN hn a.1).symm

noncomputable def wordPacketPerm : List (V × Bool) →
    Equiv.Perm (FiniteHomotopyClass U (K := K))
  | [] => 1
  | a :: w => signedPacketPerm Q step hstep N hN hn a * wordPacketPerm w

variable {I : Type u} [Fintype I] [DecidableEq I]
lemma signedPacketPerm_sum (a : V × Bool) (x : I → FiniteHomotopyClass U (K := K)) :
    signedPacketPerm Q step hstep N hN hn a (classSum U x) =
      classSum U (fun i => signedPacketPerm Q step hstep N hN hn a (x i)) := by
  unfold signedPacketPerm colorPacketPerm
  cases a.2 <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact classPacketPerm_inverse_sum U _ _ _ x
  · exact classPacketPerm_sum U _ _ _ x

lemma wordPacketPerm_sum (w : List (V × Bool)) (x : I → FiniteHomotopyClass U (K := K)) :
    wordPacketPerm Q step hstep N hN hn w (classSum U x) =
      classSum U (fun i => wordPacketPerm Q step hstep N hN hn w (x i)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change signedPacketPerm Q step hstep N hN hn a
      (wordPacketPerm Q step hstep N hN hn w (classSum U x)) = _
    rw [ih,signedPacketPerm_sum]
    rfl

variable (orient : B → Bool) (μ : J → K) (A : K)
  (ho : ∀ b, orient (Q.reverse b) = !(orient b))
  (hμ : ∀ a, μ a ≠ 0) (δ : K)
  (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
  (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

lemma classLabel_signedPacket (a : V × Bool) (x : FiniteHomotopyClass U (K := K)) :
    F (signedPacketPerm Q step hstep N hN hn a x) =
      signedPacketPerm Q step hstep N hN hn a (F x) := by
  unfold signedPacketPerm
  cases a.2 <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact classLabel_packet_inverse Q step hstep N hN orient μ A ho hμ δ hA hroot hPF hn a.1 x
  · exact classLabel_packet Q step hstep N hN orient μ A ho hμ δ hA hroot hPF hn a.1 x

lemma classLabel_wordPacket (w : List (V × Bool)) (x : FiniteHomotopyClass U (K := K)) :
    F (wordPacketPerm Q step hstep N hN hn w x) =
      wordPacketPerm Q step hstep N hN hn w (F x) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change F (signedPacketPerm Q step hstep N hN hn a (wordPacketPerm Q step hstep N hN hn w x)) = _
    rw [classLabel_signedPacket,ih]
    rfl

lemma classLabel_wordOrbit (w : List (V × Bool)) (v : V) (c : J) :
    F (wordPacketPerm Q step hstep N hN hn w (initialClass U (v,c))) =
      classSum U (fun a : {a : J // N c a} =>
        wordPacketPerm Q step hstep N hN hn w (initialClass U (v,a))) := by
  rw [classLabel_wordPacket,classLabel_initial,wordPacketPerm_sum]

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
