import Mathlib
import OAI.Topology.ArtinGroups.Functors.PacketSwitchMatrix
import OAI.Topology.ArtinGroups.Functors.ConeIndexEquiv
import OAI.Topology.ArtinGroups.Complexes.ReindexConeIsomorphism

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "M" => map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

lemma packetComparison_matrix (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    (packetComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u).forward.matrix =
      packetSwitchMatrix Q step hstep N hN orient μ A E.placement u := by
  rfl

noncomputable def packetTwistComparison (E : Zigzag.BasedComplex U (K := K) T) (u:V) :
    Zigzag.BasedComplex.ChainIsomorphism U
      (C (E.packetTwist U (fun a:J => (u,a))))
      ((C E).packetTwist U (fun a:J => (u,a))) := by
  let f := M (E.packetEvaluation U (fun a:J => (u,a)))
  let g := (C E).packetEvaluation U (fun a:J => (u,a))
  let e := leftPacketEquiv Q step hstep N hN E.placement u
  let d := rightPacketEquiv Q step hstep N hN E.placement u
  let a := packetComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u
  let b := Zigzag.BasedComplex.ChainIsomorphism.refl U ((C E).reindex U (Equiv.refl _))
  have comm : a.forward.matrix * (g.reindex U d (Equiv.refl _)).matrix =
      (f.reindex U e (Equiv.refl _)).matrix * b.forward.matrix := by
    have h := packetEvaluation_comparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u
    rw [show a.forward.matrix = packetSwitchMatrix Q step hstep N hN orient μ A E.placement u from
      packetComparison_matrix Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E u]
    exact h.trans (Zigzag.mul_projectiveIdentity U (f.reindex U e (Equiv.refl _)).entries).symm
  let middle := Zigzag.BasedComplex.ChainIsomorphism.cone U
    (f.reindex U e (Equiv.refl _)) (g.reindex U d (Equiv.refl _)) a b comm
  exact (((coneComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
      (E.packetEvaluation U (fun a:J => (u,a)))).trans U
    (f.reindexConeIsomorphism U e (Equiv.refl _))).trans U middle).trans U
      (g.reindexConeIsomorphism U d (Equiv.refl _)).symm

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
