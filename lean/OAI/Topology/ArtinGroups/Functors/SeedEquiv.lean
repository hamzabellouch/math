import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Initial
import OAI.Topology.ArtinGroups.Complexes.Sum
import OAI.Topology.ArtinGroups.Functors.ColorPacketPerm

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

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

def seedEquiv (v:V) (c:J) :
    (Σ _ : {a:J // N c a}, PUnit.{u+1}) ≃
      Index N (initialProjective U (K := K) (v,c) : Zigzag.BasedComplex U PUnit.{u+1}).placement where
  toFun x := ⟨PUnit.unit,x.1⟩
  invFun x := ⟨x.2,PUnit.unit⟩
  left_inv x := by rcases x with ⟨a,⟨⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨⟩,a⟩; rfl

lemma seed_eq (v:V) (c:J) :
    (C (initialProjective U (v,c) : Zigzag.BasedComplex U PUnit.{u+1})).reindex U
      (seedEquiv Q step hstep N hN (K := K) v c) =
      finiteSum U (fun a : {a:J // N c a} => (initialProjective U (v,a) : Zigzag.BasedComplex U PUnit.{u+1})) := by
  apply ext_placement_differential U
  · funext x
    rcases x with ⟨a,⟨⟩⟩
    rfl
  · change (matrix Q step hstep N hN orient μ A _ _ 0).submatrix _ _ =
      Matrix.blockDiagonal' (fun _ : {a:J // N c a} => (0 : Matrix PUnit.{u+1} PUnit.{u+1} (Zigzag U K)))
    rw [matrix_zero,Matrix.submatrix_zero]
    exact Matrix.blockDiagonal'_zero.symm

lemma classLabel_initial (v:V) (c:J) :
    F (initialClass U (v,c)) =
      classSum U (fun a : {a:J // N c a} => initialClass U (v,a)) := by
  change classOfComplex U (C (initialProjective U (v,c) : Zigzag.BasedComplex U PUnit.{u+1})) = _
  change _ = classSum U (fun a : {a:J // N c a} =>
    classOfComplex U (initialProjective U (v,a) : Zigzag.BasedComplex U PUnit.{u+1}))
  rw [classSum_complex]
  exact (classOfComplex_reindex U _ (seedEquiv Q step hstep N hN (K := K) v c)).trans
    (congrArg (classOfComplex U) (seed_eq Q step hstep N hN orient μ A ho hμ δ hA hroot hPF v c))

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
