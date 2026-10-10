import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Functors.Index
import OAI.Topology.ArtinGroups.Complexes.Refl

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T R : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
local notation "L" => linearMap Q step hstep N hN orient μ A
variable [Fintype T] [Fintype R] [DecidableEq T] [DecidableEq R]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "M" => map Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

def coneIndexEquiv {E : Zigzag.BasedComplex U (K := K) T}
    {D : Zigzag.BasedComplex U (K := K) R} (f : Zigzag.BasedComplex.Map U E D) :
    Index N E.placement ⊕ Index N D.placement ≃ Index N (Zigzag.BasedComplex.Map.cone U (I := T) (J := R) (E := E) (F := D) f).placement where
  toFun
    | .inl ⟨i,c⟩ => ⟨.inl i,c⟩
    | .inr ⟨i,c⟩ => ⟨.inr i,c⟩
  invFun
    | ⟨.inl i,c⟩ => .inl ⟨i,c⟩
    | ⟨.inr i,c⟩ => .inr ⟨i,c⟩
  left_inv i := by rcases i with ⟨i,c⟩|⟨i,c⟩ <;> rfl
  right_inv i := by rcases i with ⟨i,c⟩; cases i <;> rfl

omit [DecidableEq T] [DecidableEq R] in
lemma cone_complex_eq {E : Zigzag.BasedComplex U (K := K) T}
    {D : Zigzag.BasedComplex U (K := K) R} (f : Zigzag.BasedComplex.Map U E D) :
    (C (Zigzag.BasedComplex.Map.cone U (I := T) (J := R) (E := E) (F := D) f)).reindex U (coneIndexEquiv Q step hstep N hN f) = (M f).cone U := by
  apply Zigzag.BasedComplex.ext_placement_differential
  · funext i
    rcases i with ⟨i,c⟩|⟨i,c⟩ <;> rfl
  · apply Matrix.ext
    intro i j
    rcases i with ⟨i,c⟩|⟨i,c⟩ <;> rcases j with ⟨j,d⟩|⟨j,d⟩
    · change L (-E.differential i j) (indexEmbed N E.placement ⟨i,c⟩)
          (indexEmbed N E.placement ⟨j,d⟩) =
        -(L (E.differential i j) (indexEmbed N E.placement ⟨i,c⟩)
          (indexEmbed N E.placement ⟨j,d⟩))
      simp only [map_neg,Matrix.neg_apply]
    · rfl
    · change L 0 _ _ = 0
      simp only [map_zero,Matrix.zero_apply]
    · rfl

noncomputable def coneComparison {E : Zigzag.BasedComplex U (K := K) T}
    {D : Zigzag.BasedComplex U (K := K) R} (f : Zigzag.BasedComplex.Map U E D) :
    Zigzag.BasedComplex.ChainIsomorphism U (C (Zigzag.BasedComplex.Map.cone U (I := T) (J := R) (E := E) (F := D) f)) ((M f).cone U (E := C E) (F := C D)) := by
  rw [← cone_complex_eq Q step hstep N hN orient μ A ho hμ δ hA hroot hPF f]
  exact Zigzag.BasedComplex.reindexChainIsomorphism U _ (coneIndexEquiv Q step hstep N hN f)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
