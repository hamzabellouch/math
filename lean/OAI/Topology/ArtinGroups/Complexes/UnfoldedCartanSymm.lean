import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Extend
import OAI.Topology.ArtinGroups.Complexes.TermwiseSplitInjection

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open scoped Matrix

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [Fintype A] [DecidableEq A] in
lemma unfoldedCartan_symm (α β : V) : unfoldedCartan Q α β = unfoldedCartan Q β α := by
  let e : {a : A // Q.source a = α ∧ Q.target a = β} ≃
      {a : A // Q.source a = β ∧ Q.target a = α} := {
    toFun a := ⟨Q.reverse a, by simpa only [Q.source_reverse, Q.target_reverse] using a.property.symm⟩
    invFun a := ⟨Q.reverse a, by simpa only [Q.source_reverse, Q.target_reverse] using a.property.symm⟩
    left_inv a := by apply Subtype.ext; exact Q.reverse_reverse a
    right_inv a := by apply Subtype.ext; exact Q.reverse_reverse a }
  simp only [unfoldedCartan]
  rw [Nat.card_congr e]
  congr 1
  simp only [eq_comm]

omit [Fintype V] [Fintype A] [DecidableEq A] in
lemma unfoldedCartan_off_nonpos (α β : V) (h : α ≠ β) : unfoldedCartan Q α β ≤ 0 := by
  simp only [unfoldedCartan, ite_eq_right h, zero_sub, neg_nonpos]
  exact Nat.cast_nonneg _

variable {I : Type*} [Fintype I]

omit [Fintype V] [DecidableEq A] in
lemma generatorVector_nonneg (E : BasedComplex Q (K := K) I) (α : V) :
    0 ≤ generatorVector Q E α := Nat.cast_nonneg _

omit [Fintype V] [DecidableEq A] in
lemma generatorVector_eq_zero_off (E : BasedComplex Q (K := K) I) (active : Set V)
    (hs : ∀ i, (E.placement i).color ∈ active) (α : V) (hα : α ∉ active) :
    generatorVector Q E α = 0 := by
  rw [generatorVector_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hne : (E.placement i).color ≠ α := fun h => hα (h ▸ hs i)
  simp only [ite_eq_right hne]

variable {T : Type*} [Fintype T]

lemma pure_subobject_null_separation
    (M : BasedComplex Q (K := K) I) (Y : BasedComplex Q (K := K) T)
    {q d : ℤ} (hM : ∀ i, (M.placement i).level = q) (hY : ∀ i, (Y.placement i).level = d)
    {B : Type*} (N : B → ℕ) (S : ∀ b, BasedComplex Q (K := K) (Fin (N b)))
    (hS : ∀ b i, ((S b).placement i).level = q)
    (incl : ∀ b, TermwiseSplitInjection Q (S b) M)
    (active openColors : Set V) (c : V → ℝ)
    (hc : ∀ α, 0 ≤ c α) (hcSupport : ∀ α ∉ active, c α = 0)
    (hcPos : ∀ α ∈ active, 0 < c α)
    (hcNull : ∀ α ∈ active, (unfoldedCartan Q *ᵥ c) α = 0)
    (hext : ∀ α ∉ openColors, generatorVector Q M α = c α)
    (hsupp : ∀ b i, ((S b).placement i).color ∈ openColors)
    (hinterior : (fun j : openColors => generatorVector Q M j - c j) ∈
      interior (convexHull ℝ (Set.range fun b : B =>
        (fun j : openColors => generatorVector Q (S b) j))))
    (hsoc : ∀ α ∈ openColors, ∀ k, coefficientSocle Q Y α k = ⊥)
    (hmid : totalHomDimension Q M Y (d-q+1) = 0) :
    (∀ α ∉ active, (∃ β ∈ active, unfoldedCartan Q α β < 0) → generatorVector Q Y α = 0) ∧
      (∀ j ∈ openColors, (unfoldedCartan Q *ᵥ generatorVector Q Y) j = 0) ∧
      totalHomDimension Q M Y (d-q) = 0 ∧ totalHomDimension Q Y M (q-d) = 0 := by
  classical
  have hbound : ∀ s ∈ (Set.range fun b : B =>
      (fun j : openColors => generatorVector Q (S b) j)),
      (totalHomDimension Q M Y (d-q) : ℝ) ≤
        (generatorVector Q M - NullBoundary.extend openColors s) ⬝ᵥ
          (unfoldedCartan Q *ᵥ generatorVector Q Y) := by
    rintro _ ⟨b, rfl⟩
    have he : NullBoundary.extend openColors (fun j : openColors => generatorVector Q (S b) j) =
        generatorVector Q (S b) :=
      NullBoundary.extend_restrict openColors (generatorVector Q (S b))
        (generatorVector_eq_zero_off Q (S b) openColors (hsupp b))
    rw [he]
    exact subobject_cartan_inequality Q M (S b) Y hM (hS b) hY (incl b)
      openColors (hsupp b) hsoc hmid
  have hsep := NullBoundary.convex_null_boundary_separation (unfoldedCartan Q)
    active openColors c (generatorVector Q M) (generatorVector Q Y)
    (Set.range fun b : B => (fun j : openColors => generatorVector Q (S b) j))
    (totalHomDimension Q M Y (d-q) : ℝ)
    (unfoldedCartan_symm Q) (unfoldedCartan_off_nonpos Q) hc hcSupport hcPos hcNull
    (generatorVector_nonneg Q Y) hext hinterior (Nat.cast_nonneg _) hbound
  have hz : totalHomDimension Q M Y (d-q) = 0 := by exact_mod_cast hsep.2.2.1
  refine ⟨hsep.1, hsep.2.1, hz, ?_⟩
  have heuler := pure_cartan_euler Q M Y hM hY
  rw [hsep.2.2.2, hmid, hz, Nat.cast_zero, sub_self, zero_add] at heuler
  exact_mod_cast heuler.symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
