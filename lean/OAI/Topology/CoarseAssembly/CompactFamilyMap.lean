import OAI.Topology.CoarseAssembly.LocallyFinite
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! # Proper maps preserving compact components

The properness argument for the family of boundary loops uses compactness
of each source component and preservation of the discrete component index.
-/

noncomputable section

namespace CoarseAssembly

open Topology

variable {X Y : ℕ → Type} [∀ j, TopologicalSpace (X j)]
  [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (X j)] [∀ j, T2Space (Y j)]

def compactFamilyContinuousMap (γ : ∀ j, C(X j, Y j)) : C(Sigma X, Sigma Y) where
  toFun z := ⟨z.1, γ z.1 z.2⟩
  continuous_toFun := continuous_sigma (fun j => continuous_sigmaMk.comp (γ j).continuous)

theorem compactFamily_preimage_compact (γ : ∀ j, C(X j, Y j))
    (K : Set (Sigma Y)) (hK : IsCompact K) :
    IsCompact ((compactFamilyContinuousMap γ) ⁻¹' K) := by
  obtain ⟨s, t, hs, _ht, heq⟩ := hK.sigma_exists_finite_sigma_eq
  have hcover : (compactFamilyContinuousMap γ) ⁻¹' K ⊆
      s.sigma (fun j => (Set.univ : Set (X j))) := by
    rintro ⟨j, z⟩ hz
    change Sigma.mk j (γ j z) ∈ K at hz
    rw [← heq] at hz
    exact ⟨hz.1, Set.mem_univ _⟩
  exact (Set.isCompact_sigma hs (fun _ _ => isCompact_univ)).of_isClosed_subset
    (hK.isClosed.preimage (compactFamilyContinuousMap γ).continuous) hcover

def compactFamilyMap (γ : ∀ j, C(X j, Y j)) : CocompactMap (Sigma X) (Sigma Y) where
  toContinuousMap := compactFamilyContinuousMap γ
  cocompact_tendsto' := CocompactMap.tendsto_of_forall_preimage
    (compactFamily_preimage_compact γ)

@[simp] theorem compactFamilyMap_apply (γ : ∀ j, C(X j, Y j)) (j : ℕ) (x : X j) :
    compactFamilyMap γ ⟨j, x⟩ = ⟨j, γ j x⟩ := rfl

end CoarseAssembly

end

end OAI
