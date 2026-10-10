import OAI.Topology.CoarseAssembly.RegularConstants
import OAI.Topology.CoarseAssembly.KazhdanInput
import OAI.Analysis.NuclearUltrapower.Kazhdan

namespace OAI

/-! # Applying the integral spectral certificate to the finite congruence fibers

The required gap follows from surjectivity of elementary reduction.
-/

noncomputable section

namespace CoarseAssembly

open Congruence
open NuclearUltrapower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def elementaryReduction (k : ℕ) : SOS.E →* Congruence.Quotient k :=
  (reduce k).comp SOS.elementary.subtype

def elementaryRegular (k : ℕ) : SOS.E →*
    (lp (fun _ : Congruence.Quotient k => H) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : Congruence.Quotient k => H) 2) :=
  (leftTranslationHom (H := H) (Congruence.Quotient k)).comp (elementaryReduction k)

def elementaryLaplacian (k : ℕ) :
    lp (fun _ : Congruence.Quotient k => H) 2 →L[ℂ] lp (fun _ : Congruence.Quotient k => H) 2 :=
  SOS.ElementarySpectral.deltaOp (elementaryRegular (H := H) k)

theorem certificateGenerators_subset : SOS.genSet ⊆ elementaryMoves := by
  decide +kernel

omit [CompleteSpace H] in
theorem elementaryEnergy_le (k : ℕ) (x : lp (fun _ : Congruence.Quotient k => H) 2) :
    SOSEnergy.energy SOS.eGenSet (elementaryRegular (H := H) k) x ≤ translationEnergy elementaryMoves k x := by
  classical
  have hs : SOSEnergy.energy SOS.eGenSet (elementaryRegular (H := H) k) x =
      ∑ g ∈ SOS.genSet, ‖leftTranslation (Congruence.Quotient k) (reduce k g) x - x‖ ^ 2 := by
    unfold SOSEnergy.energy
    apply Finset.sum_bij (fun (g : SOS.E) _ => (g : SOS.SL))
    · intro g hg
      exact SOS.mem_eGenSet.mp hg
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro g hg
      let e : SOS.E := ⟨g, Subgroup.subset_closure hg⟩
      exact ⟨e, SOS.mem_eGenSet.mpr hg, rfl⟩
    · intro g _
      rfl
  rw [hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg certificateGenerators_subset (fun _ _ _ => sq_nonneg _)

theorem elementaryKernel_projection (k : ℕ)
    (hsurj : Function.Surjective (elementaryReduction k))
    (x : lp (fun _ : Congruence.Quotient k => H) 2)
    (hx : x ∈ (elementaryLaplacian (H := H) k).ker) :
    constantProjection (Congruence.Quotient k) x = x := by
  apply regular_fixed_projection
  intro q
  obtain ⟨g, rfl⟩ := hsurj q
  exact SOS.ElementarySpectral.deltaOp_ker_fixed (elementaryRegular (H := H) k) x hx g

theorem elementaryEnergy_gap (k : ℕ)
    (hsurj : Function.Surjective (elementaryReduction k))
    (x : lp (fun _ : Congruence.Quotient k => H) 2)
    (hx : constantProjection (Congruence.Quotient k) x = 0) :
    (1 / 10 : ℝ) * ‖x‖ ^ 2 ≤ translationEnergy elementaryMoves k x := by
  have ho : x ∈ (elementaryLaplacian (H := H) k).kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    exact inner_eq_zero_of_projection_zero _ x y hx (elementaryKernel_projection k hsurj y hy)
  exact (SOS.ElementarySpectral.deltaOp_gap (elementaryRegular (H := H) k) x ho).trans (elementaryEnergy_le k x)

/-- The required published gap follows from the integral certificate and
surjectivity onto the specified finite quotients. -/
theorem publishedKazhdanInput_of_elementaryReduction
    (hsurj : ∀ k, Function.Surjective (elementaryReduction k)) : PublishedKazhdanInput := by
  apply uniformAveragingGap_of_energy elementaryMoves elementaryMoves_nonempty (1 / 10)
    (by norm_num)
  · have hc : (1 : ℝ) ≤ elementaryMoves.card := by
      exact_mod_cast elementaryMoves_nonempty.card_pos
    linarith
  · intro k x hx
    exact elementaryEnergy_gap k (hsurj k) x hx

end CoarseAssembly

end

end OAI
