import OAI.Topology.ArtinGroups.ParabolicIntersections.EmptyPlacement
import OAI.Topology.ArtinGroups.ParabolicIntersections.SphericalCochain
import OAI.Topology.ArtinGroups.ParabolicIntersections.ConnectedSupport

namespace OAI

/-! The gap contradiction in Proposition 7.4 of paper 082-03. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

/-- A missing cochain placement separates every generator below it from
all generators above it. The actual endomorphism dimension rules out
such a separation for a transported indecomposable projective. -/
lemma no_cochain_gap (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q)
    (hd : homDimension Q E E 0 0 ≤ 1) (r : ℤ)
    (hgap : ∀ i, (E.placement i).cochain ≠ r)
    (i j : I) (hi : (E.placement i).cochain < r)
    (hj : r < (E.placement j).cochain) : False := by
  apply no_proper_block Q E hE hd {k | (E.placement k).cochain < r} _ i j hi (not_lt.mpr hj.le)
  intro a b hab
  have hc : (E.placement b).cochain = (E.placement a).cochain+1 := by
    by_contra hn
    exact hab ((E.degree a b).1 hn)
  change (E.placement a).cochain < r ↔ (E.placement b).cochain < r
  have ha := hgap a
  have hb := hgap b
  omega

/-- Once the cochain tests have moved below the fixed exterior and the
path bound forces a gap, all tests vanish. This is the contradiction
used in the bounded-positive-height argument. -/
theorem tests_exact_of_empty_gap (U : Set V) (E : BasedComplex Q (K := ℂ) I)
    (hE : E.IsMinimal Q) (hd : homDimension Q E E 0 0 ≤ 1)
    (l r : ℤ) (hlr : l ≤ r)
    (hgap : ∀ i, (E.placement i).cochain ≠ r)
    (j : I) (hj : r < (E.placement j).cochain)
    (hex : ∀ α ∈ U, ∀ d c, l ≤ c → ScalarExactAt Q (E.testComplex Q α) α d c) :
    ∀ α ∈ U, ∀ d c, ScalarExactAt Q (E.testComplex Q α) α d c := by
  intro α hα d c
  by_cases hc : l ≤ c
  · exact hex α hα d c hc
  · apply scalarExact_of_absent_cochain Q
    intro i hi
    change (E.placement i.1).cochain = c at hi
    exact (no_cochain_gap Q E hE hd r hgap i.1 j (by omega) hj).elim

/-- The quantitative form of Proposition 7.4: with fixed generator-level
bounds and a fixed exterior lower placement, nonzero tests cannot all
move arbitrarily far down in cochain degree. -/
theorem cochain_lower_obstruction_of_mesh (U : Set V) (hmesh : MeshNilpotent Q U) :
    ∃ N : ℕ, 0 < N ∧ ∀ (I : Type) [Fintype I] (E : BasedComplex Q (K := ℂ) I),
      E.IsMinimal Q → homDimension Q E E 0 0 ≤ 1 →
      ∀ d₁ d₂ p : ℤ, d₁ ≤ d₂ →
      (∀ i, d₁ ≤ (E.placement i).level ∧ (E.placement i).level ≤ d₂) →
      (∀ i, (E.placement i).color ∉ U → p ≤ (E.placement i).cochain) →
      (∃ j, p ≤ (E.placement j).cochain) →
      (∀ α ∈ U, ∀ d c, p-1-N*(d₂-d₁+1) ≤ c →
        ScalarExactAt Q (E.testComplex Q α) α d c) →
      ∀ α ∈ U, ∀ d c, ScalarExactAt Q (E.testComplex Q α) α d c := by
  obtain ⟨N, hN, hgap⟩ := empty_placement_of_mesh Q U hmesh
  refine ⟨N, hN, ?_⟩
  intro J _ E hE hd d₁ d₂ p hdd hlevels hout hj hex
  let r := p-1
  let l := r-N*(d₂-d₁+1)
  have hNl : (0 : ℤ) ≤ N*(d₂-d₁+1) := mul_nonneg (Int.natCast_nonneg N) (by omega)
  have hlr : l ≤ r := by dsimp only [l]; omega
  have hempty : ∀ i, (E.placement i).cochain ≠ r := by
    intro i hi
    apply hgap J E hE l r d₁ d₂ hdd hlevels
      (fun k hk hkr => by
        by_contra hn
        have := hout k hn
        dsimp only [r] at hkr
        omega)
      (fun α hα c hc _ d => hex α hα d c hc) i
    · dsimp only [l] at *
      omega
    · omega
  obtain ⟨j, hj⟩ := hj
  apply tests_exact_of_empty_gap Q U E hE hd l r hlr hempty j (by dsimp only [r]; omega)
  exact hex

end HarmonicArtin.ParabolicIntersections

end OAI
