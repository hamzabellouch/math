import OAI.Topology.ArtinGroups.ParabolicIntersections.LayerErasure

namespace OAI

/-! The empty-placement lemma (Lemma 7.3 of paper 082-03). -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]

/-- Exact vertex tests on a spherical interval force a gap after at most
`N` placements per occupied layer. Only the abstract published path
identity is assumed; the layer-removal argument is proved here. -/
theorem empty_placement_of_mesh (U : Set V) (hmesh : MeshNilpotent Q U) :
    ∃ N : ℕ, 0 < N ∧ ∀ (I : Type) [Fintype I] (E : BasedComplex Q (K := ℂ) I),
      E.IsMinimal Q → ∀ l r d₁ d₂ : ℤ, d₁ ≤ d₂ →
      (∀ i, d₁ ≤ (E.placement i).level ∧ (E.placement i).level ≤ d₂) →
      (∀ i, l ≤ (E.placement i).cochain → (E.placement i).cochain ≤ r →
        (E.placement i).color ∈ U) →
      (∀ α ∈ U, ∀ c, l ≤ c → c ≤ r → ∀ d,
        ScalarExactAt Q (E.testComplex Q α) α d c) →
      ∀ i, l+N*(d₂-d₁+1) ≤ (E.placement i).cochain →
        (E.placement i).cochain ≤ r → False := by
  obtain ⟨N, hN, hwords⟩ := hmesh
  refine ⟨N, hN, ?_⟩
  intro I _ E hE l r d₁ d₂ hdd hlevels hcolors hex
  have herase : ∀ n : ℕ, ∀ i, l+(n:ℤ)*N ≤ (E.placement i).cochain →
      (E.placement i).cochain ≤ r → d₂-(n:ℤ) < (E.placement i).level → False := by
    intro n
    induction n with
    | zero =>
      intro i _ _ hi
      have := (hlevels i).2
      simp only [Int.natCast_zero, sub_zero] at hi
      omega
    | succ n ih =>
      intro i hi hir hlev
      by_cases htop : d₂-(n:ℤ) < (E.placement i).level
      · apply ih i _ hir htop
        have : (0 : ℤ) ≤ N := Int.natCast_nonneg N
        push_cast at hi
        nlinarith
      · have heq : (E.placement i).level = d₂-(n:ℤ) := by
          push_cast at hlev
          omega
        apply one_layer_erasure Q U N hwords E hE (l+(n:ℤ)*N) r (d₂-(n:ℤ))
          (fun j hj hjr => hcolors j (by have := Int.natCast_nonneg n; have := Int.natCast_nonneg N; nlinarith) hjr)
          (fun α hα c hc hcr d => hex α hα c
            (by have := Int.natCast_nonneg n; have := Int.natCast_nonneg N; nlinarith) hcr d)
          (fun j hj hjr hhigh => ih j hj hjr hhigh) i heq _ hir
        push_cast at hi
        nlinarith
  let n := (d₂-d₁+1).toNat
  have hn : (n : ℤ) = d₂-d₁+1 := Int.toNat_of_nonneg (by omega)
  intro i hi hir
  apply herase n i _ hir _
  · rw [hn]
    nlinarith
  · rw [hn]
    have := (hlevels i).1
    omega

end HarmonicArtin.ParabolicIntersections

end OAI
