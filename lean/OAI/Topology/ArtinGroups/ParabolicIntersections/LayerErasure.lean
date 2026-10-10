import OAI.Topology.ArtinGroups.ParabolicIntersections.IncomingSpanning

namespace OAI

/-! Nilpotent coefficient paths remove one layer on a shorter interval. -/
namespace HarmonicArtin.ParabolicIntersections
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) [Fintype V] [Fintype A]
  {I : Type} [Fintype I]

theorem one_layer_erasure (U : Set V) (N : ℕ)
    (hwords : ∀ w : List A, w.length = N →
      (w.map (FreeAlgebra.ι ℂ)).prod ∈ TwoSidedIdeal.span (meshRelations Q U))
    (E : BasedComplex Q (K := ℂ) I) (hE : E.IsMinimal Q)
    (l r q : ℤ)
    (hcolors : ∀ i, l ≤ (E.placement i).cochain → (E.placement i).cochain ≤ r →
      (E.placement i).color ∈ U)
    (hex : ∀ α ∈ U, ∀ c, l ≤ c → c ≤ r → ∀ d,
      ScalarExactAt Q (E.testComplex Q α) α d c)
    (hhigher : ∀ i, l ≤ (E.placement i).cochain → (E.placement i).cochain ≤ r →
      q < (E.placement i).level → False) :
    ∀ i, (E.placement i).level = q → l+N ≤ (E.placement i).cochain →
      (E.placement i).cochain ≤ r → False := by
  let J := {i | l ≤ (E.placement i).cochain ∧ (E.placement i).cochain ≤ r}
  let F := cochainInterval Q E l r
  let B := arrowMatrix Q F
  have hF : F.IsMinimal Q := restrict_minimal Q E hE _ _
  have hU : ∀ i, (F.placement i).color ∈ U := fun i => hcolors i i.property.1 i.property.2
  have hnil : ∀ w : List A, w.length = N → (w.map B).prod = 0 := by
    intro w hw
    exact mesh_word_evaluate Q B (arrowMatrix_outside Q F U hU)
      (arrowMatrix_noncomposable Q F) (fun v _ => arrowMatrix_mesh Q F hF v) w (hwords w hw)
  have hbound : ∀ n : ℕ, ∀ i : J, (E.placement i).level = q →
      l+n ≤ (E.placement i).cochain → Pi.single i (1 : ℂ) ∈ pathImages B n := by
    intro n
    induction n with
    | zero => exact fun i _ _ => mem_pathImages_zero B _
    | succ n ih =>
      intro i hi hp
      apply incoming_spanning_step Q E hE l r i (by omega)
      · exact hex _ (hU i) _ i.property.1 i.property.2 _
      · intro j hj hlev
        apply hhigher j
        · omega
        · have := i.property.2; omega
        · rwa [← hi]
      · intro j hj hpj
        apply ih j (hj.trans hi)
        omega
  intro i hi hp hr
  let j : J := ⟨i, by constructor <;> omega⟩
  have hj := hbound N j hi hp
  rw [pathImages_eq_bot B N hnil] at hj
  have hz : (Pi.single j (1 : ℂ) : J → ℂ) = 0 := hj
  have hc := congrFun hz j
  exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using hc)

end HarmonicArtin.ParabolicIntersections

end OAI
