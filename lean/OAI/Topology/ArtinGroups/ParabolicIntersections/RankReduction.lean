import OAI.Topology.ArtinGroups.ParabolicIntersections.StabilizerDescent

namespace OAI

/-! Rank descent restricted to the subgroup of colors avoiding the frame. -/
namespace HarmonicArtin.ParabolicIntersections
variable {S : Type*} [Finite S] (M : CoxeterMatrix S)
variable {V : Type*} [MulAction (Artin M) V] (v : V)

/-- The induction keeps the transported point inside the prescribed orbit.
This permits the extra frame color in the relative diagram to remain fixed. -/
theorem relativeStabilizers_of_reductions_on (U : Set S)
    (hred : ∀ Y : Set S, Y ⊆ U → ∀ x : Artin M, x ∈ artinParabolic M U →
      ReductionAt M v Y x)
    (Y : Set S) (hYU : Y ⊆ U) (x : Artin M) (hx : x ∈ artinParabolic M U) :
    ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      relativeStabilizer M v Y x = conjugate c⁻¹ (artinParabolic M R) := by
  suffices h : ∀ n : ℕ, ∀ Y : Set S, Y.ncard = n → Y ⊆ U →
      ∀ x : Artin M, x ∈ artinParabolic M U →
      ∃ (R : Set S) (c : Artin M), R ⊆ Y ∧ c ∈ artinParabolic M Y ∧
        relativeStabilizer M v Y x = conjugate c⁻¹ (artinParabolic M R) from h _ Y rfl hYU x hx
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Y hY hYU x hx
    rcases hred Y hYU x hx with hfixed | ⟨D,b,hD,hb,hcontain⟩ | ⟨T,K,hT,hK,hnorm,hsplit⟩
    · refine ⟨Y,1,Set.Subset.rfl,(artinParabolic M Y).one_mem,?_⟩
      simpa using hfixed
    · have hlt : D.ncard < n := hY ▸ Set.ncard_lt_ncard hD
      obtain ⟨R,c,hRD,hc,he⟩ := ih _ hlt D rfl (hD.subset.trans hYU) (b*x)
        ((artinParabolic M U).mul_mem (standard_mono M hYU hb) hx)
      have hconj := relativeStabilizer_conjugation M v Y D b x hD.subset hb hcontain
      have heq := congrArg (conjugate b⁻¹) (hconj.trans he)
      refine ⟨R,c*b,hRD.trans hD.subset,
        (artinParabolic M Y).mul_mem (standard_mono M hD.subset hc) hb,?_⟩
      simpa only [← conjugate_mul,inv_mul_cancel,conjugate_one,mul_inv_rev] using heq
    · have hlt : T.ncard < n := hY ▸ Set.ncard_lt_ncard hT
      obtain ⟨R,c,hRT,hc,he⟩ := ih _ hlt T rfl (hT.subset.trans hYU) x hx
      have hn := hnorm c⁻¹ ((artinParabolic M T).inv_mem hc)
      refine ⟨K ∪ R,c,Set.union_subset hK (hRT.trans hT.subset),
        standard_mono M hT.subset hc,?_⟩
      rw [hsplit,he,standard_union,conjugate_sup,hn]

end HarmonicArtin.ParabolicIntersections

end OAI
