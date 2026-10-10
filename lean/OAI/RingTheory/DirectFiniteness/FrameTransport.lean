import OAI.RingTheory.DirectFiniteness.FieldExtensions

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Module
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A B R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup B] [Module Q B] [AddCommGroup E] [Module Q E]

namespace DirectionFrame

def transport (F : DirectionFrame Q A R E) (f : A ≃ₗ[Q] B) : DirectionFrame Q B R E where
  w r := f.toLinearMap.comp (F.w r)
  e j := f.toLinearMap.comp (F.e j)
  winj r := f.injective.comp (F.winj r)
  einj j := f.injective.comp (F.einj j)
  direct := by
    intro k hk j hj x hx hz
    have hm (i : Fin k) : f.symm (x i) ∈ Sum.elim (fun r => (F.w r).range) (fun j => (F.e j).range) (j i) := by
      have hxi := hx i
      cases he : j i with
      | inl r =>
        simp only [he,Sum.elim_inl] at hxi ⊢
        obtain ⟨a,ha⟩ := hxi
        exact ⟨a,by rw [← ha]; exact (f.symm_apply_apply _).symm⟩
      | inr t =>
        simp only [he,Sum.elim_inr] at hxi ⊢
        obtain ⟨a,ha⟩ := hxi
        exact ⟨a,by rw [← ha]; exact (f.symm_apply_apply _).symm⟩
    have hsum : ∑ i, f.symm (x i)=0 := by rw [← map_sum,hz,map_zero]
    have hh := F.direct k hk j hj (fun i => f.symm (x i)) hm hsum
    intro i
    exact f.symm.injective ((hh i).trans f.symm.map_zero.symm)

end DirectionFrame

lemma exists_coordinate_frame (Q : Type) [Field Q] [Fintype Q] [CharP Q 2]
    (R : Type) [Fintype R]
    (hsize : Fintype.card R + Fintype.card R * Fintype.card Q ≤ (Fintype.card Q)^120) :
    Nonempty (DirectionFrame Q (Fin 1200 → Q) R (Fin 119 → Q)) := by
  obtain ⟨F,hF,hA,hfin,hD⟩ := exists_finite_extension Q 120 (by decide)
  let _ := hF
  let _ := hA
  let _ := hfin
  have hcard : Fintype.card F=(Fintype.card Q)^120 := by
    rw [Module.card_eq_pow_finrank (K := Q) (V := F),hD]
  obtain ⟨frame⟩ := exists_directionFrame (Q := Q) (F := F) (R := R) 120 (by decide) hD (by rwa [hcard])
  let f : (Fin 10 → F) ≃ₗ[Q] (Fin 1200 → Q) := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_pi_fintype,Module.finrank_pi]
    simp [hD])
  exact ⟨frame.transport f⟩

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
