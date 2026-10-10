import OAI.RingTheory.DirectFiniteness.DirectionFrame

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
open Module
namespace KaplanskyCounterexample.FiniteGeometry

theorem exists_directionFrame {Q : Type u_1} {F : Type u_2} {R : Type u_3} [Field Q] [Field F] [Algebra Q F]
    [FiniteDimensional Q F] [Fintype Q] [Fintype F] [Fintype R]
    (b : ℕ) (hb : 2 ≤ b) (hdim : finrank Q F = b)
    (hsize : Fintype.card R + Fintype.card R * Fintype.card Q ≤ Fintype.card F) :
    Nonempty (DirectionFrame Q (Fin 10 → F) R (Fin (b-1) → Q)) := by
  let ι := R ⊕ (R × Q)
  let dim : ι → ℕ := Sum.elim (fun _ => 2) (fun _ => b-1)
  obtain ⟨P,hd,hP⟩ := exists_shortDirect_subspaces (Q := Q) (F := F)
    (ι := ι) (by decide : 0 < 10) dim (by
      intro i
      cases i <;> simp [dim,hdim,hb]) (by simpa [ι] using hsize)
  let W (r : R) : (Q × Q) ≃ₗ[Q] P (.inl r) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [dim] using (hd (.inl r)).symm)
  let E (j : R × Q) : (Fin (b-1) → Q) ≃ₗ[Q] P (.inr j) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [dim] using (hd (.inr j)).symm)
  let w (r : R) := (P (.inl r)).subtype.comp (W r).toLinearMap
  let e (j : R × Q) := (P (.inr j)).subtype.comp (E j).toLinearMap
  refine ⟨{w := w, e := e, winj := ?_, einj := ?_, direct := ?_}⟩
  · intro r
    exact Subtype.val_injective.comp (W r).injective
  · intro j
    exact Subtype.val_injective.comp (E j).injective
  · intro k hk j hj x hx hz
    apply hP k hk j hj x _ hz
    intro i
    have hh := hx i
    cases hji : j i with
    | inl r =>
      simp only [hji, Sum.elim_inl] at hh
      obtain ⟨a,ha⟩ := hh
      rw [← ha]
      exact (W r a).property
    | inr t =>
      simp only [hji, Sum.elim_inr] at hh
      obtain ⟨a,ha⟩ := hh
      rw [← ha]
      exact (E t a).property

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
