import Mathlib
import OAI.RingTheory.Kurosh.AlgebraicClosure
import OAI.RingTheory.Kurosh.FiniteDescent
import OAI.RingTheory.Kurosh.InfiniteDimension

namespace OAI

/-! The division ring obtained from a compatible scheduled tower. -/

namespace KuroshConstruction

open Filter

lemma field_limit_countable (K : ℕ → Type*) [∀ i, Field (K i)] [∀ i, Countable (K i)]
    (f : ∀ i j, i ≤ j → K i →+* K j)
    [DirectedSystem K (fun i j h => f i j h)] : Countable (DirectLimit K f) := by
  apply Function.Surjective.countable (f := fun p : Sigma K => DirectLimit.Ring.of K f p.1 p.2)
  intro z
  obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk f z
  exact ⟨⟨i, x⟩, hx.symm⟩

lemma generated_adjoin_eq_top {L D I : Type*} [CommSemiring L] [Semiring D]
    [Algebra L D] (Y : I → D) :
    Algebra.adjoin L (Set.range (fun c : I =>
      (⟨Y c, Algebra.subset_adjoin ⟨c, rfl⟩⟩ : Algebra.adjoin L (Set.range Y)))) = ⊤ := by
  have he : Set.range (fun c : I =>
      (⟨Y c, Algebra.subset_adjoin ⟨c, rfl⟩⟩ : Algebra.adjoin L (Set.range Y))) =
      ((↑) : Algebra.adjoin L (Set.range Y) → D) ⁻¹' Set.range Y := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, hc⟩; exact ⟨c, Subtype.ext hc⟩
  rw [he]
  exact Algebra.adjoin_adjoin_coe_preimage

def MainStatement : Prop :=
  ∃ (D : Type) (_ : DivisionRing D),
    Countable D ∧ CharZero D ∧
    ∃ x y : D,
      Algebra.adjoin (Subring.center D) ({x, y} : Set D) = ⊤ ∧
      centerDivisionAdjoin D ({x, y} : Set D) = ⊤ ∧
      ¬ Module.Finite (Subring.center D) D ∧
      ∀ a : D, IsAlgebraic (Subring.center D) a

theorem scheduled_tower_yields_main
    (K A : ℕ → Type) [∀ i, Field (K i)] [∀ i, DivisionRing (A i)]
    [∀ i, Algebra (K i) (A i)] [∀ i, Module.Finite (K i) (A i)]
    [∀ i, Countable (K i)] [∀ i, CharZero (A i)]
    (f : ∀ i j, i ≤ j → K i →+* K j)
    [DirectedSystem K (fun i j h => f i j h)]
    (X : Fin 2 → ∀ i, A i)
    (hgen : ∀ i, Algebra.adjoin (K i) (Set.range (fun c => X c i)) = ⊤)
    (hgrow : ∀ n : ℕ, ∀ᶠ i in atTop, n ≤ Module.finrank (K i) (A i))
    (hs : RelationsScheduled K A f X) : MainStatement := by
  classical
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let : Fact ((U : Filter ℕ) ≤ atTop) := ⟨Ultrafilter.of_le _⟩
  let L := DirectLimit K f
  let : Countable L := field_limit_countable K f
  let Y : Fin 2 → DivisionUltraproduct U A := fun c => ultraMap U A (X c)
  let R := Algebra.adjoin L (Set.range Y)
  let : DivisionRing R := scheduledDivisionRing U K A f X hs
  let : Countable R := countable_generated_algebra L (DivisionUltraproduct U A) (Fin 2) Y
  let : Algebra.IsAlgebraic L R := ⟨fun r =>
    ((isIntegral_algHom_iff R.val Subtype.val_injective).mp
      (scheduled_isIntegral U K A f X hs r r.property)).isAlgebraic⟩
  let y : Fin 2 → R := fun c => ⟨Y c, Algebra.subset_adjoin ⟨c, rfl⟩⟩
  have hy : Set.range y = ({y 0, y 1} : Set R) := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨c, rfl⟩
      fin_cases c <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hgenR : Algebra.adjoin L ({y 0, y 1} : Set R) = ⊤ := by
    rw [← hy]
    exact generated_adjoin_eq_top Y
  have hinf : ¬ Module.Finite L R := generated_ultra_not_finite U K A f X hgen hgrow
  have hcenter : Algebra.adjoin (Subring.center R) ({y 0, y 1} : Set R) = ⊤ :=
    adjoin_center_eq_top hgenR
  refine ⟨R, inferInstance, inferInstance, inferInstance, y 0, y 1,
    hcenter, centerDivisionAdjoin_eq_top hcenter, ?_, ?_⟩
  · apply not_finite_over_center (k := L) ({y 0, y 1} : Finset R) _ hinf
    simpa using hgenR
  · exact algebraic_over_center (k := L)

end KuroshConstruction

end OAI
