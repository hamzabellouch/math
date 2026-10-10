import Mathlib
import OAI.RingTheory.Kurosh.Independence
import OAI.RingTheory.Kurosh.IndependentWords

namespace OAI

/-! Infinite dimension of the algebra generated in the ultraproduct. -/

namespace KuroshConstruction

open Filter

section InfiniteAlgebra

variable (U : Ultrafilter ℕ) [hU : Fact ((U : Filter ℕ) ≤ atTop)]
  (K A : ℕ → Type*) [∀ i, Field (K i)] [∀ i, DivisionRing (A i)]
  [∀ i, Algebra (K i) (A i)] [∀ i, Module.Finite (K i) (A i)]
  (f : ∀ i j, i ≤ j → K i →+* K j)
  [DirectedSystem K (fun i j h => f i j h)]
  {I : Type*} [Finite I] (X : I → ∀ i, A i)

omit hU [Finite I] in
lemma ultra_wordValue (w : List I) :
    ultraMap U A (fun i => wordValue (A i) I (fun c => X c i) w) =
      wordValue (DivisionUltraproduct U A) I (fun c => ultraMap U A (X c)) w := by
  induction w with
  | nil => exact map_one (ultraMap U A)
  | cons c w hw =>
    change ultraMap U A (X c * (fun i => wordValue (A i) I (fun c => X c i) w)) = _
    rw [map_mul, hw]
    rfl

omit [Finite I] in
lemma wordValue_mem_adjoin {L D : Type*} [CommSemiring L] [Ring D] [Algebra L D]
    (Y : I → D) (w : List I) : wordValue D I Y w ∈ Algebra.adjoin L (Set.range Y) := by
  induction w with
  | nil => exact (Algebra.adjoin _ _).one_mem
  | cons c w hw =>
    exact (Algebra.adjoin _ _).mul_mem (Algebra.subset_adjoin ⟨c, rfl⟩) hw

theorem generated_ultra_not_finite
    (hgen : ∀ i, Algebra.adjoin (K i) (Set.range (fun c => X c i)) = ⊤)
    (hgrow : ∀ n : ℕ, ∀ᶠ i in atTop, n ≤ Module.finrank (K i) (A i)) :
    ¬ Module.Finite (DirectLimit K f)
      (Algebra.adjoin (DirectLimit K f) (Set.range (fun c => ultraMap U A (X c)))) := by
  classical
  intro hfinite
  let L := DirectLimit K f
  let Y : I → DivisionUltraproduct U A := fun c => ultraMap U A (X c)
  let R := Algebra.adjoin L (Set.range Y)
  let : Module.Finite L R := hfinite
  let n := Module.finrank L R
  have hex : ∀ᶠ i in U, ∃ w : Fin (n+1) → BoundedWord I n,
      LinearIndependent (K i) (fun j => wordValue (A i) I (fun c => X c i) (w j).val) :=
    ((hgrow (n+1)).filter_mono hU.out).mono (fun i hi =>
      exists_independent_bounded_words (fun c => X c i) (hgen i) n hi)
  obtain ⟨w, hw⟩ := Ultrafilter.eventually_exists_iff.mp hex
  have hli := ultra_linearIndependent U K A f
    (fun j i => wordValue (A i) I (fun c => X c i) (w j).val) hw
  simp_rw [ultra_wordValue] at hli
  let v : Fin (n+1) → R := fun j =>
    ⟨wordValue _ I Y (w j).val, wordValue_mem_adjoin Y (w j).val⟩
  have hi : LinearIndependent L v := LinearIndependent.of_comp R.val.toLinearMap hli
  have hc := hi.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hc
  exact Nat.not_succ_le_self n hc

end InfiniteAlgebra

end KuroshConstruction

end OAI
