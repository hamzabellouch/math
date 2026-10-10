import Mathlib

namespace OAI

/-! Division-ring ultraproducts and equality of representatives. -/

namespace KuroshConstruction

open Filter

variable {ι : Type*} (U : Ultrafilter ι) (A : ι → Type*) [∀ i, DivisionRing (A i)]

def ultraCongruence : RingCon (∀ i, A i) where
  r f g := ∀ᶠ i in U, f i = g i
  iseqv := ⟨fun _ => Eventually.of_forall (fun _ => rfl),
    fun h => h.mono (fun _ => Eq.symm),
    fun h k => (h.and k).mono (fun _ h => h.1.trans h.2)⟩
  mul' h k := (h.and k).mono (fun _ h => congrArg₂ (· * ·) h.1 h.2)
  add' h k := (h.and k).mono (fun _ h => congrArg₂ (· + ·) h.1 h.2)

abbrev DivisionUltraproduct := (ultraCongruence U A).Quotient

noncomputable def ultraMap : (∀ i, A i) →+* DivisionUltraproduct U A :=
  (ultraCongruence U A).mk'

lemma ultraMap_eq_iff (f g : ∀ i, A i) :
    ultraMap U A f = ultraMap U A g ↔ ∀ᶠ i in U, f i = g i :=
  RingCon.eq _

instance divisionUltraproduct_nontrivial : Nontrivial (DivisionUltraproduct U A) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hh : ultraMap U A 0 = ultraMap U A 1 := by simpa using h
  have he := (ultraMap_eq_iff U A 0 1).mp hh
  obtain ⟨i, hi⟩ := he.exists
  exact zero_ne_one hi

noncomputable instance divisionUltraproductDivisionRing : DivisionRing (DivisionUltraproduct U A) :=
  DivisionRing.ofIsUnitOrEqZero (fun q => by
    classical
    by_cases h : q = 0
    · exact Or.inr h
    · left
      obtain ⟨f, rfl⟩ := (ultraCongruence U A).mk'_surjective q
      have hf : ∀ᶠ i in U, f i ≠ 0 := by
        rw [Ultrafilter.eventually_not]
        intro hf
        apply h
        have he := (ultraMap_eq_iff U A f 0).mpr hf
        simpa [ultraMap] using he
      let g : ∀ i, A i := fun i => (f i)⁻¹
      have hfg : ultraMap U A f * ultraMap U A g = 1 := by
        rw [← map_mul, ← map_one (ultraMap U A)]
        apply (ultraMap_eq_iff U A _ _).mpr
        exact hf.mono (fun i hi => mul_inv_cancel₀ hi)
      have hgf : ultraMap U A g * ultraMap U A f = 1 := by
        rw [← map_mul, ← map_one (ultraMap U A)]
        apply (ultraMap_eq_iff U A _ _).mpr
        exact hf.mono (fun i hi => inv_mul_cancel₀ hi)
      exact ⟨⟨ultraMap U A f, ultraMap U A g, hfg, hgf⟩, rfl⟩)

instance [∀ i, CharZero (A i)] : CharZero (DivisionUltraproduct U A) where
  cast_injective m n h := by
    have he : ultraMap U A (m : ∀ i, A i) = ultraMap U A (n : ∀ i, A i) := by
      simpa using h
    obtain ⟨i, hi⟩ := ((ultraMap_eq_iff U A _ _).mp he).exists
    exact Nat.cast_injective (R := A i) hi

end KuroshConstruction

end OAI
