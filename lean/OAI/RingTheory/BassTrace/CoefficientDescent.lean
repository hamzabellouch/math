import Mathlib

namespace OAI

/-! Descent through countable coefficient rings. -/

open scoped Classical
noncomputable section
namespace TorsionFreeBass

/-- A countable characteristic-zero field admits an embedding in the complex numbers. -/
theorem countable_field_embeds_complex (F : Type*) [Field F] [CharZero F] [Countable F] :
    Nonempty (F →+* ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ F
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hc : Cardinal.mk ℂ = Cardinal.mk t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
      _ ht (by simp) (by simpa using Cardinal.aleph0_lt_continuum)
  have : Infinite t := by
    by_contra! h
    have : Finite t := h
    have hf := Cardinal.lt_aleph0_of_finite t
    rw [← hc, Cardinal.mk_complex] at hf
    exact (not_lt_of_ge Cardinal.aleph0_lt_continuum.le) hf
  let : Encodable s := Encodable.ofCountable s
  let j : s ↪ t := (Encodable.encode' s).trans (Infinite.natEmbedding t)
  let A := Algebra.adjoin ℚ (Set.range (fun x : s => (x : F)))
  let f : A →+* ℂ := (MvPolynomial.aeval (fun x : s => (j x : ℂ))).toRingHom.comp
    hs.1.aevalEquiv.symm.toRingHom
  have hf : Function.Injective f :=
    (algebraicIndependent_iff_injective_aeval.mp (ht.1.comp j j.injective)).comp
      hs.1.aevalEquiv.symm.injective
  let : Algebra A ℂ := f.toAlgebra
  have : FaithfulSMul A ℂ := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  have : Algebra.IsAlgebraic A F := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift : F →ₐ[A] ℂ).toRingHom⟩

/-- The countable coefficient ring itself embeds, without an embedding of the ambient domain. -/
theorem countable_domain_embeds_complex (R : Type*) [CommRing R] [IsDomain R]
    [CharZero R] [Countable R] : ∃ f : R →+* ℂ, Function.Injective f := by
  have : Countable (FractionRing R) :=
    Function.Surjective.countable (IsLocalization.mk'_surjective (nonZeroDivisors R))
  obtain ⟨f⟩ := countable_field_embeds_complex (FractionRing R)
  exact ⟨f.comp (algebraMap R (FractionRing R)),
    f.injective.comp (IsFractionRing.injective R (FractionRing R))⟩

/-- Descent of the scalar idempotent assertion from complex coefficients to a
characteristic-zero domain, using only the finitely many coefficients. -/
theorem descend_idempotents {G : Type*} [Group G]
    (hC : ∀ e : MonoidAlgebra ℂ G, e * e = e → e = 0 ∨ e = 1)
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (e : MonoidAlgebra R G) (he : e * e = e) : e = 0 ∨ e = 1 := by
  let S := e.coeff.support
  let v : S → R := fun g => e.coeff g
  let f : MvPolynomial S ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) v
  let R₀ := f.range
  have hmem (g : G) : e.coeff g ∈ R₀ := by
    by_cases h : g ∈ S
    · exact ⟨MvPolynomial.X ⟨g,h⟩, by simp [f, v]⟩
    · have hz : e.coeff g = 0 := Finsupp.notMem_support_iff.mp h
      rw [hz]
      exact R₀.zero_mem
  have : Countable (MvPolynomial S ℤ) :=
    Function.Injective.countable AddMonoidAlgebra.coeff_injective
  have : Countable R₀ := Function.Surjective.countable f.rangeRestrict_surjective
  obtain ⟨j, hj⟩ := countable_domain_embeds_complex R₀
  let a : MonoidAlgebra R₀ G := MonoidAlgebra.ofCoeff
    (Finsupp.onFinset S (fun g : G => (⟨e.coeff g, hmem g⟩ : R₀))
      (fun g hg => Finsupp.mem_support_iff.mpr (by simpa using hg)))
  let i : MonoidAlgebra R₀ G →+* MonoidAlgebra R G := MonoidAlgebra.mapRingHom G R₀.subtype
  have hi : Function.Injective i := MonoidAlgebra.map_injective R₀.subtype.toAddMonoidHom
    Subtype.val_injective
  have ha : i a = e := by ext g; rfl
  have ha' : a * a = a := hi (by rw [map_mul, ha, he])
  let k := MonoidAlgebra.mapRingHom G j
  have hk : Function.Injective k := MonoidAlgebra.map_injective j.toAddMonoidHom hj
  rcases hC (k a) (by rw [← map_mul, ha']) with hz | ho
  · left
    have : a = 0 := hk (hz.trans (map_zero k).symm)
    rw [← ha, this, map_zero]
  · right
    have : a = 1 := hk (ho.trans (map_one k).symm)
    rw [← ha, this, map_one]

end TorsionFreeBass
end

end OAI
