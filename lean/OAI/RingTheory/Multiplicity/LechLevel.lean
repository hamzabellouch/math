import Mathlib
import OAI.RingTheory.Multiplicity.FiniteComplexTopInclusion

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech
universe u
variable {R : Type u} [CommRing R]
namespace IdealFiltration

def level (I J : Ideal R) (n : ℕ) : Ideal R := I ^ n ⊔ J

def next (I J : Ideal R) (n : ℕ) : Submodule R (level I J n) :=
  Submodule.comap (level I J n).subtype (level I J (n + 1))

abbrev Piece (I J : Ideal R) (n : ℕ) := level I J n ⧸ next I J n

lemma level_succ_le (I J : Ideal R) (n : ℕ) : level I J (n + 1) ≤ level I J n :=
  sup_le_sup_right (Ideal.pow_le_pow_right (Nat.le_succ n)) _

def inclusion (I J : Ideal R) (n : ℕ) : Piece I J n →ₗ[R] R ⧸ level I J (n + 1) :=
  (next I J n).liftQ (((level I J (n + 1)).mkQ).comp (level I J n).subtype) (by
    intro x hx
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, next, Submodule.mem_comap] using hx)

lemma inclusion_injective (I J : Ideal R) (n : ℕ) :
    Function.Injective (inclusion I J n) := by
  rw [← LinearMap.ker_eq_bot, inclusion, Submodule.ker_liftQ_eq_bot]
  simpa only [LinearMap.ker_comp, Submodule.ker_mkQ, next] using (le_refl (next I J n))

def transition (I J : Ideal R) (n : ℕ) :
    (R ⧸ level I J (n + 1)) →ₗ[R] R ⧸ level I J n :=
  (level I J (n + 1)).mapQ (level I J n) LinearMap.id (level_succ_le I J n)

lemma transition_surjective (I J : Ideal R) (n : ℕ) :
    Function.Surjective (transition I J n) := by
  intro x
  obtain ⟨a, rfl⟩ := (level I J n).mkQ_surjective x
  exact ⟨(level I J (n + 1)).mkQ a, rfl⟩

lemma piece_exact (I J : Ideal R) (n : ℕ) :
    Function.Exact (inclusion I J n) (transition I J n) := by
  rw [LinearMap.exact_iff]
  simp only [inclusion, transition, Submodule.ker_mapQ, Submodule.range_liftQ,
    LinearMap.range_comp, Submodule.range_subtype, Submodule.comap_id]

lemma quotient_torsion (I J : Ideal R) (n : ℕ) :
    powerTorsion I (ModuleCat.of R (R ⧸ level I J n)) := by
  refine ⟨n, ?_⟩
  rw [Ideal.annihilator_quotient]
  exact le_sup_left

lemma piece_torsion (I J : Ideal R) (n : ℕ) :
    powerTorsion I (ModuleCat.of R (Piece I J n)) := by
  have : CategoryTheory.Mono (ModuleCat.ofHom (inclusion I J n)) :=
    (ModuleCat.mono_iff_injective _).mpr (inclusion_injective I J n)
  exact powerTorsion_mono I (ModuleCat.ofHom (inclusion I J n)) (quotient_torsion I J _)

lemma length_successor (I J : Ideal R) (ℓ : TorsionLength I) (n : ℕ) :
    ℓ.value (ModuleCat.of R (R ⧸ level I J (n + 1))) =
      ℓ.value (ModuleCat.of R (Piece I J n)) +
      ℓ.value (ModuleCat.of R (R ⧸ level I J n)) :=
  ℓ.additive_linear (inclusion I J n) (transition I J n)
    (inclusion_injective I J n) (transition_surjective I J n) (piece_exact I J n)
    (quotient_torsion I J _)

lemma length_eq_sum (I J : Ideal R) (ℓ : TorsionLength I) (N : ℕ) :
    ℓ.value (ModuleCat.of R (R ⧸ level I J N)) =
      ∑ n ∈ Finset.range N, ℓ.value (ModuleCat.of R (Piece I J n)) := by
  induction N with
  | zero =>
    have hz : CategoryTheory.Limits.IsZero (ModuleCat.of R (R ⧸ level I J 0)) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      simp only [level, pow_zero, Ideal.one_eq_top, top_sup_eq]
      infer_instance
    simp [ℓ.zero hz]
  | succ N ih => rw [length_successor, ih, Finset.sum_range_succ, add_comm]

lemma length_quotient (I J : Ideal R) (ℓ : TorsionLength I)
    (N : ℕ) (hN : I ^ N ≤ J) :
    ℓ.value (ModuleCat.of R (R ⧸ J)) =
      ∑ n ∈ Finset.range N, ℓ.value (ModuleCat.of R (Piece I J n)) := by
  have h : level I J N = J := sup_eq_right.mpr hN
  exact (congrArg (fun K : Ideal R => ℓ.value (ModuleCat.of R (R ⧸ K))) h).symm.trans
    (length_eq_sum I J ℓ N)

end IdealFiltration
end Lech

open CategoryTheory
namespace Lech
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

lemma powerTorsion_quotient : powerTorsion I (ModuleCat.of R (R ⧸ I)) := by
  refine ⟨1, ?_⟩
  rw [pow_one, Ideal.annihilator_quotient]

lemma powerTorsion_pi_small {M : Type u} [AddCommGroup M] [Module R M] (ι : Type)
    (hM : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R (ι → M)) := by
  obtain ⟨a, ha⟩ := hM
  refine ⟨a, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext i
  exact Module.mem_annihilator.mp (ha hr) (x i)

namespace TorsionLength
variable (ℓ : TorsionLength I)
lemma value_fintype_small {M : Type u} [AddCommGroup M] [Module R M]
    (hM : powerTorsion I (ModuleCat.of R M)) (ι : Type) [Fintype ι] :
    ℓ.value (ModuleCat.of R (ι → M)) = Fintype.card ι • ℓ.value (ModuleCat.of R M) := by
  classical
  let e : (ι → M) ≃ₗ[R] (Fin (Fintype.card ι) → M) :=
    LinearEquiv.piCongrLeft R (fun _ => M) (Fintype.equivFin ι)
  exact (ℓ.value_linearEquiv e (powerTorsion_fin _ hM)).trans (ℓ.value_fin hM _)
end TorsionLength

namespace ResidueGenerators
variable {M : Type u} [AddCommGroup M] [Module R M]
    (hM : I ≤ Module.annihilator R M)

noncomputable def coefficient (m : M) : (R ⧸ I) →ₗ[R] M :=
  I.liftQ (LinearMap.toSpanSingleton R M m) (by
    intro r hr
    exact Module.mem_annihilator.mp (hM hr) m)

@[simp] lemma coefficient_mk (m : M) (r : R) :
    coefficient hM m (Ideal.Quotient.mk I r) = r • m := rfl

variable {ι : Type} [Fintype ι]
noncomputable def map (v : ι → M) : (ι → R ⧸ I) →ₗ[R] M :=
  (Finsupp.lsum R (fun i => coefficient hM (v i))).comp
    (Finsupp.linearEquivFunOnFinite R (R ⧸ I) ι).symm.toLinearMap

lemma generators_mem_range (v : ι → M) (i : ι) : v i ∈ (map hM v).range := by
  classical
  refine ⟨(Finsupp.linearEquivFunOnFinite R (R ⧸ I) ι) (Finsupp.single i 1), ?_⟩
  simp only [map, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    Finsupp.lsum_single]
  change (coefficient hM (v i)) (Ideal.Quotient.mk I 1) = v i
  rw [coefficient_mk, one_smul]

lemma surjective_of_span (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Function.Surjective (map hM v) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hv, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact generators_mem_range hM v i

include hM in
lemma value_le (ℓ : TorsionLength I) (v : ι → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    ℓ.value (ModuleCat.of R M) ≤ Fintype.card ι • ℓ.value (ModuleCat.of R (R ⧸ I)) := by
  have : Epi (ModuleCat.ofHom (map hM v)) :=
    (ModuleCat.epi_iff_surjective _).mpr (surjective_of_span hM v hv)
  exact (ℓ.le_of_epi (ModuleCat.ofHom (map hM v))
    (powerTorsion_pi_small _ powerTorsion_quotient)).trans_eq
      (ℓ.value_fintype_small powerTorsion_quotient _)

end ResidueGenerators
end Lech


namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma span_subquotient {ι : Type*} (P Q : Submodule R R) (hQP : Q ≤ P)
    (v : ι → P) (hv : P ≤ Submodule.span R (Set.range (fun i => (v i : R))) ⊔ Q) :
    Submodule.span R (Set.range (fun i =>
      (Submodule.comap P.subtype Q).mkQ (v i))) = ⊤ := by
  change Submodule.span R (Set.range ((Submodule.comap P.subtype Q).mkQ ∘ v)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, Submodule.map_mkQ_eq_top]
  apply Submodule.map_injective_of_injective P.injective_subtype
  rw [Submodule.map_sup, Submodule.map_comap_subtype, inf_eq_right.mpr hQP,
    Submodule.map_span, Submodule.map_subtype_top]
  change Q ⊔ Submodule.span R (P.subtype '' Set.range v) = P
  rw [← Set.range_comp]
  apply le_antisymm
  · exact sup_le hQP (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => (v i).property))
  · simpa only [sup_comm, Function.comp_def, Submodule.subtype_apply] using hv

namespace MonomialSpanning
variable {h : ℕ} (z : Fin h → R)

noncomputable def monic (d : Fin h →₀ ℕ) : R :=
  MvPolynomial.eval z (MvPolynomial.monomial d 1)

lemma span_monic_degree (n : ℕ) :
    Ideal.span (Set.range z) ^ n =
      Ideal.span (monic z '' {d : Fin h →₀ ℕ | d.degree = n}) := by
  have hm : Ideal.map (MvPolynomial.eval z) (MvPolynomial.idealOfVars (Fin h) R) =
      Ideal.span (Set.range z) := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    congr 1
    ext i
    simp [Function.comp_def]
  rw [← hm, ← Ideal.map_pow, MvPolynomial.pow_idealOfVars_eq_span, Ideal.map_span,
    ← Set.image_comp]
  rfl

lemma monic_mem_power {n : ℕ} {d : Fin h →₀ ℕ} (hd : d.degree = n) :
    monic z d ∈ Ideal.span (Set.range z) ^ n := by
  rw [span_monic_degree]
  exact Ideal.subset_span ⟨d, hd, rfl⟩

lemma monic_mem_powers {a : ℕ} {d : Fin h →₀ ℕ} (i : Fin h) (hd : a ≤ d i) :
    monic z d ∈ Ideal.span (Set.range (fun i => z i ^ a)) := by
  have hs : Finsupp.single i a ≤ d := Finsupp.single_le_iff.mpr hd
  obtain ⟨e, rfl⟩ := exists_add_of_le hs
  simp only [monic, MvPolynomial.monomial_single_add, map_mul, map_pow,
    MvPolynomial.eval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

 
def Bounded (h a n : ℕ) := {e : Fin h → Fin a // ∑ i, (e i : ℕ) = n}

noncomputable instance boundedFintype (a n : ℕ) : Fintype (Bounded h a n) := by
  classical
  unfold Bounded
  infer_instance

noncomputable def exponent {a n : ℕ} (e : Bounded h a n) : Fin h →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e.val i : ℕ))

@[simp] lemma exponent_apply {a n : ℕ} (e : Bounded h a n) (i : Fin h) :
    exponent e i = (e.val i : ℕ) := by simp [exponent]

lemma exponent_degree {a n : ℕ} (e : Bounded h a n) : (exponent e).degree = n := by
  rw [Finsupp.degree_eq_sum]
  simpa only [exponent_apply] using e.property

lemma exists_bounded {a n : ℕ} (d : Fin h →₀ ℕ) (hn : d.degree = n)
    (hd : ∀ i, d i < a) : ∃ e : Bounded h a n, exponent e = d := by
  refine ⟨⟨fun i => ⟨d i, hd i⟩, ?_⟩, ?_⟩
  · exact (Finsupp.degree_eq_sum d).symm.trans hn
  · ext i
    simp [exponent]

lemma power_le_bounded_span (a n : ℕ) :
    Ideal.span (Set.range z) ^ n ≤
      Ideal.span (Set.range (fun e : Bounded h a n => monic z (exponent e))) ⊔
      Ideal.span (Set.range (fun i => z i ^ a)) := by
  classical
  rw [span_monic_degree, Ideal.span_le]
  rintro _ ⟨d, hd, rfl⟩
  by_cases hd' : ∀ i, d i < a
  · obtain ⟨e, rfl⟩ := exists_bounded d hd hd'
    exact (show Ideal.span (Set.range (fun e : Bounded h a n => monic z (exponent e))) ≤ _ from le_sup_left) (Ideal.subset_span ⟨e, rfl⟩)
  · obtain ⟨i, hi⟩ := not_forall.mp hd'
    exact (show Ideal.span (Set.range (fun i => z i ^ a)) ≤ _ from le_sup_right) (monic_mem_powers z i (Nat.le_of_not_gt hi))

end MonomialSpanning



namespace IdealFiltration
lemma piece_annihilator (I J : Ideal R) (n : ℕ) :
    I ≤ Module.annihilator R (Piece I J n) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨x, rfl⟩ := (next I J n).mkQ_surjective x
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change r * (x : R) ∈ I ^ (n + 1) ⊔ J
  have hm : I * level I J n ≤ level I J (n + 1) := by
    simp only [level, Ideal.mul_sup, pow_succ']
    exact sup_le_sup_left Ideal.mul_le_right _
  exact hm (Ideal.mul_mem_mul hr x.property)
end IdealFiltration

namespace MonomialSpanning
variable {h : ℕ} (z : Fin h → R)

noncomputable def lift (a n : ℕ) (e : Bounded h a n) :
    IdealFiltration.level (Ideal.span (Set.range z))
      (Ideal.span (Set.range (fun i => z i ^ a))) n :=
  ⟨monic z (exponent e), (show Ideal.span (Set.range z) ^ n ≤ _ from le_sup_left)
      (monic_mem_power z (exponent_degree e))⟩

noncomputable def pieceGenerator (a n : ℕ) (e : Bounded h a n) :
    IdealFiltration.Piece (Ideal.span (Set.range z))
      (Ideal.span (Set.range (fun i => z i ^ a))) n :=
  Submodule.Quotient.mk (lift z a n e)

lemma pieceGenerator_span (a n : ℕ) :
    Submodule.span R (Set.range (pieceGenerator z a n)) = ⊤ := by
  apply span_subquotient _ _ (IdealFiltration.level_succ_le _ _ _) (lift z a n)
  apply sup_le
  · exact (power_le_bounded_span z a n).trans
      (sup_le_sup_left (show Ideal.span (Set.range (fun i => z i ^ a)) ≤
        IdealFiltration.level _ _ (n+1) from le_sup_right) _)
  · exact le_sup_of_le_right le_sup_right

lemma piece_value_le (ℓ : TorsionLength (Ideal.span (Set.range z))) (a n : ℕ) :
    ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z))
      (Ideal.span (Set.range (fun i => z i ^ a))) n)) ≤
      Fintype.card (Bounded h a n) •
        ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
  let I : Ideal R := Ideal.span (Set.range z)
  let J : Ideal R := Ideal.span (Set.range (fun i => z i ^ a))
  have hM : I ≤ Module.annihilator R (IdealFiltration.Piece I J n) :=
    IdealFiltration.piece_annihilator I J n
  exact ResidueGenerators.value_le (I := I) (M := IdealFiltration.Piece I J n)
    (ι := Bounded h a n) hM ℓ (pieceGenerator z a n) (pieceGenerator_span z a n)

lemma bounded_degree_le (a : ℕ) (e : Fin h → Fin a) :
    ∑ i, (e i : ℕ) ≤ h * a := by
  calc
    ∑ i, (e i : ℕ) ≤ ∑ _i : Fin h, a :=
      Finset.sum_le_sum fun i _ => (e i).isLt.le
    _ = h * a := by simp

noncomputable def boundedSigmaEquiv (h a : ℕ) :
    (Σ n : Fin (h*a+1), Bounded h a n) ≃ (Fin h → Fin a) where
  toFun e := e.2.val
  invFun e := ⟨⟨∑ i, (e i : ℕ), Nat.lt_succ_of_le (bounded_degree_le a e)⟩, ⟨e, rfl⟩⟩
  left_inv e := by
    rcases e with ⟨⟨n, hn⟩, ⟨e, he⟩⟩
    change ∑ i, (e i : ℕ) = n at he
    subst n
    rfl
  right_inv _ := rfl

lemma sum_bounded_card (h a : ℕ) :
    ∑ n ∈ Finset.range (h*a+1), Fintype.card (Bounded h a n) = a ^ h := by
  have hh := Fintype.card_congr (boundedSigmaEquiv h a)
  rw [Fintype.card_sigma] at hh
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [Fintype.card_fun, Fintype.card_fin] using hh

lemma powers_contain_power (a : ℕ) :
    Ideal.span (Set.range z) ^ (h*a+1) ≤ Ideal.span (Set.range (fun i => z i ^ a)) := by
  have he : IsEmpty (Bounded h a (h*a+1)) := ⟨fun e => by
    have hh := bounded_degree_le a e.val
    rw [e.property] at hh
    omega⟩
  have hh := power_le_bounded_span z a (h*a+1)
  simpa only [Set.range_eq_empty, Ideal.span_empty, bot_sup_eq] using hh

end MonomialSpanning
end Lech


namespace Lech
universe u

lemma ennreal_finite_sum_saturated {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ≥0∞) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hg : ∀ i ∈ s, g i ≠ ⊤) (hs : ∑ i ∈ s, f i = ∑ i ∈ s, g i) :
    ∀ i ∈ s, f i = g i := by
  have hf : ∀ i ∈ s, f i ≠ ⊤ := fun i hi => ne_top_of_le_ne_top (hg i hi) (hfg i hi)
  have hr : ∑ i ∈ s, (f i).toReal = ∑ i ∈ s, (g i).toReal := by
    rw [← ENNReal.toReal_sum hf, ← ENNReal.toReal_sum hg, hs]
  have he := (Finset.sum_eq_sum_iff_of_le (fun i hi =>
    (ENNReal.toReal_le_toReal (hf i hi) (hg i hi)).mpr (hfg i hi))).mp hr
  intro i hi
  exact (ENNReal.toReal_eq_toReal_iff' (hf i hi) (hg i hi)).mp (he i hi)

variable {R : Type u} [CommRing R]
namespace TorsionLength
variable {I : Ideal R} (ℓ : TorsionLength I)
lemma kernel_zero_of_surjective_value_eq
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hM : powerTorsion I (ModuleCat.of R M))
    (hfin : ℓ.value (ModuleCat.of R N) ≠ ⊤)
    (he : ℓ.value (ModuleCat.of R M) = ℓ.value (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R f.ker) = 0 := by
  have hh := ℓ.additive_linear f.ker.subtype f f.ker.injective_subtype hf
    f.exact_subtype_ker_map hM
  rw [he] at hh
  exact (ENNReal.add_left_inj hfin).mp (hh.symm.trans (zero_add _).symm)
end TorsionLength

namespace MonomialSpanning
variable {h : ℕ} (z : Fin h → R)
variable (ℓ : TorsionLength (Ideal.span (Set.range z)))

lemma piece_value_eq (a : ℕ)
    (hμ : ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≠ ⊤)
    (ha : ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))))
    (n : ℕ) (hn : n < h*a+1) :
    ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z))
      (Ideal.span (Set.range (fun i => z i ^ a))) n)) =
      Fintype.card (Bounded h a n) •
        ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
  apply ennreal_finite_sum_saturated (Finset.range (h*a+1))
      (fun n => ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z))
        (Ideal.span (Set.range (fun i => z i ^ a))) n)))
      (fun n => Fintype.card (Bounded h a n) •
        ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))))
  · intro i _
    exact piece_value_le z ℓ a i
  · intro i _
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hμ
  · rw [← IdealFiltration.length_quotient _ _ ℓ _ (powers_contain_power z a),
      Finset.sum_nsmul_assoc, sum_bounded_card, ha]
  · exact Finset.mem_range.mpr hn

lemma piece_map_kernel_zero (a : ℕ)
    (hμ : ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≠ ⊤)
    (ha : ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))))
    (n : ℕ) (hn : n < h*a+1) :
    ℓ.value (ModuleCat.of R (ResidueGenerators.map
      (IdealFiltration.piece_annihilator (Ideal.span (Set.range z))
        (Ideal.span (Set.range (fun i => z i ^ a))) n)
      (pieceGenerator z a n)).ker) = 0 := by
  have he := piece_value_eq z ℓ a hμ ha n hn
  apply ℓ.kernel_zero_of_surjective_value_eq _
    (ResidueGenerators.surjective_of_span _ _ (pieceGenerator_span z a n))
    (powerTorsion_pi_small _ powerTorsion_quotient)
  · rw [he, nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hμ
  · exact (ℓ.value_fintype_small powerTorsion_quotient _).trans he.symm

end MonomialSpanning
end Lech
end

end OAI
