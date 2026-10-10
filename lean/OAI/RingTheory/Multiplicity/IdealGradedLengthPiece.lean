import Mathlib
import OAI.RingTheory.Multiplicity.LechHilbertSerre

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.IdealGraded
open Filter
variable {R : Type*} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
lemma length_piece_eq_length (I : Ideal R) (n : ℕ) :
    Module.length R (Piece I n) = Module.length (R ⧸ I) (Piece I n) := by
  apply Module.length_eq_of_surjective
  simpa only [Ideal.Quotient.algebraMap_eq] using
    (Ideal.Quotient.mk_surjective (I := I))

lemma eventuallyPolynomial_piece_length (I : Ideal R) [IsArtinianRing (R ⧸ I)] :
    Lech.EventuallyPolynomial (fun n => ((Module.length R (Piece I n)).toNat : ℚ)) := by
  obtain ⟨n, x, hx, hxmem⟩ := exists_generators I
  have h := Lech.LengthHilbert.hilbertSerre (R ⧸ I) n (Ring I) (Ring I) x hx
    (grade I) (by
      intro j i m hm
      simpa only [smul_eq_mul, add_comm] using grade_mul I (hxmem j) hm)
  have he (n : ℕ) : Module.length R (Piece I n) = Module.length (R ⧸ I) (grade I n) := by
    rw [length_piece_eq_length]
    exact (pieceEquiv I n).length_eq
  simpa only [he] using h

lemma eventuallyPolynomial_length_of_artinian (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] :
    Lech.EventuallyPolynomial (fun n => ((Module.length R (R ⧸ I ^ n)).toNat : ℚ)) := by
  have hfin (n : ℕ) : Module.length R (Piece I n) ≠ ⊤ := by
    rw [length_piece_eq_length]
    exact Module.length_ne_top
  have hsum (N : ℕ) : Module.length R (R ⧸ I ^ N) ≠ ⊤ := by
    rw [length_eq_sum]
    exact ENat.sum_ne_top.mpr (fun n _ => hfin n)
  apply Lech.EventuallyPolynomial.of_sub_succ
  have he : (fun n => ((Module.length R (R ⧸ I ^ (n + 1))).toNat : ℚ) -
      ((Module.length R (R ⧸ I ^ n)).toNat : ℚ)) =
      (fun n => ((Module.length R (Piece I n)).toNat : ℚ)) := by
    funext n
    rw [length_successor, ENat.toNat_add (hfin n) (hsum n), Nat.cast_add,
      add_sub_cancel_right]
  rw [he]
  exact eventuallyPolynomial_piece_length I
end Lech.IdealGraded


namespace Lech.Primary
open Filter
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma artinian_quotient (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    IsArtinianRing (R ⧸ I) := by
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I
  rw [← Ideal.radical_minimalPrimes, hI, Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

lemma exists_maximal_pow_le (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∃ a : ℕ, (IsLocalRing.maximalIdeal R) ^ a ≤ I := by
  simpa only [hI] using I.exists_radical_pow_le_of_fg I.radical.fg_of_isNoetherianRing

noncomputable def colength (I : Ideal R) (N : ℕ) : ℕ :=
  (Module.length R (R ⧸ I ^ N)).toNat

lemma length_ne_top (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (N : ℕ) :
    Module.length R (R ⧸ I ^ N) ≠ ⊤ := by
  obtain ⟨a, ha⟩ := exists_maximal_pow_le I hI
  have hle := Lech.length_quotient_le R (show
    (IsLocalRing.maximalIdeal R) ^ (a * N) ≤ I ^ N by
      rw [pow_mul]
      exact pow_le_pow_left' ha N)
  exact ne_top_of_le_ne_top (Lech.quotient_length_ne_top R (a * N)) hle

lemma colength_cast (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (N : ℕ) :
    (colength I N : ℕ∞) = Module.length R (R ⧸ I ^ N) :=
  ENat.natCast_toNat (length_ne_top I hI N)

lemma colength_mono {I J : Ideal R} (hI : I.radical = IsLocalRing.maximalIdeal R)
    (hJ : J.radical = IsLocalRing.maximalIdeal R) (h : I ≤ J) (N : ℕ) :
    colength J N ≤ colength I N := by
  have hle := Lech.length_quotient_le R (pow_le_pow_left' h N)
  rw [← colength_cast I hI N, ← colength_cast J hJ N] at hle
  exact ENat.natCast_le_natCast.mp hle

lemma polynomial_bound (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∃ C : ℕ, ∀ N : ℕ, colength I N ≤ N ^ Lech.dimension R * C := by
  obtain ⟨a, ha⟩ := exists_maximal_pow_le I hI
  obtain ⟨C, hC⟩ := Lech.colength_polynomial_bound R
  refine ⟨a ^ Lech.dimension R * C, fun N => ?_⟩
  have hle := Lech.length_quotient_le R (show
    (IsLocalRing.maximalIdeal R) ^ (a * N) ≤ I ^ N by
      rw [pow_mul]
      exact pow_le_pow_left' ha N)
  rw [← colength_cast I hI N, ← Lech.colength_cast R (a * N)] at hle
  apply (ENat.natCast_le_natCast.mp hle).trans
  simpa only [mul_pow, mul_assoc, mul_left_comm] using hC (a * N)

noncomputable def normalizedColength (I : Ideal R) (N : ℕ) : ℝ :=
  (Nat.factorial (Lech.dimension R) : ℝ) * (colength I N : ℝ) / (N : ℝ) ^ Lech.dimension R

noncomputable def multiplicity (I : Ideal R) : ℝ :=
  Filter.limUnder atTop (normalizedColength I)

theorem multiplicity_is_limit (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    Tendsto (normalizedColength I) atTop (𝓝 (multiplicity I)) := by
  let := artinian_quotient I hI
  obtain ⟨L, hL⟩ := Lech.exists_div_limit_of_eventually_polynomial (colength I)
    (Lech.dimension R) (IdealGraded.eventuallyPolynomial_length_of_artinian I)
    (polynomial_bound I hI)
  have ht : Tendsto (normalizedColength I) atTop
      (𝓝 ((Nat.factorial (Lech.dimension R) : ℝ) * L)) := by
    change Tendsto (fun N => (Nat.factorial (Lech.dimension R) : ℝ) *
      (colength I N : ℝ) / (N : ℝ) ^ Lech.dimension R) atTop
        (𝓝 ((Nat.factorial (Lech.dimension R) : ℝ) * L))
    simpa only [mul_div_assoc] using
      hL.const_mul (Nat.factorial (Lech.dimension R) : ℝ)
  rw [show multiplicity I = (Nat.factorial (Lech.dimension R) : ℝ) * L from ht.limUnder_eq]
  exact ht

lemma multiplicity_nonneg (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    0 ≤ multiplicity I := by
  apply ge_of_tendsto (multiplicity_is_limit I hI)
  exact Filter.Eventually.of_forall fun N => by
    dsimp [Lech.Primary.normalizedColength]
    positivity

lemma multiplicity_antitone {I J : Ideal R} (hI : I.radical = IsLocalRing.maximalIdeal R)
    (hJ : J.radical = IsLocalRing.maximalIdeal R) (h : I ≤ J) :
    multiplicity J ≤ multiplicity I := by
  apply le_of_tendsto_of_tendsto (multiplicity_is_limit J hJ) (multiplicity_is_limit I hI)
  exact Filter.Eventually.of_forall fun N => by
    dsimp [Lech.Primary.normalizedColength]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast colength_mono hI hJ h N) (by positivity)) (by positivity)

omit [IsNoetherianRing R] in
lemma maximal_multiplicity_eq :
    multiplicity (IsLocalRing.maximalIdeal R) = Lech.multiplicity R := rfl
end Lech.Primary


namespace Lech.FrobeniusGrowth
open Filter
open scoped Topology nonZeroDivisors
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma powerIdeal_le_pow (H : Ideal R) (q : ℕ) : powerIdeal H q ≤ H^q := by
  apply Ideal.span_le.mpr
  rintro _ ⟨x,hx,rfl⟩
  exact Ideal.pow_mem_pow hx q

lemma ordinary_error_tendsto (H : Ideal R)
    (hH : H.radical = IsLocalRing.maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    Tendsto (fun q : ℕ =>
      ((Module.length R (R ⧸ (H^q ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := quotient_colength_bound H hH hg
  apply squeeze_zero' (Eventually.of_forall (fun q => by positivity))
    ((eventually_ge_atTop 1).mono (fun q hq => ?_))
    (normalized_error_tendsto H hH hg)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hb := Lech.length_quotient_le R (sup_le_sup_right (powerIdeal_le_pow H q) (Ideal.span {g}))
  have hf : Module.length R (R ⧸ (powerIdeal H q ⊔ Ideal.span {g})) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [← Nat.cast_pow,← Nat.cast_mul]; exact ENat.natCast_ne_top _) (hC q hq)
  exact_mod_cast ENat.toNat_le_toNat hb hf

end Lech.FrobeniusGrowth


namespace Lech.FrobeniusGrowth
open Filter IsLocalRing
open scoped Topology nonZeroDivisors
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma normalized_error_of_linear_containment (J : ℕ → Ideal R)
    (b : ℕ) (hb : 0 < b) (hJ : ∀ q, 1 ≤ q → (maximalIdeal R)^(b*q) ≤ J q)
    {g : R} (hg : g ∈ R⁰) :
    Tendsto (fun q : ℕ =>
      ((Module.length R (R ⧸ (J q ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R) atTop (𝓝 0) := by
  have hmul : Tendsto (fun q : ℕ => b*q) atTop atTop :=
    tendsto_atTop_mono (fun q => Nat.le_mul_of_pos_left q hb) tendsto_id
  have ht := (ordinary_error_tendsto (maximalIdeal R) (Ideal.IsPrime.radical inferInstance) hg).comp hmul
  have ht' : Tendsto (fun q : ℕ =>
      ((Module.length R (R ⧸ ((maximalIdeal R)^(b*q) ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R) atTop (𝓝 0) := by
    have h := ht.const_mul ((b : ℝ)^Lech.dimension R)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with q hq
    dsimp only [Function.comp_apply]
    rw [Nat.cast_mul,mul_pow]
    field_simp
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity))
    ((eventually_ge_atTop 1).mono (fun q hq => ?_)) ht'
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hl := Lech.length_quotient_le R (sup_le_sup_right (hJ q hq) (Ideal.span {g}))
  have hf : Module.length R (R ⧸ ((maximalIdeal R)^(b*q) ⊔ Ideal.span {g})) ≠ ⊤ :=
    ne_top_of_le_ne_top (Lech.quotient_length_ne_top R (b*q))
      (Lech.length_quotient_le R le_sup_left)
  exact_mod_cast ENat.toNat_le_toNat hl hf

omit [IsNoetherianRing R] in
lemma parameter_power_linear_containment (h : ℕ) (hh : 0 < h) (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R) (q : ℕ) (hq : 1 ≤ q) :
    (maximalIdeal R)^(h*q) ≤ Ideal.span (Set.range fun i => z i^q) := by
  have he : h*(q-1)+1 ≤ h*q := by
    calc
      _ ≤ h*(q-1)+h := Nat.add_le_add_left hh _
      _ = h*q := by rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hq]
  rw [← hz]
  exact (Ideal.pow_le_pow_right he).trans (Lech.parameter_power_cofinality h q hq z).1

lemma parameter_error_tendsto (h : ℕ) (hh : 0 < h) (z : Fin h → R)
    (hz : Ideal.span (Set.range z) = maximalIdeal R) {g : R} (hg : g ∈ R⁰) :
    Tendsto (fun q : ℕ =>
      ((Module.length R (R ⧸ (Ideal.span (Set.range fun i => z i^q) ⊔ Ideal.span {g}))).toNat : ℝ) /
        (q : ℝ)^Lech.dimension R) atTop (𝓝 0) :=
  normalized_error_of_linear_containment _ h hh (parameter_power_linear_containment h hh z hz) hg

end Lech.FrobeniusGrowth


-- Retain the namespaces exported by this module.
namespace Lech
namespace TorsionLength
end TorsionLength
namespace IdealFiltration
end IdealFiltration
end Lech

open CategoryTheory
namespace Lech
namespace ResidueGenerators
end ResidueGenerators
namespace MonomialSpanning
end MonomialSpanning
end Lech

namespace Lech
universe u
variable {R : Type u} [CommRing R]
noncomputable def ordinaryLength (I : Ideal R) : TorsionLength I where
  value M := (Module.length R M).toENNReal
  zero h := by
    have := ModuleCat.isZero_iff_subsingleton.mp h
    simp
  additive {S} h _ := by
    rw [Module.length_eq_add_of_exact S.f.hom S.g.hom
      h.moduleCat_injective_f h.moduleCat_surjective_g
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.exact),
      ENat.toENNReal_add]
end Lech


namespace Lech.RootTower
open MvPowerSeries IsLocalRing
variable {σ k : Type*} [Fintype σ] [Field k] (q : ℕ) [NeZero q]
instance expandedLocal : IsLocalRing (Expanded (σ := σ) (R := k) q) :=
  inferInstanceAs (IsLocalRing (MvPowerSeries σ k))
instance expandedLocalHom : IsLocalHom
    (algebraMap (MvPowerSeries σ k) (Expanded (σ := σ) (R := k) q)) :=
  expansion_local q

omit [Fintype σ] in
lemma expansion_residue_surjective : Function.Surjective
    (ResidueField.map (algebraMap (MvPowerSeries σ k) (Expanded (σ := σ) (R := k) q))) := by
  intro x
  obtain ⟨f,rfl⟩ := residue_surjective x
  refine ⟨residue (MvPowerSeries σ k) (C (constantCoeff f)), ?_⟩
  rw [ResidueField.map_residue]
  change residue (MvPowerSeries σ k) (expand q (NeZero.ne q) (C (constantCoeff f))) = _
  rw [expand_C]
  exact (residue_eq_constant f).symm

lemma variable_powers_colength :
    Module.length (MvPowerSeries σ k)
      (MvPowerSeries σ k ⧸ Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ k)^q))) =
      (q ^ Fintype.card σ : ℕ) := by
  have hid : (maximalIdeal (MvPowerSeries σ k)).map
      (expand (σ := σ) (R := k) q (NeZero.ne q)).toRingHom =
      Ideal.span (Set.range (fun i : σ => (X i : MvPowerSeries σ k)^q)) := by
    rw [Lech.PowerSeries.maximalIdeal_eq_variables, Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact MvPowerSeries.expand_X q (NeZero.ne q) i
  have h := fiber_length_of_basis (expansionBasis (σ := σ) (R := k) q)
    (expansion_residue_surjective (σ := σ) (k := k) q)
  change Module.length (MvPowerSeries σ k) (MvPowerSeries σ k ⧸
    (maximalIdeal (MvPowerSeries σ k)).map
      (expand q (NeZero.ne q)).toRingHom) = _ at h
  rw [hid] at h
  simpa only [Fintype.card_fun, Fintype.card_fin] using h

end Lech.RootTower


namespace Lech.PowerSeries
open MvPowerSeries IsLocalRing
variable {k : Type*} [Field k] (h : ℕ)

lemma maximal_power_colength (hh : 0 < h) (N : ℕ) (hN : 0 < N) :
    Module.length (MvPowerSeries (Fin h) k)
      (MvPowerSeries (Fin h) k ⧸ maximalIdeal (MvPowerSeries (Fin h) k)^N) =
      ((N+h-1).choose h : ℕ) := by
  let R := MvPowerSeries (Fin h) k
  let z : Fin h → R := X
  have hm : Ideal.span (Set.range z) = maximalIdeal R := maximalIdeal_eq_variables.symm
  have hμ : (ordinaryLength (Ideal.span (Set.range z))).value
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) = 1 := by
    change (Module.length R (R ⧸ Ideal.span (Set.range z))).toENNReal = 1
    let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    rw [hm, Module.length_eq_of_surjective (R := R ⧸ maximalIdeal R)
      Ideal.Quotient.mk_surjective]
    rw [Module.length_eq_one]
    simp
  have ha (a : ℕ) (ha : 0 < a) :
      (ordinaryLength (Ideal.span (Set.range z))).value
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
        a ^ h • (ordinaryLength (Ideal.span (Set.range z))).value
          (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
    let : NeZero a := ⟨ha.ne'⟩
    rw [hμ]
    change (Module.length R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))).toENNReal = _
    rw [RootTower.variable_powers_colength]
    simp
  have H := MonomialSpanning.power_colength z (ordinaryLength _) hh
    (by rw [hμ]; exact ENNReal.one_ne_top) ha N hN
  rw [hμ,nsmul_eq_mul,mul_one] at H
  change (Module.length R (R ⧸ Ideal.span (Set.range z)^N)).toENNReal = _ at H
  rw [hm] at H
  exact ENat.toENNReal_inj.mp (by simpa using H)
end Lech.PowerSeries


namespace Lech
open Filter
open scoped Topology

lemma ascFactorial_normalized_tendsto (h : ℕ) :
    Tendsto (fun n : ℕ => (n.ascFactorial h : ℝ) / (n : ℝ)^h) atTop (𝓝 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have ht : Tendsto (fun n : ℕ => ((n : ℝ) + h)/(n : ℝ)) atTop (𝓝 1) := by
      have hc : Tendsto (fun n : ℕ => (h : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have hh := hc.const_add 1
      apply (show Tendsto (fun n : ℕ => 1 + (h : ℝ)/(n : ℝ)) atTop (𝓝 1) from by
        simpa only [add_zero] using hh).congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [add_div,div_self (by exact_mod_cast hn.ne')]
    convert ht.mul ih using 1
    · funext n
      rw [Nat.ascFactorial_succ,Nat.cast_mul,Nat.cast_add,pow_succ]
      ring
    · simp

lemma binomial_normalized_tendsto (h : ℕ) :
    Tendsto (fun n : ℕ => (h.factorial : ℝ) * ((n+h-1).choose h : ℝ) /
      (n : ℝ)^h) atTop (𝓝 1) := by
  simpa only [Nat.ascFactorial_eq_factorial_mul_choose',Nat.cast_mul] using
    ascFactorial_normalized_tendsto h

end Lech
end

end OAI
