import Mathlib
import OAI.RingTheory.Multiplicity.IdealGradedLengthPiece

namespace OAI

noncomputable section
namespace Lech.ArtinReesLength
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (I : Ideal R) (N : Submodule R M)
abbrev induced (n : ℕ) : Submodule R N := (I^n • (⊤ : Submodule R M)).comap N.subtype
lemma internal_le_induced (n : ℕ) : I^n • (⊤ : Submodule R N) ≤ induced I N n :=
  Submodule.smul_top_le_comap_smul_top _ N.subtype
lemma exists_shift [IsNoetherianRing R] [Module.Finite R M] :
    ∃ k : ℕ, ∀ n, induced I N (n+k) ≤ I^n • (⊤ : Submodule R N) := by
  obtain ⟨k,hk⟩ := I.exists_pow_inf_eq_pow_smul N
  refine ⟨k,fun n => ?_⟩
  apply (Submodule.map_le_map_iff_of_injective N.injective_subtype _ _).mp
  rw [Submodule.map_smul'',Submodule.map_subtype_top]
  change (Submodule.comap N.subtype (I^(n+k) • (⊤ : Submodule R M))).map N.subtype ≤ _
  rw [Submodule.map_comap_eq,Submodule.range_subtype,inf_comm,hk (n+k) (Nat.le_add_left _ _),Nat.add_sub_cancel]
  exact smul_mono_right _ inf_le_right

lemma length_exact (n : ℕ) :
    Module.length R (M ⧸ I^n • (⊤ : Submodule R M)) =
      Module.length R (N ⧸ induced I N n) +
      Module.length R ((M ⧸ N) ⧸ I^n • (⊤ : Submodule R (M ⧸ N))) := by
  let P := I^n • (⊤ : Submodule R M)
  let Q := I^n • (⊤ : Submodule R (M ⧸ N))
  let f : (N ⧸ induced I N n) →ₗ[R] M ⧸ P := (induced I N n).mapQ P N.subtype le_rfl
  let g : (M ⧸ P) →ₗ[R] (M ⧸ N) ⧸ Q := P.mapQ Q N.mkQ
    (Submodule.smul_top_le_comap_smul_top _ _)
  have hf : Function.Injective f := by
    rw [←LinearMap.ker_eq_bot]
    dsimp [f]
    rw [Submodule.ker_mapQ]
    exact Submodule.mkQ_map_self _
  have hg : Function.Surjective g := by
    rw [←LinearMap.range_eq_top]
    dsimp [g]
    rw [Submodule.range_mapQ,Submodule.range_mkQ,Submodule.map_top,Submodule.range_mkQ]
  have hfg : Function.Exact f g := by
    rw [LinearMap.exact_iff]
    dsimp [f,g]
    rw [Submodule.range_mapQ,Submodule.range_subtype,Submodule.ker_mapQ]
    change (Q.comap N.mkQ).map P.mkQ = N.map P.mkQ
    rw [Submodule.comap_smul_top_of_surjective _ N.mkQ N.mkQ_surjective,
      Submodule.ker_mkQ,Submodule.map_sup,Submodule.mkQ_map_self,bot_sup_eq]
  exact Module.length_eq_add_of_exact f g hf hg hfg

lemma quotient_length_antitone {V : Type*} [AddCommGroup V] [Module R V]
    {P Q : Submodule R V} (h : P ≤ Q) : Module.length R (V ⧸ Q) ≤ Module.length R (V ⧸ P) :=
  Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

lemma length_upper (n : ℕ) :
    Module.length R (M ⧸ I^n • (⊤ : Submodule R M)) ≤
      Module.length R (N ⧸ I^n • (⊤ : Submodule R N)) +
      Module.length R ((M ⧸ N) ⧸ I^n • (⊤ : Submodule R (M ⧸ N))) := by
  rw [length_exact I N n]
  exact add_le_add (quotient_length_antitone (internal_le_induced I N n)) le_rfl

lemma exists_length_lower [IsNoetherianRing R] [Module.Finite R M] :
    ∃ k : ℕ, ∀ n,
      Module.length R (N ⧸ I^n • (⊤ : Submodule R N)) +
        Module.length R ((M ⧸ N) ⧸ I^(n+k) • (⊤ : Submodule R (M ⧸ N))) ≤
      Module.length R (M ⧸ I^(n+k) • (⊤ : Submodule R M)) := by
  obtain ⟨k,hk⟩ := exists_shift I N
  refine ⟨k,fun n => ?_⟩
  rw [length_exact I N (n+k)]
  exact add_le_add (quotient_length_antitone (hk n)) le_rfl
end Lech.ArtinReesLength

namespace Lech.ArtinReesLength
open scoped TensorProduct
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
lemma finite_quotient_length [Module.Finite R M] (I : Ideal R)
    (hI : Module.length R (R ⧸ I) ≠ ⊤) :
    Module.length R (M ⧸ I • (⊤ : Submodule R M)) ≠ ⊤ := by
  obtain ⟨c,w,hw⟩ := Module.Finite.exists_fin' R M
  let B := R ⧸ I
  let e := TensorProduct.piScalarRight R B B (Fin c)
  let w' := (w.baseChange B).comp e.symm.toLinearMap
  have hw' : Function.Surjective w' := (LinearMap.baseChange_surjective B hw).comp e.symm.surjective
  have hlen := Module.length_le_of_surjective w' hw'
  rw [Module.length_pi,ENat.card_eq_coe_fintype_card,Fintype.card_fin] at hlen
  rw [←Module.length_eq_of_surjective (R := B) Ideal.Quotient.mk_surjective,
    (TensorProduct.quotTensorEquivQuotSMul M I).length_eq] at hlen
  have hB : Module.length B B = Module.length R (R ⧸ I) := by
    rw [Module.length_eq_of_surjective (R := B) Ideal.Quotient.mk_surjective]
  rw [hB] at hlen
  exact ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top c) hI) hlen

def colength (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) : ℕ :=
  (Module.length R (M ⧸ I ^ n • (⊤ : Submodule R M))).toNat

lemma colength_cast [Module.Finite R M] (I : Ideal R)
    (hI : ∀ n : ℕ, Module.length R (R ⧸ I ^ n) ≠ ⊤) (n : ℕ) :
    (colength I M n : ℕ∞) = Module.length R (M ⧸ I ^ n • (⊤ : Submodule R M)) :=
  ENat.natCast_toNat (finite_quotient_length (M := M) (I ^ n) (hI n))

open Filter
open scoped Topology
lemma shifted_denominator {f : ℕ → ℝ} {d : ℕ} {l : ℝ}
    (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)^d) atTop (𝓝 l)) (k : ℕ) :
    Tendsto (fun n : ℕ => f n/((n+k : ℕ) : ℝ)^d) atTop (𝓝 l) := by
  have hr : Tendsto (fun n : ℕ => ((n+k : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 1) := by
    have hc : Tendsto (fun n : ℕ => (k : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have ht := hc.const_add 1
    apply (show Tendsto (fun n : ℕ => 1+(k : ℝ)/(n : ℝ)) atTop (𝓝 1) from by simpa using ht).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [Nat.cast_add,add_div,div_self (by positivity)]
  have ht := hf.div (hr.pow d) (by simp)
  simp only [one_pow,div_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  change f n/(n : ℝ)^d / (((n+k : ℕ) : ℝ)/(n : ℝ))^d = _
  rw [div_pow]
  field_simp

theorem normalized_additivity [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (N : Submodule R M)
    (hI : ∀ n : ℕ, Module.length R (R ⧸ (I ^ n)) ≠ ⊤)
    (d : ℕ) (lN lQ : ℝ)
    (hN : Tendsto (fun n : ℕ => (colength I N n : ℝ)/(n : ℝ)^d) atTop (𝓝 lN))
    (hQ : Tendsto (fun n : ℕ => (colength I (M ⧸ N) n : ℝ)/(n : ℝ)^d) atTop (𝓝 lQ)) :
    Tendsto (fun n : ℕ => (colength I M n : ℝ)/(n : ℝ)^d) atTop (𝓝 (lN+lQ)) := by
  have hu (n : ℕ) : colength I M n ≤ colength I N n + colength I (M ⧸ N) n := by
    apply ENat.natCast_le_natCast.mp
    rw [Nat.cast_add,colength_cast I hI,colength_cast I hI,colength_cast I hI]
    exact length_upper I N n
  obtain ⟨k,hk⟩ := exists_length_lower I N
  have hl (n : ℕ) : colength I N n + colength I (M ⧸ N) (n+k) ≤ colength I M (n+k) := by
    apply ENat.natCast_le_natCast.mp
    rw [Nat.cast_add,colength_cast I hI,colength_cast I hI,colength_cast I hI]
    exact hk n
  apply (tendsto_add_atTop_iff_nat k).mp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    ((shifted_denominator hN k).add (hQ.comp (tendsto_add_atTop_nat k)))
    ((hN.add hQ).comp (tendsto_add_atTop_nat k))
  · intro n
    dsimp only [Function.comp_apply]
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hl n
  · intro n
    dsimp only [Function.comp_apply]
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hu (n+k)
end Lech.ArtinReesLength
namespace Lech.PrimeFiltration
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
 
inductive Above : Submodule R M → Prop
  | top : Above ⊤
  | cons (I J : Submodule R M) (hIJ : I ≤ J) (p : Ideal R) (hp : p.IsPrime)
      (e : Nonempty ((J.map I.mkQ) ≃ₗ[R] R ⧸ p)) (tail : Above J) : Above I

lemma next [IsNoetherianRing R] (I : Submodule R M) (hI : I ≠ ⊤) :
    ∃ J : Submodule R M, I < J ∧ ∃ p : Ideal R, p.IsPrime ∧
      Nonempty ((J.map I.mkQ) ≃ₗ[R] R ⧸ p) := by
  let : Nontrivial (M ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr hI
  obtain ⟨x,hx⟩ := exists_ne (0 : M ⧸ I)
  obtain ⟨p,hp,_⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  obtain ⟨hp,y,hy⟩ := isAssociatedPrime_iff.mp hp
  let f : R →ₗ[R] M ⧸ I := LinearMap.toSpanSingleton R (M ⧸ I) y
  have hker : f.ker = p := by
    rw [hy]
    ext r
    simp only [LinearMap.mem_ker,f,LinearMap.toSpanSingleton_apply,Submodule.mem_colon_singleton,
      Submodule.mem_bot]
  have hy0 : y ≠ 0 := by
    intro hz
    apply hp.ne_top
    rw [hy,hz]
    ext r
    simp
  let J := f.range.comap I.mkQ
  have hmap : J.map I.mkQ = f.range := by
    exact Submodule.map_comap_eq_of_surjective (I.mkQ_surjective) f.range
  have hle : I ≤ J := by
    intro m hm
    change I.mkQ m ∈ f.range
    rw [Submodule.mkQ_apply,(Submodule.Quotient.mk_eq_zero I).mpr hm]
    exact Submodule.zero_mem _
  have hlt : I < J := by
    refine lt_of_le_of_ne hle ?_
    intro he
    have hz : f.range = ⊥ := by rw [←hmap,←he,Submodule.mkQ_map_self]
    have hm : y ∈ f.range := ⟨1,by simp [f]⟩
    exact hy0 (by simpa [hz] using hm)
  refine ⟨J,hlt,p,hp,?_⟩
  rw [hmap]
  have he := f.quotKerEquivRange.symm
  rw [hker] at he
  exact ⟨he⟩

theorem exists_above [IsNoetherianRing R] [Module.Finite R M] (I : Submodule R M) :
    Above I := by
  apply IsNoetherian.induction (R := R) (M := M) (P := Above) _ I
  intro I ih
  by_cases ht : I = ⊤
  · rw [ht]
    exact .top
  · obtain ⟨J,hJ,p,hp,e⟩ := next I ht
    exact .cons I J hJ.le p hp e (ih J hJ)
end Lech.PrimeFiltration
namespace Lech.ArtinReesLength
variable {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup V] [Module R V]
lemma colength_equiv (I : Ideal R) (e : M ≃ₗ[R] V) (n : ℕ) :
    colength I M n = colength I V n := by
  let P := I ^ n • (⊤ : Submodule R M)
  let Q := I ^ n • (⊤ : Submodule R V)
  let f := P.mapQ Q e.toLinearMap (Submodule.smul_top_le_comap_smul_top _ _)
  have hf : Function.Bijective f := by
    constructor
    · rw [←LinearMap.ker_eq_bot]
      dsimp [f,Q,P]
      rw [Submodule.ker_mapQ,Submodule.comap_smul_top_of_surjective _ _ e.surjective,
        LinearEquiv.ker, sup_bot_eq,Submodule.mkQ_map_self]
    · rw [←LinearMap.range_eq_top]
      dsimp [f]
      rw [Submodule.range_mapQ,LinearEquiv.range,Submodule.map_top,Submodule.range_mkQ]
  exact congrArg ENat.toNat (LinearEquiv.ofBijective f hf).length_eq

lemma cyclic_colength (I p : Ideal R) (n : ℕ) :
    colength I (R ⧸ p) n = Lech.Primary.colength (I.map (Ideal.Quotient.mk p)) n := by
  unfold colength Lech.Primary.colength
  congr 1
  rw [Ideal.smul_top_eq_map,Ideal.map_pow]
  rw [(Submodule.Quotient.restrictScalarsEquiv R _).length_eq]
  exact (Module.length_eq_of_surjective (R := R ⧸ p)
    (M := (R ⧸ p) ⧸ (I.map (Ideal.Quotient.mk p)) ^ n) Ideal.Quotient.mk_surjective)
end Lech.ArtinReesLength

namespace Lech.PrimeFiltration
open Filter IsLocalRing
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
local instance quotient_local (p : Ideal R) [p.IsPrime] : IsLocalRing (R ⧸ p) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

omit [IsNoetherianRing R] in
lemma primary_quotient (I p : Ideal R) [p.IsPrime] (hI : I.radical = maximalIdeal R) :
    (I.map (Ideal.Quotient.mk p)).radical = maximalIdeal (R ⧸ p) := by
  let : IsLocalHom (Ideal.Quotient.mk p) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  apply le_antisymm
  · apply (maximalIdeal.isMaximal _).isPrime.radical_le_iff.mpr
    exact (Ideal.map_mono (Ideal.le_radical.trans hI.le)).trans
      (map_maximalIdeal_le (Ideal.Quotient.mk p))
  · rw [←map_maximalIdeal_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective]
    rw [←hI]
    exact Ideal.map_radical_le (Ideal.Quotient.mk p)

lemma quotient_dimension_le (p : Ideal R) (hp : p.IsPrime) :
    Lech.dimension (R ⧸ p) ≤ Lech.dimension R := by
  let : p.IsPrime := hp
  apply (Nat.cast_le (α := WithBot ℕ∞)).mp
  rw [Lech.dimension_cast,Lech.dimension_cast]
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

lemma primary_unscaled_limit (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    Tendsto (fun n : ℕ => (Lech.Primary.colength I n : ℝ)/(n : ℝ)^Lech.dimension R)
      atTop (𝓝 (Lech.Primary.multiplicity I / ((Lech.dimension R).factorial : ℝ))) := by
  have h := (Lech.Primary.multiplicity_is_limit I hI).div_const
    ((Lech.dimension R).factorial : ℝ)
  apply h.congr
  intro n
  dsimp [Lech.Primary.normalizedColength]
  have hfac : (((Lech.dimension R).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

lemma lower_dimension_limit {f : ℕ → ℝ} {e d : ℕ} {l : ℝ} (hed : e < d)
    (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)^e) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => f n/(n : ℝ)^d) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => (n : ℝ)^(d-e)) atTop atTop :=
    (tendsto_pow_atTop (by omega : d-e ≠ 0)).comp tendsto_natCast_atTop_atTop
  have ht := hf.div_atTop hg
  apply ht.congr
  intro n
  rw [div_div,←pow_add,Nat.add_sub_cancel' hed.le]

noncomputable def contribution (I p : Ideal R) : ℝ := by
  classical
  exact if hp : p.IsPrime then
    letI : p.IsPrime := hp
    if Lech.dimension (R ⧸ p) = Lech.dimension R then
      Lech.Primary.multiplicity (I.map (Ideal.Quotient.mk p)) /
        ((Lech.dimension R).factorial : ℝ) else 0
  else 0

lemma cyclic_limit (I p : Ideal R) (hI : I.radical = maximalIdeal R) (hp : p.IsPrime) :
    Tendsto (fun n : ℕ => (Lech.ArtinReesLength.colength I (R ⧸ p) n : ℝ)/
      (n : ℝ)^Lech.dimension R) atTop (𝓝 (contribution I p)) := by
  let : p.IsPrime := hp
  simp_rw [Lech.ArtinReesLength.cyclic_colength]
  have ht := primary_unscaled_limit (I.map (Ideal.Quotient.mk p)) (primary_quotient I p hI)
  rw [contribution,dite_eq_left hp]
  split_ifs with hd
  · simpa only [hd] using ht
  · exact lower_dimension_limit (lt_of_le_of_ne (quotient_dimension_le p hp) hd) ht
end Lech.PrimeFiltration

namespace Lech.PrimeFiltration
open Filter IsLocalRing
open scoped Topology
variable {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem limit_of_above (I : Ideal R) (hI : I.radical = maximalIdeal R)
    (N : Submodule R M) (hN : Above N) :
    ∃ ps : List (Ideal R), (∀ p ∈ ps, p.IsPrime) ∧
      Tendsto (fun n : ℕ => (Lech.ArtinReesLength.colength I (M ⧸ N) n : ℝ)/
        (n : ℝ)^Lech.dimension R) atTop (𝓝 ((ps.map (contribution I)).sum)) := by
  induction hN with
  | top =>
    refine ⟨[],by simp,?_⟩
    simp [Lech.ArtinReesLength.colength]
  | cons N J hNJ p hp e tail ih =>
    obtain ⟨ps,hps,hlim⟩ := ih
    obtain ⟨e⟩ := e
    refine ⟨p::ps,?_,?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact hps q hq
    · have hsub : Tendsto (fun n : ℕ =>
          (Lech.ArtinReesLength.colength I (J.map N.mkQ) n : ℝ)/(n : ℝ)^Lech.dimension R)
          atTop (𝓝 (contribution I p)) := by
        simpa only [Lech.ArtinReesLength.colength_equiv I e] using cyclic_limit I p hI hp
      have hquot : Tendsto (fun n : ℕ =>
          (Lech.ArtinReesLength.colength I ((M ⧸ N) ⧸ J.map N.mkQ) n : ℝ)/
            (n : ℝ)^Lech.dimension R) atTop (𝓝 ((ps.map (contribution I)).sum)) := by
        simpa only [Lech.ArtinReesLength.colength_equiv I
          (Submodule.quotientQuotientEquivQuotient N J hNJ)] using hlim
      simpa only [List.map_cons,List.sum_cons] using
        Lech.ArtinReesLength.normalized_additivity I (J.map N.mkQ)
          (Lech.Primary.length_ne_top I hI) (Lech.dimension R) _ _ hsub hquot

 

theorem exists_limit_decomposition (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    ∃ ps : List (Ideal R), (∀ p ∈ ps, p.IsPrime) ∧
      Tendsto (fun n : ℕ => (Lech.ArtinReesLength.colength I M n : ℝ)/
        (n : ℝ)^Lech.dimension R) atTop (𝓝 ((ps.map (contribution I)).sum)) := by
  obtain ⟨ps,hps,ht⟩ := limit_of_above I hI (⊥ : Submodule R M) (exists_above ⊥)
  refine ⟨ps,hps,?_⟩
  simpa only [Lech.ArtinReesLength.colength_equiv I (Submodule.quotEquivOfEqBot _ rfl)] using ht
end Lech.PrimeFiltration

namespace Lech.LocalizationLength
open scoped TensorProduct
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]
lemma tensor_length_exact [Module.Flat R S] (N : Submodule R M) :
    Module.length S (S ⊗[R] M) = Module.length S (S ⊗[R] N) +
      Module.length S (S ⊗[R] (M ⧸ N)) := by
  exact Module.length_eq_add_of_exact (N.subtype.baseChange S) (N.mkQ.baseChange S)
    (Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype)
    (LinearMap.baseChange_surjective S N.mkQ_surjective)
    (Module.Flat.lTensor_exact S (by
      rw [LinearMap.exact_iff,Submodule.ker_mkQ,Submodule.range_subtype]))

lemma tensor_cyclic_length (p : Ideal R) :
    Module.length S (S ⊗[R] (R ⧸ p)) =
      Module.length S (S ⧸ p.map (algebraMap R S)) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S p).toLinearEquiv.length_eq.symm

variable (p : Ideal R) [p.IsPrime]
lemma local_cyclic_self :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] (R ⧸ p)) = 1 := by
  rw [tensor_cyclic_length,IsLocalization.AtPrime.map_eq_maximalIdeal]
  let S := Localization.AtPrime p
  have : IsSimpleModule S (S ⧸ IsLocalRing.maximalIdeal S) :=
    isSimpleModule_iff_quot_maximal.mpr
      ⟨IsLocalRing.maximalIdeal S, inferInstance, ⟨LinearEquiv.refl S _⟩⟩
  exact Module.length_eq_one _ _

lemma local_cyclic_zero (q : Ideal R) (hqp : ¬ q ≤ p) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] (R ⧸ q)) = 0 := by
  rw [tensor_cyclic_length]
  have he : q.map (algebraMap R (Localization.AtPrime p)) = ⊤ :=
    IsLocalization.map_eq_top_of_not_subset (M := p.primeCompl) (S := Localization.AtPrime p)
      (by
        intro hs
        apply hqp
        intro x hx
        exact not_not.mp (hs hx))
  rw [he]
  exact Module.length_eq_zero
end Lech.LocalizationLength
namespace Lech.PrimeFiltration
open IsLocalRing
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
local instance prime_quotient_local (p : Ideal R) [p.IsPrime] : IsLocalRing (R ⧸ p) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

lemma eq_of_le_full_dim (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    (hd : Lech.dimension (R ⧸ p) = Lech.dimension R) (hqp : q ≤ p) : q = p := by
  by_contra hne
  obtain ⟨x,hxp,hxq⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hqp hne)
  have hx0 : Ideal.Quotient.mk q x ≠ 0 := by
    simpa only [ne_eq,Ideal.Quotient.eq_zero_iff_mem] using hxq
  have hb := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hqp)
    (Ideal.Quotient.factor_surjective hqp) (mem_nonZeroDivisors_iff_ne_zero.mpr hx0)
    (by rw [Ideal.Quotient.factor_mk]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hxp)
  rw [←Lech.dimension_cast (R ⧸ p),←Lech.dimension_cast (R ⧸ q)] at hb
  have hb' : Lech.dimension (R ⧸ p)+1 ≤ Lech.dimension (R ⧸ q) := by exact_mod_cast hb
  have hc := quotient_dimension_le q (inferInstance : q.IsPrime)
  omega

lemma full_dim_minimal (p : Ideal R) [p.IsPrime]
    (hd : Lech.dimension (R ⧸ p) = Lech.dimension R) : IsMinimalPrime p := by
  rw [IsMinimalPrime.iff_minimal]
  refine ⟨inferInstance,?_⟩
  intro q hq hqp
  let : q.IsPrime := hq
  exact (eq_of_le_full_dim p q hd hqp).ge
end Lech.PrimeFiltration
namespace Lech.PrimeFiltration
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
inductive Factors : Submodule R M → List (Ideal R) → Prop
  | top : Factors ⊤ []
  | cons (N J : Submodule R M) (hNJ : N ≤ J) (p : Ideal R) (hp : p.IsPrime)
      (e : Nonempty ((J.map N.mkQ) ≃ₗ[R] R ⧸ p)) {ps : List (Ideal R)}
      (tail : Factors J ps) : Factors N (p::ps)

lemma factors_of_above {N : Submodule R M} (h : Above N) : ∃ ps, Factors N ps := by
  induction h with
  | top => exact ⟨[],.top⟩
  | cons N J hNJ p hp e tail ih =>
    obtain ⟨ps,hps⟩ := ih
    exact ⟨p::ps,.cons N J hNJ p hp e hps⟩

lemma Factors.isPrime {N : Submodule R M} {ps : List (Ideal R)} (h : Factors N ps) :
    ∀ p ∈ ps, p.IsPrime := by
  induction h with
  | top => simp
  | cons N J hNJ q hq e tail ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hq
    · exact ih p hp

open scoped TensorProduct
lemma Factors.tensor_length (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]
    {N : Submodule R M} {ps : List (Ideal R)} (h : Factors N ps) :
    Module.length S (S ⊗[R] (M ⧸ N)) =
      (ps.map (fun p => Module.length S (S ⊗[R] (R ⧸ p)))).sum := by
  induction h with
  | top => simp
  | @cons N J hNJ p hp e qs tail ih =>
    obtain ⟨e⟩ := e
    rw [Lech.LocalizationLength.tensor_length_exact (J.map N.mkQ),
      (e.baseChange R S _ _).length_eq,
      ((Submodule.quotientQuotientEquivQuotient N J hNJ).baseChange R S _ _).length_eq,ih]
    rfl

lemma Factors.localized_length {N : Submodule R M} {ps : List (Ideal R)}
    (h : Factors N ps) (p : Ideal R) [p.IsPrime] (hp : IsMinimalPrime p) :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] (M ⧸ N)) =
      (ps.count p : ℕ∞) := by
  classical
  rw [h.tensor_length (Localization.AtPrime p)]
  have he (q : Ideal R) (hq : q ∈ ps) :
      Module.length (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] (R ⧸ q)) =
        if q = p then 1 else 0 := by
    split_ifs with hqp
    · subst q
      exact Lech.LocalizationLength.local_cyclic_self p
    · apply Lech.LocalizationLength.local_cyclic_zero p q
      intro hle
      exact hqp (le_antisymm hle (((IsMinimalPrime.iff_minimal p).mp hp).2 (h.isPrime q hq) hle))
  rw [List.map_congr_left he]
  have hcount (qs : List (Ideal R)) :
      (qs.map (fun q => if q = p then (1 : ℕ∞) else 0)).sum = (qs.count p : ℕ∞) := by
    induction qs with
    | nil => simp
    | cons q qs ih =>
      by_cases hqp : q = p
      · subst q
        simp [ih,add_comm]
      · simp [hqp,ih]
  exact hcount ps

open Filter IsLocalRing
open scoped Topology
variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
lemma Factors.colength_limit {N : Submodule R M} {ps : List (Ideal R)} (h : Factors N ps)
    (I : Ideal R) (hI : I.radical = maximalIdeal R) :
    Tendsto (fun n : ℕ => (Lech.ArtinReesLength.colength I (M ⧸ N) n : ℝ)/
      (n : ℝ)^Lech.dimension R) atTop (𝓝 ((ps.map (contribution I)).sum)) := by
  induction h with
  | top => simp [Lech.ArtinReesLength.colength]
  | @cons N J hNJ p hp e qs tail ih =>
    obtain ⟨e⟩ := e
    have hsub : Tendsto (fun n : ℕ =>
        (Lech.ArtinReesLength.colength I (J.map N.mkQ) n : ℝ)/(n : ℝ)^Lech.dimension R)
        atTop (𝓝 (contribution I p)) := by
      simpa only [Lech.ArtinReesLength.colength_equiv I e] using cyclic_limit I p hI hp
    have hquot : Tendsto (fun n : ℕ =>
        (Lech.ArtinReesLength.colength I ((M ⧸ N) ⧸ J.map N.mkQ) n : ℝ)/
          (n : ℝ)^Lech.dimension R) atTop (𝓝 ((qs.map (contribution I)).sum)) := by
      simpa only [Lech.ArtinReesLength.colength_equiv I
        (Submodule.quotientQuotientEquivQuotient N J hNJ)] using ih
    simpa only [List.map_cons,List.sum_cons] using
      Lech.ArtinReesLength.normalized_additivity I (J.map N.mkQ)
        (Lech.Primary.length_ne_top I hI) (Lech.dimension R) _ _ hsub hquot
end Lech.PrimeFiltration

end

end OAI
