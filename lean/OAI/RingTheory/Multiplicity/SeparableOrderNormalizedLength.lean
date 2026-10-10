import Mathlib
import OAI.RingTheory.Multiplicity.KoszulConeFunctor

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
namespace Lech.SeparableOrder
open Lech.RootTower Lech.PerfectDomainStages Lech.Koszul
open CategoryTheory CochainComplex HomologicalComplex
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]

local instance separableOrderCoordinatePowerSeriesIsDomain :
    IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _

include K L in
 

theorem normalizedLength_coordinate_power_koszul (a : ℕ) (ha : a ≠ 0)
    (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((tensor (((List.ofFn (fun j : Fin h =>
          (MvPowerSeries.X j : MvPowerSeries (Fin h) k)^a)).map
          (PerfectClosure.of (MvPowerSeries (Fin h) k) p)).reverse)
        (singleModule (ModuleCat.of (PerfectClosure (MvPowerSeries (Fin h) k) p)
          (PerfectClosure D p)))).homology i) = 0 := by
  let A := MvPowerSeries (Fin h) k
  let B := order A D K L
  let E := separableClosure K L
  let : CharP B p := B.val.toRingHom.charP Subtype.val_injective p
  let : CharP E p := (algebraMap E L).charP (algebraMap E L).injective p
  let P := PerfectClosure A p
  let ys : List P := ((List.ofFn (fun j : Fin h => (MvPowerSeries.X j : A)^a)).map
    (PerfectClosure.of A p)).reverse
  obtain ⟨e,he⟩ := uniform_power A D K L p
  let eqv := perfectAlgEquiv p B.val Subtype.val_injective
    ⟨e,fun d => ⟨⟨d^(p^e),he d⟩,rfl⟩⟩
  let eqh := (homologyFunctor (ModuleCat P) (.up ℤ) i).mapIso
    ((tensorFunctor ys).mapIso ((single (ModuleCat P) (.up ℤ) 0).mapIso
      eqv.toLinearEquiv.toModuleIso))
  have hnorm := (regularTower (Fin h) k p).length_eq_of_equiv eqh.toLinearEquiv
  exact hnorm.symm.trans
    (Lech.PerfectDomainStages.normalizedLength_coordinate_power_koszul h k B p K E a ha i hi)
end Lech.SeparableOrder


namespace Lech.SeparableOrder
open Lech.PerfectDomainStages Lech.RootTower Lech.Koszul CategoryTheory CategoryTheory.Limits CochainComplex
universe u
variable (h : ℕ) (k D : Type u) [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [Algebra (MvPowerSeries (Fin h) k) D]
  [IsLocalHom (algebraMap (MvPowerSeries (Fin h) k) D)]
  [Module.Finite (MvPowerSeries (Fin h) k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
  (K L : Type u) [Field K] [Field L]
  [Algebra (MvPowerSeries (Fin h) k) K] [IsFractionRing (MvPowerSeries (Fin h) k) K]
  [Algebra (MvPowerSeries (Fin h) k) L] [Algebra D L] [IsScalarTower (MvPowerSeries (Fin h) k) D L]
  [Algebra K L] [IsScalarTower (MvPowerSeries (Fin h) k) K L] [IsFractionRing D L]
  [FiniteDimensional K L] [CharP K p] [CharP L p]

local instance separableOrderParameterPowerSeriesIsDomain :
    IsDomain (MvPowerSeries (Fin h) k) := NoZeroDivisors.to_isDomain _

include K L in
 

theorem normalizedLength_parameter_koszul (ys : List D) (hlen : ys.length = h)
    (hys : (entryIdeal ys).radical = IsLocalRing.maximalIdeal D) (i : ℤ) (hi : i < 0) :
    normalizedLength (Fin h) k p
      ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries (Fin h) k) p)
        (PerfectClosure D p))).obj ((unit (ys.map (PerfectClosure.of D p))).homology i)) = 0 := by
  let A := MvPowerSeries (Fin h) k
  let P := PerfectClosure A p
  let C := PerfectClosure D p
  let f := algebraMap A D
  let Q := entryIdeal ys
  let I := (IsLocalRing.maximalIdeal A).map f
  have hIQ : I ≤ Q.radical := by
    rw [hys]
    exact IsLocalRing.map_maximalIdeal_le f
  obtain ⟨t,ht⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIQ
    (Ideal.FG.map (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A)) f)
  let a := t+1
  have ha : a ≠ 0 := Nat.succ_ne_zero t
  have hp : I^a ≤ Q := (Ideal.pow_le_pow_right (Nat.le_add_right t 1)).trans ht
  let zsA : List A := List.ofFn fun j : Fin h => (MvPowerSeries.X j : A)^a
  let zsP : List P := (zsA.map (PerfectClosure.of A p)).reverse
  let zsC : List C := zsP.map (algebraMap P C)
  let F := unit (ys.map (PerfectClosure.of D p))
  let T := regularTower (Fin h) k p
  let ell : Lech.TorsionLength (⊥ : Ideal C) := T.torsionLength (algebraMap P C) ⊥
  have hzlen : zsC.length = h := by simp [zsC,zsP,zsA]
  have hK (j : ℤ) (hj : j < 0) : ell.zeroClass ((unit zsC).homology j) := by
    refine ⟨⟨1, by simp⟩,?_⟩
    change T.length ((ModuleCat.restrictScalars (algebraMap P C)).obj
      ((unit zsC).homology j)) = 0
    change T.length ((ModuleCat.restrictScalars (algebraMap P C)).obj
      ((tensor (zsP.map (algebraMap P C)) ((single (ModuleCat C) (.up ℤ) 0).obj
        (ModuleCat.of C C))).homology j)) = 0
    rw [T.length_eq_of_equiv
      (restrictScalarsSingleTensorHomologyIso (algebraMap P C) zsP (ModuleCat.of C C) j).toLinearEquiv]
    exact normalizedLength_coordinate_power_koszul h k D p K L a ha j hj
  have hnull (b : C) (hb : b ∈ zsC) : Nonempty (Homotopy (b • 𝟙 F) 0) := by
    apply unit_nullhomotopic_of_mem
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    change w ∈ (zsA.map (PerfectClosure.of A p)).reverse at hw
    have hw' : w ∈ zsA.map (PerfectClosure.of A p) := by simpa only [List.mem_reverse] using hw
    obtain ⟨v,hv,heq⟩ := List.mem_map.mp hw'
    subst w
    change v ∈ List.ofFn (fun j : Fin h => (MvPowerSeries.X j : A)^a) at hv
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hv
    subst v
    have hm : (MvPowerSeries.X j : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [Lech.PowerSeries.maximalIdeal_eq_variables]
      exact Ideal.subset_span ⟨j,rfl⟩
    have hq : f (MvPowerSeries.X j)^a ∈ Q := hp
      (Ideal.pow_mem_pow (Ideal.mem_map_of_mem f hm) a)
    have hmap : algebraMap P C (PerfectClosure.of A p ((MvPowerSeries.X j : A)^a)) =
        PerfectClosure.of D p (f (MvPowerSeries.X j)^a) := by
      change perfectMap p f (PerfectClosure.of A p _) = _
      rw [perfectMap_of,map_pow]
    rw [hmap]
    have hspan : Q.map (PerfectClosure.of D p) = entryIdeal (ys.map (PerfectClosure.of D p)) := by
      dsimp only [Q]
      rw [entryIdeal,Ideal.map_span]
      congr 1
      ext z
      simp only [Set.mem_image,Set.mem_ofPred_eq,List.mem_map]
    rw [← hspan]
    exact Ideal.mem_map_of_mem _ hq
  have hh := Lech.acyclicity_of_koszul ell.zeroClass zsC F
    (unit_terms_free _) (unit_terms_finite _) (fun j hj => ?_) hnull hK i hi
  · exact hh.2
  · apply unit_bounded
    simpa only [F,List.length_map,hlen,hzlen] using hj
end Lech.SeparableOrder


namespace Lech.Grading
open DirectSum
variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [DecidableEq ι]
variable (G : ι → Submodule R M) [Decomposition G]
variable (f : M →ₗ[R] N)


end Lech.Grading


namespace Lech.Grading
open DirectSum
variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
  [Decomposition G] [Decomposition H]

def projection (i : ℕ) : M →ₗ[R] M :=
  (G i).subtype.comp ((DirectSum.component R ℕ (fun i => ↥(G i)) i).comp
    (decomposeLinearEquiv G).toLinearMap)

@[simp] lemma projection_apply (i : ℕ) (x : M) :
    projection G i x = (decompose G x i : M) := rfl

lemma proj_of_mem {i j : ℕ} {x : M} (hx : x ∈ G i) :
    projection G j x = if i = j then x else 0 := by
  by_cases hij : i = j
  · subst j
    simp [DirectSum.decompose_of_mem_same G hx]
  · simp [hij, DirectSum.decompose_of_mem_ne G hx hij]

variable (f : M →ₗ[R] N)
variable (hf : ∀ i, (G i).map f ≤ H (i + 1))
include hf

lemma projection_succ_comp (i : ℕ) :
    (projection H (i + 1)).comp f = f.comp (projection G i) := by
  apply DirectSum.decompose_lhom_ext G
  intro j
  apply LinearMap.ext
  intro x
  have hfx : f (x : M) ∈ H (j + 1) := hf j (Submodule.mem_map_of_mem x.property)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [proj_of_mem H hfx, proj_of_mem G x.property]
  by_cases hi : j = i <;> simp [hi]

lemma projection_zero_comp : (projection H 0).comp f = 0 := by
  apply DirectSum.decompose_lhom_ext G
  intro j
  apply LinearMap.ext
  intro x
  have hfx : f (x : M) ∈ H (j + 1) := hf j (Submodule.mem_map_of_mem x.property)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply]
  rw [proj_of_mem H hfx]
  simp

lemma ker_homogeneous : f.ker.IsHomogeneous G := by
  intro i x hx
  change f (projection G i x) = 0
  rw [← LinearMap.comp_apply, ← projection_succ_comp G H f hf,
    LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]

lemma range_homogeneous : f.range.IsHomogeneous H := by
  intro i y hy
  obtain ⟨x, rfl⟩ := hy
  cases i with
  | zero =>
      have h := DFunLike.congr_fun (projection_zero_comp G H f hf) x
      change projection H 0 (f x) ∈ f.range
      rw [show projection H 0 (f x) = 0 from h]
      exact f.range.zero_mem
  | succ i =>
      refine ⟨projection G i x, ?_⟩
      exact (DFunLike.congr_fun (projection_succ_comp G H f hf i) x).symm

def step (i : ℕ) : G i →ₗ[R] H (i + 1) :=
  (f.comp (G i).subtype).codRestrict _ fun x =>
    hf i (Submodule.mem_map_of_mem x.property)

omit [Decomposition G] [Decomposition H] in
@[simp] lemma step_apply (i : ℕ) (x : G i) :
    (step G H f hf i x : N) = f (x : M) := rfl

omit [Decomposition G] [Decomposition H] in
lemma step_ker (i : ℕ) : (step G H f hf i).ker = f.ker.comap (G i).subtype := by
  ext x
  simp [LinearMap.mem_ker, Subtype.ext_iff]

lemma step_range (i : ℕ) :
    (step G H f hf i).range = f.range.comap (H (i + 1)).subtype := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    change f x = (y : N) at hx
    refine ⟨decompose G x i, ?_⟩
    apply Subtype.ext
    change f (projection G i x) = (y : N)
    have he := DFunLike.congr_fun (projection_succ_comp G H f hf i) x
    rw [LinearMap.comp_apply, hx, proj_of_mem H y.property, ite_eq_left rfl] at he
    exact he.symm

end Lech.Grading


namespace Lech.Grading
open DirectSum Filter
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
variable (G : ℕ → Submodule K M) [Decomposition G]

lemma eventually_eq_bot [Module.Finite K M] : ∀ᶠ n in atTop, G n = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := M)
  let t := s.biUnion (fun x => (decompose G x).support)
  refine Filter.eventually_atTop.mpr ⟨t.sup id + 1, fun n hn => ?_⟩
  have hp : projection G n = 0 := by
    apply (Submodule.linearMap_eq_zero_iff_of_span_eq_top _ hs).mpr
    intro x
    have hnot : n ∉ (decompose G x.val).support := by
      intro hx
      have hnt : n ∈ t := Finset.mem_biUnion.mpr ⟨x.val, x.property, hx⟩
      have ht := Finset.le_sup (f := id) hnt
      dsimp at ht
      omega
    have hz : decompose G x.val n = 0 := DFinsupp.notMem_support_iff.mp hnot
    exact congrArg (fun z : G n => (z : M)) hz
  apply eq_bot_iff.mpr
  intro x hx
  rw [Submodule.mem_bot]
  have he := DFunLike.congr_fun hp x
  simpa [proj_of_mem G hx] using he

omit [Decomposition G] in
lemma subPiece_finrank (P : Submodule K M) (i : ℕ) :
    Module.finrank K (subPiece G P i) = Module.finrank K (P.comap (G i).subtype) := by
  let e : subPiece G P i ≃ₗ[K] P.comap (G i).subtype :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finrank_eq

variable {N : Type*} [AddCommGroup N] [Module K N]
omit [Decomposition G] in
lemma pieceMap_surjective (q : M →ₗ[K] N) (i : ℕ) :
    Function.Surjective (pieceMap G q i) := by
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

omit [Decomposition G] in
lemma pieceMap_ker (q : M →ₗ[K] N) (i : ℕ) :
    (pieceMap G q i).ker = q.ker.comap (G i).subtype := by
  ext x
  simp [LinearMap.mem_ker, Subtype.ext_iff]

lemma finrank_recurrence [∀ i, Module.Finite K (G i)]
    (f : M →ₗ[K] M) (hf : ∀ i, (G i).map f ≤ G (i + 1))
    (q : M →ₗ[K] N) (hq : q.ker = f.range) (i : ℕ) :
    Module.finrank K (G (i + 1)) + Module.finrank K (subPiece G f.ker i) =
      Module.finrank K (G i) + Module.finrank K (imagePiece G q (i + 1)) := by
  have h1 := (step G G f hf i).finrank_range_add_finrank_ker
  have h2 := (pieceMap G q (i + 1)).finrank_range_add_finrank_ker
  have he : Module.finrank K (pieceMap G q (i + 1)).range =
      Module.finrank K (imagePiece G q (i + 1)) := by
    rw [LinearMap.range_eq_top.mpr (pieceMap_surjective G q (i + 1))]
    simp
  rw [he, pieceMap_ker, hq, ← step_range G G f hf i] at h2
  rw [step_ker] at h1
  rw [subPiece_finrank]
  omega

end Lech.Grading


namespace Lech
open Polynomial Filter
open scoped BigOperators

noncomputable def sumPolynomial (p : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ p.support, Polynomial.C (p.coeff j / (j + 1 : ℚ)) *
    (Polynomial.bernoulli (j + 1) - Polynomial.C (_root_.bernoulli (j + 1)))

lemma sumPolynomial_eval (p : ℚ[X]) (n : ℕ) :
    (sumPolynomial p).eval (n : ℚ) = ∑ k ∈ Finset.range n, p.eval (k : ℚ) := by
  simp only [sumPolynomial, eval_finsetSum, eval_mul, eval_C, eval_sub]
  have h (j : ℕ) :
      Polynomial.eval (n : ℚ) (Polynomial.bernoulli (j + 1)) - _root_.bernoulli (j + 1) =
        (j + 1 : ℚ) * ∑ k ∈ Finset.range n, (k : ℚ) ^ j :=
    (Polynomial.sum_range_pow_eq_bernoulli_sub n j).symm
  simp_rw [h]
  have hn (j : ℕ) : (j + 1 : ℚ) ≠ 0 := by positivity
  simp_rw [← mul_assoc, div_mul_cancel₀ _ (hn _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  exact (Polynomial.eval_eq_sum (p := p) (x := (k : ℚ))).symm

def EventuallyPolynomial (f : ℕ → ℚ) : Prop :=
  ∃ p : ℚ[X], ∀ᶠ n in atTop, f n = p.eval (n : ℚ)

lemma eventuallyPolynomial_zero : EventuallyPolynomial (fun _ : ℕ => (0 : ℚ)) :=
  ⟨0, by simp⟩

lemma EventuallyPolynomial.add {f g : ℕ → ℚ}
    (hf : EventuallyPolynomial f) (hg : EventuallyPolynomial g) :
    EventuallyPolynomial (fun n => f n + g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, by filter_upwards [hp, hq] with n hn hm; simp [hn, hm]⟩

lemma EventuallyPolynomial.sub {f g : ℕ → ℚ}
    (hf : EventuallyPolynomial f) (hg : EventuallyPolynomial g) :
    EventuallyPolynomial (fun n => f n - g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, by filter_upwards [hp, hq] with n hn hm; simp [hn, hm]⟩

lemma EventuallyPolynomial.succ {f : ℕ → ℚ} (hf : EventuallyPolynomial f) :
    EventuallyPolynomial (fun n => f (n + 1)) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨p.comp (Polynomial.X + 1), ?_⟩
  have ht := (Filter.tendsto_add_atTop_nat 1).eventually hp
  filter_upwards [ht] with n hn
  simpa using hn

lemma EventuallyPolynomial.of_sub_succ {f : ℕ → ℚ}
    (hf : EventuallyPolynomial (fun n => f (n + 1) - f n)) :
    EventuallyPolynomial f := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hp
  let q := sumPolynomial p
  have hq (n : ℕ) : q.eval (n + 1 : ℚ) - q.eval (n : ℚ) = p.eval (n : ℚ) := by
    have he := sumPolynomial_eval p (n + 1)
    rw [Finset.sum_range_succ, ← sumPolynomial_eval p n] at he
    dsimp [q]
    push_cast at he
    linarith
  refine ⟨q + Polynomial.C (f N - q.eval (N : ℚ)), Filter.eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hstep := hN n hn
      have hqstep := hq n
      simp only [eval_add, eval_C] at ih ⊢
      push_cast
      linarith

lemma EventuallyPolynomial.of_recurrence {f k c : ℕ → ℚ}
    (hk : EventuallyPolynomial k) (hc : EventuallyPolynomial c)
    (hrec : ∀ n, f (n + 1) + k n = f n + c (n + 1)) : EventuallyPolynomial f := by
  apply EventuallyPolynomial.of_sub_succ
  have h := hc.succ.sub hk
  have he : (fun n => f (n + 1) - f n) = (fun n => c (n + 1) - k n) := by
    funext n
    linarith [hrec n]
  rwa [he]

end Lech


namespace Lech

variable {K S M : Type*} [Field K] [CommRing S] [Algebra K S]
  [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]

lemma quotient_generators {n : ℕ} (x : Fin (n + 1) → S)
    (hx : Algebra.adjoin K (Set.range x) = ⊤) :
    Algebra.adjoin K (Set.range (fun i : Fin n =>
      Ideal.Quotient.mk (Ideal.span {x 0}) (x i.succ))) = ⊤ := by
  let q := Ideal.Quotient.mkₐ K (Ideal.span {x 0})
  have he := congrArg (Subalgebra.map q) hx
  rw [AlgHom.map_adjoin, Algebra.map_top,
    (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mk_surjective)] at he
  rw [Fin.range_fin_succ, Set.image_insert_eq, ← Set.range_comp] at he
  have hzero : q (x 0) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hzero, Algebra.adjoin_insert_zero] at he
  exact he

lemma finite_of_no_generators [Module.Finite S M]
    (hx : Algebra.adjoin K (∅ : Set S) = ⊤) : Module.Finite K M := by
  have hs : Function.Surjective (algebraMap K S) := by
    apply Algebra.surjective_algebraMap_iff.mpr
    simpa only [Algebra.adjoin_empty] using hx.symm
  exact ⟨by simpa using (Module.Finite.fg_top (R := S) (M := M)).restrictScalars_of_surjective hs⟩

variable (x : S)

lemma ker_smul_killed : Module.IsTorsionBy S (LinearMap.lsmul S M x).ker x := by
  intro m
  apply Subtype.ext
  exact LinearMap.mem_ker.mp m.property

lemma coker_smul_killed : Module.IsTorsionBy S (M ⧸ (LinearMap.lsmul S M x).range) x := by
  apply (Module.isTorsionBy_quotient_iff _ _).mpr
  intro m
  exact ⟨m, rfl⟩

end Lech
end

end OAI
