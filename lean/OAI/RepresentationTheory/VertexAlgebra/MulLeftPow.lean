import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.EnergyShiftPow

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace LocalSkewFlow
open Finset
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
section Algebra
variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
lemma mulLeft_pow_apply (x y : B) (n : ℕ) :
    ((LinearMap.mulLeft R x)^n) y = x^n * y := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, ih, LinearMap.mulLeft_apply, mul_assoc]

lemma mulRight_pow_apply (x y : B) (n : ℕ) :
    ((LinearMap.mulRight R x)^n) y = y * x^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LinearMap.mulRight_apply, mul_assoc,
      ← pow_succ, pow_succ']

def commutatorOperator (x : B) : Module.End R B :=
  LinearMap.mulLeft R x + LinearMap.mulRight R (-x)

lemma commutatorOperator_apply (x y : B) : commutatorOperator (R := R) x y = x*y-y*x := by
  simp [commutatorOperator, sub_eq_add_neg]

lemma commutatorOperator_pow (x y : B) (n : ℕ) :
    (commutatorOperator (R := R) x ^ n) y =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        n.choose p.1 • (x^p.1 * y * (-x)^p.2) := by
  rw [commutatorOperator, (LinearMap.commute_mulLeft_right x (-x)).add_pow']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    mulLeft_pow_apply, mulRight_pow_apply, mul_assoc]

end Algebra

section Normalized
variable {B : Type*} [Ring B] [Algebra ℂ B]

lemma commutatorOperator_pow_normalized (x y : B) (t : ℂ) (n : ℕ) :
    (t^n / (n.factorial : ℂ)) • ((commutatorOperator (R := ℂ) x)^n) y =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        ((t^p.1 / (p.1.factorial : ℂ)) * ((-t)^p.2 / (p.2.factorial : ℂ))) •
          (x^p.1 * y * x^p.2) := by
  rw [commutatorOperator_pow, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← he]
  have hn : (-x)^p.2 = (-1 : ℂ)^p.2 • x^p.2 := by
    rw [← neg_one_smul ℂ x, smul_pow]
  rw [hn, mul_smul_comm]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul, Nat.cast_add_choose ℂ]
  have h1 : (p.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (p.2.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : ((p.1 + p.2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  congr 1
  rw [pow_add, neg_pow t p.2]
  field_simp

end Normalized

section BCHFlow
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (K T : Module.End ℂ V)

def insertedExpTerm (t : ℝ) (n : ℕ) (v : V) : UniformSpace.Completion V :=
  ((t : ℂ)^n / (n.factorial : ℂ)) • ((T ((K^n) v) : V) : UniformSpace.Completion V)

def insertedExp (t : ℝ) (v : V) : UniformSpace.Completion V :=
  ∑' n, insertedExpTerm K T t n v

lemma inner_insertedExpTerm
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (t : ℝ) (i j : ℕ) (v w : V) :
    inner ℂ (skewExpTerm K (-t) i v) (insertedExpTerm K T (-t) j w) =
      ((t : ℂ)^i / (i.factorial : ℂ)) * (((-t : ℝ) : ℂ)^j / (j.factorial : ℂ)) *
        inner ℂ v ((K^i * T * K^j) w) := by
  have hmove : inner ℂ ((K^i) v) (T ((K^j) w)) =
      (-1 : ℂ)^i * inner ℂ v ((K^i) (T ((K^j) w))) := by
    simpa using skew_pow_inner K hs i 0 v (T ((K^j) w))
  simp only [skewExpTerm, insertedExpTerm, inner_smul_left, inner_smul_right,
    UniformSpace.Completion.inner_coe, map_div₀, map_pow, Complex.conj_ofReal, map_natCast,
    hmove, Module.End.mul_apply]
  have hi : (((-t : ℝ) : ℂ)^i) * (-1 : ℂ)^i = (t : ℂ)^i := by
    rw [← mul_pow]
    simp
  calc
    _ = ((((-t : ℝ) : ℂ)^i) * (-1 : ℂ)^i) / (i.factorial : ℂ) *
        (((-t : ℝ) : ℂ)^j / (j.factorial : ℂ)) *
        inner ℂ v ((K^i) (T ((K^j) w))) := by ring
    _ = _ := by rw [hi]

lemma inner_skewExp_inserted
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (t : ℝ) (v w : V)
    (hv : Summable (fun n => ‖skewExpTerm K (-t) n v‖))
    (hw : Summable (fun n => ‖insertedExpTerm K T (-t) n w‖)) :
    inner ℂ (skewExp K (-t) v) (insertedExp K T (-t) w) =
      ∑' n, ((t : ℂ)^n / (n.factorial : ℂ)) *
        inner ℂ v (((commutatorOperator (R := ℂ) K)^n) T w) := by
  have hf : Summable (fun p : ℕ × ℕ =>
      inner ℂ (skewExpTerm K (-t) p.1 v) (insertedExpTerm K T (-t) p.2 w)) := by
    apply Summable.of_norm_bounded
      (hv.mul_of_nonneg hw (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    intro p
    exact norm_inner_le_norm _ _
  rw [skewExp, insertedExp, inner_tsum_prod _ _ hv hw, tsum_prod_antidiagonal _ hf]
  apply tsum_congr
  intro n
  simp_rw [inner_insertedExpTerm K T hs]
  have h := congrArg (fun f : Module.End ℂ V => inner ℂ v (f w))
    (commutatorOperator_pow_normalized K T (t : ℂ) n)
  simp only [LinearMap.smul_apply, inner_smul_right, LinearMap.sum_apply, inner_sum,
    Complex.ofReal_neg] at h ⊢
  exact h.symm

end BCHFlow

section InsertedEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (K T : Module.End ℂ V)

lemma insertedExpTerm_norm_bound {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    {N r : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    (hT : ∀ n : ℕ, ‖T ((K^n) v)‖ ≤ D * (1 + (N : ℝ) + n)^r * ‖(K^n) v‖)
    (t : ℝ) (n : ℕ) :
    ‖insertedExpTerm K T t n v‖ ≤
      D * (1 + (N : ℝ) + n)^r * (2 : ℝ)^N * (2 * |t| * C)^n * ‖v‖ := by
  have hn := skewExpTerm_norm_bound K hC hb t n
  have hcoef : 0 ≤ ‖(t : ℂ)^n / (n.factorial : ℂ)‖ := norm_nonneg _
  calc
    _ = ‖(t : ℂ)^n / (n.factorial : ℂ)‖ * ‖T ((K^n) v)‖ := by
      simp [insertedExpTerm, norm_smul]
    _ ≤ ‖(t : ℂ)^n / (n.factorial : ℂ)‖ *
        (D * (1 + (N : ℝ) + n)^r * ‖(K^n) v‖) := by gcongr; exact hT n
    _ = D * (1 + (N : ℝ) + n)^r * ‖skewExpTerm K t n v‖ := by
      simp only [skewExpTerm, norm_smul, UniformSpace.Completion.norm_coe]
      ring
    _ ≤ D * (1 + (N : ℝ) + n)^r * ((2 : ℝ)^N * (2 * |t| * C)^n * ‖v‖) := by
      gcongr
    _ = _ := by ring

lemma summable_norm_insertedExpTerm {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    {N r : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    (hT : ∀ n : ℕ, ‖T ((K^n) v)‖ ≤ D * (1 + (N : ℝ) + n)^r * ‖(K^n) v‖)
    {t : ℝ} (ht : 2 * |t| * C < 1) :
    Summable (fun n => ‖insertedExpTerm K T t n v‖) := by
  have hg := summable_shifted_pow_geometric (1 + (N : ℝ)) (by positivity) r
    (by positivity : 0 ≤ 2 * |t| * C) ht
  have hg' : Summable (fun n : ℕ => D * (1 + (N : ℝ) + n)^r *
      (2 : ℝ)^N * (2 * |t| * C)^n * ‖v‖) := by
    have he : (fun n : ℕ => D * (1 + (N : ℝ) + n)^r *
        (2 : ℝ)^N * (2 * |t| * C)^n * ‖v‖) =
        (fun n : ℕ => (D * (2 : ℝ)^N * ‖v‖) *
          ((1 + (N : ℝ) + n)^r * (2 * |t| * C)^n)) := by
      funext n
      ring
    rw [he]
    exact hg.mul_left (D * (2 : ℝ)^N * ‖v‖)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (insertedExpTerm_norm_bound K T hC hD hb hT t) hg'

lemma insertedExpTerm_tail_bound {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    {N r : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    (hT : ∀ n : ℕ, ‖T ((K^n) v)‖ ≤ D * (1 + (N : ℝ) + n)^r * ‖(K^n) v‖)
    (t : ℝ) (n : ℕ) (hn : N ≤ n) :
    ‖insertedExpTerm K T t n v‖ ≤
      D * (2 : ℝ)^r * (1 + (n : ℝ))^r * (4 * |t| * C)^n * ‖v‖ := by
  apply (insertedExpTerm_norm_bound K T hC hD hb hT t n).trans
  have h := shifted_pow_geometric_tail_uniform r N n hn
    (by positivity : 0 ≤ 2 * |t| * C)
  calc
    _ = D * ((2 : ℝ)^N * (1 + (N : ℝ) + n)^r * (2 * |t| * C)^n) * ‖v‖ := by ring
    _ ≤ D * ((2 : ℝ)^r * (1 + (n : ℝ))^r * (2 * (2 * |t| * C))^n) * ‖v‖ := by gcongr
    _ = _ := by congr 1; ring

end InsertedEstimates

section Tails
variable {E : Type*} [NormedAddCommGroup E]

lemma norm_tsum_tail_le {f : ℕ → E} {g : ℕ → ℝ}
    (hf : Summable (fun n => ‖f n‖)) (hg : Summable g) (hg0 : ∀ n, 0 ≤ g n)
    (N : ℕ) (H : ∀ n, N ≤ n → ‖f n‖ ≤ g n) :
    ‖∑' n, f (n + N)‖ ≤ ∑' n, g n := by
  have hfN := (summable_nat_add_iff N).mpr hf
  have hgN := (summable_nat_add_iff N).mpr hg
  apply (norm_tsum_le_tsum_norm hfN).trans
  apply (hfN.tsum_le_tsum (fun n => H (n + N) (by omega)) hgN).trans
  have hs := hg.sum_add_tsum_nat_add N
  have hpos : 0 ≤ ∑ i ∈ Finset.range N, g i := Finset.sum_nonneg (fun i _ => hg0 i)
  linarith

end Tails

section Taylor
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (K T : Module.End ℂ V)

 
def skewTaylor (t : ℝ) (N : ℕ) (v : V) : V :=
  ∑ n ∈ Finset.range N, ((t : ℂ)^n / (n.factorial : ℂ)) • (K^n) v

lemma coe_skewTaylor (t : ℝ) (N : ℕ) (v : V) :
    ((skewTaylor K t N v : V) : UniformSpace.Completion V) =
      ∑ n ∈ Finset.range N, skewExpTerm K t n v := by
  unfold skewTaylor
  change UniformSpace.Completion.toCompl (∑ n ∈ Finset.range N,
    ((t : ℂ)^n / (n.factorial : ℂ)) • (K^n) v) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact UniformSpace.Completion.coe_smul _ _

lemma coe_apply_skewTaylor (t : ℝ) (N : ℕ) (v : V) :
    (T (skewTaylor K t N v) : UniformSpace.Completion V) =
      ∑ n ∈ Finset.range N, insertedExpTerm K T t n v := by
  simp only [skewTaylor, map_sum, map_smul]
  change UniformSpace.Completion.toCompl (∑ n ∈ Finset.range N,
    ((t : ℂ)^n / (n.factorial : ℂ)) • T ((K^n) v)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact UniformSpace.Completion.coe_smul _ _

lemma skewTaylor_add_tail {t : ℝ} {N : ℕ} {v : V}
    (hf : Summable (fun n => ‖skewExpTerm K t n v‖)) :
    ((skewTaylor K t N v : V) : UniformSpace.Completion V) +
      ∑' n, skewExpTerm K t (n + N) v = skewExp K t v := by
  rw [coe_skewTaylor, skewExp]
  exact hf.of_norm.sum_add_tsum_nat_add N

lemma apply_skewTaylor_add_tail {t : ℝ} {N : ℕ} {v : V}
    (hf : Summable (fun n => ‖insertedExpTerm K T t n v‖)) :
    (T (skewTaylor K t N v) : UniformSpace.Completion V) +
      ∑' n, insertedExpTerm K T t (n + N) v = insertedExp K T t v := by
  rw [coe_apply_skewTaylor, insertedExp]
  exact hf.of_norm.sum_add_tsum_nat_add N

lemma skewExp_tail_bound {C : ℝ} (hC : 0 ≤ C) {N : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    {t : ℝ} (ht : 4 * |t| * C < 1) :
    ‖∑' n, skewExpTerm K t (n + N) v‖ ≤ (1 - 4 * |t| * C)⁻¹ * ‖v‖ := by
  have hq0 : 0 ≤ 4 * |t| * C := by positivity
  have hq : 2 * |t| * C < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hC]
  have hf := summable_norm_skewExpTerm K hC hb hq
  have hg := (summable_geometric_of_lt_one hq0 ht).mul_right ‖v‖
  have hbnd : ∀ n, N ≤ n → ‖skewExpTerm K t n v‖ ≤ (4 * |t| * C)^n * ‖v‖ := by
    intro n hn
    apply (skewExpTerm_norm_bound K hC hb t n).trans
    calc
      _ ≤ (2 : ℝ)^n * (2 * |t| * C)^n * ‖v‖ := by gcongr; norm_num
      _ = _ := by rw [← mul_pow]; congr 2; ring
  have h := norm_tsum_tail_le hf hg (fun _ => by positivity) N hbnd
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 ht] at h
  exact h

lemma skewTaylor_norm_bound
    (hs : ∀ v w, inner ℂ (K v) w = -inner ℂ v (K w))
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    {t : ℝ} (ht : 4 * |t| * C < 1) :
    ‖skewTaylor K t N v‖ ≤ (1 + (1 - 4 * |t| * C)⁻¹) * ‖v‖ := by
  have hq : 2 * |t| * C < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hC]
  have hf := summable_norm_skewExpTerm K hC hb hq
  have he := skewTaylor_add_tail K (N := N) hf
  have hne := norm_skewExp K hs t v hf
  have htbd := skewExp_tail_bound K hC hb ht
  have he' : ((skewTaylor K t N v : V) : UniformSpace.Completion V) =
      skewExp K t v - ∑' n, skewExpTerm K t (n + N) v := (eq_sub_iff_add_eq).mpr he
  rw [← UniformSpace.Completion.norm_coe, he']
  calc
    _ ≤ ‖skewExp K t v‖ + ‖∑' n, skewExpTerm K t (n + N) v‖ := norm_sub_le _ _
    _ ≤ ‖v‖ + (1 - 4 * |t| * C)⁻¹ * ‖v‖ := by rw [hne]; gcongr
    _ = _ := by ring

lemma insertedExp_tail_norm_bound {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    {N r : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    (hT : ∀ n : ℕ, ‖T ((K^n) v)‖ ≤ D * (1 + (N : ℝ) + n)^r * ‖(K^n) v‖)
    {t : ℝ} (ht : 4 * |t| * C < 1) :
    ‖∑' n, insertedExpTerm K T t (n + N) v‖ ≤
      (D * (2 : ℝ)^r * ∑' n : ℕ, (1 + (n : ℝ))^r * (4 * |t| * C)^n) * ‖v‖ := by
  have hq0 : 0 ≤ 4 * |t| * C := by positivity
  have hq : 2 * |t| * C < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hC]
  have hf := summable_norm_insertedExpTerm K T hC hD hb hT hq
  have hg₀ := summable_shifted_pow_geometric 1 (by norm_num) r hq0 ht
  have hg := (hg₀.mul_left (D * (2 : ℝ)^r)).mul_right ‖v‖
  have hbnd : ∀ n, N ≤ n → ‖insertedExpTerm K T t n v‖ ≤
      D * (2 : ℝ)^r * ((1 + (n : ℝ))^r * (4 * |t| * C)^n) * ‖v‖ := by
    intro n hn
    convert insertedExpTerm_tail_bound K T hC hD hb hT t n hn using 1; ring
  have h := norm_tsum_tail_le hf hg (fun _ => by positivity) N hbnd
  rw [tsum_mul_right, tsum_mul_left] at h
  exact h

end Taylor

end LocalSkewFlow

namespace MobiusCoefficients

 
def step (d : ℕ) : Module.End ℝ (ℤ →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun m =>
    Finsupp.single (m + 1) (((d : ℝ) - 1 - m) / 2) +
    Finsupp.single (m - 1) (((d : ℝ) - 1 + m) / 2))

def InRange (d : ℕ) (f : ℤ →₀ ℝ) : Prop :=
  ∀ m ∈ f.support, -((d : ℤ) - 1) ≤ m ∧ m ≤ (d : ℤ) - 1

def Nonnegative (f : ℤ →₀ ℝ) : Prop := ∀ m, 0 ≤ f m

def total : (ℤ →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ (fun _ => 1)

lemma step_single (d : ℕ) (m : ℤ) (c : ℝ) :
    step d (Finsupp.single m c) = c •
      (Finsupp.single (m + 1) (((d : ℝ) - 1 - m) / 2) +
       Finsupp.single (m - 1) (((d : ℝ) - 1 + m) / 2)) := by
  exact Finsupp.linearCombination_single ℝ c m

lemma total_single (m : ℤ) (x : ℝ) : total (Finsupp.single m x) = x := by
  simp [total]

lemma total_step (d : ℕ) (f : ℤ →₀ ℝ) : total (step d f) = ((d : ℝ) - 1) * total f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; ring
  | single m c =>
      rw [step_single, map_smul, map_add, total_single, total_single, total_single]
      simp only [smul_eq_mul]
      ring

lemma step_apply (d : ℕ) (f : ℤ →₀ ℝ) (m : ℤ) :
    step d f m = f.sum (fun j x => x *
      ((Finsupp.single (j + 1) (((d : ℝ) - 1 - j) / 2) : ℤ →₀ ℝ) m +
       (Finsupp.single (j - 1) (((d : ℝ) - 1 + j) / 2) : ℤ →₀ ℝ) m)) := by
  rw [step, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  apply Finsupp.sum_congr
  intro j _
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]

lemma step_range {d : ℕ} {f : ℤ →₀ ℝ} (hf : InRange d f) : InRange d (step d f) := by
  classical
  intro m hm
  by_contra h
  have hz : step d f m = 0 := by
    rw [step_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hjr := hf j hj
    have hplus : (Finsupp.single (j + 1) (((d : ℝ) - 1 - j) / 2) : ℤ →₀ ℝ) m = 0 := by
      by_cases he : j + 1 = m
      · rw [← he, Finsupp.single_eq_same]
        have heq : j = (d : ℤ) - 1 := by omega
        rw [heq]
        push_cast
        ring
      · exact Finsupp.single_eq_of_ne (Ne.symm he)
    have hminus : (Finsupp.single (j - 1) (((d : ℝ) - 1 + j) / 2) : ℤ →₀ ℝ) m = 0 := by
      by_cases he : j - 1 = m
      · rw [← he, Finsupp.single_eq_same]
        have heq : j = -((d : ℤ) - 1) := by omega
        rw [heq]
        push_cast
        ring
      · exact Finsupp.single_eq_of_ne (Ne.symm he)
    dsimp only
    rw [hplus, hminus]
    ring
  exact Finsupp.mem_support_iff.mp hm hz

lemma step_nonnegative {d : ℕ} {f : ℤ →₀ ℝ} (hr : InRange d f) (hf : Nonnegative f) :
    Nonnegative (step d f) := by
  classical
  intro m
  rw [step_apply]
  apply Finsupp.sum_nonneg
  intro j hj
  have hjr := hr j hj
  have hl : -((d : ℝ) - 1) ≤ (j : ℝ) := by exact_mod_cast hjr.1
  have hu : (j : ℝ) ≤ (d : ℝ) - 1 := by exact_mod_cast hjr.2
  apply mul_nonneg (hf j)
  apply add_nonneg
  · by_cases he : j + 1 = m
    · rw [← he, Finsupp.single_eq_same]
      linarith
    · rw [Finsupp.single_eq_of_ne (Ne.symm he)]
  · by_cases he : j - 1 = m
    · rw [← he, Finsupp.single_eq_same]
      linarith
    · rw [Finsupp.single_eq_of_ne (Ne.symm he)]

def coeff (d n : ℕ) : ℤ →₀ ℝ := (step d ^ n) (Finsupp.single 1 1)

lemma coeff_range {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : InRange d (coeff d n) := by
  induction n with
  | zero =>
      intro m hm
      have he : m = 1 := by simpa [coeff] using hm
      subst m
      constructor <;> omega
  | succ n ih => simpa only [coeff, pow_succ', Module.End.mul_apply] using step_range ih

lemma coeff_nonnegative {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : Nonnegative (coeff d n) := by
  induction n with
  | zero => intro m; simp [coeff, Finsupp.single_apply]; split_ifs <;> norm_num
  | succ n ih =>
      simpa only [coeff, pow_succ', Module.End.mul_apply] using
        step_nonnegative (coeff_range hd n) ih

lemma total_coeff (d n : ℕ) : total (coeff d n) = ((d : ℝ) - 1)^n := by
  induction n with
  | zero => simp [coeff, total_single]
  | succ n ih =>
      simp only [coeff, pow_succ', Module.End.mul_apply]
      rw [total_step]
      change ((d : ℝ) - 1) * total (coeff d n) = _
      rw [ih]

lemma coeff_le_total {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (m : ℤ) :
    coeff d n m ≤ ((d : ℝ) - 1)^n := by
  classical
  rw [← total_coeff]
  by_cases hm : m ∈ (coeff d n).support
  · change coeff d n m ≤ (coeff d n).sum (fun _ x => x • (1 : ℝ))
    simpa only [Finsupp.sum, smul_eq_mul, mul_one] using
      (Finset.single_le_sum (fun j _ => coeff_nonnegative hd n j) hm)
  · rw [Finsupp.notMem_support_iff.mp hm]
    change 0 ≤ (coeff d n).sum (fun _ x => x • (1 : ℝ))
    apply Finsupp.sum_nonneg
    intro i _
    simpa using coeff_nonnegative hd n i

lemma coeff_one_zero (d : ℕ) : coeff d 1 0 = (d : ℝ) / 2 := by
  simp [coeff, step_single]

 
def mean (d : ℕ) (t : ℝ) : ℝ := ∑' n, t^n / (n.factorial : ℝ) * coeff d n 0

lemma summable_mean {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun n => t^n / (n.factorial : ℝ) * coeff d n 0) := by
  have hd0 : 0 ≤ (d : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) ≤ (d : ℤ) - 1 by omega)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (coeff_nonnegative hd n 0)) _
    (Real.summable_pow_div_factorial (t * ((d : ℝ) - 1)))
  intro n
  calc
    _ ≤ t^n / (n.factorial : ℝ) * ((d : ℝ) - 1)^n := by
      gcongr
      exact coeff_le_total hd n 0
    _ = _ := by rw [mul_pow]; ring

lemma mean_pos {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (ht : 0 < t) : 0 < mean d t := by
  have hsum := summable_mean hd ht.le
  have hle := hsum.le_tsum 1 (fun n _ =>
    mul_nonneg (by positivity) (coeff_nonnegative hd n 0))
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [coeff_one_zero] at hle
  norm_num only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hle
  exact lt_of_lt_of_le (by positivity) hle

section Representation
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

 
def representation (B : ℤ → E) : (ℤ →₀ ℝ) →ₗ[ℝ] E := Finsupp.linearCombination ℝ B

lemma representation_single (B : ℤ → E) (m : ℤ) (c : ℝ) :
    representation B (Finsupp.single m c) = c • B m :=
  Finsupp.linearCombination_single ℝ c m

lemma representation_step (B : ℤ → E) (L : Module.End ℝ E) (d : ℕ)
    (h : ∀ m, L (B m) = (((d : ℝ) - 1 - m) / 2) • B (m + 1) +
      (((d : ℝ) - 1 + m) / 2) • B (m - 1)) (f : ℤ →₀ ℝ) :
    L (representation B f) = representation B (step d f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m c =>
      rw [representation_single, map_smul, h, step_single, map_smul,
        map_add, representation_single, representation_single]

lemma representation_coeff (B : ℤ → E) (L : Module.End ℝ E) (d : ℕ)
    (h : ∀ m, L (B m) = (((d : ℝ) - 1 - m) / 2) • B (m + 1) +
      (((d : ℝ) - 1 + m) / 2) • B (m - 1)) (n : ℕ) :
    (L^n) (B 1) = representation B (coeff d n) := by
  induction n with
  | zero => simp [coeff, representation_single]
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, ih, representation_step B L d h]
      simp only [coeff, pow_succ', Module.End.mul_apply]

 
lemma diagonal_representation (B : ℤ → E) (l : E →ₗ[ℝ] ℂ)
    (h : ∀ m : ℤ, m ≠ 0 → l (B m) = 0) (f : ℤ →₀ ℝ) :
    l (representation B f) = (f 0) • l (B 0) := by
  classical
  rw [representation, Finsupp.linearCombination_apply, map_finsuppSum]
  simp only [map_smul]
  rw [Finsupp.sum_eq_single 0]
  · intro m _ hm
    rw [h m hm, smul_zero]
  · simp

end Representation

end MobiusCoefficients

namespace CFTTypeVOA

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
