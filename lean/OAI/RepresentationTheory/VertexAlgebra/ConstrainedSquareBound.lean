import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.EnergyCutoff

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace SharpCombinatorics

theorem constrained_square_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (P : ι → κ → Prop) [DecidableRel P]
    (A : ι → ℝ) (B : κ → ℝ) (L R : ℝ)
    (hL : ∀ j ∈ t, ((s.filter (fun i => P i j)).card : ℝ) ≤ L)
    (hR : ∀ i ∈ s, ((t.filter (P i)).card : ℝ) ≤ R) :
    (∑ i ∈ s, ∑ j ∈ t with P i j, A i * B j)^2 ≤
      (R * ∑ i ∈ s, (A i)^2) * (L * ∑ j ∈ t, (B j)^2) := by
  let u := (s ×ˢ t).filter (fun p => P p.1 p.2)
  have he : (∑ i ∈ s, ∑ j ∈ t with P i j, A i * B j) =
      ∑ p ∈ u, A p.1 * B p.2 := by
    simp only [u, Finset.sum_filter]
    rw [Finset.sum_product]
  rw [he]
  have ha : ∑ p ∈ u, (A p.1)^2 ≤ R * ∑ i ∈ s, (A i)^2 := by
    dsimp [u]
    rw [Finset.sum_filter, Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ = ((t.filter (P i)).card : ℝ) * (A i)^2 := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hR i hi) (sq_nonneg _)
  have hb : ∑ p ∈ u, (B p.2)^2 ≤ L * ∑ j ∈ t, (B j)^2 := by
    dsimp [u]
    rw [Finset.sum_filter, Finset.sum_product, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      _ = ((s.filter (fun i => P i j)).card : ℝ) * (B j)^2 := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hL j hj) (sq_nonneg _)
  calc
    _ ≤ (∑ p ∈ u, (A p.1)^2) * (∑ p ∈ u, (B p.2)^2) :=
      Finset.sum_mul_sq_le_sq_mul_sq u (fun p => A p.1) (fun p => B p.2)
    _ ≤ _ := mul_le_mul ha hb (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by
      exact (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans ha)

 

theorem card_tuple_sum_le (q J : ℕ) (c : ℕ) :
    ((Finset.univ : Finset (Fin (q + 1) → Fin J)).filter
      (fun x => ∑ i, (x i).val = c)).card ≤ J^q := by
  let s := ((Finset.univ : Finset (Fin (q + 1) → Fin J)).filter
    (fun x => ∑ i, (x i).val = c))
  have hinj : Set.InjOn (fun x : Fin (q + 1) → Fin J => fun i : Fin q => x i.succ) s := by
    intro x hx y hy he
    have hxsum := (Finset.mem_filter.mp hx).2
    have hysum := (Finset.mem_filter.mp hy).2
    have ht : (∑ i : Fin q, (x i.succ).val) = ∑ i : Fin q, (y i.succ).val := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg Fin.val (congrFun he i)
    rw [Fin.sum_univ_succ] at hxsum hysum
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · omega
    · exact congrArg Fin.val (congrFun he j)
  have hcard := Finset.card_le_card_of_injOn
    (fun x : Fin (q + 1) → Fin J => fun i : Fin q => x i.succ)
    (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using hcard

 

theorem sum_tuple_succ {M : Type*} [AddCommMonoid M] (q J : ℕ)
    (f : (Fin (q + 1) → Fin J) → M) :
    (∑ x, f x) = ∑ i : Fin J, ∑ x : Fin q → Fin J, f (Fin.cons i x) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (q + 1) => Fin J))
    (fun x => f (Fin.cons x.1 x.2)) f (fun _ => rfl), Fintype.sum_prod_type]

section Paths
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

 
def path {J : ℕ} : (q : ℕ) → (Fin q → Fin J → Module.End ℂ V) →
    (Fin q → Fin J) → Module.End ℂ V
  | 0, _, _ => 1
  | q + 1, T, x => path q (fun i => T i.succ) (fun i => x i.succ) * T 0 (x 0)

 

theorem sum_path_sq_le {J q : ℕ} (T : Fin q → Fin J → Module.End ℂ V)
    (E : Fin (q + 1) → Submodule ℂ V) (K : Fin q → ℝ)
    (hK : ∀ i, 0 ≤ K i)
    (hmap : ∀ i j, ∀ v ∈ E i.castSucc, T i j v ∈ E i.succ)
    (hcol : ∀ i, ∀ v ∈ E i.castSucc, ∑ j, ‖T i j v‖^2 ≤ K i * ‖v‖^2)
    {v : V} (hv : v ∈ E 0) :
    (∑ x : Fin q → Fin J, ‖path q T x v‖^2) ≤ (∏ i, K i) * ‖v‖^2 := by
  induction q generalizing v with
  | zero => simp [path]
  | succ q ih =>
    rw [sum_tuple_succ, Fin.prod_univ_succ]
    simp only [path, Fin.cons_zero, Fin.cons_succ, Module.End.mul_apply]
    have hprod : 0 ≤ ∏ i : Fin q, K i.succ := Finset.prod_nonneg fun i _ => hK i.succ
    calc
      _ ≤ ∑ j : Fin J, (∏ i : Fin q, K i.succ) * ‖T 0 j v‖^2 := by
        apply Finset.sum_le_sum
        intro j _
        exact ih (fun i => T i.succ) (fun i => E i.succ) (fun i => K i.succ)
          (fun i => hK i.succ) (fun i r w hw => hmap i.succ r w hw)
          (fun i w hw => hcol i.succ w hw) (hmap 0 j v hv)
      _ = (∏ i : Fin q, K i.succ) * ∑ j : Fin J, ‖T 0 j v‖^2 := by rw [Finset.mul_sum]
      _ ≤ (∏ i : Fin q, K i.succ) * (K 0 * ‖v‖^2) :=
        mul_le_mul_of_nonneg_left (hcol 0 v hv) hprod
      _ = _ := by ring

end Paths

end SharpCombinatorics

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

 

instance energyCutoff_finite (N : ℕ) : FiniteDimensional ℂ (A.energyCutoff N) := by
  let := A.grade_finite
  apply Submodule.finiteDimensional_of_le (S₂ := (Finset.range (N + 1)).sup A.grade)
  intro v hv
  rw [← A.cutoffProjection_of_mem hv, cutoffProjection_apply]
  apply Submodule.sum_mem
  intro d hd
  exact Finset.le_sup (f := A.grade) hd (A.gradeComponent_mem d v)

 

def positiveColumn (a : V) (d N : ℕ) :
    A.energyCutoff N →L[ℂ] PiLp 2 (fun _ : Fin (N + 1) => V) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℂ (Fin (N + 1) → V)).symm.toLinearMap.comp
      (LinearMap.pi (fun m => (A.physicalMode a d m).comp (A.energyCutoff N).subtype)))

@[simp]
theorem positiveColumn_apply (a : V) (d N : ℕ) (v : A.energyCutoff N)
    (m : Fin (N + 1)) : (A.positiveColumn a d N v).ofLp m = A.physicalMode a d m v := rfl

 
def positiveColumnNorm (a : V) (d N : ℕ) : ℝ := ‖A.positiveColumn a d N‖

theorem positiveColumnNorm_nonneg (a : V) (d N : ℕ) :
    0 ≤ A.positiveColumnNorm a d N := norm_nonneg (A.positiveColumn a d N)

theorem positiveColumn_norm_sq (a : V) (d N : ℕ) (v : A.energyCutoff N) :
    ‖A.positiveColumn a d N v‖^2 =
      ∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [positiveColumn_apply]
  exact Fin.sum_univ_eq_sum_range (fun m => ‖A.physicalMode a d m v‖^2) (N + 1)

theorem sum_positive_modes_sq_le (a : V) (d : ℕ) {N : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff N) :
    (∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2) ≤
      A.positiveColumnNorm a d N ^ 2 * ‖v‖^2 := by
  rw [← A.positiveColumn_norm_sq a d N ⟨v, hv⟩, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((A.positiveColumn a d N).le_opNorm ⟨v, hv⟩) 2

theorem physicalMode_zero_above_cutoff {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℤ) (hm : (N : ℤ) < m) :
    A.physicalMode a d m v = 0 := by
  rw [← A.cutoffProjection_of_mem hv, cutoffProjection_apply, map_sum]
  apply Finset.sum_eq_zero
  intro e he
  apply A.mode_eq_zero_of_negative_energy ha (A.gradeComponent_mem e v)
  have he := Finset.mem_range.mp he
  omega

theorem physicalMode_mem_cutoff {a : V} {d N M : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℤ) (hm : (N : ℤ) - m ≤ M) :
    A.physicalMode a d m v ∈ A.energyCutoff M := by
  rw [← A.cutoffProjection_of_mem hv, cutoffProjection_apply, map_sum]
  apply Submodule.sum_mem
  intro e he
  by_cases hem : (e : ℤ) < m
  · rw [show A.physicalMode a d m (A.gradeComponent e v) = 0 from
      A.mode_eq_zero_of_negative_energy ha (A.gradeComponent_mem e v) _ (by omega)]
    exact Submodule.zero_mem _
  · have hek : (e : ℤ) - m = ((e : ℤ) - m).toNat := by omega
    apply A.grade_le_energyCutoff (d := ((e : ℤ) - m).toNat)
      (by have he := Finset.mem_range.mp he; omega)
    exact A.mode_mem_grade ha (A.gradeComponent_mem e v) _ (by omega)

theorem positiveColumnNorm_mono (a : V) (d : ℕ) :
    Monotone (A.positiveColumnNorm a d) := by
  intro N M hNM
  apply ContinuousLinearMap.opNorm_le_bound _ (A.positiveColumnNorm_nonneg a d M)
  intro v
  have hR := A.positiveColumnNorm_nonneg a d M
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, A.positiveColumn_norm_sq]
  calc
    _ ≤ ∑ m ∈ Finset.range (M + 1), ‖A.physicalMode a d m v‖^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro i _ _
      positivity
    _ ≤ _ := A.sum_positive_modes_sq_le a d (A.energyCutoff_mono hNM v.property)

end CFTTypeVOA

lemma negative_binomial (n j : ℕ) :
    (-1 : ℂ)^j * Ring.choose (-1 - (n : ℂ)) j = ((n + j).choose n : ℂ) := by
  rw [show (-1 : ℂ) - n = -((n + 1 : ℕ) : ℂ) by push_cast; ring, Ring.choose_neg]
  have he : ((n + 1 : ℕ) : ℂ) + j - 1 = ((n + j : ℕ) : ℂ) := by push_cast; ring
  rw [he, Ring.choose_natCast]
  simp only [Units.smul_def, Int.coe_negOnePow_natCast, zsmul_eq_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, ← mul_assoc, ← mul_pow]
  rw [show (-1 : ℂ) * (-1) = 1 by norm_num, one_pow, one_mul,
    ← Nat.choose_symm (show n ≤ n + j by omega)]
  simp

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem positive_mode_norm_le_column {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℕ) :
    ‖A.physicalMode a d m v‖ ≤ A.positiveColumnNorm a d N * ‖v‖ := by
  have hR := A.positiveColumnNorm_nonneg a d N
  by_cases hm : N < m
  · rw [A.physicalMode_zero_above_cutoff ha hv m (by exact_mod_cast hm), norm_zero]
    positivity
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow]
    apply le_trans _ (A.sum_positive_modes_sq_le a d hv)
    exact Finset.single_le_sum (f := fun i : ℕ => ‖A.physicalMode a d i v‖^2)
      (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (show m < N + 1 by omega))

theorem finsum_positive_modes_sq_eq {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) :
    (∑ᶠ m : ℕ, ‖A.physicalMode a d m v‖^2) =
      ∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2 := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro m hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  apply hm
  change ‖A.physicalMode a d m v‖^2 = 0
  rw [A.physicalMode_zero_above_cutoff ha hv m (by omega)]
  simp

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

theorem negative_mode_norm_le_column {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℕ) :
    ‖A.physicalMode a d (-(m : ℤ)) v‖ ≤ A.positiveColumnNorm a d (N + m) * ‖v‖ := by
  have hR := A.positiveColumnNorm_nonneg a d (N + m)
  have hmem := A.physicalMode_mem_cutoff ha hv (-(m : ℤ)) (M := N + m) (by omega)
  have hb := A.positive_mode_norm_le_column ha hmem m
  have hs := U.mode_norm_sq_le_adjoint ha hq hh (-(m : ℤ)) v
  simp only [neg_neg] at hs
  have h := hs.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg v))
  by_cases hx : ‖A.physicalMode a d (-(m : ℤ)) v‖ = 0
  · rw [hx]; positivity
  · have hxpos : 0 < ‖A.physicalMode a d (-(m : ℤ)) v‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    apply (mul_le_mul_iff_of_pos_right hxpos).mp
    nlinarith [h]

 

theorem shifted_column_sq_le {a : V} {d N s J : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {v : V} (hv : v ∈ A.energyCutoff N) :
    (∑ j ∈ Finset.range J, ‖A.physicalMode a d ((j : ℤ) - s) v‖^2) ≤
      ((s : ℝ) + 1) * A.positiveColumnNorm a d (N + s)^2 * ‖v‖^2 := by
  classical
  let R := A.positiveColumnNorm a d (N + s)
  have hR : 0 ≤ R := A.positiveColumnNorm_nonneg a d (N + s)
  have hpos : (∑ j ∈ Finset.range (J + s + N + 1),
      ‖A.physicalMode a d j v‖^2) ≤ R^2 * ‖v‖^2 := by
    have he : (∑ j ∈ Finset.range (J + s + N + 1), ‖A.physicalMode a d j v‖^2) =
        ∑ j ∈ Finset.range (N + 1), ‖A.physicalMode a d j v‖^2 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      rw [A.physicalMode_zero_above_cutoff ha hv j (by
        simp only [Finset.mem_range] at hj; omega)]
      simp
    rw [he]
    apply (A.sum_positive_modes_sq_le a d hv).trans
    have hRN := A.positiveColumnNorm_nonneg a d N
    have hm := A.positiveColumnNorm_mono a d (show N ≤ N + s by omega)
    change A.positiveColumnNorm a d N ^ 2 * ‖v‖^2 ≤ _
    gcongr
  have hneg : (∑ j ∈ Finset.range s, ‖A.physicalMode a d ((j : ℤ) - s) v‖^2) ≤
      (s : ℝ) * (R^2 * ‖v‖^2) := by
    calc
      _ ≤ ∑ j ∈ Finset.range s, R^2 * ‖v‖^2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hj := Finset.mem_range.mp hj
        have he : (j : ℤ) - s = -((s - j : ℕ) : ℤ) := by omega
        rw [he, ← mul_pow]
        have hn := (U.negative_mode_norm_le_column ha hq hh hv (s - j)).trans
          (mul_le_mul_of_nonneg_right
            (A.positiveColumnNorm_mono a d (show N + (s - j) ≤ N + s by omega)) (norm_nonneg v))
        exact pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := by simp
  calc
    _ ≤ ∑ j ∈ Finset.range (s + (J + s + N + 1)),
        ‖A.physicalMode a d ((j : ℤ) - s) v‖^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro i _ _
      positivity
    _ = (∑ j ∈ Finset.range s, ‖A.physicalMode a d ((j : ℤ) - s) v‖^2) +
        ∑ j ∈ Finset.range (J + s + N + 1), ‖A.physicalMode a d j v‖^2 := by
      rw [Finset.sum_range_add]
      simp only [Nat.cast_add, add_sub_cancel_left]
    _ ≤ (s : ℝ) * (R^2 * ‖v‖^2) + R^2 * ‖v‖^2 := add_le_add hneg hpos
    _ = _ := by dsimp [R]; ring

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem virasoro_one_pow_mem_grade {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (j : ℕ) (hj : j ≤ d) : (A.virasoroMode 1 ^ j) a ∈ A.grade (d - j) := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact A.virasoro_mem_grade (ih (by omega)) 1 (by omega)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

 

def adjointPhysicalMode (a : V) (d : ℕ) (m : ℤ) : Module.End ℂ V :=
  ((-1 : ℂ)^d) • ∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
    A.physicalMode ((A.virasoroMode 1 ^ j) (U.pct a)) (d - j) (-m)

theorem adjointPhysicalMode_inner {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (m : ℤ) (v w : V) :
    inner ℂ (A.physicalMode a d m v) w = inner ℂ v (U.adjointPhysicalMode a d m w) := by
  have h := U.invariant d a ha (m + d - 1) v w
  refine h.trans ?_
  apply congrArg (fun x : V => inner ℂ v x)
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply]
  apply congrArg (fun x : V => ((-1 : ℂ)^d) • x)
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  dsimp only [physicalMode]
  congr 2
  have hj := Finset.mem_range.mp hj
  omega

theorem adjointPhysicalMode_mem_cutoff {a : V} {d N M : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℤ) (hm : (N : ℤ) + m ≤ M) :
    U.adjointPhysicalMode a d m v ∈ A.energyCutoff M := by
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact A.physicalMode_mem_cutoff
    (A.virasoro_one_pow_mem_grade (U.pct_mem_grade ha) j (by have := Finset.mem_range.mp hj; omega))
    hv (-m) (by omega)

theorem adjointPhysicalMode_zero_above_cutoff {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℤ) (hm : (N : ℤ) < m) :
    U.adjointPhysicalMode a d (-m) v = 0 := by
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply, neg_neg]
  have hs : (∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
      A.physicalMode ((A.virasoroMode 1 ^ j) (U.pct a)) (d - j) m v) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [A.physicalMode_zero_above_cutoff
      (A.virasoro_one_pow_mem_grade (U.pct_mem_grade ha) j (by have := Finset.mem_range.mp hj; omega))
      hv m hm, smul_zero]
  rw [hs, smul_zero]

theorem adjointPhysicalMode_eq {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (m : ℤ) :
    U.adjointPhysicalMode a d m = A.physicalMode a d (-m) := by
  ext v
  apply ext_inner_left ℂ
  intro w
  rw [← U.adjointPhysicalMode_inner ha, U.physicalMode_adjoint ha hq hh]

end UnitaryStructure
end CFTTypeVOA

namespace SharpColumns
open scoped ComplexConjugate

 

theorem sum_injective_le {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f s) (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i)
    (N : ℕ) (hzero : ∀ i, N < i → g i = 0) :
    (∑ i ∈ s, g (f i)) ≤ ∑ i ∈ Finset.range (N + 1), g i := by
  classical
  rw [← Finset.sum_image hf]
  have he : ∑ i ∈ (s.image f).filter (fun i => i ≤ N), g i = ∑ i ∈ s.image f, g i := by
    apply Finset.sum_filter_of_ne
    intro i hi hne
    by_contra h
    exact hne (hzero i (by omega))
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hi).2; omega)
  · intro i _ _
    exact hg i

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

 

theorem row_sq_le {ι : Type*} (s : Finset ι) (T T' : ι → Module.End ℂ V)
    (E : Submodule ℂ V) (K : ℝ) (hK : 0 ≤ K)
    (hadj : ∀ i ∈ s, ∀ v w, inner ℂ (T i v) w = inner ℂ v (T' i w))
    (hcol : ∀ w ∈ E, ∑ i ∈ s, ‖T' i w‖^2 ≤ K * ‖w‖^2)
    (v : ι → V) (z : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ C)
    (hv : (∑ i ∈ s, z i • T i (v i)) ∈ E) :
    ‖∑ i ∈ s, z i • T i (v i)‖^2 ≤ C^2 * K * ∑ i ∈ s, ‖v i‖^2 := by
  classical
  let w := ∑ i ∈ s, z i • T i (v i)
  have hi : ‖w‖^2 ≤ C * ∑ i ∈ s, ‖v i‖ * ‖T' i w‖ := by
    calc
      _ = ‖inner ℂ w w‖ := by rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      _ = ‖∑ i ∈ s, conj (z i) * inner ℂ (v i) (T' i w)‖ := by
        conv_lhs => arg 1; lhs; rw [show w = ∑ i ∈ s, z i • T i (v i) from rfl]
        rw [sum_inner]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [inner_smul_left, hadj i hi]
      _ ≤ ∑ i ∈ s, ‖conj (z i) * inner ℂ (v i) (T' i w)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, C * (‖v i‖ * ‖T' i w‖) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hz i hi) (norm_inner_le_norm _ _) (norm_nonneg _) hC
      _ = _ := by rw [Finset.mul_sum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖v i‖) (fun i => ‖T' i w‖)
  have hcol' := hcol w hv
  have hsum : 0 ≤ ∑ i ∈ s, ‖v i‖^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq := pow_le_pow_left₀ (sq_nonneg ‖w‖) hi 2
  rw [mul_pow] at hsq
  have hc := mul_le_mul_of_nonneg_left hcs (sq_nonneg C)
  have hk := mul_le_mul_of_nonneg_left hcol' (mul_nonneg (sq_nonneg C) hsum)
  by_cases hw : ‖w‖ = 0
  · change ‖w‖^2 ≤ _
    rw [hw, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have hp : 0 < ‖w‖^2 := sq_pos_of_ne_zero hw
    change ‖w‖^2 ≤ _
    apply (mul_le_mul_iff_of_pos_right hp).mp
    nlinarith

omit [InnerProductSpace ℂ V] in
 
theorem finite_sum_sq_le_card {ι : Type*} (s : Finset ι) (v : ι → V) :
    ‖∑ i ∈ s, v i‖^2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖v i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s v) 2).trans h

 

theorem triangular_column_sq_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (v : ι → V) (T : κ → ι → Module.End ℂ V)
    (P : κ → ι → Prop) [∀ k i, Decidable (P k i)]
    (z : κ → ι → ℂ) (C K : ℝ)
    (hz : ∀ k ∈ t, ∀ i ∈ s, P k i → ‖z k i‖ ≤ C)
    (hcol : ∀ i ∈ s, ∑ k ∈ t with P k i, ‖T k i (v i)‖^2 ≤ K * ‖v i‖^2) :
    (∑ k ∈ t, ‖∑ i ∈ s with P k i, z k i • T k i (v i)‖^2) ≤
      (s.card : ℝ) * C^2 * K * ∑ i ∈ s, ‖v i‖^2 := by
  classical
  calc
    _ ≤ ∑ k ∈ t, (s.card : ℝ) * C^2 * ∑ i ∈ s with P k i, ‖T k i (v i)‖^2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hh := finite_sum_sq_le_card (s.filter (P k)) (fun i => z k i • T k i (v i))
      apply hh.trans
      have hc : ((s.filter (P k)).card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast Finset.card_filter_le s (P k)
      have hb : ∑ i ∈ s with P k i, ‖z k i • T k i (v i)‖^2 ≤
          C^2 * ∑ i ∈ s with P k i, ‖T k i (v i)‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hz k hk i (Finset.mem_filter.mp hi).1
            (Finset.mem_filter.mp hi).2) 2) (sq_nonneg _)
      calc
        _ ≤ (s.card : ℝ) * (C^2 * ∑ i ∈ s with P k i, ‖T k i (v i)‖^2) :=
          mul_le_mul hc hb (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
        _ = _ := by ring
    _ = (s.card : ℝ) * C^2 * ∑ i ∈ s, ∑ k ∈ t with P k i, ‖T k i (v i)‖^2 := by
      simp only [Finset.sum_filter, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      rw [mul_assoc _ K]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg C))
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      exact hcol

end SharpColumns

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
