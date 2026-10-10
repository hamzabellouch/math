import OAI.RingTheory.DirectFiniteness.TradeGirth

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Classical
open MvPolynomial
namespace KaplanskyCounterexample.PolynomialPairing

variable {Q : Type u_1} [Field Q] {n q d : ℕ}

abbrev Simplex (n q d : ℕ) := {k : Fin n → Fin q // ∑ i, (k i).val ≤ d}

def point (a : Fin q ≃ Q) (k : Fin n → Fin q) : Fin n → Q := fun i => a (k i)

def newton (a : Fin q ≃ Q) (k : Fin n → Fin q) : MvPolynomial (Fin n) Q :=
  ∏ i, ∏ u : Fin (k i).val, (X i - C (a ⟨u.val, u.isLt.trans (k i).isLt⟩))

lemma newton_degree (a : Fin q ≃ Q) (k : Fin n → Fin q) :
    (newton a k).totalDegree ≤ ∑ i, (k i).val := by
  apply (totalDegree_finsetProd _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (totalDegree_finsetProd _ _).trans
  have h : ∀ u : Fin (k i).val,
      (X i - C (a ⟨u.val, u.isLt.trans (k i).isLt⟩) : MvPolynomial (Fin n) Q).totalDegree ≤ 1 := by
    intro u
    exact (totalDegree_sub_C_le _ _).trans (by simp)
  simpa using Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => h u)

lemma newton_eval_zero (a : Fin q ≃ Q) (k j : Fin n → Fin q)
    (h : ¬ k ≤ j) : eval (point a j) (newton a k) = 0 := by
  have hi : ∃ i, (j i).val < (k i).val := by
    simpa only [Pi.le_def, not_forall, not_le, Fin.lt_def] using h
  obtain ⟨i, hi⟩ := hi
  simp only [newton, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨(j i).val, hi⟩ : Fin (k i).val))
  simp [point]

lemma newton_eval_diag_ne_zero (a : Fin q ≃ Q) (k : Fin n → Fin q) :
    eval (point a k) (newton a k) ≠ 0 := by
  simp only [newton, map_prod, map_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro u _
  apply sub_ne_zero.mpr
  intro h
  have h' := congrArg Fin.val (a.injective h)
  exact (Nat.ne_of_gt u.isLt) h'

/-- Triangular interpolation on the exact index simplex. The proof provides
its total-degree bound, rather than using unrestricted finite-set interpolation. -/
theorem exists_interpolation (a : Fin q ≃ Q) (values : Simplex n q d → Q) :
    ∃ f : MvPolynomial (Fin n) Q, f.totalDegree ≤ d ∧
      ∀ k : Simplex n q d, eval (point a k.val) f = values k := by
  let I := LinearExtension (Simplex n q d)
  let : Fintype (LinearExtension (Simplex n q d)) := inferInstanceAs (Fintype (Simplex n q d))
  let B : Matrix I I Q := fun j k => eval (point a j.val) (newton a k.val)
  have htri : B.IsLowerTriangular := by
    intro j k hjk
    apply newton_eval_zero
    intro hle
    have hh : (k : I) ≤ j := (toLinearExtension (α := Simplex n q d)).monotone hle
    exact (not_le_of_gt hjk) hh
  have hdet : B.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular B htri]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => newton_eval_diag_ne_zero a k.val)
  have hunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) values
  refine ⟨∑ k : I, c k • newton a k.val, ?_, ?_⟩
  · apply (totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro k _
    exact (totalDegree_smul_le _ _).trans ((newton_degree a k.val).trans k.property)
  · intro k
    have h := congrFun hc k
    simpa [B, Matrix.mulVec, dotProduct, smul_eq_C_mul, mul_comm] using h

end KaplanskyCounterexample.PolynomialPairing

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.PolynomialPairing

variable {Q : Type u_2} {σ : Type u_3} [Field Q]

/-- Restriction to the full parametrized affine line. -/
def lineRestriction (u v : σ → Q) (P : MvPolynomial σ Q) : Polynomial Q :=
  MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X) P

lemma lineRestriction_eval (u v : σ → Q) (P : MvPolynomial σ Q) (t : Q) :
    (lineRestriction u v P).eval t = MvPolynomial.eval (fun i => u i + t * v i) P := by
  unfold lineRestriction
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P R hP hR => simp [hP, hR]
  | mul_X P i hP => simp [hP, mul_comm t]

lemma lineRestriction_degree (u v : σ → Q) (P : MvPolynomial σ Q) :
    (lineRestriction u v P).natDegree ≤ P.totalDegree := by
  rw [lineRestriction, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  apply (Polynomial.natDegree_mul_le).trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply le_trans _ (MvPolynomial.le_totalDegree hd)
  change (∑ i ∈ d.support, _) ≤ ∑ i ∈ d.support, d i
  apply Finset.sum_le_sum
  intro i _
  apply (Polynomial.natDegree_pow_le).trans
  have hc : (Polynomial.C (u i) + Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    simp only [Polynomial.natDegree_C, max_le_iff, zero_le, true_and]
    simpa using Polynomial.natDegree_C_mul_X_pow_le (v i) 1
  simpa using Nat.mul_le_mul_left (d i) hc

/-- The exact finite-field power-sum consequence used on every line. -/
lemma sum_polynomial_eval [Fintype Q] (P : Polynomial Q)
    (hP : P.natDegree < Fintype.card Q - 1) : ∑ t : Q, P.eval t = 0 := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← Finset.mul_sum]
  have hk' : k < Fintype.card Q - 1 := lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp k hk) hP
  rw [FiniteField.sum_pow_lt_card_sub_one Q k hk', mul_zero]

theorem line_sum_zero [Fintype Q] (u v : σ → Q) (P : MvPolynomial σ Q)
    (hP : P.totalDegree < Fintype.card Q - 1) :
    ∑ t : Q, MvPolynomial.eval (fun i => u i + t * v i) P = 0 := by
  simpa only [lineRestriction_eval] using sum_polynomial_eval (lineRestriction u v P)
    (lt_of_le_of_lt (lineRestriction_degree u v P) hP)

/-- Partitioning the entire affine space into coordinate-parallel lines. -/
theorem affine_space_sum_zero [Fintype Q] [Fintype σ] (i : σ) (P : MvPolynomial σ Q)
    (hP : P.totalDegree < Fintype.card Q - 1) :
    ∑ x : σ → Q, MvPolynomial.eval x P = 0 := by
  rw [← (Equiv.funSplitAt i Q).symm.sum_comp (fun x => MvPolynomial.eval x P)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  let u : σ → Q := fun j => if h : j = i then 0 else x ⟨j, h⟩
  let v : σ → Q := fun j => if j = i then 1 else 0
  have hparam (t : Q) : (Equiv.funSplitAt i Q).symm (t, x) = fun j => u j + t * v j := by
    funext j
    by_cases h : j = i <;> simp [Equiv.funSplitAt, u, v, h]
  simpa only [hparam] using line_sum_zero u v P hP

end KaplanskyCounterexample.PolynomialPairing

namespace KaplanskyCounterexample.PolynomialPairing

variable {Q : Type u_4} [Field Q] [Fintype Q] {n q : ℕ}

def simplexPoints (a : Fin q ≃ Q) (n d : ℕ) : Finset (Fin n → Q) :=
  Finset.univ.image (fun k : Simplex n q d => point a k.val)

omit [Field Q] [Fintype Q] in
lemma mem_simplexPoints (a : Fin q ≃ Q) {d : ℕ} {x : Fin n → Q} :
    x ∈ simplexPoints a n d ↔ ∃ k : Simplex n q d, point a k.val = x := by
  simp [simplexPoints]

/-- The interpolation choice is constrained by the exact degree cutoff. -/
def holePolynomial (a : Fin q ≃ Q) (d : ℕ) (o : Fin n → Q) :
    MvPolynomial (Fin n) Q :=
  (exists_interpolation a (fun k : Simplex n q d => if point a k.val = o then 1 else 0)).choose

omit [Fintype Q] in
lemma holePolynomial_degree (a : Fin q ≃ Q) (d : ℕ) (o : Fin n → Q) :
    (holePolynomial a d o).totalDegree ≤ d :=
  (exists_interpolation a (fun k : Simplex n q d => if point a k.val = o then 1 else 0)).choose_spec.1

omit [Fintype Q] in
lemma holePolynomial_eval (a : Fin q ≃ Q) (d : ℕ) (o x : Fin n → Q)
    (hx : x ∈ simplexPoints a n d) :
    MvPolynomial.eval x (holePolynomial a d o) = if x = o then 1 else 0 := by
  obtain ⟨k, rfl⟩ := (mem_simplexPoints a).mp hx
  exact (exists_interpolation a (fun k : Simplex n q d => if point a k.val = o then 1 else 0)).choose_spec.2 k

/-- The exact column vector x_v, indexed by the chosen holes. -/
def column (a : Fin q ≃ Q) (d : ℕ) (O : Finset (Fin n → Q)) (v : Fin n → Q) : O → Q :=
  fun o => MvPolynomial.eval v (holePolynomial a d o.val)

def gramColumn (a : Fin q ≃ Q) (d : ℕ) (O : Finset (Fin n → Q)) (v : Fin n → Q) :
    Matrix O O Q := fun o o' => column a d O v o * column a d O v o'

omit [Fintype Q] in
lemma sum_holes_gram (a : Fin q ≃ Q) {d : ℕ} (O : Finset (Fin n → Q))
    (hO : O ⊆ simplexPoints a n d) :
    ∑ v ∈ O, gramColumn a d O v = 1 := by
  ext o o'
  simp only [Matrix.sum_apply, gramColumn, column]
  calc
    _ = ∑ v ∈ O, (if v = o.val then (1 : Q) else 0) *
        (if v = o'.val then (1 : Q) else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [holePolynomial_eval a d _ _ (hO hv), holePolynomial_eval a d _ _ (hO hv)]
    _ = _ := by
      rw [Finset.sum_eq_single_of_mem o.val o.property]
      · simp only [ite_true, one_mul, Matrix.one_apply]
        congr 1
        exact propext Subtype.val_inj
      · intro v _ hv
        rw [ite_eq_right hv, zero_mul]

omit [Fintype Q] in
lemma gram_degree (a : Fin q ≃ Q) (d : ℕ) (o o' : Fin n → Q) :
    (holePolynomial a d o * holePolynomial a d o').totalDegree ≤ 2 * d := by
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (by simpa [two_mul] using (Nat.add_le_add (holePolynomial_degree a d o)
      (holePolynomial_degree a d o')))

lemma cutoff_degree (q : ℕ) (hq : 2 ≤ q) : 2 * ((q - 2) / 2) < q - 1 := by
  have h := Nat.mul_div_le (q - 2) 2
  omega

/-- All entries of the Gram column sum vanish on the full affine space. -/
lemma sum_all_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q) (hn : 0 < n)
    (O : Finset (Fin n → Q)) :
    ∑ v : Fin n → Q, gramColumn a ((q - 2) / 2) O v = 0 := by
  ext o o'
  simp only [Matrix.sum_apply, Matrix.zero_apply, gramColumn, column]
  have hq2 : 2 ≤ q := hq ▸ Nat.succ_le_iff.mpr (Fintype.one_lt_card (α := Q))
  convert! (affine_space_sum_zero (⟨0, hn⟩ : Fin n)
    (holePolynomial a ((q - 2) / 2) o.val * holePolynomial a ((q - 2) / 2) o'.val)
    ((gram_degree a _ _ _).trans_lt (hq ▸ cutoff_degree q hq2))) using 1
  simp only [map_mul]
  exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)

/-- The precise global identity on V, with no characteristic simplification. -/
theorem sum_complement_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q) (hn : 0 < n)
    (O : Finset (Fin n → Q)) (hO : O ⊆ simplexPoints a n ((q - 2) / 2)) :
    ∑ v ∈ Finset.univ \ O, gramColumn a ((q - 2) / 2) O v = -1 := by
  have h := Finset.sum_sdiff (f := gramColumn a ((q - 2) / 2) O) (Finset.subset_univ O)
  rw [sum_holes_gram a O hO, sum_all_gram a hq hn O] at h
  exact eq_neg_of_add_eq_zero_left h

/-- A full affine line, not a segment or a subset of one. -/
structure AffineLine (Q : Type u_5) [Field Q] (n : ℕ) where
  base : Fin n → Q
  direction : Fin n → Q
  direction_ne_zero : direction ≠ 0

def AffineLine.param (L : AffineLine Q n) (t : Q) : Fin n → Q :=
  fun i => L.base i + t * L.direction i

omit [Fintype Q] in
lemma AffineLine.param_injective (L : AffineLine Q n) : Function.Injective L.param := by
  intro t u h
  have hi : ∃ i, L.direction i ≠ 0 := by
    by_contra! h
    exact L.direction_ne_zero (funext h)
  obtain ⟨i, hi⟩ := hi
  have he := congrFun h i
  exact mul_right_cancel₀ hi (add_left_cancel he)

def AffineLine.points (L : AffineLine Q n) : Finset (Fin n → Q) :=
  Finset.univ.image L.param

lemma AffineLine.card_points (L : AffineLine Q n) : L.points.card = Fintype.card Q := by
  rw [AffineLine.points, Finset.card_image_of_injective _ L.param_injective, Finset.card_univ]

theorem sum_line_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (O : Finset (Fin n → Q)) (L : AffineLine Q n) :
    ∑ v ∈ L.points, gramColumn a ((q - 2) / 2) O v = 0 := by
  rw [AffineLine.points, Finset.sum_image (L.param_injective.injOn)]
  ext o o'
  simp only [Matrix.sum_apply, Matrix.zero_apply, gramColumn, column]
  have hq2 : 2 ≤ q := hq ▸ Nat.succ_le_iff.mpr (Fintype.one_lt_card (α := Q))
  convert! (line_sum_zero L.base L.direction
    (holePolynomial a ((q - 2) / 2) o.val * holePolynomial a ((q - 2) / 2) o'.val)
    ((gram_degree a _ _ _).trans_lt (hq ▸ cutoff_degree q hq2))) using 1
  simp only [map_mul]
  apply Finset.sum_congr rfl
  intro t _
  rfl

end KaplanskyCounterexample.PolynomialPairing
end
end

end OAI
