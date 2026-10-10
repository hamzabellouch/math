import OAI.RepresentationTheory.RowColumn.LineStates
import OAI.LinearAlgebra.MatrixState.Postselection

namespace OAI

section

namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [Fintype C] [DecidableEq C] in
lemma actWord_swap_fixed (w : Words (S := S) odd k) (x y : S) (he : w.1 x = w.1 y) :
    actWord (Equiv.swap x y) w = w := by
  apply Subtype.ext
  funext z
  change w.1 ((Equiv.swap x y)⁻¹ z) = w.1 z
  rw [Equiv.swap_inv]
  by_cases hx : z = x
  · subst z; simp [he]
  by_cases hy : z = y
  · subst z; simp [he]
  · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

omit [Fintype C] [DecidableEq C] in
lemma oddPerm_swap_sign (w : Words (S := S) odd k) (x y : S)
    (hxy : x ≠ y) (he : w.1 x = w.1 y) :
    permSign (oddPerm (Equiv.swap x y) w) = if odd (w.1 x) then -1 else 1 := by
  have hw := actWord_swap_fixed w x y he
  split_ifs with ho
  · rw [oddPerm_sign_of_stabilizes _ w hw]
    · simp [permSign, Equiv.Perm.sign_swap hxy]
    · intro z hz
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; subst z; exact hz ho
      · intro h; subst z; exact hz (he ▸ ho)
  · rw [oddPerm_of_odd_fixed _ w hw]
    · simp [permSign]
    · intro z hz
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; subst z; exact ho hz
      · intro h; subst z; exact ho (he.symm ▸ hz)

omit [Fintype C] in
/-- Repeated opposite-parity pair symbols force a commutant coefficient to
vanish. This is the finite-sign obstruction behind signed postselection. -/
lemma commuting_coefficient_zero_of_pair_repeat
    (T : Representation.IntertwiningMap (representation (S := S) (odd := odd) (k := k))
      (representation (S := S) (odd := odd) (k := k)))
    (w v : Words (S := S) odd k) (x y : S) (hxy : x ≠ y)
    (hw : w.1 x = w.1 y) (hv : v.1 x = v.1 y)
    (hp : ¬ (odd (w.1 x) ↔ odd (v.1 x))) : T (wordVector v) w = 0 := by
  let g := Equiv.swap x y
  have he := congrArg (fun z : EuclideanSpace ℂ (Words (S := S) odd k) => z (actWord g w))
    (Representation.IntertwiningMap.isIntertwining _ _ T g (wordVector v))
  rw [signedMap_wordVector, map_smul, signedMap_transport_apply] at he
  change permSign (oddPerm g v) * T (wordVector (actWord g v)) (actWord g w) =
    permSign (oddPerm g w) * T (wordVector v) w at he
  dsimp only [g] at he
  rw [actWord_swap_fixed w x y hw, actWord_swap_fixed v x y hv,
    oddPerm_swap_sign v x y hxy hv, oddPerm_swap_sign w x y hxy hw] at he
  by_cases hwo : odd (w.1 x) <;> by_cases hvo : odd (v.1 x)
  · exact (hp (iff_of_true hwo hvo)).elim
  · simp only [ite_eq_left hwo, ite_eq_right hvo, one_mul, neg_mul, one_mul] at he
    linear_combination (1/2 : ℂ) * he
  · simp only [ite_eq_right hwo, ite_eq_left hvo, one_mul, neg_mul, one_mul] at he
    linear_combination (-1/2 : ℂ) * he
  · exact (hp (iff_of_false hwo hvo)).elim

abbrev ParityMismatch (w v : Words (S := S) odd k) :=
  {x : S // ¬ (odd (w.1 x) ↔ odd (v.1 x))}

omit [Fintype C] in
lemma mismatch_pair_injective
    (T : Representation.IntertwiningMap (representation (S := S) (odd := odd) (k := k))
      (representation (S := S) (odd := odd) (k := k)))
    (w v : Words (S := S) odd k) (hn : T (wordVector v) w ≠ 0) :
    Function.Injective (fun x : ParityMismatch w v => (w.1 x.1, v.1 x.1)) := by
  intro x y he
  apply Subtype.ext
  by_contra hxy
  exact hn (commuting_coefficient_zero_of_pair_repeat T w v x.1 y.1 hxy
    (congrArg Prod.fst he) (congrArg Prod.snd he) x.2)

/-- Every nonzero coefficient changes parity in at most |C|² slots. For the
actual slot space C=Fin h ⊕ Fin h this is at most 4h², independent of s. -/
lemma commuting_parity_bandwidth
    (T : Representation.IntertwiningMap (representation (S := S) (odd := odd) (k := k))
      (representation (S := S) (odd := odd) (k := k)))
    (w v : Words (S := S) odd k) (hn : T (wordVector v) w ≠ 0) :
    Fintype.card (ParityMismatch w v) ≤ Fintype.card C ^ 2 := by
  simpa only [Fintype.card_prod, pow_two] using
    Fintype.card_le_of_injective _ (mismatch_pair_injective T w v hn)
end RowColumn.Signed

noncomputable section
open scoped BigOperators Classical
namespace RowColumn

variable {S : Type*} [Fintype S] [DecidableEq S]

abbrev ShortSubsets (q : ℕ) := {t : Finset S // t.card ≤ q}

def shortSubsetCode {q : ℕ} (t : ShortSubsets (S := S) q) (i : Fin q) : Option S :=
  if hi : i.1 < t.1.card then some ((t.1.equivFin).symm ⟨i.1, hi⟩).1 else none

omit [Fintype S] [DecidableEq S] in
lemma shortSubsetCode_mem {q : ℕ} (t : ShortSubsets (S := S) q) (x : S) :
    (∃ i, shortSubsetCode t i = some x) ↔ x ∈ t.1 := by
  constructor
  · rintro ⟨i, hi⟩
    unfold shortSubsetCode at hi
    split_ifs at hi with hj
    · have he := Option.some.inj hi
      rw [← he]
      exact ((t.1.equivFin).symm ⟨i.1, hj⟩).2
  · intro hx
    let j := t.1.equivFin ⟨x, hx⟩
    refine ⟨⟨j.1, j.2.trans_le t.2⟩, ?_⟩
    simp only [shortSubsetCode, dite_eq_left j.2]
    exact congrArg (fun z : t.1 => some z.1) (t.1.equivFin.symm_apply_apply ⟨x, hx⟩)

omit [Fintype S] [DecidableEq S] in
lemma shortSubsetCode_injective {q : ℕ} : Function.Injective (shortSubsetCode (S := S) (q := q)) := by
  intro t u he
  apply Subtype.ext
  apply Finset.ext
  intro x
  rw [← shortSubsetCode_mem t x, ← shortSubsetCode_mem u x, he]

omit [DecidableEq S] in
lemma card_shortSubsets_le (q : ℕ) :
    Fintype.card (ShortSubsets (S := S) q) ≤ (Fintype.card S + 1)^q := by
  simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin] using
    Fintype.card_le_of_injective _ (shortSubsetCode_injective (S := S) (q := q))

def parityDifference (b c : S → Bool) : Finset S := Finset.univ.filter (fun x => b x ≠ c x)

def parityNear (q : ℕ) (b c : S → Bool) : Prop := (parityDifference b c).card ≤ q

instance (q : ℕ) : DecidableRel (parityNear (S := S) q) := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

omit [DecidableEq S] in
lemma parityNear_symm (q : ℕ) : Std.Symm (parityNear (S := S) q) := by
  constructor
  intro b c hc
  have he : parityDifference c b = parityDifference b c := by
    ext x
    simp only [parityDifference, Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]
  unfold parityNear at *
  rwa [he]

omit [DecidableEq S] in
lemma parityDifference_injective (b : S → Bool) : Function.Injective (parityDifference b) := by
  intro c d he
  funext x
  have hh : (b x ≠ c x) ↔ (b x ≠ d x) := by
    have ht := Finset.ext_iff.mp he x
    simpa only [parityDifference, Finset.mem_filter, Finset.mem_univ, true_and] using ht
  cases hbx : b x <;> cases hcx : c x <;> cases hdx : d x <;> simp_all

lemma parityNear_count (q : ℕ) (b : S → Bool) :
    (Finset.univ.filter (parityNear q b)).card ≤ (Fintype.card S + 1)^q := by
  let f : {c : S → Bool // parityNear q b c} → ShortSubsets (S := S) q :=
    fun c => ⟨parityDifference b c.1, c.2⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    exact parityDifference_injective b (congrArg Subtype.val he)
  have hh := (Fintype.card_le_of_injective f hf).trans (card_shortSubsets_le (S := S) q)
  simpa only [Fintype.card_subtype] using hh

end RowColumn
noncomputable section
open scoped BigOperators Classical
namespace RowColumn

section PositiveBanded
variable {V B : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [Fintype B] [DecidableEq B]

def energy (A : V →ₗ[ℂ] V) (x : V) : ℝ := (inner ℂ x (A x)).re

lemma positive_cross_bound (A : V →ₗ[ℂ] V) (hA : A.IsPositive) (x y : V) :
    2 * (inner ℂ x (A y)).re ≤ energy A x + energy A y := by
  have hp := hA.re_inner_nonneg_right (x-y)
  have hs : (inner ℂ y (A x)).re = (inner ℂ x (A y)).re := by
    rw [← hA.isSymmetric x y]
    exact inner_re_symm (𝕜 := ℂ) _ _
  change 0 ≤ (inner ℂ (x-y) (A (x-y))).re at hp
  simp only [map_sub, inner_sub_left, inner_sub_right, Complex.sub_re] at hp
  rw [hs] at hp
  dsimp only [energy]
  linarith

omit [DecidableEq B] in
/-- A positive block-banded matrix is dominated by its block diagonal times
the maximum number of nonzero block neighbours. This will be applied to
physical parity allocations, where signed symmetry supplies a polynomial bound. -/
lemma positive_banded_sum (A : V →ₗ[ℂ] V) (hA : A.IsPositive)
    (v : B → V) (R : B → B → Prop) [DecidableRel R]
    (hRs : Std.Symm R) (D : ℕ)
    (hD : ∀ i, (Finset.univ.filter (R i)).card ≤ D)
    (hz : ∀ i j, ¬ R i j → inner ℂ (v i) (A (v j)) = 0) :
    energy A (∑ i, v i) ≤ (D : ℝ) * ∑ i, energy A (v i) := by
  have hn (i : B) : 0 ≤ energy A (v i) := hA.re_inner_nonneg_right _
  have he (i j : B) : 2 * (inner ℂ (v i) (A (v j))).re ≤
      if R i j then energy A (v i) + energy A (v j) else 0 := by
    split_ifs with hr
    · exact positive_cross_bound A hA _ _
    · rw [hz i j hr]; simp
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => he i j))
  have hleft : (∑ i, ∑ j, 2 * (inner ℂ (v i) (A (v j))).re) =
      2 * energy A (∑ i, v i) := by
    simp only [energy, map_sum, sum_inner, inner_sum, Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hleft] at hs
  have htrace : (∑ i, ∑ j, if R i j then energy A (v i) + energy A (v j) else 0) =
      2 * ∑ i, ((Finset.univ.filter (R i)).card : ℝ) * energy A (v i) := by
    have hsplit (i j : B) : (if R i j then energy A (v i) + energy A (v j) else 0) =
        (if R i j then energy A (v i) else 0) + (if R i j then energy A (v j) else 0) := by
      split_ifs <;> simp
    simp only [hsplit, Finset.sum_add_distrib]
    have hswap : (∑ i, ∑ j, if R i j then energy A (v j) else 0) =
        ∑ i, ∑ j, if R i j then energy A (v i) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have hr : R j i ↔ R i j := ⟨fun h => hRs.symm _ _ h, fun h => hRs.symm _ _ h⟩
      simp only [hr]
    rw [hswap]
    have hcard (i : B) : (∑ j, if R i j then energy A (v i) else 0) =
        ((Finset.univ.filter (R i)).card : ℝ) * energy A (v i) := by
      rw [← Finset.sum_filter]
      simp
    simp only [hcard]
    ring
  rw [htrace] at hs
  have hd : (∑ i, ((Finset.univ.filter (R i)).card : ℝ) * energy A (v i)) ≤
      (D : ℝ) * ∑ i, energy A (v i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hD i) (hn i))
  linarith

end PositiveBanded
end RowColumn
namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

def parityPattern (w : Words (S := S) odd k) : S → Bool := fun x => decide (odd (w.1 x))

def parityMask (b : S → Bool) (v : EuclideanSpace ℂ (Words (S := S) odd k)) :
    EuclideanSpace ℂ (Words (S := S) odd k) :=
  WithLp.toLp 2 (fun w => if parityPattern w = b then v w else 0)

omit [Fintype C] [DecidableEq C] in
lemma sum_parityMasks (v : EuclideanSpace ℂ (Words (S := S) odd k)) :
    (∑ b : S → Bool, parityMask b v) = v := by
  ext w
  simp [WithLp.ofLp_sum, parityMask]

lemma inner_wordVector (w : Words (S := S) odd k)
    (x : EuclideanSpace ℂ (Words (S := S) odd k)) : inner ℂ (wordVector w) x = x w := by
  simp [PiLp.inner_apply, wordVector, RCLike.inner_apply]

lemma parityNear_of_coefficient_ne_zero
    (T : Representation.IntertwiningMap (representation (S := S) (odd := odd) (k := k))
      (representation (S := S) (odd := odd) (k := k)))
    (w v : Words (S := S) odd k) (hn : T (wordVector v) w ≠ 0) :
    RowColumn.parityNear (Fintype.card C ^ 2) (parityPattern w) (parityPattern v) := by
  have he : (RowColumn.parityDifference (parityPattern w) (parityPattern v)).card =
      Fintype.card (ParityMismatch w v) := by
    unfold RowColumn.parityDifference
    rw [Fintype.card_subtype]
    congr 2
    funext x
    apply propext
    simp [parityPattern]
  change (RowColumn.parityDifference (parityPattern w) (parityPattern v)).card ≤ _
  rw [he]
  exact commuting_parity_bandwidth T w v hn

lemma parityMask_inner_zero
    (T : Representation.IntertwiningMap (representation (S := S) (odd := odd) (k := k))
      (representation (S := S) (odd := odd) (k := k)))
    (b c : S → Bool)
    (hx : ¬ RowColumn.parityNear (Fintype.card C ^ 2) b c)
    (x y : EuclideanSpace ℂ (Words (S := S) odd k)) :
    inner ℂ (parityMask b x) (T (parityMask c y)) = 0 := by
  rw [← sum_wordVectors (parityMask b x), ← sum_wordVectors (parityMask c y)]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_wordVector]
  apply Finset.sum_eq_zero
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro w _
  change (parityMask c y) v *
    ((starRingEnd ℂ) ((parityMask b x) w) * T (wordVector v) w) = 0
  by_cases hb : parityPattern w = b
  · by_cases hc : parityPattern v = c
    · have hz : T (wordVector v) w = 0 := by
        by_contra hn
        exact hx (by simpa only [hb, hc] using parityNear_of_coefficient_ne_zero T w v hn)
      simp only [hz, mul_zero]
    · simp [parityMask, hc]
  · simp [parityMask, hb]

/-- Exact signed dephasing inequality. No LR or highest-weight estimate:
positivity plus the swap-forced bandwidth yields polynomial cost in the
physical parity allocation, the hard structural step for local domination. -/
theorem signed_parity_dephasing
    (T : Representation.IntertwiningMap (representation (S := S) (odd := odd) (k := k))
      (representation (S := S) (odd := odd) (k := k)))
    (hT : T.toLinearMap.IsPositive)
    (x : EuclideanSpace ℂ (Words (S := S) odd k)) :
    RowColumn.energy T.toLinearMap x ≤
      ((Fintype.card S + 1) ^ (Fintype.card C ^ 2) : ℕ) *
        ∑ b : S → Bool, RowColumn.energy T.toLinearMap (parityMask b x) := by
  have hh := RowColumn.positive_banded_sum T.toLinearMap hT
    (fun b : S → Bool => parityMask b x) (RowColumn.parityNear (Fintype.card C ^ 2))
    (RowColumn.parityNear_symm _) ((Fintype.card S + 1) ^ (Fintype.card C ^ 2))
    (RowColumn.parityNear_count _) (fun b c h => parityMask_inner_zero T b c h x x)
  simpa only [sum_parityMasks] using hh
end RowColumn.Signed

namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht
variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] {odd : C → Prop} [DecidablePred odd] {k : ℕ}
  (line : S → L)

omit [Fintype S] [Fintype L] [DecidableEq L] in
lemma swap_mem_lineGroup (x y : S) (hl : line x=line y) :
    Equiv.swap x y ∈ RowColumn.lineGroup line := by
  intro z
  by_cases hx : z=x
  · subst z; simp [hl]
  by_cases hy : z=y
  · subst z; simp [hl]
  · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

omit [Fintype C] [Fintype L] [DecidableEq L] in
lemma line_coefficient_zero_of_pair_repeat
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (w v : Words (S := S) odd k) (x y : S) (hxy : x ≠ y) (hl : line x=line y)
    (hw : w.1 x = w.1 y) (hv : v.1 x = v.1 y)
    (hp : ¬ (odd (w.1 x) ↔ odd (v.1 x))) : T (wordVector v) w = 0 := by
  have he := commuting_coefficient_relation line T
    ⟨Equiv.swap x y,swap_mem_lineGroup line x y hl⟩ w v
  change permSign (oddPerm (Equiv.swap x y) v) *
      T (wordVector (actWord (Equiv.swap x y) v)) (actWord (Equiv.swap x y) w) =
    permSign (oddPerm (Equiv.swap x y) w) * T (wordVector v) w at he
  rw [actWord_swap_fixed w x y hw, actWord_swap_fixed v x y hv,
    oddPerm_swap_sign v x y hxy hv, oddPerm_swap_sign w x y hxy hw] at he
  by_cases hwo : odd (w.1 x) <;> by_cases hvo : odd (v.1 x)
  · exact (hp (iff_of_true hwo hvo)).elim
  · simp only [ite_eq_left hwo, ite_eq_right hvo, one_mul, neg_mul, one_mul] at he
    linear_combination (1/2 : ℂ) * he
  · simp only [ite_eq_right hwo, ite_eq_left hvo, one_mul, neg_mul, one_mul] at he
    linear_combination (-1/2 : ℂ) * he
  · exact (hp (iff_of_false hwo hvo)).elim

omit [Fintype C] [Fintype L] [DecidableEq L] in
lemma line_mismatch_injective
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (w v : Words (S := S) odd k) (hn : T (wordVector v) w ≠ 0) :
    Function.Injective (fun x : ParityMismatch w v => (line x.1, w.1 x.1, v.1 x.1)) := by
  intro x y he
  apply Subtype.ext
  by_contra hxy
  exact hn (line_coefficient_zero_of_pair_repeat line T w v x.1 y.1 hxy
    (congrArg Prod.fst he) (congrArg (fun z => z.2.1) he)
    (congrArg (fun z => z.2.2) he) x.2)

omit [DecidableEq L] in
lemma line_parity_bandwidth
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (w v : Words (S := S) odd k) (hn : T (wordVector v) w ≠ 0) :
    Fintype.card (ParityMismatch w v) ≤ Fintype.card L * Fintype.card C ^ 2 := by
  simpa only [Fintype.card_prod, pow_two] using
    Fintype.card_le_of_injective _ (line_mismatch_injective line T w v hn)

omit [DecidableEq L]

lemma line_parityNear_of_coefficient_ne_zero
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (w v : Words (S := S) odd k) (hn : T (wordVector v) w ≠ 0) :
    RowColumn.parityNear (Fintype.card L * Fintype.card C ^ 2) (parityPattern w) (parityPattern v) := by
  have he : (RowColumn.parityDifference (parityPattern w) (parityPattern v)).card =
      Fintype.card (ParityMismatch w v) := by
    unfold RowColumn.parityDifference
    rw [Fintype.card_subtype]
    congr 2
    funext x
    apply propext
    simp [parityPattern]
  change (RowColumn.parityDifference (parityPattern w) (parityPattern v)).card ≤ _
  rw [he]
  exact line_parity_bandwidth line T w v hn

lemma line_parityMask_inner_zero
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (b c : S → Bool)
    (hx : ¬ RowColumn.parityNear (Fintype.card L * Fintype.card C ^ 2) b c)
    (x y : EuclideanSpace ℂ (Words (S := S) odd k)) :
    inner ℂ (parityMask b x) (T (parityMask c y)) = 0 := by
  rw [← sum_wordVectors (parityMask b x), ← sum_wordVectors (parityMask c y)]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_wordVector]
  apply Finset.sum_eq_zero
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro w _
  change (parityMask c y) v *
    ((starRingEnd ℂ) ((parityMask b x) w) * T (wordVector v) w) = 0
  by_cases hb : parityPattern w = b
  · by_cases hc : parityPattern v = c
    · have hz : T (wordVector v) w = 0 := by
        by_contra hn
        exact hx (by simpa only [hb, hc] using line_parityNear_of_coefficient_ne_zero line T w v hn)
      simp only [hz, mul_zero]
    · simp [parityMask, hc]
  · simp [parityMask, hb]

/-- Exact signed dephasing inequality. No LR or highest-weight estimate:
positivity plus the swap-forced bandwidth yields polynomial cost in the
physical parity allocation, the hard structural step for local domination. -/
theorem line_signed_parity_dephasing
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (hT : T.toLinearMap.IsPositive)
    (x : EuclideanSpace ℂ (Words (S := S) odd k)) :
    RowColumn.energy T.toLinearMap x ≤
      ((Fintype.card S + 1) ^ (Fintype.card L * Fintype.card C ^ 2) : ℕ) *
        ∑ b : S → Bool, RowColumn.energy T.toLinearMap (parityMask b x) := by
  have hh := RowColumn.positive_banded_sum T.toLinearMap hT
    (fun b : S → Bool => parityMask b x) (RowColumn.parityNear (Fintype.card L * Fintype.card C ^ 2))
    (RowColumn.parityNear_symm _) ((Fintype.card S + 1) ^ (Fintype.card L * Fintype.card C ^ 2))
    (RowColumn.parityNear_count _) (fun b c h => line_parityMask_inner_zero line T b c h x x)
  simpa only [sum_parityMasks] using hh
end RowColumn.Signed

end
end
end

end OAI
