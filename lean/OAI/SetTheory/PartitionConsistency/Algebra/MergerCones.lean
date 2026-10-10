import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.MergerWords

namespace OAI

namespace PartitionConsistency.DiagramOrder
variable {α : Type*} [PartialOrder α]

/-- A uniformly strict bound on all missed costs. This is an equivalent,
convenient form of the supremum margin for a strict comparison. -/
def UniformMargin (ρ ε : α → ℝ) (x y : α) : Prop :=
  ∃ c : ℝ, c < ρ y - ρ x ∧ ∀ d, d ≤ y → ¬ d ≤ x → ε d ≤ c

namespace UniformMargin
variable {ρ ε : α → ℝ} {x y z : α}

theorem supremum_lt (h : UniformMargin ρ ε x y) (hxy : x < y) :
    sSup (ε '' {d | d ≤ y ∧ ¬d ≤ x}) < ρ y - ρ x := by
  obtain ⟨c, hc, hb⟩ := h
  have he : (ε '' {d | d ≤ y ∧ ¬d ≤ x}).Nonempty :=
    ⟨ε y, y, ⟨le_rfl, not_le_of_gt hxy⟩, rfl⟩
  refine (csSup_le he ?_).trans_lt hc
  rintro _ ⟨d, hd, rfl⟩
  exact hb d hd.1 hd.2

/-- Margins compose across an intervening element. The proof controls the
supremum, not merely each individual cost. -/
theorem trans (hxy : x < y) (hyz : y < z) (hε : ∀ a, 0 < ε a)
    (h₁ : UniformMargin ρ ε x y) (h₂ : UniformMargin ρ ε y z) :
    UniformMargin ρ ε x z := by
  obtain ⟨a, ha, hba⟩ := h₁
  obtain ⟨b, hb, hbb⟩ := h₂
  have hapos : 0 < a := (hε y).trans_le (hba y le_rfl (not_le_of_gt hxy))
  have hbpos : 0 < b := (hε z).trans_le (hbb z le_rfl (not_le_of_gt hyz))
  refine ⟨max a b, max_lt (by linarith) (by linarith), ?_⟩
  intro d hdz hdx
  by_cases hdy : d ≤ y
  · exact (hba d hdy hdx).trans (le_max_left _ _)
  · exact (hbb d hdz hdy).trans (le_max_right _ _)
end UniformMargin

namespace HeightCost
/-- The old margin supplies one uniform upper bound for every missed cost. -/
theorem uniform_margin (H : HeightCost α) {x y : α} (hxy : x < y) :
    UniformMargin H.height H.cost x y := by
  refine ⟨sSup (H.cost '' {d | d ≤ y ∧ ¬d ≤ x}), H.margin hxy, ?_⟩
  intro d hdy hdx
  refine le_csSup (s := H.cost '' {d | d ≤ y ∧ ¬d ≤ x}) ?_ ⟨d, ⟨hdy, hdx⟩, rfl⟩
  refine ⟨1, ?_⟩
  rintro _ ⟨a, _, rfl⟩
  exact H.cost_le_one a
end HeightCost
end PartitionConsistency.DiagramOrder


namespace PartitionConsistency.MergerAlgebra
universe u v

/-- Right divisibility in a free right monoid-set, used for the quotient
letters, not for words in the new monoid. -/
def RightDivOrder (_M : Type u) (D : Type v) := D

namespace RightDivOrder
variable {M : Type u} {D : Type v} [Monoid M] [RightFreeAction M D]
  [DiagramOrder.IsConical M]

instance : RightFreeAction M (RightDivOrder M D) := inferInstanceAs (RightFreeAction M D)

instance : PartialOrder (RightDivOrder M D) where
  le := RightFreeAction.Reaches M
  le_refl := RightFreeAction.reaches_refl
  le_trans _ _ _ := RightFreeAction.reaches_trans
  le_antisymm z w hzw hwz := by
    obtain ⟨m, hm⟩ := hzw
    obtain ⟨n, hn⟩ := hwz
    have he : m * n = 1 := by
      apply RightFreeAction.factor_injective z
      rw [← RightFreeAction.act_mul, hm, hn, RightFreeAction.act_one]
    have hm1 := (DiagramOrder.IsConical.eq_one_of_mul_eq_one he).1
    simpa only [hm1, RightFreeAction.act_one] using hm

lemma le_iff (z w : RightDivOrder M D) : z ≤ w ↔ RightFreeAction.Reaches M z w := Iff.rfl
end RightDivOrder
end PartitionConsistency.MergerAlgebra

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u
open Classical DiagramOrder MergerAlgebra MergerAlgebra.RightFreeAction
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {n : ℕ}
variable (P : OverlapPrescription M n) (hP : P.Valid)

/-- A coordinate of the quotient letter exists when the letter belongs to
that prescribed copy. Each such representative is unique. -/
def HasRep (i : Fin n) (z : P.Copies hP) : Prop := ∃ x : M, P.copy hP i x = z

noncomputable def coordHeight (H : HeightCost (LeftDivOrder M)) (i : Fin n)
    (z : P.Copies hP) : ℝ :=
  if h : P.HasRep hP i z then H.height h.choose else 0

noncomputable def coordCost (H : HeightCost (LeftDivOrder M)) (i : Fin n)
    (z : P.Copies hP) : ℝ :=
  if h : P.HasRep hP i z then H.cost h.choose else 1

variable (H : HeightCost (LeftDivOrder M))

@[simp] theorem coordHeight_copy (i : Fin n) (x : M) :
    P.coordHeight hP H i (P.copy hP i x) = H.height x := by
  have h : P.HasRep hP i (P.copy hP i x) := ⟨x, rfl⟩
  have hx : h.choose = x := P.copy_injective hP i h.choose_spec
  simp only [coordHeight, dite_eq_left h, hx]

@[simp] theorem coordCost_copy (i : Fin n) (x : M) :
    P.coordCost hP H i (P.copy hP i x) = H.cost x := by
  have h : P.HasRep hP i (P.copy hP i x) := ⟨x, rfl⟩
  have hx : h.choose = x := P.copy_injective hP i h.choose_spec
  simp only [coordCost, dite_eq_left h, hx]

theorem coordHeight_nonneg (i : Fin n) (z : P.Copies hP) :
    0 ≤ P.coordHeight hP H i z := by
  classical
  unfold coordHeight
  split_ifs with h
  · exact (H.height_pos _).le
  · exact le_rfl

theorem coordHeight_lt_one (i : Fin n) (z : P.Copies hP) :
    P.coordHeight hP H i z < 1 := by
  classical
  unfold coordHeight
  split_ifs with h
  · exact H.height_lt_one _
  · exact zero_lt_one

theorem coordCost_pos (i : Fin n) (z : P.Copies hP) :
    0 < P.coordCost hP H i z := by
  classical
  unfold coordCost
  split_ifs with h
  · exact H.cost_pos _
  · exact zero_lt_one

theorem coordCost_le_one (i : Fin n) (z : P.Copies hP) :
    P.coordCost hP H i z ≤ 1 := by
  classical
  unfold coordCost
  split_ifs with h
  · exact H.cost_le_one _
  · exact le_rfl

omit [IsConical M] in
/-- A representation persists when its letter is multiplied on the right. -/
theorem hasRep_of_reaches {i : Fin n} {z w : P.Copies hP}
    (hz : P.HasRep hP i z) (hzw : Reaches M z w) : P.HasRep hP i w := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨m, hm⟩ := hzw
  exact ⟨x * m, hm⟩

/-- Every summand of the finite average is nondecreasing. -/
theorem coordHeight_mono (i : Fin n) :
    Monotone (α := RightDivOrder M (P.Copies hP)) (P.coordHeight hP H i) := by
  classical
  intro z w hzw
  by_cases hz : P.HasRep hP i z
  · obtain ⟨x, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hzw
    change P.coordHeight hP H i (P.copy hP i x) ≤
      P.coordHeight hP H i (P.copy hP i (x * m))
    rw [coordHeight_copy, coordHeight_copy]
    exact H.strictMono_height.monotone ⟨m, rfl⟩
  · have he : P.coordHeight hP H i z = 0 := by simp only [coordHeight, dite_eq_right hz]
    rw [he]
    exact P.coordHeight_nonneg hP H i w

/-- On every represented copy, a proper quotient-letter comparison makes
that coordinate strictly increase. -/
theorem coordHeight_strict {i : Fin n} {z w : RightDivOrder M (P.Copies hP)}
    (hzw : z < w) (hz : P.HasRep hP i z) :
    P.coordHeight hP H i z < P.coordHeight hP H i w := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨m, rfl⟩ := hzw.le
  change P.coordHeight hP H i (P.copy hP i x) <
    P.coordHeight hP H i (P.copy hP i (x * m))
  rw [coordHeight_copy, coordHeight_copy]
  apply H.strictMono_height
  refine lt_iff_le_and_ne.2 ⟨⟨m, rfl⟩, ?_⟩
  intro he
  apply hzw.ne
  exact congrArg (P.copy hP i) he

/-- The literal finite average used in the merger height construction. -/
noncomputable def copiesHeight (z : P.Copies hP) : ℝ :=
  (∑ i : Fin n, P.coordHeight hP H i z) / n

/-- A positive choice of costs below all the source's required finite
bounds. The finite product is at most each represented old cost. -/
noncomputable def copiesCost (z : P.Copies hP) : ℝ :=
  min (H.height 1 / 2) (∏ i : Fin n, P.coordCost hP H i z) / n

theorem copiesHeight_pos (hn : 0 < n) (z : P.Copies hP) :
    0 < P.copiesHeight hP H z := by
  apply div_pos _ (Nat.cast_pos.mpr hn)
  apply Finset.sum_pos'
  · intro i _
    exact P.coordHeight_nonneg hP H i z
  · obtain ⟨⟨i, x⟩, rfl⟩ := Quotient.exists_rep z
    refine ⟨i, Finset.mem_univ i, ?_⟩
    change 0 < P.coordHeight hP H i (P.copy hP i x)
    rw [coordHeight_copy]
    exact H.height_pos x

theorem copiesHeight_lt_one (hn : 0 < n) (z : P.Copies hP) :
    P.copiesHeight hP H z < 1 := by
  apply (div_lt_one (Nat.cast_pos.mpr hn)).2
  calc
    (∑ i : Fin n, P.coordHeight hP H i z) < ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact (P.coordHeight_lt_one hP H i z).le
      · exact ⟨⟨0, hn⟩, Finset.mem_univ _, P.coordHeight_lt_one hP H _ z⟩
    _ = (n : ℝ) := by simp

theorem copiesHeight_strictMono (hn : 0 < n) :
    StrictMono (α := RightDivOrder M (P.Copies hP)) (P.copiesHeight hP H) := by
  intro z w hzw
  apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr hn)
  apply Finset.sum_lt_sum
  · intro i _
    exact P.coordHeight_mono hP H i hzw.le
  · obtain ⟨⟨i, x⟩, hx⟩ := Quotient.exists_rep z
    exact ⟨i, Finset.mem_univ _, P.coordHeight_strict hP H hzw ⟨x, hx⟩⟩

/-- Every coordinate increase is bounded by the increase of the average,
after division by the number of copies. -/
theorem copiesHeight_gap (_hn : 0 < n) (i : Fin n)
    {z w : RightDivOrder M (P.Copies hP)} (hzw : z ≤ w) :
    (P.coordHeight hP H i w - P.coordHeight hP H i z) / n ≤
      P.copiesHeight hP H w - P.copiesHeight hP H z := by
  have hc : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ P.coordHeight hP H j w - P.coordHeight hP H j z := by
    intro j _
    exact sub_nonneg.mpr (P.coordHeight_mono hP H j hzw)
  have hb := Finset.single_le_sum hc (Finset.mem_univ i)
  have hd := div_le_div_of_nonneg_right hb (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [copiesHeight, Finset.sum_sub_distrib, sub_div] using hd

theorem copiesCost_pos (hn : 0 < n) (z : P.Copies hP) :
    0 < P.copiesCost hP H z := by
  apply div_pos _ (Nat.cast_pos.mpr hn)
  apply lt_min
  · exact div_pos (H.height_pos 1) (by norm_num)
  · exact Finset.prod_pos (fun i _ => P.coordCost_pos hP H i z)

theorem copiesCost_le_cap (hn : 0 < n) (z : P.Copies hP) :
    P.copiesCost hP H z ≤ (H.height 1 / 2) / n :=
  div_le_div_of_nonneg_right (min_le_left _ _) (Nat.cast_pos.mpr hn).le

theorem copiesCost_le_one (hn : 0 < n) (z : P.Copies hP) :
    P.copiesCost hP H z ≤ 1 := by
  apply (P.copiesCost_le_cap hP H hn z).trans
  apply (div_le_one (Nat.cast_pos.mpr hn)).2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh := H.height_lt_one 1
  linarith

/-- The chosen cost satisfies the bound from every copy representing the
letter, not just from the representative used to construct it. -/
theorem copiesCost_le_copy (hn : 0 < n) (i : Fin n) (x : M) :
    P.copiesCost hP H (P.copy hP i x) ≤ H.cost x / n := by
  have hp : (∏ j : Fin n, P.coordCost hP H j (P.copy hP i x)) ≤
      P.coordCost hP H i (P.copy hP i x) := by
    simpa only [Finset.prod_singleton] using
      (Finset.prod_le_prod_of_subset_of_le_one₀
        (s := {i}) (t := Finset.univ) (f := fun j => P.coordCost hP H j (P.copy hP i x))
        (Finset.subset_univ _) (fun j _ => (P.coordCost_pos hP H j _).le)
        (fun j _ _ => P.coordCost_le_one hP H j _))
  rw [coordCost_copy] at hp
  exact div_le_div_of_nonneg_right ((min_le_right _ _).trans hp) (Nat.cast_pos.mpr hn).le

/-- Comparisons within a represented copy are precisely old comparisons. -/
theorem copy_le_copy_iff (i : Fin n) (x y : M) :
    @LE.le (RightDivOrder M (P.Copies hP)) _ (P.copy hP i x) (P.copy hP i y) ↔
      @LE.le (LeftDivOrder M) _ x y := by
  change Reaches M (P.copy hP i x) (P.copy hP i y) ↔ ∃ t, x * t = y
  rw [reaches_same_copy_iff]
  exact exists_congr (fun _ => eq_comm)

/-- A strict bound for the missed costs that have a representative in a
specified copy. Crucially it is one bound for that whole class of divisors. -/
theorem copies_coordinate_margin (hn : 0 < n)
    {z w : RightDivOrder M (P.Copies hP)} (hzw : z < w) (i : Fin n) :
    ∃ c : ℝ, c < P.copiesHeight hP H w - P.copiesHeight hP H z ∧
      ∀ d : RightDivOrder M (P.Copies hP), d ≤ w → ¬ d ≤ z →
        P.HasRep hP i d → P.copiesCost hP H d ≤ c := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hz : P.HasRep hP i z
  · obtain ⟨x, rfl⟩ := hz
    obtain ⟨m, rfl⟩ := hzw.le
    have hxm : @LT.lt (LeftDivOrder M) _ x (x * m) := by
      refine lt_iff_le_and_ne.2 ⟨⟨m, rfl⟩, ?_⟩
      intro he
      exact hzw.ne (congrArg (P.copy hP i) he)
    obtain ⟨c, hc, hbound⟩ := H.uniform_margin hxm
    have hgap := P.copiesHeight_gap hP H hn i hzw.le
    change (P.coordHeight hP H i (P.copy hP i (x * m)) -
      P.coordHeight hP H i (P.copy hP i x)) / n ≤ _ at hgap
    rw [coordHeight_copy, coordHeight_copy] at hgap
    refine ⟨c / n, (div_lt_div_of_pos_right hc hnR).trans_le hgap, ?_⟩
    intro d hdw hdz hdrep
    obtain ⟨y, rfl⟩ := hdrep
    have hdy := (P.copy_le_copy_iff hP i y (x * m)).1 hdw
    have hdn : ¬ @LE.le (LeftDivOrder M) _ y x :=
      fun h => hdz ((P.copy_le_copy_iff hP i y x).2 h)
    exact (P.copiesCost_le_copy hP H hn i y).trans
      (div_le_div_of_nonneg_right (hbound y hdy hdn) hnR.le)
  · by_cases hw : P.HasRep hP i w
    · obtain ⟨y, hy⟩ := hw
      have hz0 : P.coordHeight hP H i z = 0 := by simp only [coordHeight, dite_eq_right hz]
      have hwy : P.coordHeight hP H i w = H.height y := by
        rw [← hy, coordHeight_copy]
      have hgap := P.copiesHeight_gap hP H hn i hzw.le
      rw [hz0, hwy, sub_zero] at hgap
      have hhy : H.height 1 ≤ H.height y :=
        H.strictMono_height.monotone ⟨y, one_mul y⟩
      have hlt : H.height 1 / 2 < H.height y := by
        have hp := H.height_pos 1
        linarith
      refine ⟨(H.height 1 / 2) / n,
        (div_lt_div_of_pos_right hlt hnR).trans_le hgap, ?_⟩
      intro d _ _ _
      exact P.copiesCost_le_cap hP H hn d
    · refine ⟨0, sub_pos.mpr (P.copiesHeight_strictMono hP H hn hzw), ?_⟩
      intro d hdw _ hdrep
      exact (hw (P.hasRep_of_reaches hP hdrep hdw)).elim

/-- Finiteness of the copies converts their separate strict bounds into a
single strict bound for the complete missed-cost supremum. -/
theorem copies_uniform_margin (hn : 0 < n)
    {z w : RightDivOrder M (P.Copies hP)} (hzw : z < w) :
    UniformMargin (α := RightDivOrder M (P.Copies hP))
      (P.copiesHeight hP H) (P.copiesCost hP H) z w := by
  choose c hc hb using P.copies_coordinate_margin hP H hn hzw
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ c
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨c i, hc i, ?_⟩
  intro d hdw hdz
  obtain ⟨⟨j, x⟩, hx⟩ := Quotient.exists_rep d
  exact (hb j d hdw hdz ⟨x, hx⟩).trans (hmax j (Finset.mem_univ _))

/-- Actual heights and costs on the prescribed quotient, satisfying the
strict supremum margin. -/
noncomputable def copiesHeightCost (hn : 0 < n) :
    HeightCost (RightDivOrder M (P.Copies hP)) where
  height := P.copiesHeight hP H
  cost := P.copiesCost hP H
  height_pos := P.copiesHeight_pos hP H hn
  height_lt_one := P.copiesHeight_lt_one hP H hn
  cost_pos := P.copiesCost_pos hP H hn
  cost_le_one := P.copiesCost_le_one hP H hn
  margin hzw := (P.copies_uniform_margin hP H hn hzw).supremum_lt hzw

end PartitionConsistency.DiagramForcing.OverlapPrescription

namespace PartitionConsistency.MergerAlgebra.Word
universe u v
open DiagramOrder
variable {M : Type u} {D : Type v} [LeftCancelMonoid M] [IsConical M]
  [RightFreeAction M D]
variable (H : HeightCost (LeftDivOrder M)) (HD : HeightCost (RightDivOrder M D))

/-- Word heights with the source's parameters `θ = φ = 1/4`. -/
noncomputable def wordHeight : Word M D → ℝ
  | old x => H.height x
  | snoc w z => wordHeight w + (1 - wordHeight w) * (1 / 4 + HD.height z / 4)

/-- Positive costs satisfying both of the required last-letter bounds. -/
noncomputable def wordCost : Word M D → ℝ
  | old x => H.cost x
  | snoc w z => (1 - wordHeight H HD w) * min (1 / 8) (HD.cost z / 4)

@[simp] theorem wordHeight_old (x : M) : wordHeight H HD (.old x) = H.height x := rfl
@[simp] theorem wordHeight_snoc (w : Word M D) (z : D) :
    wordHeight H HD (snoc w z) =
      wordHeight H HD w + (1 - wordHeight H HD w) * (1 / 4 + HD.height z / 4) := rfl
@[simp] theorem wordCost_old (x : M) : wordCost H HD (.old x) = H.cost x := rfl
@[simp] theorem wordCost_snoc (w : Word M D) (z : D) :
    wordCost H HD (snoc w z) = (1 - wordHeight H HD w) * min (1 / 8) (HD.cost z / 4) := rfl

theorem wordHeight_bounds (w : Word M D) :
    0 < wordHeight H HD w ∧ wordHeight H HD w < 1 := by
  induction w with
  | old x => exact ⟨H.height_pos x, H.height_lt_one x⟩
  | snoc w z ih =>
      have hp : 0 < 1 - wordHeight H HD w := sub_pos.mpr ih.2
      have hz : 0 < 1 / 4 + HD.height z / 4 := by have := HD.height_pos z; linarith
      have hz1 : 1 / 4 + HD.height z / 4 < 1 := by have := HD.height_lt_one z; linarith
      have hpos := mul_pos hp hz
      have hlt := mul_lt_mul_of_pos_left hz1 hp
      simp only [wordHeight_snoc, mul_one] at *
      constructor <;> linarith

theorem wordCost_pos (w : Word M D) : 0 < wordCost H HD w := by
  cases w with
  | old x => exact H.cost_pos x
  | snoc w z =>
      apply mul_pos (sub_pos.mpr (wordHeight_bounds H HD w).2)
      exact lt_min (by norm_num) (div_pos (HD.cost_pos z) (by norm_num))

theorem wordCost_le_one (w : Word M D) : wordCost H HD w ≤ 1 := by
  cases w with
  | old x => exact H.cost_le_one x
  | snoc w z =>
      have hw := wordHeight_bounds H HD w
      have hb := mul_le_mul_of_nonneg_left
        (min_le_left (1 / 8 : ℝ) (HD.cost z / 4)) (by linarith : 0 ≤ 1 - wordHeight H HD w)
      change (1 - wordHeight H HD w) * min (1 / 8) (HD.cost z / 4) ≤ 1
      linarith

/-- Every proper one-letter extension is a strict divisibility comparison. -/
theorem prefix_lt_snoc (w : Word M D) (z : D) :
    @LT.lt (LeftDivOrder (Word M D)) _ w (snoc w z) := by
  refine lt_iff_le_and_ne.2 ⟨⟨snoc (old 1) z, ?_⟩, ?_⟩
  · change product w (snoc (old 1) z) = snoc w z
    simp only [product, act_one]
  · intro he
    have hl := congrArg length he
    simp only [length_snoc] at hl
    omega

/-- The uniform bound for the new divisors appearing at one extra letter. -/
theorem uniform_margin_snoc (w : Word M D) (z : D) :
    UniformMargin (α := LeftDivOrder (Word M D))
      (wordHeight H HD) (wordCost H HD) w (snoc w z) := by
  have hw := wordHeight_bounds H HD w
  have hz := HD.height_pos z
  refine ⟨(1 - wordHeight H HD w) / 8, ?_, ?_⟩
  · rw [wordHeight_snoc]
    nlinarith [mul_pos (by linarith : 0 < 1 - wordHeight H HD w) hz]
  · intro d hdy hdx
    have hdy' : d ∣ snoc w z := by obtain ⟨q, hq⟩ := hdy; exact ⟨q, hq.symm⟩
    rcases (dvd_snoc_iff d w z).1 hdy' with hdw | ⟨t, rfl, _⟩
    · obtain ⟨q, hq⟩ := hdw
      exact (hdx ⟨q, hq.symm⟩).elim
    · rw [wordCost_snoc]
      have hb := mul_le_mul_of_nonneg_left
        (min_le_left (1 / 8 : ℝ) (HD.cost t / 4)) (by linarith : 0 ≤ 1 - wordHeight H HD w)
      linarith

/-- For equal-length words with a common prefix, all shorter divisors are
shared and the only new missed costs are controlled by the last-letter margin. -/
theorem uniform_margin_same_prefix (w : Word M D) {z t : RightDivOrder M D}
    (hzt : z < t) :
    UniformMargin (α := LeftDivOrder (Word M D))
      (wordHeight H HD) (wordCost H HD) (snoc w z) (snoc w t) := by
  have hw := wordHeight_bounds H HD w
  have hp : 0 < 1 - wordHeight H HD w := by linarith
  obtain ⟨c, hc, hb⟩ := HD.uniform_margin hzt
  refine ⟨(1 - wordHeight H HD w) * (c / 4), ?_, ?_⟩
  · have hlt := mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hc (by norm_num : (0 : ℝ) < 4)) hp
    rw [wordHeight_snoc H HD w t, wordHeight_snoc H HD w z]
    nlinarith
  · intro d hdt hdz
    have hdt' : d ∣ snoc w t := by obtain ⟨q, hq⟩ := hdt; exact ⟨q, hq.symm⟩
    rcases (dvd_snoc_iff d w t).1 hdt' with hdw | ⟨a, rfl, hat⟩
    · have hdz' := (dvd_snoc_iff d w z).2 (Or.inl hdw)
      obtain ⟨q, hq⟩ := hdz'
      exact (hdz ⟨q, hq.symm⟩).elim
    · have han : ¬ @LE.le (RightDivOrder M D) _ a z := by
        rintro ⟨m, hm⟩
        exact hdz ⟨old m, congrArg (snoc w) hm⟩
      have hcost := hb a hat han
      rw [wordCost_snoc]
      apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hp.le).trans
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcost (by norm_num)) hp.le

/-- A comparison between old words has exactly its old missed costs,
because no new word divides an old word. -/
theorem uniform_margin_old {x y : LeftDivOrder M} (hxy : x < y) :
    UniformMargin (α := LeftDivOrder (Word M D))
      (wordHeight H HD) (wordCost H HD) (old x) (old y) := by
  obtain ⟨c, hc, hb⟩ := H.uniform_margin hxy
  refine ⟨c, hc, ?_⟩
  intro d hdy hdx
  obtain ⟨q, hq⟩ := hdy
  obtain ⟨a, b, rfl, rfl, hab⟩ := factors_of_old hq
  have ha : @LE.le (LeftDivOrder M) _ a y := ⟨b, hab⟩
  have hn : ¬ @LE.le (LeftDivOrder M) _ a x := by
    rintro ⟨m, hm⟩
    exact hdx ⟨old m, congrArg old hm⟩
  exact hb a ha hn

/-- Induction through the literal normal forms verifies every strict
comparison, not just the comparisons between the adjoined roots. -/
theorem word_uniform_margin (y : Word M D) :
    ∀ x : Word M D, @LT.lt (LeftDivOrder (Word M D)) _ x y →
      UniformMargin (α := LeftDivOrder (Word M D))
        (wordHeight H HD) (wordCost H HD) x y := by
  induction y with
  | old y =>
      intro x hxy
      obtain ⟨q, hq⟩ := hxy.le
      obtain ⟨a, b, rfl, rfl, hab⟩ := factors_of_old hq
      have ha : @LT.lt (LeftDivOrder M) _ a y := by
        refine lt_iff_le_and_ne.2 ⟨⟨b, hab⟩, ?_⟩
        exact fun he => hxy.ne (congrArg old he)
      exact uniform_margin_old H HD ha
  | snoc w z ih =>
      intro x hxy
      have hxy' : x ∣ snoc w z := by obtain ⟨q, hq⟩ := hxy.le; exact ⟨q, hq.symm⟩
      rcases (dvd_snoc_iff x w z).1 hxy' with hxw | ⟨t, rfl, htz⟩
      · by_cases he : x = w
        · subst x
          exact uniform_margin_snoc H HD w z
        · have hxw' : @LT.lt (LeftDivOrder (Word M D)) _ x w := by
            obtain ⟨q, hq⟩ := hxw
            exact lt_iff_le_and_ne.2 ⟨⟨q, hq.symm⟩, he⟩
          exact UniformMargin.trans hxw' (prefix_lt_snoc w z) (wordCost_pos H HD)
            (ih x hxw') (uniform_margin_snoc H HD w z)
      · have htz' : @LT.lt (RightDivOrder M D) _ t z :=
          lt_iff_le_and_ne.2 ⟨htz, fun he => hxy.ne (congrArg (snoc w) he)⟩
        exact uniform_margin_same_prefix H HD w htz'

/-- Extension of the old height and cost to the actual merger monoid. -/
noncomputable def wordHeightCost : HeightCost (LeftDivOrder (Word M D)) where
  height := wordHeight H HD
  cost := wordCost H HD
  height_pos w := (wordHeight_bounds H HD w).1
  height_lt_one w := (wordHeight_bounds H HD w).2
  cost_pos := wordCost_pos H HD
  cost_le_one := wordCost_le_one H HD
  margin {x y} hxy := (word_uniform_margin H HD y x hxy).supremum_lt hxy

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.MergerAlgebra.Word
universe u v
open DiagramOrder
variable {M : Type u} {D : Type v} [LeftCancelMonoid M] [IsConical M]
  [RightFreeAction M D]
  (H : HeightCost (LeftDivOrder M)) (HD : HeightCost (RightDivOrder M D))

/-- The set of costs of divisors missed by an old comparison is literally
unchanged, since every divisor of an old word is itself an old word. -/
theorem old_missed_costs (x y : LeftDivOrder M) :
    (wordHeightCost H HD).cost ''
        {d : LeftDivOrder (Word M D) | d ≤ old y ∧ ¬ d ≤ old x} =
      H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x} := by
  ext r
  constructor
  · rintro ⟨d, ⟨⟨q, hq⟩, hdx⟩, hr⟩
    obtain ⟨a, b, rfl, rfl, hab⟩ := factors_of_old hq
    refine ⟨a, ⟨⟨b, hab⟩, ?_⟩, hr⟩
    rintro ⟨m, hm⟩
    exact hdx ⟨old m, congrArg old hm⟩
  · rintro ⟨a, ⟨⟨b, hab⟩, hax⟩, hr⟩
    refine ⟨old a, ⟨⟨old b, congrArg old hab⟩, ?_⟩, hr⟩
    rintro ⟨q, hq⟩
    obtain ⟨c, d, hac, hqd, hcd⟩ := factors_of_old hq
    have hac' : a = c := old.inj hac
    subst c
    exact hax ⟨d, hcd⟩

/-- In particular, the old missed-cost supremum is exactly preserved. -/
theorem old_cost_supremum (x y : LeftDivOrder M) :
    sSup ((wordHeightCost H HD).cost ''
      {d : LeftDivOrder (Word M D) | d ≤ old y ∧ ¬ d ≤ old x}) =
        sSup (H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x}) :=
  congrArg sSup (old_missed_costs H HD x y)

end PartitionConsistency.MergerAlgebra.Word

namespace PartitionConsistency.DiagramForcing.OverlapPrescription
universe u
open DiagramOrder MergerAlgebra
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {n : ℕ}
  (P : OverlapPrescription M n) (hP : P.Valid)
  (H : HeightCost (LeftDivOrder M))

/-- The height and cost extension for the literal finite nonempty merger,
not an assumed extension and not merely a margin on the adjoined roots. -/
noncomputable def mergerHeightCost (hn : 0 < n) :
    HeightCost (LeftDivOrder (P.Merger hP)) :=
  Word.wordHeightCost H (P.copiesHeightCost hP H hn)

@[simp] theorem merger_height_old (hn : 0 < n) (x : M) :
    (P.mergerHeightCost hP H hn).height (Word.old x) = H.height x := rfl

@[simp] theorem merger_cost_old (hn : 0 < n) (x : M) :
    (P.mergerHeightCost hP H hn).cost (Word.old x) = H.cost x := rfl

/-- Combining the old-divisor calculation with the constructed margins. -/
theorem merger_old_cost_supremum (hn : 0 < n) (x y : LeftDivOrder M) :
    sSup ((P.mergerHeightCost hP H hn).cost ''
      {d : LeftDivOrder (P.Merger hP) | d ≤ Word.old y ∧ ¬ d ≤ Word.old x}) =
        sSup (H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x}) :=
  Word.old_cost_supremum H (P.copiesHeightCost hP H hn) x y

end PartitionConsistency.DiagramForcing.OverlapPrescription

-- The main consistency proof appears after the concrete construction below.
-- In particular, no inaccessible, transitive-ground, interpretation or forcing
-- assumption has been smuggled into its signature. The open target is stated
-- in Challenge.lean only.

end OAI
