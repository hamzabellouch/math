import OAI.LinearAlgebra.RankMatching.Basic

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.PivotTopology
open HahnSeries
open scoped BigOperators Topology
variable {k : Type*} [Field k]

def poleLattice (J : ℤ) : Submodule k (LaurentSeries k) where
  carrier := {f | ∀ i : ℤ, J < i → f.coeff (-i) = 0}
  zero_mem' := by simp
  add_mem' hf hg i hi := by simp [hf i hi, hg i hi]
  smul_mem' c f hf i hi := by simp [hf i hi]

def monomial (j : ℤ) : LaurentSeries k := HahnSeries.single (-j) 1

def PreservesPoles (a : LaurentSeries k →ₗ[k] LaurentSeries k) : Prop :=
  ∀ J, ∀ f ∈ poleLattice (k := k) J, a f ∈ poleLattice (k := k) J

def matrixOf (a : LaurentSeries k →ₗ[k] LaurentSeries k) : Matrix ℤ ℤ k :=
  fun l j => (a (monomial j)).coeff (-l)

def HasLeadingTerm (f : LaurentSeries k) (j : ℤ) : Prop :=
  f ∈ poleLattice (k := k) j ∧ f.coeff (-j) = 1

def HasLeadingPosition (f : LaurentSeries k) (j : ℤ) : Prop :=
  f ∈ poleLattice (k := k) j ∧ f.coeff (-j) ≠ 0

def crossing (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J : ℤ) : Set (ℤ × ℤ) :=
  {p | RankMatching.Matched (matrixOf a) p.1 p.2 ∧ p.1 ≤ J ∧ J < p.2}

def crossingQuotient (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J : ℤ) :=
  ↥(LinearMap.range a ⊓ poleLattice (k := k) J) ⧸
    Submodule.comap (LinearMap.range a ⊓ poleLattice (k := k) J).subtype
      ((poleLattice (k := k) J).map a)

instance crossingQuotient_addCommGroup (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J : ℤ) :
    AddCommGroup (crossingQuotient a J) := by
  unfold crossingQuotient
  infer_instance

instance crossingQuotient_module (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J : ℤ) :
    Module k (crossingQuotient a J) := by
  unfold crossingQuotient
  infer_instance

@[simp] lemma mem_poleLattice (J : ℤ) (f : LaurentSeries k) :
    f ∈ poleLattice J ↔ ∀ i : ℤ, J < i → f.coeff (-i) = 0 := Iff.rfl

lemma poleLattice_mono {I J : ℤ} (h : I ≤ J) :
    poleLattice (k := k) I ≤ poleLattice J := by
  intro f hf i hi
  exact hf i (lt_of_le_of_lt h hi)

@[simp] lemma coeff_monomial (j i : ℤ) :
    (monomial (k := k) j).coeff (-i) = if i = j then 1 else 0 := by
  simp [monomial, HahnSeries.coeff_single]

lemma monomial_mem {j J : ℤ} (h : j ≤ J) : monomial (k := k) j ∈ poleLattice J := by
  intro i hi
  simp [show i ≠ j by omega]

lemma exists_poleLattice (f : LaurentSeries k) : ∃ J, f ∈ poleLattice J := by
  refine ⟨-f.order, ?_⟩
  intro i hi
  exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)

lemma matrixOf_triangular (a : LaurentSeries k →ₗ[k] LaurentSeries k)
    (ha : PreservesPoles a) : RankMatching.Triangular (matrixOf a) := by
  intro l j h
  exact ha j (monomial j) (monomial_mem le_rfl) l h

def truncate (f : LaurentSeries k) (L J : ℤ) : LaurentSeries k :=
  ∑ c ∈ Finset.Icc L J, f.coeff (-c) • monomial c

lemma coeff_truncate (f : LaurentSeries k) (L J i : ℤ) :
    (truncate f L J).coeff (-i) = if L ≤ i ∧ i ≤ J then f.coeff (-i) else 0 := by
  classical
  simp [truncate, HahnSeries.coeff_sum, HahnSeries.coeff_smul, smul_eq_mul,
    mul_ite]

lemma truncate_mem (f : LaurentSeries k) (L J : ℤ) : truncate f L J ∈ poleLattice J := by
  intro i hi
  rw [coeff_truncate, ite_eq_right (by omega)]

lemma sub_truncate_mem {f : LaurentSeries k} {L J : ℤ} (hf : f ∈ poleLattice J) :
    f - truncate f L J ∈ poleLattice (L - 1) := by
  intro i hi
  rw [HahnSeries.coeff_sub, coeff_truncate]
  by_cases hij : i ≤ J
  · rw [ite_eq_left (by omega), sub_self]
  · rw [ite_eq_right (by omega), sub_zero, hf i (by omega)]

def poleProjection (L : ℤ) : LaurentSeries k →ₗ[k] (ℤ → k) where
  toFun f i := if L ≤ i then f.coeff (-i) else 0
  map_add' f g := by ext i; by_cases hi : L ≤ i <;> simp [hi]
  map_smul' c f := by ext i; by_cases hi : L ≤ i <;> simp [hi]

lemma poleProjection_eq_zero {L : ℤ} {f : LaurentSeries k} :
    poleProjection L f = 0 ↔ f ∈ poleLattice (L - 1) := by
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [poleProjection, show L ≤ i by omega] using this
  · intro h
    ext i
    by_cases hi : L ≤ i
    · simp [poleProjection, hi, h i (by omega)]
    · simp [poleProjection, hi]

@[simp] lemma poleProjection_monomial_image
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (L j : ℤ) :
    poleProjection L (a (monomial j)) = RankMatching.column (matrixOf a) L j := rfl

lemma poleProjection_truncate_image (a : LaurentSeries k →ₗ[k] LaurentSeries k)
    (ha : PreservesPoles a) {f : LaurentSeries k} {L J : ℤ}
    (hf : f ∈ poleLattice J) :
    poleProjection L (a (truncate f L J)) = poleProjection L (a f) := by
  have h := (poleProjection_eq_zero).mpr (ha (L - 1) _ (sub_truncate_mem hf))
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h.symm

lemma columnSpace_eq_projectedImage (a : LaurentSeries k →ₗ[k] LaurentSeries k)
    (ha : PreservesPoles a) (L J : ℤ) :
    RankMatching.columnSpace (matrixOf a) L J =
      ((poleLattice J).map a).map (poleProjection L) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨a (monomial c), ⟨monomial c, monomial_mem hc, rfl⟩, rfl⟩
  · rintro y ⟨z, ⟨f,hf,rfl⟩,rfl⟩
    rw [← poleProjection_truncate_image a ha hf]
    simp only [truncate, map_sum, map_smul]
    exact Submodule.sum_mem _ fun c hc =>
      Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨c, (Finset.mem_Icc.mp hc).2, rfl⟩)

lemma increment_zero_iff_finite_solution
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a) (L j : ℤ) :
    RankMatching.increment (matrixOf a) L j = 0 ↔
      ∃ f, HasLeadingTerm f j ∧ a f ∈ poleLattice (L - 1) := by
  rw [RankMatching.increment_eq_zero_iff, columnSpace_eq_projectedImage a ha]
  constructor
  · rintro ⟨z, ⟨g,hg,rfl⟩,heq⟩
    refine ⟨monomial j - g, ⟨?_, ?_⟩, ?_⟩
    · intro i hi
      simp only [HahnSeries.coeff_sub, coeff_monomial,
        ite_eq_right (show i ≠ j by omega), hg i (by omega), sub_self]
    · simp [HahnSeries.coeff_sub, hg j (by omega)]
    · apply poleProjection_eq_zero.mp
      rw [map_sub, map_sub, poleProjection_monomial_image, ← heq, sub_self]
  · rintro ⟨f, ⟨hf,hfj⟩,haf⟩
    have hg : monomial j - f ∈ poleLattice (j - 1) := by
      intro i hi
      by_cases hij : i = j
      · subst i; simp [HahnSeries.coeff_sub, hfj]
      · simp [HahnSeries.coeff_sub, coeff_monomial, hij, hf i (by omega)]
    refine ⟨a (monomial j - f), ⟨monomial j - f, hg, rfl⟩, ?_⟩
    rw [map_sub, map_sub, poleProjection_monomial_image,
      poleProjection_eq_zero.mpr haf, sub_zero]

open WithZero

lemma mem_poleLattice_iff_valuation (J : ℤ) (f : LaurentSeries k) :
    f ∈ poleLattice J ↔ Valued.v f ≤ WithZero.exp J := by
  rw [show J = -(-J) by omega, LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
  constructor
  · intro hf n hn
    simpa using hf (-n) (by omega)
  · intro hf i hi
    exact hf (-i) (by omega)

lemma poleLattice_eq_ball (J : ℤ) :
    (poleLattice (k := k) J : Set (LaurentSeries k)) =
      {f | (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).restrict f ≤
        (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).restrict (monomial J)} := by
  ext f
  change f ∈ poleLattice J ↔ (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).restrict f ≤
    (Valued.v : Valuation (LaurentSeries k) ℤᵐ⁰).restrict (monomial J)
  rw [Valuation.restrict_le_iff, mem_poleLattice_iff_valuation]
  simp [monomial, LaurentSeries.valuation_single_zpow]

lemma isClosed_poleLattice (J : ℤ) : IsClosed (poleLattice (k := k) J : Set (LaurentSeries k)) := by
  rw [poleLattice_eq_ball]
  exact Valued.isClosed_closedBall _ _

lemma isOpen_poleLattice (J : ℤ) : IsOpen (poleLattice (k := k) J : Set (LaurentSeries k)) := by
  rw [poleLattice_eq_ball]
  apply Valued.isOpen_closedBall
  rw [ne_eq, Valuation.restrict_eq_zero_iff]
  simp [monomial, LaurentSeries.valuation_single_zpow]

lemma poleLattice_nhds_basis :
    (𝓝 (0 : LaurentSeries k)).HasBasis (fun _ : ℤ => True)
      (fun J => (poleLattice (k := k) J : Set (LaurentSeries k))) := by
  let v : Valuation (LaurentSeries k) ℤᵐ⁰ := Valued.v
  apply (Valued.hasBasis_nhds_zero (LaurentSeries k) ℤᵐ⁰).to_hasBasis
  · intro γ _
    let r : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
    have hr : r ≠ 0 := (Units.map
      (MonoidWithZeroHom.ValueGroup₀.embedding (f := .ofClass v)).toMonoidHom γ).ne_zero
    refine ⟨WithZero.log r - 1, trivial, ?_⟩
    intro f hf
    rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
    apply (mem_poleLattice_iff_valuation _ f).mp hf |>.trans_lt
    change WithZero.exp (WithZero.log r - 1) < r
    calc
      _ < WithZero.exp (WithZero.log r) := WithZero.exp_lt_exp.mpr (by omega)
      _ = r := WithZero.exp_log hr
  · intro J _
    have hn : v.restrict (monomial J) ≠ 0 := by
      rw [ne_eq, Valuation.restrict_eq_zero_iff]
      simp [v, monomial, LaurentSeries.valuation_single_zpow]
    refine ⟨Units.mk0 _ hn, trivial, ?_⟩
    intro f hf
    rw [poleLattice_eq_ball]
    change v.restrict f < v.restrict (monomial J) at hf
    exact hf.le

lemma continuous_of_preservesPoles (a : LaurentSeries k →ₗ[k] LaurentSeries k)
    (ha : PreservesPoles a) : Continuous a := by
  apply continuous_of_continuousAt_zero a
  simp only [ContinuousAt, map_zero]
  rw [poleLattice_nhds_basis.tendsto_iff poleLattice_nhds_basis]
  exact fun J _ => ⟨J, trivial, ha J⟩

lemma continuous_of_bounded_coefficients [UniformSpace k] [DiscreteTopology k]
    {X : Type*} [TopologicalSpace X] (g : X → LaurentSeries k) (J : ℤ)
    (hg : ∀ x, g x ∈ poleLattice J)
    (hcoeff : ∀ n : ℤ, Continuous (fun x => (g x).coeff n)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x
  apply tendsto_sub_nhds_zero_iff.mp
  rw [poleLattice_nhds_basis.tendsto_right_iff]
  intro M _
  have hev : ∀ᶠ y in 𝓝 x, ∀ i ∈ Finset.Ioc M J,
      (g y).coeff (-i) = (g x).coeff (-i) := by
    rw [Filter.eventually_all_finset]
    intro i _
    exact (hcoeff (-i)).continuousAt.eventually
      ((isOpen_discrete {(g x).coeff (-i)}).mem_nhds rfl)
  filter_upwards [hev] with y hy
  intro i hi
  rw [HahnSeries.coeff_sub, sub_eq_zero]
  by_cases hij : i ≤ J
  · exact hy i (Finset.mem_Ioc.mpr ⟨hi,hij⟩)
  · rw [hg y i (by omega), hg x i (by omega)]

def stageSeries (J : ℤ) (c : ℤ → k) : LaurentSeries k :=
  HahnSeries.ofSuppBddBelow (fun n => if -J ≤ n then c n else 0)
    ⟨-J, by
      intro n hn
      by_contra h
      exact hn (ite_eq_right h)⟩

@[simp] lemma coeff_stageSeries (J : ℤ) (c : ℤ → k) (n : ℤ) :
    (stageSeries J c).coeff n = if -J ≤ n then c n else 0 := rfl

lemma stageSeries_mem (J : ℤ) (c : ℤ → k) : stageSeries J c ∈ poleLattice J := by
  intro i hi
  rw [coeff_stageSeries, ite_eq_right (by omega)]

lemma range_stageSeries (J : ℤ) :
    Set.range (stageSeries (k := k) J) = (poleLattice (k := k) J : Set (LaurentSeries k)) := by
  ext f
  constructor
  · rintro ⟨c,rfl⟩
    exact stageSeries_mem J c
  · intro hf
    refine ⟨f.coeff, ?_⟩
    apply HahnSeries.ext
    funext n
    rw [coeff_stageSeries]
    split_ifs with hn
    · rfl
    · symm
      simpa using hf (-n) (by omega)

lemma continuous_stageSeries [UniformSpace k] [DiscreteTopology k] (J : ℤ) :
    Continuous (stageSeries (k := k) J) := by
  apply continuous_of_bounded_coefficients _ J (stageSeries_mem J)
  intro n
  simp only [coeff_stageSeries]
  split_ifs
  · exact continuous_apply n
  · exact continuous_const

lemma isCompact_poleLattice [Finite k] (J : ℤ) :
    IsCompact (poleLattice (k := k) J : Set (LaurentSeries k)) := by
  let : UniformSpace k := ⊥
  rw [← range_stageSeries, ← Set.image_univ]
  exact isCompact_univ.image (continuous_stageSeries J)

lemma isCompact_leadingTerm [Finite k] (j : ℤ) :
    IsCompact {f : LaurentSeries k | HasLeadingTerm f j} := by
  let : UniformSpace k := ⊥
  exact (isCompact_poleLattice j).inter_right
    (isClosed_eq (LaurentSeries.uniformContinuous_coeff (-j)).continuous continuous_const)

lemma isClosed_leadingTerm (j : ℤ) :
    IsClosed {f : LaurentSeries k | HasLeadingTerm f j} := by
  let : UniformSpace k := ⊥
  exact (isClosed_poleLattice j).inter
    (isClosed_eq (LaurentSeries.uniformContinuous_coeff (-j)).continuous continuous_const)

lemma unmatched_iff_increments_zero (A : Matrix ℤ ℤ k)
    (hA : RankMatching.Triangular A) (j : ℤ) :
    (∀ l, ¬ RankMatching.Matched A l j) ↔ ∀ L, RankMatching.increment A L j = 0 := by
  constructor
  · intro h L
    by_cases hLj : L ≤ j
    · have hw : ∀ l, RankMatching.weight A l j = 0 := fun l =>
        (RankMatching.weight_zero_or_one A hA l j).resolve_right (h l)
      have hs := RankMatching.sum_interval_difference
        (fun l => (RankMatching.increment A l j : ℤ)) L j (by omega)
      simp_rw [← RankMatching.weight_eq_increment_sub A hA, hw] at hs
      rw [RankMatching.increment_zero A hA (show j < j + 1 by omega)] at hs
      simpa using hs.symm
    · exact RankMatching.increment_zero A hA (by omega)
  · intro h l hm
    have hi := (RankMatching.matched_iff_increments A hA l j).mp hm
    rw [h l] at hi
    exact Nat.zero_ne_one hi.1

theorem unmatched_iff_kernel [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a) (j : ℤ) :
    (∀ l, ¬ RankMatching.Matched (matrixOf a) l j) ↔
      ∃ f, a f = 0 ∧ HasLeadingTerm f j := by
  rw [unmatched_iff_increments_zero _ (matrixOf_triangular a ha)]
  constructor
  · intro h
    let S : ℤ → Set (LaurentSeries k) := fun L =>
      {f | HasLeadingTerm f j ∧ a f ∈ poleLattice (L - 1)}
    have hc : ∀ L, IsClosed (S L) := fun L =>
      (isClosed_leadingTerm j).inter
        ((isClosed_poleLattice (L - 1)).preimage (continuous_of_preservesPoles a ha))
    have hk : ∀ L, IsCompact (S L) := fun L =>
      (isCompact_leadingTerm j).of_isClosed_subset (hc L) (fun _ h => h.1)
    have hn : ∀ L, (S L).Nonempty := fun L =>
      (increment_zero_iff_finite_solution a ha L j).mp (h L)
    have hd : Directed (fun s t : Set (LaurentSeries k) => s ⊇ t) S := by
      intro L M
      refine ⟨min L M, ?_, ?_⟩
      · intro f hf
        exact ⟨hf.1, poleLattice_mono (by omega) hf.2⟩
      · intro f hf
        exact ⟨hf.1, poleLattice_mono (by omega) hf.2⟩
    obtain ⟨f,hf⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hd hn hk hc
    have hf' : ∀ L, f ∈ S L := Set.mem_iInter.mp hf
    refine ⟨f, ?_, (hf' j).1⟩
    apply HahnSeries.ext
    funext n
    simpa using (hf' (-n)).2 (-n) (by omega)
  · rintro ⟨f,haf,hfj⟩ L
    apply (increment_zero_iff_finite_solution a ha L j).mpr
    exact ⟨f,hfj,haf ▸ (poleLattice (L - 1)).zero_mem⟩

lemma rowRank_step (A : Matrix ℤ ℤ k) (hA : RankMatching.Triangular A) (l J : ℤ) :
    RankMatching.blockRank A l J = RankMatching.blockRank A (l + 1) J +
      RankMatching.increment (RankMatching.reflected A) (-J) (-l) := by
  have h := RankMatching.blockRank_step (RankMatching.reflected A)
    (RankMatching.triangular_reflected A hA) (-J) (-l)
  simpa only [RankMatching.blockRank_reflected, neg_neg, neg_sub,
    Int.reduceNeg, sub_neg_eq_add, add_comm] using h

lemma matchedRow_iff_unequal_ranks (A : Matrix ℤ ℤ k)
    (hA : RankMatching.Triangular A) (l : ℤ) :
    (∃ j, RankMatching.Matched A l j) ↔
      ∃ J, RankMatching.blockRank A l J ≠ RankMatching.blockRank A (l + 1) J := by
  have hn : (∀ j, ¬ RankMatching.Matched A l j) ↔
      ∀ J, RankMatching.blockRank A l J = RankMatching.blockRank A (l + 1) J := by
    have hh := unmatched_iff_increments_zero (RankMatching.reflected A)
      (RankMatching.triangular_reflected A hA) (-l)
    constructor
    · intro h J
      have hh' : ∀ r, ¬ RankMatching.Matched (RankMatching.reflected A) r (-l) := by
        intro r hr
        apply h (-r)
        simpa only [RankMatching.Matched, RankMatching.weight_reflected, neg_neg] using hr
      rw [rowRank_step A hA l J, hh.mp hh' (-J), add_zero]
    · intro h j hm
      have hh' : ∀ r, RankMatching.increment (RankMatching.reflected A) r (-l) = 0 := by
        intro r
        have hs := rowRank_step A hA l (-r)
        rw [neg_neg, h (-r)] at hs
        omega
      apply hh.mpr hh' (-j)
      simpa only [RankMatching.Matched, RankMatching.weight_reflected, neg_neg] using hm
  simpa only [not_forall, not_not] using not_congr hn

lemma exists_rowCut_kernel_of_unequal_ranks (A : Matrix ℤ ℤ k)
    (hA : RankMatching.Triangular A) (l J : ℤ)
    (hr : RankMatching.blockRank A l J ≠ RankMatching.blockRank A (l + 1) J) :
    ∃ v ∈ RankMatching.columnSpace A l J,
      RankMatching.rowCut (l + 1) v = 0 ∧ v l ≠ 0 := by
  let F : RankMatching.columnSpace A l J →ₗ[k] RankMatching.columnSpace A (l + 1) J :=
    (RankMatching.rowCut (l + 1)).restrict
      (fun _ hv => RankMatching.rowCut_columnSpace A (by omega) J hv)
  have hs : Function.Surjective F := by
    intro v
    have hm : (v : ℤ → k) ∈ (RankMatching.columnSpace A l J).map
        (RankMatching.rowCut (l + 1)) := by
      rw [RankMatching.rowCut_map_columnSpace A (by omega)]
      exact v.property
    obtain ⟨w,hw,he⟩ := Submodule.mem_map.mp hm
    exact ⟨⟨w,hw⟩, Subtype.ext he⟩
  have hni : ¬ Function.Injective F := by
    intro hi
    apply hr
    have he := (LinearEquiv.ofBijective F ⟨hi,hs⟩).finrank_eq
    simpa only [RankMatching.blockRank_eq_finrank A hA] using he
  have hk : F.ker ≠ ⊥ := fun h => hni (LinearMap.ker_eq_bot.mp h)
  obtain ⟨v,hv,hvz⟩ := F.ker.ne_bot_iff.mp hk
  have hcut : RankMatching.rowCut (l + 1) (v : ℤ → k) = 0 :=
    congrArg Subtype.val (show F v = 0 from hv)
  refine ⟨v, v.property, hcut, ?_⟩
  intro hvl
  apply hvz
  apply Subtype.ext
  funext r
  rcases lt_trichotomy r l with hlt | heq | hgt
  · exact RankMatching.columnSpace_supported A l J v.property hlt
  · simpa [heq] using hvl
  · have he := congrFun hcut r
    simpa [RankMatching.rowCut, hgt] using he

theorem matched_row_iff_image
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a) (l : ℤ) :
    (∃ j, RankMatching.Matched (matrixOf a) l j) ↔
      ∃ f, HasLeadingPosition (a f) l := by
  rw [matchedRow_iff_unequal_ranks _ (matrixOf_triangular a ha)]
  constructor
  · rintro ⟨J,hJ⟩
    obtain ⟨v,hv,hcut,hvl⟩ := exists_rowCut_kernel_of_unequal_ranks
      (matrixOf a) (matrixOf_triangular a ha) l J hJ
    rw [columnSpace_eq_projectedImage a ha] at hv
    obtain ⟨z,⟨f,hf,rfl⟩,rfl⟩ := hv
    refine ⟨f, ?_, ?_⟩
    · intro i hi
      have he := congrFun hcut i
      simpa [RankMatching.rowCut, poleProjection, hi,
        show l ≤ i by omega] using he
    · simpa [poleProjection] using hvl
  · rintro ⟨f,hf,hfl⟩
    obtain ⟨J,hJ⟩ := exists_poleLattice f
    refine ⟨J, ?_⟩
    intro heq
    have hv : poleProjection l (a f) ∈ RankMatching.columnSpace (matrixOf a) l J := by
      rw [columnSpace_eq_projectedImage a ha]
      exact ⟨a f,⟨f,hJ,rfl⟩,rfl⟩
    have hcut : RankMatching.rowCut (l + 1) (poleProjection l (a f)) = 0 := by
      ext i
      by_cases hi : l + 1 ≤ i
      · simp [RankMatching.rowCut, poleProjection, show l ≤ i by omega,
          hf i (by omega)]
      · simp [RankMatching.rowCut, show ¬ l < i by omega]
    have hi := RankMatching.rowCut_injOn_of_equal_ranks
      (matrixOf a) (matrixOf_triangular a ha) l J heq
    have he : poleProjection l (a f) = 0 := hi hv (Submodule.zero_mem _) (by simpa using hcut)
    apply hfl
    simpa [poleProjection] using congrFun he l

def stageImage (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J : ℤ) :
    Submodule k (LaurentSeries k) := (poleLattice J).map a

lemma stageImage_mono (a : LaurentSeries k →ₗ[k] LaurentSeries k) : Monotone (stageImage a) := by
  intro I J h
  exact Submodule.map_mono (poleLattice_mono h)

lemma stageImage_le_poleLattice (a : LaurentSeries k →ₗ[k] LaurentSeries k)
    (ha : PreservesPoles a) (J : ℤ) : stageImage a J ≤ poleLattice J := by
  rintro z ⟨f,hf,rfl⟩
  exact ha J f hf

lemma stageImage_step (a : LaurentSeries k →ₗ[k] LaurentSeries k) (j : ℤ) :
    stageImage a j = stageImage a (j - 1) ⊔ Submodule.span k {a (monomial j)} := by
  apply le_antisymm
  · rintro z ⟨f,hf,rfl⟩
    have ht : f - f.coeff (-j) • monomial j ∈ poleLattice (j - 1) := by
      intro i hi
      by_cases hij : i = j
      · subst i; simp [HahnSeries.coeff_sub, HahnSeries.coeff_smul]
      · simp [HahnSeries.coeff_sub, HahnSeries.coeff_smul, coeff_monomial, hij,
          hf i (by omega)]
    apply Submodule.mem_sup.mpr
    refine ⟨a (f - f.coeff (-j) • monomial j), ⟨_,ht,rfl⟩,
      f.coeff (-j) • a (monomial j),
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)), ?_⟩
    simp
  · apply sup_le (stageImage_mono a (by omega))
    rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨monomial j, monomial_mem le_rfl, rfl⟩

lemma monomial_image_mem_iff_unmatched [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a) (j : ℤ) :
    a (monomial j) ∈ stageImage a (j - 1) ↔
      ∀ l, ¬ RankMatching.Matched (matrixOf a) l j := by
  rw [unmatched_iff_kernel a ha]
  constructor
  · rintro ⟨g,hg,he⟩
    refine ⟨monomial j - g, by simp [he], ?_, ?_⟩
    · intro i hi
      simp [HahnSeries.coeff_sub, coeff_monomial, show i ≠ j by omega, hg i (by omega)]
    · simp [HahnSeries.coeff_sub, hg j (by omega)]
  · rintro ⟨f,haf,hf,hfj⟩
    refine ⟨monomial j - f, ?_, by simp [haf]⟩
    intro i hi
    by_cases hij : i = j
    · subst i; simp [HahnSeries.coeff_sub, hfj]
    · simp [HahnSeries.coeff_sub, coeff_monomial, hij, hf i (by omega)]

def imageModulo (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J N : ℤ) :
    Submodule k (LaurentSeries k ⧸ stageImage a J) :=
  (stageImage a N).map (stageImage a J).mkQ

lemma imageModulo_mono (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J : ℤ) :
    Monotone (imageModulo a J) := fun _ _ h => Submodule.map_mono (stageImage_mono a h)

lemma imageModulo_zero (a : LaurentSeries k →ₗ[k] LaurentSeries k) {J N : ℤ} (h : N ≤ J) :
    imageModulo a J N = ⊥ := by
  apply le_antisymm _ bot_le
  rw [imageModulo, Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
  exact stageImage_mono a h

lemma imageModulo_step (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J n : ℤ) :
    imageModulo a J n = imageModulo a J (n - 1) ⊔
      Submodule.span k {(stageImage a J).mkQ (a (monomial n))} := by
  rw [imageModulo, stageImage_step a n, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
  rfl

lemma imageModulo_finite (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J N : ℤ) :
    FiniteDimensional k (imageModulo a J N) := by
  by_cases h : J ≤ N
  · induction N, h using Int.leInduction with
    | base => rw [imageModulo_zero a le_rfl]; infer_instance
    | succ n hn ih =>
      rw [imageModulo_step, add_sub_cancel_right]
      let := ih
      infer_instance
  · rw [imageModulo_zero a (by omega)]
    infer_instance

lemma mem_imageModulo (a : LaurentSeries k →ₗ[k] LaurentSeries k) {J N : ℤ}
    (h : J ≤ N) (f : LaurentSeries k) :
    (stageImage a J).mkQ f ∈ imageModulo a J N ↔ f ∈ stageImage a N := by
  change f ∈ ((stageImage a N).map (stageImage a J).mkQ).comap (stageImage a J).mkQ ↔ _
  rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr (stageImage_mono a h)]

open scoped Classical

lemma imageModulo_finrank_step [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a) {J n : ℤ}
    (h : J < n) :
    Module.finrank k (imageModulo a J n) = Module.finrank k (imageModulo a J (n - 1)) +
      if ∃ l, RankMatching.Matched (matrixOf a) l n then 1 else 0 := by
  classical
  let := imageModulo_finite a J (n - 1)
  rw [imageModulo_step, RankMatching.finrank_sup_singleton,
    mem_imageModulo a (by omega), monomial_image_mem_iff_unmatched a ha]
  by_cases hm : ∃ l, RankMatching.Matched (matrixOf a) l n
  · have hn : ¬ (∀ l, ¬ RankMatching.Matched (matrixOf a) l n) :=
      fun hh => hh hm.choose hm.choose_spec
    simp [hm, hn]
  · simp [show ∀ l, ¬ RankMatching.Matched (matrixOf a) l n from fun l hl => hm ⟨l,hl⟩]

lemma imageModulo_finrank [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a) (J N : ℤ) :
    Module.finrank k (imageModulo a J N) =
      ∑ j ∈ Finset.Ioc J N, if ∃ l, RankMatching.Matched (matrixOf a) l j then 1 else 0 := by
  classical
  by_cases h : J ≤ N
  · induction N, h using Int.leInduction with
    | base => rw [imageModulo_zero a (J := J) (N := J) le_rfl, finrank_bot]; simp
    | succ n hn ih =>
      have he : Finset.Ioc J (n + 1) = insert (n + 1) (Finset.Ioc J n) := by
        ext i
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      rw [imageModulo_finrank_step a ha (by omega), add_sub_cancel_right, ih,
        he, Finset.sum_insert (by simp)]
      omega
  · rw [imageModulo_zero a (by omega), finrank_bot, Finset.Ioc_eq_empty_of_le (by omega),
      Finset.sum_empty]

lemma matched_le (A : Matrix ℤ ℤ k) (hA : RankMatching.Triangular A) {l j : ℤ}
    (h : RankMatching.Matched A l j) : l ≤ j := by
  by_contra hn
  have hz := RankMatching.increment_zero A hA (lt_of_not_ge hn)
  have ho := ((RankMatching.matched_iff_increments A hA l j).mp h).1
  omega

def columnMatches (A : Matrix ℤ ℤ k) (J N : ℤ) : Set (ℤ × ℤ) :=
  {p | RankMatching.Matched A p.1 p.2 ∧ J < p.2 ∧ p.2 ≤ N}

def crossingStageMatches (A : Matrix ℤ ℤ k) (J N : ℤ) : Set (ℤ × ℤ) :=
  {p | RankMatching.Matched A p.1 p.2 ∧ p.1 ≤ J ∧ J < p.2 ∧ p.2 ≤ N}

lemma columnMatches_snd_inj (A : Matrix ℤ ℤ k) (hA : RankMatching.Triangular A)
    (J N : ℤ) : Set.InjOn Prod.snd (columnMatches A J N) := by
  rintro ⟨l,j⟩ hp ⟨l',j'⟩ hq he
  change j = j' at he
  subst j'
  exact Prod.ext (RankMatching.column_unique A hA hp.1 hq.1) rfl

lemma columnMatches_finite (A : Matrix ℤ ℤ k) (hA : RankMatching.Triangular A)
    (J N : ℤ) : (columnMatches A J N).Finite := by
  exact Set.Finite.of_injOn (fun _ hp => hp.2) (columnMatches_snd_inj A hA J N)
    (Set.finite_Ioc J N)

lemma columnMatches_ncard (A : Matrix ℤ ℤ k) (hA : RankMatching.Triangular A)
    (J N : ℤ) : (columnMatches A J N).ncard =
      ∑ j ∈ Finset.Ioc J N, if ∃ l, RankMatching.Matched A l j then 1 else 0 := by
  classical
  have he : Prod.snd '' columnMatches A J N =
      ↑((Finset.Ioc J N).filter (fun j => ∃ l, RankMatching.Matched A l j)) := by
    ext j
    simp only [Set.mem_image, columnMatches, Set.mem_ofPred_eq, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨l,j'⟩,⟨hm,hJ,hN⟩,rfl⟩
      exact ⟨⟨hJ,hN⟩,l,hm⟩
    · rintro ⟨⟨hJ,hN⟩,l,hm⟩
      exact ⟨(l,j),⟨hm,hJ,hN⟩,rfl⟩
  rw [← (columnMatches_snd_inj A hA J N).ncard_image, he,
    Set.ncard_coe_finset, Finset.sum_boole]
  rfl

lemma columnMatches_partition (A : Matrix ℤ ℤ k) (hA : RankMatching.Triangular A)
    (J N : ℤ) :
    (columnMatches A J N).ncard = (crossingStageMatches A J N).ncard +
      RankMatching.blockRank A (J + 1) N := by
  classical
  let high := ((Finset.Icc (J + 1) N ×ˢ Finset.Icc (J + 1) N).filter
    (fun p : ℤ × ℤ => RankMatching.Matched A p.1 p.2))
  have he : columnMatches A J N = crossingStageMatches A J N ∪ (high : Set (ℤ × ℤ)) := by
    ext p
    simp only [columnMatches, crossingStageMatches, Set.mem_ofPred_eq, Set.mem_union,
      high, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨hm,hJ,hN⟩
      by_cases hl : p.1 ≤ J
      · exact Or.inl ⟨hm,hl,hJ,hN⟩
      · have hh := matched_le A hA hm
        exact Or.inr ⟨⟨⟨by omega,by omega⟩,⟨by omega,hN⟩⟩,hm⟩
    · rintro (⟨hm,hl,hJ,hN⟩ | ⟨⟨hl,hj⟩,hm⟩)
      · exact ⟨hm,hJ,hN⟩
      · exact ⟨hm,by omega,hj.2⟩
  have hd : Disjoint (crossingStageMatches A J N) (high : Set (ℤ × ℤ)) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    simp only [high, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at hq
    have hh := hp.2.1
    omega
  have hf : (crossingStageMatches A J N).Finite :=
    (columnMatches_finite A hA J N).subset (fun _ h => ⟨h.1,h.2.2⟩)
  rw [he, Set.ncard_union_eq hd hf high.finite_toSet, Set.ncard_coe_finset,
    RankMatching.rank_eq_count A hA]
  rfl

lemma imageModulo_finrank_partition [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a) (J N : ℤ) :
    Module.finrank k (imageModulo a J N) =
      (crossingStageMatches (matrixOf a) J N).ncard + RankMatching.blockRank (matrixOf a) (J + 1) N := by
  rw [imageModulo_finrank a ha, ← columnMatches_ncard _ (matrixOf_triangular a ha),
    columnMatches_partition _ (matrixOf_triangular a ha)]

lemma stageImage_le_ker_projection (a : LaurentSeries k →ₗ[k] LaurentSeries k)
    (ha : PreservesPoles a) (J : ℤ) : stageImage a J ≤ (poleProjection (J + 1)).ker := by
  intro f hf
  change poleProjection (J + 1) f = 0
  apply poleProjection_eq_zero.mpr
  simpa using stageImage_le_poleLattice a ha J hf

def quotientProjection (a : LaurentSeries k →ₗ[k] LaurentSeries k)
    (ha : PreservesPoles a) (J : ℤ) :
    (LaurentSeries k ⧸ stageImage a J) →ₗ[k] (ℤ → k) :=
  (stageImage a J).liftQ (poleProjection (J + 1)) (stageImage_le_ker_projection a ha J)

@[simp] lemma quotientProjection_mkQ (a : LaurentSeries k →ₗ[k] LaurentSeries k)
    (ha : PreservesPoles a) (J : ℤ) (f : LaurentSeries k) :
    quotientProjection a ha J ((stageImage a J).mkQ f) = poleProjection (J + 1) f := rfl

def crossingStage (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J N : ℤ) :
    Submodule k (LaurentSeries k ⧸ stageImage a J) :=
  (stageImage a N ⊓ poleLattice J).map (stageImage a J).mkQ

lemma crossingStage_mono (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J : ℤ) :
    Monotone (crossingStage a J) := fun _ _ h =>
  Submodule.map_mono (inf_le_inf_right _ (stageImage_mono a h))

lemma crossingStage_finite (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J N : ℤ) :
    FiniteDimensional k (crossingStage a J N) := by
  let := imageModulo_finite a J N
  exact Submodule.finiteDimensional_of_le (show crossingStage a J N ≤ imageModulo a J N
    from Submodule.map_mono inf_le_left)

lemma crossingStage_eq_inf (a : LaurentSeries k →ₗ[k] LaurentSeries k)
    (ha : PreservesPoles a) (J N : ℤ) :
    crossingStage a J N = imageModulo a J N ⊓ (quotientProjection a ha J).ker := by
  ext z
  constructor
  · rintro ⟨f,⟨hf,hJ⟩,rfl⟩
    exact ⟨⟨f,hf,rfl⟩, poleProjection_eq_zero.mpr (by simpa using hJ)⟩
  · rintro ⟨⟨f,hf,rfl⟩,hz⟩
    refine ⟨f,⟨hf,?_⟩,rfl⟩
    have he : poleProjection (J + 1) f = 0 := hz
    simpa using poleProjection_eq_zero.mp he

lemma quotientProjection_stage_range (a : LaurentSeries k →ₗ[k] LaurentSeries k)
    (ha : PreservesPoles a) (J N : ℤ) :
    ((quotientProjection a ha J).domRestrict (imageModulo a J N)).range =
      RankMatching.columnSpace (matrixOf a) (J + 1) N := by
  rw [LinearMap.range_domRestrict, columnSpace_eq_projectedImage a ha]
  ext v
  constructor
  · rintro ⟨z,⟨f,hf,rfl⟩,rfl⟩
    exact ⟨f,hf,rfl⟩
  · rintro ⟨f,hf,rfl⟩
    exact ⟨(stageImage a J).mkQ f, ⟨f,hf,rfl⟩,rfl⟩

lemma crossingStage_finrank [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a) (J N : ℤ) :
    Module.finrank k (crossingStage a J N) = (crossingStageMatches (matrixOf a) J N).ncard := by
  let := imageModulo_finite a J N
  let f := (quotientProjection a ha J).domRestrict (imageModulo a J N)
  have hr := LinearMap.finrank_range_add_finrank_ker f
  have hk : Module.finrank k f.ker = Module.finrank k (crossingStage a J N) := by
    rw [← Submodule.finrank_map_subtype_eq (imageModulo a J N) f.ker,
      show f.ker = ((quotientProjection a ha J).ker).comap (imageModulo a J N).subtype
        from LinearMap.ker_domRestrict _ _,
      Submodule.map_comap_subtype, ← crossingStage_eq_inf a ha]
  have hi : Module.finrank k f.range = RankMatching.blockRank (matrixOf a) (J + 1) N := by
    rw [quotientProjection_stage_range, ← RankMatching.blockRank_eq_finrank _ (matrixOf_triangular a ha)]
  rw [hk,hi,imageModulo_finrank_partition a ha] at hr
  omega

def crossingSpace (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J : ℤ) :
    Submodule k (LaurentSeries k ⧸ stageImage a J) :=
  (a.range ⊓ poleLattice J).map (stageImage a J).mkQ

lemma crossingStage_le_space (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J N : ℤ) :
    crossingStage a J N ≤ crossingSpace a J := by
  apply Submodule.map_mono
  apply inf_le_inf_right
  rintro f ⟨g,hg,rfl⟩
  exact ⟨g,rfl⟩

lemma crossingSpace_stabilizes [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a)
    (J : ℤ) (hc : (crossing a J).Finite) :
    ∃ N : ℤ, J ≤ N ∧ crossingSpace a J = crossingStage a J N ∧
      crossingStageMatches (matrixOf a) J N = crossing a J := by
  obtain ⟨b,hb⟩ := (hc.image Prod.snd).bddAbove
  let N := max J b
  have he (M : ℤ) (hM : N ≤ M) :
      crossingStageMatches (matrixOf a) J M = crossing a J := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1,hp.2.1,hp.2.2.1⟩
    · intro hp
      exact ⟨hp.1,hp.2.1,hp.2.2,le_trans (hb ⟨p,hp,rfl⟩) (le_trans (le_max_right J b) hM)⟩
  refine ⟨N, le_max_left _ _, ?_, he N le_rfl⟩
  apply le_antisymm _ (crossingStage_le_space a J N)
  rintro z ⟨f,⟨⟨x,hx⟩,hf⟩,rfl⟩
  obtain ⟨M,hM⟩ := exists_poleLattice x
  have heq : crossingStage a J N = crossingStage a J (max N M) := by
    let := crossingStage_finite a J (max N M)
    apply Submodule.eq_of_le_of_finrank_eq (crossingStage_mono a J (le_max_left _ _))
    rw [crossingStage_finrank a ha, crossingStage_finrank a ha,
      he N le_rfl, he (max N M) (le_max_left _ _)]
  rw [heq]
  exact ⟨f,⟨⟨x,poleLattice_mono (le_max_right N M) hM,hx⟩,hf⟩,rfl⟩

def crossingQuotientEquiv (a : LaurentSeries k →ₗ[k] LaurentSeries k) (J : ℤ) :
    crossingQuotient a J ≃ₗ[k] crossingSpace a J := by
  let I := a.range ⊓ poleLattice (k := k) J
  let f := (stageImage a J).mkQ.domRestrict I
  have hk : f.ker = (stageImage a J).comap I.subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ]
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ (LinearMap.range_domRestrict _ _)))

theorem crossing_dimension [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a)
    (hc : ∀ J, (crossing a J).Finite) (J : ℤ) :
    FiniteDimensional k (crossingQuotient a J) ∧
      Module.finrank k (crossingQuotient a J) = (crossing a J).ncard := by
  obtain ⟨N,hN,he,hcN⟩ := crossingSpace_stabilizes a ha J (hc J)
  have : FiniteDimensional k (crossingSpace a J) := by
    rw [he]
    exact crossingStage_finite a J N
  refine ⟨(crossingQuotientEquiv a J).symm.finiteDimensional, ?_⟩
  rw [(crossingQuotientEquiv a J).finrank_eq, he, crossingStage_finrank a ha, hcN]

lemma range_inf_stabilizes [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a)
    (J : ℤ) (hc : (crossing a J).Finite) :
    ∃ N : ℤ, a.range ⊓ poleLattice J = stageImage a N ⊓ poleLattice J := by
  obtain ⟨N,hN,he,_⟩ := crossingSpace_stabilizes a ha J hc
  refine ⟨N,le_antisymm ?_ ?_⟩
  · intro f hf
    have hq : (stageImage a J).mkQ f ∈ crossingStage a J N := by
      rw [← he]
      exact ⟨f,hf,rfl⟩
    have hi : (stageImage a J).mkQ f ∈ imageModulo a J N :=
      (Submodule.map_mono (show stageImage a N ⊓ poleLattice J ≤ stageImage a N
        from inf_le_left)) hq
    exact ⟨(mem_imageModulo a hN f).mp hi,hf.2⟩
  · rintro f ⟨⟨x,hx,rfl⟩,hf⟩
    exact ⟨⟨x,rfl⟩,hf⟩

lemma isCompact_range_inter_poleLattice [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a)
    (J : ℤ) (hc : (crossing a J).Finite) :
    IsCompact ((Set.range a) ∩ (poleLattice (k := k) J : Set (LaurentSeries k))) := by
  obtain ⟨N,he⟩ := range_inf_stabilizes a ha J hc
  change IsCompact (↑(a.range ⊓ poleLattice J) : Set (LaurentSeries k))
  rw [he]
  change IsCompact ((a '' (poleLattice (k := k) N : Set (LaurentSeries k))) ∩
    (poleLattice (k := k) J : Set (LaurentSeries k)))
  exact ((isCompact_poleLattice N).image (continuous_of_preservesPoles a ha)).inter_right
    (isClosed_poleLattice J)

theorem closed_image [Finite k]
    (a : LaurentSeries k →ₗ[k] LaurentSeries k) (ha : PreservesPoles a)
    (hc : ∀ J, (crossing a J).Finite) :
    IsClosed (Set.range a) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro f hf
  obtain ⟨J,hJ⟩ := exists_poleLattice f
  refine ⟨(poleLattice (k := k) J : Set (LaurentSeries k)) ∩
    ((Set.range a) ∩ (poleLattice (k := k) J : Set (LaurentSeries k)))ᶜ, ?_, ?_, ?_⟩
  · intro g hg hga
    exact hg.2 ⟨hga,hg.1⟩
  · exact (isOpen_poleLattice J).inter
      (isCompact_range_inter_poleLattice a ha J (hc J)).isClosed.isOpen_compl
  · exact ⟨hJ,fun h => hf h.1⟩

end HahnWilson.PivotTopology

end

end OAI
