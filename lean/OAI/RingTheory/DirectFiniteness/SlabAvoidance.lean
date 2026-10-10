import OAI.RingTheory.DirectFiniteness.CandidateBounds

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace KaplanskyCounterexample.FiniteLocalLemma

variable {Ω : Type u_1} {ι : Type u_2}

/-- Avoid a finite list of bad events. -/
def avoid (E : ι → Set Ω) (s : Finset ι) : Set Ω := ⋂ i ∈ s, (E i)ᶜ

@[simp] lemma mem_avoid {E : ι → Set Ω} {s : Finset ι} {ω : Ω} :
    ω ∈ avoid E s ↔ ∀ i ∈ s, ω ∉ E i := by simp [avoid]

@[simp] lemma avoid_empty (E : ι → Set Ω) : avoid E ∅ = Set.univ := by
  simp [avoid]

variable [DecidableEq ι]

lemma avoid_insert (E : ι → Set Ω) (s : Finset ι) (i : ι) :
    avoid E (insert i s) = avoid E s \ E i := by
  ext ω
  simp only [mem_avoid, Finset.mem_insert, forall_eq_or_imp, mem_sdiff]
  tauto

lemma avoid_union (E : ι → Set Ω) (s t : Finset ι) :
    avoid E (s ∪ t) = avoid E s ∩ avoid E t := by
  ext ω
  simp only [mem_avoid, Finset.mem_union, mem_inter_iff, or_imp, forall_and]

omit [DecidableEq ι] in
lemma avoid_anti (E : ι → Set Ω) {s t : Finset ι} (h : s ⊆ t) :
    avoid E t ⊆ avoid E s := by
  intro ω hω
  exact mem_avoid.mpr fun i hi => mem_avoid.mp hω i (h hi)

variable [MeasurableSpace Ω]

omit [DecidableEq ι] in
lemma measurable_avoid {E : ι → Set Ω} (hE : ∀ i, MeasurableSet (E i))
    (s : Finset ι) : MeasurableSet (avoid E s) :=
  s.measurableSet_biInter fun i _ => (hE i).compl

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {E : ι → Set Ω}

lemma prob_avoid_insert (hE : ∀ i, MeasurableSet (E i)) (s : Finset ι) (i : ι) :
    μ.real (avoid E (insert i s)) =
      μ.real (avoid E s) - μ.real (E i ∩ avoid E s) := by
  rw [avoid_insert]
  have h := measureReal_inter_add_sdiff (μ := μ) (s := avoid E s) (hE i)
  rw [Set.inter_comm (avoid E s) (E i)] at h
  linarith

/-- Successive avoidance bounds, in multiplication form (no conditional measure
or division by a possibly zero probability). -/
lemma avoid_union_lower {x : ι → ℝ} (hE : ∀ i, MeasurableSet (E i))
    (hx : ∀ i, 0 ≤ 1 - x i) (s t : Finset ι) (hd : Disjoint s t)
    (hc : ∀ (u : Finset ι), u ⊆ s ∪ t → ∀ i ∈ t, i ∉ u →
      μ.real (E i ∩ avoid E u) ≤ x i * μ.real (avoid E u)) :
    (∏ i ∈ t, (1 - x i)) * μ.real (avoid E s) ≤ μ.real (avoid E (s ∪ t)) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have hdst : Disjoint s t := hd.mono_right (Finset.subset_insert _ _)
    have his : i ∉ s := fun his => Finset.disjoint_left.mp hd his (Finset.mem_insert_self _ _)
    have hit : i ∉ s ∪ t := by simp [his, hi]
    have hsub : s ∪ t ⊆ s ∪ insert i t :=
      Finset.union_subset_union_right (Finset.subset_insert _ _)
    have hct : ∀ u : Finset ι, u ⊆ s ∪ t → ∀ j ∈ t, j ∉ u →
        μ.real (E j ∩ avoid E u) ≤ x j * μ.real (avoid E u) := by
      intro u hu j hj hju
      exact hc u (hu.trans hsub) j (Finset.mem_insert_of_mem hj) hju
    have hlower := ih hdst hct
    have hlast := hc (s ∪ t) hsub i (Finset.mem_insert_self _ _) hit
    rw [Finset.prod_insert hi, mul_assoc]
    calc
      (1 - x i) * ((∏ j ∈ t, (1 - x j)) * μ.real (avoid E s))
          ≤ (1 - x i) * μ.real (avoid E (s ∪ t)) :=
        mul_le_mul_of_nonneg_left hlower (hx i)
      _ ≤ μ.real (avoid E (s ∪ insert i t)) := by
        rw [Finset.union_insert, prob_avoid_insert hE]
        nlinarith

/-- Product-form asymmetric Lovász local lemma on a finite event list.
The independence hypothesis is the usual independence from all non-neighbors
jointly, written directly as an equality of real probabilities. -/
theorem asymmetric {x : ι → ℝ} (hE : ∀ i, MeasurableSet (E i))
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (Γ : ι → Finset ι)
    (hind : ∀ i (s : Finset ι), i ∉ s → Disjoint s (Γ i) →
      μ.real (E i ∩ avoid E s) = μ.real (E i) * μ.real (avoid E s))
    (hprob : ∀ i, μ.real (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∀ s : Finset ι, 0 < μ.real (avoid E s) ∧
      ∀ i ∉ s, μ.real (E i ∩ avoid E s) ≤ x i * μ.real (avoid E s) := by
  intro s
  induction s using Finset.strongInductionOn with | _ s ih
  have hxp : ∀ i, 0 < 1 - x i := fun i => sub_pos.mpr (hx1 i)
  have hxn : ∀ i, 0 ≤ 1 - x i := fun i => (hxp i).le
  have hpos : 0 < μ.real (avoid E s) := by
    by_cases hs : s = ∅
    · simp [hs, probReal_univ]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have ht : s.erase i ⊂ s := Finset.erase_ssubset hi
      obtain ⟨hprev, hcond⟩ := ih (s.erase i) ht
      have hc := hcond i (Finset.notMem_erase i s)
      have hins : insert i (s.erase i) = s := Finset.insert_erase hi
      rw [← hins, prob_avoid_insert hE]
      have hm := mul_pos (hxp i) hprev
      nlinarith
  refine ⟨hpos, ?_⟩
  intro i his
  let t := s \ Γ i
  let u := s ∩ Γ i
  have hts : t ⊆ s := Finset.sdiff_subset
  have hus : u ⊆ s := Finset.inter_subset_left
  have htu : Disjoint t u := by
    apply Finset.disjoint_left.mpr
    intro j hjt hju
    exact (Finset.mem_sdiff.mp hjt).2 (Finset.mem_inter.mp hju).2
  have hsu : t ∪ u = s := by
    ext j
    simp only [t, u, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have htg : Disjoint t (Γ i) := by
    apply Finset.disjoint_left.mpr
    intro j hjt hjg
    exact (Finset.mem_sdiff.mp hjt).2 hjg
  have hit : i ∉ t := fun h => his (hts h)
  have heq := hind i t hit htg
  have hnum : μ.real (E i ∩ avoid E s) ≤ μ.real (E i) * μ.real (avoid E t) := by
    rw [← heq]
    exact measureReal_mono (Set.inter_subset_inter_right _ (avoid_anti E hts))
  have hchain : (∏ j ∈ u, (1 - x j)) * μ.real (avoid E t) ≤ μ.real (avoid E s) := by
    rw [← hsu]
    apply avoid_union_lower hE hxn t u htu
    intro v hv j hju hjv
    have hvs : v ⊂ s := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · simpa [hsu] using hv
      · intro he
        exact hjv (he.symm ▸ hus hju)
    exact (ih v hvs).2 j hjv
  have hprod : (∏ j ∈ Γ i, (1 - x j)) ≤ ∏ j ∈ u, (1 - x j) := by
    apply Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right
    · intro j _; exact hxn j
    · intro j _ _; linarith [hx0 j]
  calc
    μ.real (E i ∩ avoid E s) ≤ μ.real (E i) * μ.real (avoid E t) := hnum
    _ ≤ (x i * ∏ j ∈ u, (1 - x j)) * μ.real (avoid E t) := by
      apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
      exact (hprob i).trans (mul_le_mul_of_nonneg_left hprod (hx0 i))
    _ = x i * ((∏ j ∈ u, (1 - x j)) * μ.real (avoid E t)) := mul_assoc _ _ _
    _ ≤ x i * μ.real (avoid E s) := mul_le_mul_of_nonneg_left hchain (hx0 i)

/-- The elementary product bound used in the weighted local lemma. -/
lemma one_sub_sum_le_prod {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1) (s : Finset ι) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hsum : 0 ≤ ∑ j ∈ s, x j := Finset.sum_nonneg fun j _ => hx0 j
    have hm := mul_nonneg (hx0 i) hsum
    have hp := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hx1 i))
    nlinarith

section Weighted
variable {κ : Type u_3} [DecidableEq κ] [Fintype ι]

/-- The dependency graph obtained by sharing one of the assigned variables. -/
def neighbors (deps : ι → Finset κ) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => j ≠ i ∧ ¬Disjoint (deps i) (deps j)

/-- Total event weight at a random variable. -/
def load (deps : ι → Finset κ) (w : ι → ℝ) (v : κ) : ℝ :=
  ∑ i, if v ∈ deps i then w i else 0

omit [DecidableEq ι] in
lemma weight_le_load (deps : ι → Finset κ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) {i : ι} {v : κ} (hv : v ∈ deps i) :
    w i ≤ load deps w v := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => if v ∈ deps j then w j else 0)
    (fun j _ => by split_ifs; exact hw j; exact le_rfl) (Finset.mem_univ i)
  simpa [load, hv] using h

lemma neighbor_weight_le_loads (deps : ι → Finset κ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (i : ι) :
    ∑ j ∈ neighbors deps i, w j ≤ ∑ v ∈ deps i, load deps w v := by
  calc
    ∑ j ∈ neighbors deps i, w j
      ≤ ∑ j ∈ neighbors deps i, ∑ v ∈ deps i, if v ∈ deps j then w j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        have hnd := (Finset.mem_filter.mp hj).2.2
        obtain ⟨v, hvi, hvj⟩ := Finset.not_disjoint_iff.mp hnd
        have hh := Finset.single_le_sum (s := deps i)
          (f := fun v => if v ∈ deps j then w j else 0)
          (fun v _ => by split_ifs; exact hw j; exact le_rfl) hvi
        simpa [hvj] using hh
    _ ≤ ∑ j : ι, ∑ v ∈ deps i, if v ∈ deps j then w j else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro j _ _
        exact Finset.sum_nonneg fun v _ => by split_ifs; exact hw j; exact le_rfl
    _ = ∑ v ∈ deps i, load deps w v := by rw [Finset.sum_comm]; rfl

theorem weighted_four (hE : ∀ i, MeasurableSet (E i))
    (deps : ι → Finset κ) (hne : ∀ i, (deps i).Nonempty)
    (hcard : ∀ i, (deps i).card ≤ 4)
    (hload : ∀ v, load deps (fun i => μ.real (E i)) v ≤ 1 / 16)
    (hind : ∀ i (s : Finset ι), i ∉ s → Disjoint s (neighbors deps i) →
      μ.real (E i ∩ avoid E s) = μ.real (E i) * μ.real (avoid E s)) :
    0 < μ.real (avoid E Finset.univ) ∧ ∃ ω : Ω, ∀ i, ω ∉ E i := by
  let p : ι → ℝ := fun i => μ.real (E i)
  let x : ι → ℝ := fun i => 2 * p i
  have hp : ∀ i, 0 ≤ p i := fun _ => measureReal_nonneg
  have hpbound : ∀ i, p i ≤ 1 / 16 := by
    intro i
    obtain ⟨v, hv⟩ := hne i
    exact (weight_le_load deps hp hv).trans (hload v)
  have hx0 : ∀ i, 0 ≤ x i := fun i => mul_nonneg (by norm_num) (hp i)
  have hx1 : ∀ i, x i < 1 := by intro i; dsimp [x]; linarith [hpbound i]
  have hsum : ∀ i, ∑ j ∈ neighbors deps i, x j ≤ 1 / 2 := by
    intro i
    have hweights := neighbor_weight_le_loads deps hp i
    have hloads : (∑ v ∈ deps i, load deps p v) ≤ (deps i).card * (1 / 16 : ℝ) := by
      calc
        ∑ v ∈ deps i, load deps p v ≤ ∑ v ∈ deps i, (1 / 16 : ℝ) :=
          Finset.sum_le_sum fun v _ => hload v
        _ = _ := by simp
    have hcnt : ((deps i).card : ℝ) ≤ 4 := by exact_mod_cast hcard i
    simp only [x, ← Finset.mul_sum]
    nlinarith
  have hprob : ∀ i, μ.real (E i) ≤ x i * ∏ j ∈ neighbors deps i, (1 - x j) := by
    intro i
    have hprod := one_sub_sum_le_prod hx0 (fun j => (hx1 j).le) (neighbors deps i)
    have hhalf : (1 / 2 : ℝ) ≤ ∏ j ∈ neighbors deps i, (1 - x j) := by
      linarith [hsum i]
    have hm := mul_le_mul_of_nonneg_left hhalf (hx0 i)
    dsimp [x, p] at hm
    nlinarith
  have hh := (asymmetric hE hx0 hx1 (neighbors deps) hind hprob Finset.univ).1
  refine ⟨hh, ?_⟩
  have hset : (avoid E Finset.univ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, measureReal_empty] at hh
    exact lt_irrefl 0 hh
  obtain ⟨ω, hω⟩ := hset
  exact ⟨ω, fun i => mem_avoid.mp hω i (Finset.mem_univ i)⟩

end Weighted

section IndependentVariables
variable {κ : Type u_4} {β : Type u_5} [DecidableEq κ]

/-- An event is determined by a finite set of coordinates. -/
def DeterminedBy (f : κ → Ω → β) (s : Finset κ) (A : Set Ω) : Prop :=
  ∀ ω ω', (∀ v ∈ s, f v ω = f v ω') → (ω ∈ A ↔ ω' ∈ A)

omit [MeasurableSpace Ω] [DecidableEq κ] in
lemma preimage_image_of_determined {f : κ → Ω → β} {s : Finset κ} {A : Set Ω}
    (h : DeterminedBy f s A) :
    (fun ω (v : s) => f v ω) ⁻¹' ((fun ω (v : s) => f v ω) '' A) = A := by
  ext ω
  constructor
  · rintro ⟨ω', hω', heq⟩
    exact (h ω' ω (fun v hv => congrFun heq ⟨v, hv⟩)).mp hω'
  · intro hω
    exact ⟨ω, hω, rfl⟩

omit [DecidableEq ι] [MeasurableSpace Ω] in
lemma determined_avoid {f : κ → Ω → β} (deps : ι → Finset κ)
    (hdep : ∀ i, DeterminedBy f (deps i) (E i)) (s : Finset ι) :
    DeterminedBy f (s.biUnion deps) (avoid E s) := by
  intro ω ω' hω
  simp only [mem_avoid]
  have heq : ∀ i ∈ s, (ω ∈ E i ↔ ω' ∈ E i) := by
    intro i hi
    exact hdep i ω ω' fun v hv => hω v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)
  exact ⟨fun h i hi => (heq i hi).not.mp (h i hi),
    fun h i hi => (heq i hi).not.mpr (h i hi)⟩

variable [MeasurableSpace β] [MeasurableSingletonClass β] [Finite β]

omit [DecidableEq κ] in
lemma measurable_of_determined {f : κ → Ω → β} (hf : ∀ v, Measurable (f v))
    {s : Finset κ} {A : Set Ω} (h : DeterminedBy f s A) : MeasurableSet A := by
  rw [← preimage_image_of_determined h]
  apply MeasurableSet.preimage
  · exact (Set.toFinite _).countable.measurableSet
  · exact Measurable.of_eval fun v => hf v

omit [IsProbabilityMeasure μ] in
lemma independent_of_non_neighbors [Fintype ι] {f : κ → Ω → β}
    (hf : ∀ v, Measurable (f v)) (hf_ind : iIndepFun f μ)
    (deps : ι → Finset κ) (hdep : ∀ i, DeterminedBy f (deps i) (E i))
    (i : ι) (s : Finset ι) (his : i ∉ s) (hd : Disjoint s (neighbors deps i)) :
    μ.real (E i ∩ avoid E s) = μ.real (E i) * μ.real (avoid E s) := by
  have hdv : Disjoint (deps i) (s.biUnion deps) := by
    apply Finset.disjoint_left.mpr
    intro v hvi hvs
    obtain ⟨j, hjs, hvj⟩ := Finset.mem_biUnion.mp hvs
    have hji : j ≠ i := by intro h; exact his (h ▸ hjs)
    have hjn : j ∈ neighbors deps i := by
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hji, Finset.not_disjoint_iff.mpr ⟨v, hvi, hvj⟩⟩
    exact Finset.disjoint_left.mp hd hjs hjn
  have hp := hf_ind.indepFun_finset (deps i) (s.biUnion deps) hdv hf
  have heq := hp.measure_inter_preimage_eq_mul
    ((fun ω (v : deps i) => f v ω) '' E i)
    ((fun ω (v : s.biUnion deps) => f v ω) '' avoid E s)
    ((Set.toFinite _).countable.measurableSet)
    ((Set.toFinite _).countable.measurableSet)
  rw [preimage_image_of_determined (hdep i),
    preimage_image_of_determined (determined_avoid deps hdep s)] at heq
  simpa only [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal heq

theorem weighted_four_independent [Fintype ι] {f : κ → Ω → β}
    (hf : ∀ v, Measurable (f v)) (hf_ind : iIndepFun f μ)
    (deps : ι → Finset κ) (hdep : ∀ i, DeterminedBy f (deps i) (E i))
    (hne : ∀ i, (deps i).Nonempty) (hcard : ∀ i, (deps i).card ≤ 4)
    (hload : ∀ v, load deps (fun i => μ.real (E i)) v ≤ 1 / 16) :
    0 < μ.real (avoid E Finset.univ) ∧ ∃ ω : Ω, ∀ i, ω ∉ E i := by
  apply weighted_four (fun i => measurable_of_determined hf (hdep i)) deps hne hcard hload
  exact independent_of_non_neighbors hf hf_ind deps hdep

end IndependentVariables

end KaplanskyCounterexample.FiniteLocalLemma

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
open Module MeasureTheory

variable {Q : Type u_6} {E : Type u_7} [Field Q] [AddCommGroup E] [Module Q E]

/-- Transitivity on nonzero vectors, proved by extending an isomorphism of
one-dimensional subspaces. -/
theorem exists_linearEquiv_apply_eq {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : E ≃ₗ[Q] E, g x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton Q E x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton Q E y hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨g, ?_⟩
  have h := hg (ex 1)
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h.symm

abbrev Plane (Q : Type u_8) (E : Type u_9) [Field Q] [AddCommGroup E] [Module Q E] :=
  {P : Submodule Q E // finrank Q P = 2}

instance [Finite E] : Finite (Plane Q E) := by
  unfold Plane
  infer_instance

instance [Fintype E] : Fintype (Plane Q E) := Fintype.ofFinite _

local instance identityRingHomSurjective : RingHomSurjective (RingHom.id Q) := inferInstance

/-- An ambient automorphism permutes the plane sample space. -/
def mapPlane (g : E ≃ₗ[Q] E) : Plane Q E ≃ Plane Q E where
  toFun P := ⟨P.val.map g.toLinearMap, by rw [g.finrank_map_eq]; exact P.property⟩
  invFun P := ⟨P.val.map g.symm.toLinearMap, by rw [g.symm.finrank_map_eq]; exact P.property⟩
  left_inv P := by
    apply Subtype.ext
    ext x
    simp
  right_inv P := by
    apply Subtype.ext
    ext x
    simp

@[simp] theorem mem_mapPlane (g : E ≃ₗ[Q] E) (P : Plane Q E) (x : E) :
    g x ∈ (mapPlane g P).val ↔ x ∈ P.val := by
  change g x ∈ P.val.map g.toLinearMap ↔ x ∈ P.val
  simp

/-- The number of planes through a nonzero vector is independent of it. -/
def planesThroughEquiv {x y : E} (g : E ≃ₗ[Q] E) (h : g x = y) :
    {P : Plane Q E // x ∈ P.val} ≃ {P : Plane Q E // y ∈ P.val} where
  toFun P := ⟨mapPlane g P.val, by rw [← h, mem_mapPlane]; exact P.property⟩
  invFun P := ⟨mapPlane g.symm P.val, by
    have hg : g.symm y = x := by rw [← h]; simp
    rw [← hg, mem_mapPlane]; exact P.property⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    change (P.val.val.map g.toLinearMap).map g.symm.toLinearMap = P.val.val
    ext x
    simp
  right_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    change (P.val.val.map g.symm.toLinearMap).map g.toLinearMap = P.val.val
    ext x
    simp

variable [Fintype Q] [Fintype E]

/-- Nonzero elements of a plane are precisely its ambient nonzero vectors. -/
def planeNonzeroEquiv (P : Plane Q E) :
    {x : P.val // x ≠ 0} ≃ {x : {x : E // x ≠ 0} // x.val ∈ P.val} where
  toFun x := ⟨⟨x.val.val, by
    intro h
    exact x.property (Subtype.ext h)⟩,
    x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, by
    intro h
    exact x.val.property (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_plane_nonzero (P : Plane Q E) :
    Fintype.card {x : {x : E // x ≠ 0} // x.val ∈ P.val} = Fintype.card Q ^ 2 - 1 := by
  rw [← Fintype.card_congr (planeNonzeroEquiv P)]
  have heq : Fintype.card {x : P.val // x = 0} = 1 := Fintype.card_unique
  rw [Fintype.card_subtype_compl, heq,
    Module.card_eq_pow_finrank (K := Q) (V := P.val), P.property]

/-- Double counting of a finite relation. -/
lemma card_relation {α : Type u_10} {β : Type u_11} [Fintype α] [Fintype β] (R : α → β → Prop) :
    (∑ a, Fintype.card {b // R a b}) = ∑ b, Fintype.card {a // R a b} := by
  classical
  let e : (Σ a, {b // R a b}) ≃ (Σ b, {a // R a b}) :=
    ⟨fun ⟨a, b, h⟩ => ⟨b, a, h⟩, fun ⟨b, a, h⟩ => ⟨a, b, h⟩,
      fun _ => rfl, fun _ => rfl⟩
  simpa only [Fintype.card_sigma] using Fintype.card_congr e

lemma card_planesThrough_mul {x : E} (hx : x ≠ 0) :
    Fintype.card {P : Plane Q E // x ∈ P.val} * (Fintype.card E - 1) =
      Fintype.card (Plane Q E) * (Fintype.card Q ^ 2 - 1) := by
  classical
  have h := card_relation (fun (P : Plane Q E) (y : {y : E // y ≠ 0}) => y.val ∈ P.val)
  have hxcard (y : {y : E // y ≠ 0}) :
      Fintype.card {P : Plane Q E // y.val ∈ P.val} =
        Fintype.card {P : Plane Q E // x ∈ P.val} := by
    obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq (Q := Q) y.property hx
    exact Fintype.card_congr (planesThroughEquiv g hg)
  simp only [card_plane_nonzero, hxcard, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_subtype_compl, Fintype.card_unique] at h
  simpa only [mul_comm] using h.symm

omit [Fintype Q] [Fintype E] in
lemma plane_nonempty (h : 2 ≤ finrank Q E) : Nonempty (Plane Q E) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := Q) (M := E) h
  refine ⟨⟨Submodule.span Q (Set.range f), ?_⟩⟩
  simpa using finrank_span_eq_card hf

/-- Pure counting form of the inclusion probability. -/
lemma planesThrough_ratio [Nonempty (Plane Q E)] {x : E} (hx : x ≠ 0) :
    (Fintype.card {P : Plane Q E // x ∈ P.val} : ℝ) / Fintype.card (Plane Q E) =
      (Fintype.card Q ^ 2 - 1 : ℕ) / (Fintype.card E - 1 : ℕ) := by
  let : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  have hP : (Fintype.card (Plane Q E) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  have hE : ((Fintype.card E - 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := Fintype.one_lt_card (α := E); omega)
  apply (div_eq_div_iff hP hE).mpr
  exact_mod_cast (card_planesThrough_mul (Q := Q) hx).trans (Nat.mul_comm _ _)

theorem probability_mem_plane [Nonempty (Plane Q E)]
    [MeasurableSpace (Plane Q E)] [MeasurableSingletonClass (Plane Q E)]
    {x : E} (hx : x ≠ 0) :
    (PMF.uniformOfFintype (Plane Q E)).toMeasure.real {P | x ∈ P.val} =
      ((Fintype.card Q : ℝ) ^ 2 - 1) /
        ((Fintype.card Q : ℝ) ^ finrank Q E - 1) := by
  rw [Measure.real, PMF.toMeasure_uniformOfFintype_apply (α := Plane Q E) {P | x ∈ P.val}
    ((Set.toFinite _).countable.measurableSet)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  change (Fintype.card {P : Plane Q E // x ∈ P.val} : ℝ) / Fintype.card (Plane Q E) = _
  rw [planesThrough_ratio (Q := Q) hx]
  have hQ : 1 ≤ Fintype.card Q ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  have hE : 1 ≤ Fintype.card E := Fintype.card_pos
  rw [Nat.cast_sub hQ, Nat.cast_sub hE, Nat.cast_pow, Nat.cast_one,
    Module.card_eq_pow_finrank (K := Q) (V := E), Nat.cast_pow]

end KaplanskyCounterexample.FiniteGeometry

namespace KaplanskyCounterexample.FiniteGeometry
open Module MeasureTheory ProbabilityTheory
open KaplanskyCounterexample.FiniteLocalLemma

variable {Q : Type u_12} {E : Type u_13} {κ : Type u_14} {ι : Type u_15} [Field Q] [AddCommGroup E] [Module Q E]
  [Fintype Q] [Fintype E] [Fintype κ] [Nonempty (Plane Q E)]
  [MeasurableSpace (Plane Q E)] [MeasurableSingletonClass (Plane Q E)]

/-- The common one-vector inclusion probability. -/
def inclusionProbability (Q : Type u_16) (E : Type u_17) [Field Q] [AddCommGroup E] [Module Q E]
    [Fintype Q] : ℝ :=
  ((Fintype.card Q : ℝ) ^ 2 - 1) / ((Fintype.card Q : ℝ) ^ finrank Q E - 1)

/-- Independent choices of uniformly distributed slab direction planes. -/
def slabMeasure : Measure (κ → Plane Q E) :=
  Measure.pi fun _ => (PMF.uniformOfFintype (Plane Q E)).toMeasure

instance : IsProbabilityMeasure (slabMeasure (Q := Q) (E := E) (κ := κ)) := by
  unfold slabMeasure
  infer_instance

/-- Each bad event requires one specified nonzero vector in each of its
specified direction planes. -/
def includesAll (s : Finset κ) (w : κ → E) : Set (κ → Plane Q E) :=
  {P | ∀ v ∈ s, w v ∈ (P v).val}

lemma probability_includesAll (s : Finset κ) (w : κ → E)
    (hw : ∀ v ∈ s, w v ≠ 0) :
    (slabMeasure (Q := Q) (E := E) (κ := κ)).real (includesAll s w) =
      inclusionProbability Q E ^ s.card := by
  change (Measure.pi (fun _ : κ => (PMF.uniformOfFintype (Plane Q E)).toMeasure)).real
    ((s : Set κ).pi fun v => {P | w v ∈ P.val}) = _
  rw [Measure.real, Measure.pi_pi_finset, ENNReal.toReal_prod]
  calc
    _ = ∏ _v ∈ s, inclusionProbability Q E := by
      apply Finset.prod_congr rfl
      intro v hv
      exact probability_mem_plane (hw v hv)
    _ = _ := by simp

theorem exists_slab_assignment [Fintype ι] (deps : ι → Finset κ) (w : ι → κ → E)
    (hw : ∀ i v, v ∈ deps i → w i v ≠ 0)
    (hne : ∀ i, (deps i).Nonempty) (hcard : ∀ i, (deps i).card ≤ 4)
    (hload : ∀ v, load deps (fun i => inclusionProbability Q E ^ (deps i).card) v ≤ 1 / 16) :
    ∃ P : κ → Plane Q E, ∀ i, ∃ v ∈ deps i, w i v ∉ (P v).val := by
  let μ := slabMeasure (Q := Q) (E := E) (κ := κ)
  have hind : iIndepFun (fun v (P : κ → Plane Q E) => P v) μ :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hdet : ∀ i, DeterminedBy (fun v (P : κ → Plane Q E) => P v)
      (deps i) (includesAll (deps i) (w i)) := by
    intro i P P' heq
    change (∀ v ∈ deps i, w i v ∈ (P v).val) ↔ ∀ v ∈ deps i, w i v ∈ (P' v).val
    simp only at heq
    constructor <;> intro h v hv
    · rw [← heq v hv]; exact h v hv
    · rw [heq v hv]; exact h v hv
  have hpr (i : ι) : μ.real (includesAll (deps i) (w i)) =
      inclusionProbability Q E ^ (deps i).card := probability_includesAll _ _ (hw i)
  obtain ⟨_, P, hP⟩ := weighted_four_independent (μ := μ)
    (fun v => measurable_pi_apply v) hind deps hdet hne hcard (by simpa only [hpr] using hload)
  refine ⟨P, ?_⟩
  intro i
  simpa [includesAll] using hP i

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
