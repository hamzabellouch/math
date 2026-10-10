import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.ProbeGates

namespace OAI

/-! ## Probe extension: construction and preservation of real margins -/

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder

/-- Numerical intervals for the first-letter blocks. These inequalities are
constructed from the old margin below, rather than supplied for the extension. -/
structure HeightIntervals {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
    (A : Alphabet M S) (H : HeightCost (LeftDivOrder M)) where
  floor : S → ℝ
  offset : S → ℝ
  scale : S → ℝ
  outsideBound : S → ℝ
  floor_pos : ∀ s, 0 < floor s
  scale_pos : ∀ s, 0 < scale s
  floor_le : ∀ s x, (∃ t, A.act x t = s) → H.height x ≤ floor s
  lower_gap : ∀ s, floor s + scale s < offset s
  outside_nonneg : ∀ s, 0 ≤ outsideBound s
  upper_gap : ∀ s, offset s + scale s + outsideBound s < H.height (A.exit s)
  inside_cost : ∀ s x d, (∃ t, A.act x t = s) → (∃ t, A.act d t = s) →
    ¬ d ∣ x → H.cost d ≤ floor s - H.height x
  outside_cost : ∀ s d, d ∣ A.exit s → ¬ (∃ t, A.act d t = s) →
    H.cost d ≤ outsideBound s

namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (H : HeightCost (LeftDivOrder M))

/-- The old first-letter divisors are a bounded ideal of the old monoid. -/
def letterIdeal (s : P.Letters) : ConeIdeal (α := LeftDivOrder M) (P.target s) where
  carrier := {x | P.InCone x s}
  nonempty := ⟨1, P.one_inCone s⟩
  bounded := fun _ hx => (LeftDivOrder.le_iff_dvd _ _).2 (P.dvd_target_of_inCone hx)
  lower := fun _ _ hxy hy => P.inCone_of_dvd ((LeftDivOrder.le_iff_dvd _ _).1 hxy) hy
  join_closed {x y j} hx hy hj := by
    apply (P.inCone_intersection x y j (fun z => ?_) s).1 ⟨hx, hy⟩
    have h := (pair_lub_iff (α := LeftDivOrder M) x y j).1 hj z
    rw [LeftDivOrder.le_iff_dvd (M := M) x z, LeftDivOrder.le_iff_dvd (M := M) y z,
      LeftDivOrder.le_iff_dvd (M := M) j z] at h
    exact h

/-- The supremum of the heights of all old divisors of a new letter. -/
noncomputable def letterFloor (s : P.Letters) : ℝ :=
  sSup (H.height '' (P.letterIdeal s).carrier)

theorem letter_heights_bdd (s : P.Letters) :
    BddAbove (H.height '' (P.letterIdeal s).carrier) := by
  refine ⟨H.height (P.target s), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact H.strictMono_height.monotone ((P.letterIdeal s).bounded hx)

theorem height_le_letterFloor {s : P.Letters} {x : M} (hx : P.InCone x s) :
    H.height x ≤ P.letterFloor H s :=
  le_csSup (P.letter_heights_bdd H s) ⟨x, hx, rfl⟩

theorem letterFloor_pos (s : P.Letters) : 0 < P.letterFloor H s :=
  (H.height_pos 1).trans_le (P.height_le_letterFloor H (P.one_inCone s))

theorem letterFloor_le (s : P.Letters) : P.letterFloor H s ≤ H.height (P.target s) := by
  apply csSup_le ((P.letterIdeal s).nonempty.image H.height)
  rintro _ ⟨x, hx, rfl⟩
  exact H.strictMono_height.monotone ((P.letterIdeal s).bounded hx)

/-- Joining two old divisors inside the letter ideal provides the bound
needed for missed divisors below an old-to-new comparison. -/
theorem letter_inside_cost (hM : HasConditionalJoins (LeftDivOrder M))
    {s : P.Letters} {x d : M} (hx : P.InCone x s) (hd : P.InCone d s) (hdx : ¬ d ∣ x) :
    H.cost d ≤ P.letterFloor H s - H.height x := by
  obtain ⟨j, hj⟩ := hM x d (P.target s)
    ((P.letterIdeal s).bounded hx) ((P.letterIdeal s).bounded hd)
  have hxj : @LE.le (LeftDivOrder M) _ x j := hj.1 (Set.mem_insert _ _)
  have hdj : @LE.le (LeftDivOrder M) _ d j := hj.1 (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hdx' : ¬ @LE.le (LeftDivOrder M) _ d x := fun hh => hdx ((LeftDivOrder.le_iff_dvd _ _).1 hh)
  have hlt : @LT.lt (LeftDivOrder M) _ x j := lt_of_le_not_ge hxj (fun h => hdx' (hdj.trans h))
  have hcost := H.point_margin hlt hdj hdx'
  have hjP := (P.letterIdeal s).join_closed hx hd hj
  have hbound := P.height_le_letterFloor H hjP
  linarith

/-- The height not yet used by the letter ideal controls every divisor
of its target outside that ideal. The bound is uniform over the ideal. -/
theorem target_outside_cost {s : P.Letters} {d : M}
    (hd : d ∣ P.target s) (hdP : ¬ P.InCone d s) :
    H.cost d ≤ H.height (P.target s) - P.letterFloor H s := by
  have hu : P.letterFloor H s ≤ H.height (P.target s) - H.cost d := by
    apply csSup_le ((P.letterIdeal s).nonempty.image H.height)
    rintro _ ⟨x, hx, rfl⟩
    have hdx : ¬ @LE.le (LeftDivOrder M) _ d x := by
      intro hdx
      exact hdP (P.inCone_of_dvd ((LeftDivOrder.le_iff_dvd _ _).1 hdx) hx)
    have hxlt : @LT.lt (LeftDivOrder M) _ x (P.target s) :=
      lt_of_le_not_ge ((P.letterIdeal s).bounded hx)
        (fun hkx => hdx (((LeftDivOrder.le_iff_dvd _ _).2 hd).trans hkx))
    have hcost := H.point_margin hxlt ((LeftDivOrder.le_iff_dvd _ _).2 hd) hdx
    linarith
  linarith

include he in
/-- The target is strictly below the exit: no right cancellation is used. -/
theorem target_lt_exit (s : P.Letters) :
    @LT.lt (LeftDivOrder M) _ (P.target s) (P.exit e s) := by
  refine lt_iff_le_and_ne.2 ⟨⟨e, rfl⟩, ?_⟩
  intro h
  have he1 : e = 1 := mul_left_cancel (a := P.target s)
    ((show P.target s * e = P.target s from h.symm).trans (mul_one _).symm)
  exact he he1

include he in
/-- The source's two strict interval inequalities, with a single bound
for all the old outside costs. -/
theorem exists_letter_interval (s : P.Letters) :
    ∃ u δ K : ℝ, 0 < δ ∧ P.letterFloor H s + δ < u ∧ 0 ≤ K ∧
      u + δ + K < H.height (P.exit e s) ∧
      ∀ d : M, d ∣ P.exit e s → ¬ P.InCone d s → H.cost d ≤ K := by
  obtain ⟨C, hC, hbound⟩ := H.uniform_margin (P.target_lt_exit he s)
  let p := H.height (P.target s) - P.letterFloor H s
  let q := H.height (P.exit e s) - H.height (P.target s)
  have hp : 0 ≤ p := sub_nonneg.mpr (P.letterFloor_le H s)
  have hq : 0 < q := sub_pos.mpr (H.strictMono_height (P.target_lt_exit he s))
  have hCq : C < q := hC
  let K := max p C
  have hKpos : 0 ≤ K := hp.trans (le_max_left _ _)
  have hroom : K < H.height (P.exit e s) - P.letterFloor H s := by
    apply max_lt
    · dsimp [p] at *; linarith
    · dsimp [p, q] at *; linarith
  let δ := (H.height (P.exit e s) - P.letterFloor H s - K) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨P.letterFloor H s + 2 * δ, δ, K, hδ, by linarith, hKpos, ?_, ?_⟩
  · dsimp [δ]; linarith
  · intro d hd hn
    by_cases hdk : d ∣ P.target s
    · exact (P.target_outside_cost H hdk hn).trans (le_max_left _ _)
    · exact (hbound d ((LeftDivOrder.le_iff_dvd _ _).2 hd)
        (fun hl => hdk ((LeftDivOrder.le_iff_dvd _ _).1 hl))).trans (le_max_right _ _)

/-- Intervals for all the new letters of this actual probe extension. -/
noncomputable def heightIntervals (hM : HasConditionalJoins (LeftDivOrder M)) :
    HeightIntervals (P.alphabet he) H := by
  choose u δ K hδ hlo hK hup hcost using P.exists_letter_interval he H
  exact {
    floor := P.letterFloor H
    offset := u
    scale := δ
    outsideBound := K
    floor_pos := P.letterFloor_pos H
    scale_pos := hδ
    floor_le := fun _ _ hx => P.height_le_letterFloor H hx
    lower_gap := hlo
    outside_nonneg := hK
    upper_gap := hup
    inside_cost := fun _ _ _ hx hd hdx => P.letter_inside_cost H hM hx hd hdx
    outside_cost := hcost }

end Path
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v
open DiagramOrder Classical
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (H : HeightCost (LeftDivOrder M))

/-- A least old cone containing a word's old right multiples. It is used
only to choose a cost cap; the gate theorem proves its existence when needed. -/
def OldMinimum (w : Word A b) (g : M) : Prop :=
  ∀ y : M, w ∣ old A b y ↔ g ∣ y

theorem OldMinimum.unique {w : Word A b} {g k : M}
    (hg : OldMinimum A b w g) (hk : OldMinimum A b w k) : g = k := by
  apply le_antisymm (α := LeftDivOrder M)
  · exact (LeftDivOrder.le_iff_dvd _ _).2 ((hg k).1 ((hk k).2 (dvd_refl k)))
  · exact (LeftDivOrder.le_iff_dvd _ _).2 ((hk g).1 ((hg g).2 (dvd_refl g)))

/-- The cap is the cost of the actual least old right multiple, never
that of an arbitrarily larger old multiple (costs need not be monotone). -/
noncomputable def gateCap (w : Word A b) : ℝ :=
  if h : ∃ g : M, OldMinimum A b w g then H.cost h.choose else 1

theorem gateCap_pos (w : Word A b) : 0 < gateCap A b H w := by
  classical
  unfold gateCap
  split_ifs
  · exact H.cost_pos _
  · exact zero_lt_one

theorem gateCap_le_one (w : Word A b) : gateCap A b H w ≤ 1 := by
  classical
  unfold gateCap
  split_ifs
  · exact H.cost_le_one _
  · exact le_rfl

theorem gateCap_eq {w : Word A b} {g : M} (hg : OldMinimum A b w g) :
    gateCap A b H w = H.cost g := by
  classical
  have h : ∃ g : M, OldMinimum A b w g := ⟨g, hg⟩
  rw [gateCap, dite_eq_left h, OldMinimum.unique A b h.choose_spec hg]

variable (V : HeightIntervals A H)

/-- Recursive heights on literal irreducibles; the same formula is
harmless on unreduced strings. -/
noncomputable def rawHeight : Raw M S → ℝ
  | .old x => H.height x
  | .cons s w => V.offset s + V.scale s * rawHeight w

/-- The recursive cost makes both the suffix scale and the old gate's
cost available simultaneously. -/
noncomputable def rawCost : (w : Raw M S) → w.reduced A b → ℝ
  | .old x, _ => H.cost x
  | .cons s w, hw => min (V.scale s * rawCost w hw.1) (gateCap A b H ⟨.cons s w, hw⟩)

noncomputable def height (w : Word A b) : ℝ := rawHeight A H V w.val
noncomputable def cost (w : Word A b) : ℝ := rawCost A b H V w.val w.property

@[simp] theorem height_old (x : M) : height A b H V (old A b x) = H.height x := rfl
@[simp] theorem height_cons (s : S) (w : Word A b) (hw) :
    height A b H V (cons A b s w hw) = V.offset s + V.scale s * height A b H V w := rfl
@[simp] theorem cost_old (x : M) : cost A b H V (old A b x) = H.cost x := rfl
@[simp] theorem cost_cons (s : S) (w : Word A b) (hw) :
    cost A b H V (cons A b s w hw) =
      min (V.scale s * cost A b H V w) (gateCap A b H (cons A b s w hw)) := rfl

theorem scale_lt_one (s : S) : V.scale s < 1 := by
  have h1 := V.floor_pos s
  have h2 := V.lower_gap s
  have h3 := V.upper_gap s
  have h4 := V.outside_nonneg s
  have h5 := H.height_lt_one (A.exit s)
  linarith

theorem height_bounds (w : Word A b) : 0 < height A b H V w ∧ height A b H V w < 1 := by
  obtain ⟨w, hw⟩ := w
  induction w with
  | old x => exact ⟨H.height_pos x, H.height_lt_one x⟩
  | cons s w ih =>
    obtain ⟨hl, hu⟩ := ih hw.1
    change 0 < V.offset s + V.scale s * rawHeight A H V w ∧
      V.offset s + V.scale s * rawHeight A H V w < 1
    change 0 < rawHeight A H V w at hl
    change rawHeight A H V w < 1 at hu
    have hf := V.floor_pos s
    have hs := V.scale_pos s
    have ho := V.lower_gap s
    have hg := V.upper_gap s
    have hk := V.outside_nonneg s
    have he := H.height_lt_one (A.exit s)
    constructor <;> nlinarith

theorem cost_bounds (w : Word A b) : 0 < cost A b H V w ∧ cost A b H V w ≤ 1 := by
  obtain ⟨w, hw⟩ := w
  induction w with
  | old x => exact ⟨H.cost_pos x, H.cost_le_one x⟩
  | cons s w ih =>
    obtain ⟨hl, _⟩ := ih hw.1
    change 0 < min (V.scale s * rawCost A b H V w hw.1) (gateCap A b H ⟨.cons s w, hw⟩) ∧
      min (V.scale s * rawCost A b H V w hw.1) (gateCap A b H ⟨.cons s w, hw⟩) ≤ 1
    exact ⟨lt_min (mul_pos (V.scale_pos s) hl) (gateCap_pos A b H _),
      (min_le_right _ _).trans (gateCap_le_one A b H _)⟩

theorem cost_le_scale {w : Word A b} {s : S} (hw : head A b w = some s) :
    cost A b H V w ≤ V.scale s := by
  obtain ⟨Y, hY, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  rw [cost_cons]
  exact (min_le_left _ _).trans
    ((mul_le_mul_of_nonneg_left (cost_bounds A b H V Y).2 (V.scale_pos s).le).trans_eq
      (_root_.mul_one _))

/-- Every new word's cost is at most that of its specific old gate. -/
theorem cost_le_gate {w : Word A b} {s : S} {g : M}
    (hw : head A b w = some s) (hg : Gate A b w s g) : cost A b H V w ≤ H.cost g := by
  obtain ⟨Y, hY, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  rw [cost_cons, gateCap_eq A b H (Gate.dvd_old_iff A b hg)]
  exact min_le_right _ _

/-- Any divisor of an old element has a cost-dominating old divisor
with exactly the same old-multiple profile. -/
theorem cost_old_factor (hOld : OldIntersections A b)
    {w : Word A b} {y : M} (hwy : w ∣ old A b y) :
    ∃ g : M, OldMinimum A b w g ∧ w ∣ old A b g ∧ g ∣ y ∧ cost A b H V w ≤ H.cost g := by
  cases hs : head A b w with
  | none =>
    obtain ⟨x, rfl⟩ := (head_eq_none_iff A b w).1 hs
    exact ⟨x, old_dvd_old_iff A b x, dvd_refl _, (old_dvd_old_iff A b x y).1 hwy, le_rfl⟩
  | some s =>
    obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld w hs hwy (by intro h; cases h)
    exact ⟨g, Gate.dvd_old_iff A b hg, Gate.dvd A b hg,
      (Gate.dvd_old_iff A b hg y).1 hwy, cost_le_gate A b H V hs hg⟩

/-- The cost of an outside-block divisor is controlled by an old member
of that block's letter ideal. -/
theorem cost_other_block_factor (hOld : OldIntersections A b)
    {w z : Word A b} {s : S} (hw : head A b w ≠ some s)
    (hz : head A b z = some s) (hwz : w ∣ z) :
    ∃ g : M, w ∣ old A b g ∧ old A b g ∣ z ∧ cost A b H V w ≤ H.cost g := by
  cases ht : head A b w with
  | none =>
    obtain ⟨x, rfl⟩ := (head_eq_none_iff A b w).1 ht
    exact ⟨x, dvd_refl _, hwz, le_rfl⟩
  | some t =>
    have hzt : head A b z ≠ some t := by
      intro hzt
      have hts : t = s := Option.some.inj (hzt.symm.trans hz)
      exact hw (hts ▸ ht)
    obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld w ht hwz hzt
    exact ⟨g, Gate.dvd A b hg, (hg z).1 ⟨hwz, hzt⟩, cost_le_gate A b H V ht hg⟩

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v
open DiagramOrder Classical
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (H : HeightCost (LeftDivOrder M))
  (V : HeightIntervals A H) (hOld : OldIntersections A b)

include hOld in
/-- For old comparisons, gates dominate every new missed cost. -/
theorem uniform_margin_old {x y : LeftDivOrder M} (hxy : x < y) :
    UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V)
      (old A b x) (old A b y) := by
  obtain ⟨C, hC, hbound⟩ := H.uniform_margin hxy
  refine ⟨C, hC, ?_⟩
  intro d hdy hdx
  obtain ⟨g, _, hdg, hgy, hcost⟩ := cost_old_factor A b H V hOld
    ((LeftDivOrder.le_iff_dvd _ _).1 hdy)
  apply hcost.trans
  apply hbound g ((LeftDivOrder.le_iff_dvd _ _).2 hgy)
  intro hgx
  exact hdx ((LeftDivOrder.le_iff_dvd _ _).2
    (hdg.trans ((old_dvd_old_iff A b g x).2 ((LeftDivOrder.le_iff_dvd _ _).1 hgx))))

include hOld in
/-- Margins from an old element into a new first-letter block: outside
costs use the letter-ideal floor, inside costs use the suffix scale. -/
theorem uniform_margin_old_new {x : M} {w : Word A b} {s : S}
    (hw : head A b w = some s) (hxw : old A b x ∣ w) :
    UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V)
      (old A b x) w := by
  have hx : ∃ t, A.act x t = s := (headDiv_of_head_eq_some A b hw).1
    ((old_dvd_iff_headDiv A b x w).1 hxw)
  have hlo := V.lower_gap s
  have hfloor := V.floor_le s x hx
  have hscale := V.scale_pos s
  obtain ⟨Y, hY, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  have hpos := (height_bounds A b H V Y).1
  refine ⟨max (V.floor s - H.height x) (V.scale s), ?_, ?_⟩
  · rw [height_cons, height_old]
    apply max_lt <;> nlinarith
  · intro d hdw hdx
    have hdw' := (LeftDivOrder.le_iff_dvd _ _).1 hdw
    by_cases hds : head A b d = some s
    · exact (cost_le_scale A b H V hds).trans (le_max_right _ _)
    · obtain ⟨g, hdg, hgw, hcost⟩ := cost_other_block_factor A b H V hOld hds rfl hdw'
      have hg : ∃ t, A.act g t = s := (headDiv_of_head_eq_some A b (w := cons A b s Y hY) rfl).1
        ((old_dvd_iff_headDiv A b g _).1 hgw)
      have hgn : ¬ g ∣ x := fun he => hdx ((LeftDivOrder.le_iff_dvd _ _).2
        (hdg.trans ((old_dvd_old_iff A b g x).2 he)))
      exact (hcost.trans (V.inside_cost s x g hx hg hgn)).trans (le_max_left _ _)

include hOld in
/-- Margins from a new first-letter block to an old multiple. The old
gate bounds all costs without presuming that costs are monotone. -/
theorem uniform_margin_new_old (hb : b ≠ 1) {w : Word A b} {s : S} {y : M}
    (hw : head A b w = some s) (hwy : w ∣ old A b y) :
    UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V)
      w (old A b y) := by
  have hhey : A.exit s ∣ y := (generator_dvd_old_iff A b hb s y).1
    ((generator_dvd_of_head A b hb hw).trans hwy)
  have hheyle : @LE.le (LeftDivOrder M) _ (A.exit s) y := (LeftDivOrder.le_iff_dvd _ _).2 hhey
  obtain ⟨C, hC, hbound⟩ : ∃ C : ℝ, C ≤ H.height y - H.height (A.exit s) ∧
      ∀ d : M, d ∣ y → ¬ d ∣ A.exit s → H.cost d ≤ C := by
    by_cases he : A.exit s = y
    · exact ⟨0, by rw [← he, sub_self], fun _ hdy hds => (hds (he ▸ hdy)).elim⟩
    · obtain ⟨c, hc, hcost⟩ := H.uniform_margin (lt_iff_le_and_ne.2 ⟨hheyle, he⟩)
      exact ⟨c, hc.le, fun d hdy hds => hcost d ((LeftDivOrder.le_iff_dvd _ _).2 hdy)
        (fun he => hds ((LeftDivOrder.le_iff_dvd _ _).1 he))⟩
  have hhy := H.strictMono_height.monotone hheyle
  have hup := V.upper_gap s
  have hK := V.outside_nonneg s
  obtain ⟨Y, hY, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  have hYlt := (height_bounds A b H V Y).2
  have hsp := V.scale_pos s
  refine ⟨max (V.outsideBound s) C, ?_, ?_⟩
  · rw [height_old, height_cons]
    apply max_lt <;> nlinarith
  · intro d hdy hdw
    obtain ⟨g, _, hdg, hgy, hcost⟩ := cost_old_factor A b H V hOld
      ((LeftDivOrder.le_iff_dvd _ _).1 hdy)
    have hgn : ¬ ∃ t, A.act g t = s := by
      intro hg
      have hgw : old A b g ∣ cons A b s Y hY := (old_dvd_iff_headDiv A b g _).2 hg
      exact hdw ((LeftDivOrder.le_iff_dvd _ _).2 (hdg.trans hgw))
    by_cases hgs : g ∣ A.exit s
    · exact (hcost.trans (V.outside_cost s g hgs hgn)).trans (le_max_left _ _)
    · exact (hcost.trans (hbound g hgy hgs)).trans (le_max_right _ _)

/-- Comparisons within one block are precisely suffix comparisons. -/
theorem cons_dvd_cons_iff (hb : b ≠ 1) (s : S) (Y Z : Word A b) (hY hZ) :
    cons A b s Y hY ∣ cons A b s Z hZ ↔ Y ∣ Z := by
  rw [← generator_mul_of_not_headDiv A b hb s Y hY,
    ← generator_mul_of_not_headDiv A b hb s Z hZ]
  exact left_mul_dvd_iff _ _ _

include hOld in
/-- The uniform margin in one block is the suffix margin multiplied by
its positive scale. All other-block divisors divide both endpoints. -/
theorem uniform_margin_same_head (hb : b ≠ 1) (s : S) (Y Z : Word A b) (hY hZ)
    (hmargin : UniformMargin (α := LeftDivOrder (Word A b))
      (height A b H V) (cost A b H V) Y Z) :
    UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V)
      (cons A b s Y hY) (cons A b s Z hZ) := by
  obtain ⟨C, hC, hbound⟩ := hmargin
  refine ⟨V.scale s * C, ?_, ?_⟩
  · rw [height_cons, height_cons]
    have hc := mul_lt_mul_of_pos_left hC (V.scale_pos s)
    nlinarith
  · intro d hdZ hdY
    have hdZ' := (LeftDivOrder.le_iff_dvd _ _).1 hdZ
    by_cases hds : head A b d = some s
    · obtain ⟨D, hD, rfl⟩ := (head_eq_some_iff A b d s).1 hds
      have hDZ : @LE.le (LeftDivOrder (Word A b)) _ D Z :=
        (LeftDivOrder.le_iff_dvd _ _).2 ((cons_dvd_cons_iff A b hb s D Z hD hZ).1 hdZ')
      have hDnY : ¬ @LE.le (LeftDivOrder (Word A b)) _ D Y := by
        intro hDY
        exact hdY ((LeftDivOrder.le_iff_dvd _ _).2 ((cons_dvd_cons_iff A b hb s D Y hD hY).2
          ((LeftDivOrder.le_iff_dvd _ _).1 hDY)))
      rw [cost_cons]
      exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (hbound D hDZ hDnY) (V.scale_pos s).le)
    · exact (hdY ((LeftDivOrder.le_iff_dvd _ _).2
        (dvd_of_other_block A b hOld rfl hds hdZ' rfl))).elim

omit [IsConical M] in
/-- Old elements and elements of a first-letter block are distinct. -/
theorem new_ne_old {w : Word A b} {s : S} (hw : head A b w = some s) (x : M) : w ≠ old A b x := by
  intro he
  rw [he, head_old] at hw
  cases hw

include hOld in
/-- Structural induction checks every strict comparison of irreducible
words, using an intervening old gate precisely for different new blocks. -/
theorem uniform_margin (hb : b ≠ 1) (z : Word A b) :
    ∀ w : Word A b, @LT.lt (LeftDivOrder (Word A b)) _ w z →
      UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V) w z := by
  obtain ⟨z, hz⟩ := z
  induction z with
  | old y =>
    intro w hwy
    have hwy' := (LeftDivOrder.le_iff_dvd _ _).1 hwy.le
    cases hs : head A b w with
    | none =>
      obtain ⟨x, rfl⟩ := (head_eq_none_iff A b w).1 hs
      have hxy : @LT.lt (LeftDivOrder M) _ x y := lt_iff_le_and_ne.2
        ⟨(LeftDivOrder.le_iff_dvd _ _).2 ((old_dvd_old_iff A b x y).1 hwy'),
         fun he => hwy.ne (congrArg (old A b) he)⟩
      exact uniform_margin_old A b H V hOld hxy
    | some s => exact uniform_margin_new_old A b H V hOld hb hs hwy'
  | cons s Z ih =>
    intro w hwz
    let Z' : Word A b := ⟨Z, hz.1⟩
    change @LT.lt (LeftDivOrder (Word A b)) _ w (cons A b s Z' hz.2) at hwz
    change UniformMargin (α := LeftDivOrder (Word A b)) (height A b H V) (cost A b H V)
      w (cons A b s Z' hz.2)
    have hwz' := (LeftDivOrder.le_iff_dvd _ _).1 hwz.le
    by_cases hws : head A b w = some s
    · obtain ⟨Y, hY, rfl⟩ := (head_eq_some_iff A b w s).1 hws
      have hYZ : @LT.lt (LeftDivOrder (Word A b)) _ Y Z' := lt_iff_le_and_ne.2
        ⟨(LeftDivOrder.le_iff_dvd _ _).2 ((cons_dvd_cons_iff A b hb s Y Z' hY hz.2).1 hwz'),
          fun he => hwz.ne (Subtype.ext (congrArg (Raw.cons s) (congrArg Subtype.val he)))⟩
      exact uniform_margin_same_head A b H V hOld hb s Y Z' hY hz.2 (ih hz.1 Y hYZ)
    · cases ht : head A b w with
      | none =>
        obtain ⟨x, rfl⟩ := (head_eq_none_iff A b w).1 ht
        exact uniform_margin_old_new A b H V hOld rfl hwz'
      | some t =>
        obtain ⟨g, hwg, hgz⟩ := old_factor_of_other_block A b hOld hws rfl hwz'
        have hwglt : @LT.lt (LeftDivOrder (Word A b)) _ w (old A b g) :=
          lt_iff_le_and_ne.2 ⟨(LeftDivOrder.le_iff_dvd _ _).2 hwg, new_ne_old A b ht g⟩
        have hgzlt : @LT.lt (LeftDivOrder (Word A b)) _ (old A b g) (cons A b s Z' hz.2) :=
          lt_iff_le_and_ne.2 ⟨(LeftDivOrder.le_iff_dvd _ _).2 hgz, (new_ne_old A b rfl g).symm⟩
        exact UniformMargin.trans hwglt hgzlt (fun d => (cost_bounds A b H V d).1)
          (uniform_margin_new_old A b H V hOld hb ht hwg)
          (uniform_margin_old_new A b H V hOld rfl hgz)

/-- Extending height and cost data on the actual probe normal forms. -/
noncomputable def heightCost (hb : b ≠ 1) : HeightCost (LeftDivOrder (Word A b)) where
  height := height A b H V
  cost := cost A b H V
  height_pos w := (height_bounds A b H V w).1
  height_lt_one w := (height_bounds A b H V w).2
  cost_pos w := (cost_bounds A b H V w).1
  cost_le_one w := (cost_bounds A b H V w).2
  margin {w z} hwz := (uniform_margin A b H V hOld hb z w hwz).supremum_lt hwz

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Word
universe u v
open DiagramOrder Classical
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (H : HeightCost (LeftDivOrder M))
  (V : HeightIntervals A H) (hOld : OldIntersections A b)

include hOld in
/-- New divisors need not have old costs equal to theirs. Nevertheless,
the cost-dominating old gates preserve exactly each old missed-cost supremum. -/
theorem old_cost_supremum (x y : LeftDivOrder M) :
    sSup (cost A b H V ''
      {d : LeftDivOrder (Word A b) | d ≤ old A b y ∧ ¬ d ≤ old A b x}) =
        sSup (H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x}) := by
  let S₀ := H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬d ≤ x}
  let S₁ := cost A b H V ''
      {d : LeftDivOrder (Word A b) | d ≤ old A b y ∧ ¬ d ≤ old A b x}
  change sSup S₁ = sSup S₀
  have hsubset : S₀ ⊆ S₁ := by
    rintro r ⟨d, ⟨hdy, hdx⟩, rfl⟩
    refine ⟨old A b d, ⟨?_, ?_⟩, rfl⟩
    · exact (LeftDivOrder.le_iff_dvd _ _).2 ((old_dvd_old_iff A b d y).2
        ((LeftDivOrder.le_iff_dvd _ _).1 hdy))
    · intro hh
      exact hdx ((LeftDivOrder.le_iff_dvd _ _).2 ((old_dvd_old_iff A b d x).1
        ((LeftDivOrder.le_iff_dvd _ _).1 hh)))
  have hdom : ∀ r ∈ S₁, ∃ c ∈ S₀, r ≤ c := by
    rintro _ ⟨d, ⟨hdy, hdx⟩, rfl⟩
    obtain ⟨g, _, hdg, hgy, hcost⟩ := cost_old_factor A b H V hOld
      ((LeftDivOrder.le_iff_dvd _ _).1 hdy)
    refine ⟨H.cost g, ⟨g, ⟨(LeftDivOrder.le_iff_dvd _ _).2 hgy, ?_⟩, rfl⟩, hcost⟩
    intro hgx
    exact hdx ((LeftDivOrder.le_iff_dvd _ _).2
      (hdg.trans ((old_dvd_old_iff A b g x).2 ((LeftDivOrder.le_iff_dvd _ _).1 hgx))))
  by_cases hS : S₀.Nonempty
  · have hT : S₁.Nonempty := hS.mono hsubset
    have hbS : BddAbove S₀ := by
      refine ⟨1, ?_⟩
      rintro _ ⟨d, _, rfl⟩
      exact H.cost_le_one d
    have hbT : BddAbove S₁ := by
      refine ⟨1, ?_⟩
      rintro _ ⟨d, _, rfl⟩
      exact (cost_bounds A b H V d).2
    apply le_antisymm
    · apply csSup_le hT
      intro r hr
      obtain ⟨c, hc, hrc⟩ := hdom r hr
      exact hrc.trans (le_csSup hbS hc)
    · exact csSup_le hS (fun _ hr => le_csSup hbT (hsubset hr))
  · have hS0 : S₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have hS1 : S₁ = ∅ := Set.not_nonempty_iff_eq_empty.mp (by
      rintro ⟨r, hr⟩
      obtain ⟨c, hc, _⟩ := hdom r hr
      exact hS ⟨c, hc⟩)
    rw [hS0, hS1]

end PartitionConsistency.ProbeAlgebra.Word

namespace PartitionConsistency.ProbeAlgebra.Path
universe u
open DiagramOrder
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M) (hb : b ≠ 1)
  (H : HeightCost (LeftDivOrder M)) (hM : HasConditionalJoins (LeftDivOrder M))

/-- Source `lem:mono-probe-heights`: admissible heights and costs on the
actual indexed probe extension, constructed by its normal forms and gates. -/
noncomputable def extensionHeightCost : HeightCost (LeftDivOrder (P.Extension he b)) :=
  Word.heightCost (P.alphabet he) b H (P.heightIntervals he H hM) (P.oldIntersections he b hM) hb

@[simp] theorem extensionHeightCost_height_old (x : M) :
    (P.extensionHeightCost he b hb H hM).height (Word.old (P.alphabet he) b x) = H.height x := rfl

@[simp] theorem extensionHeightCost_cost_old (x : M) :
    (P.extensionHeightCost he b hb H hM).cost (Word.old (P.alphabet he) b x) = H.cost x := rfl

/-- The exact supremum conservativity needed at limit stages of the tower,
including the case where the set of missed divisors is empty. -/
theorem extension_old_cost_supremum (x y : LeftDivOrder M) :
    sSup ((P.extensionHeightCost he b hb H hM).cost ''
      {d : LeftDivOrder (P.Extension he b) | d ≤ Word.old (P.alphabet he) b y ∧
        ¬ d ≤ Word.old (P.alphabet he) b x}) =
      sSup (H.cost '' {d : LeftDivOrder M | d ≤ y ∧ ¬ d ≤ x}) :=
  Word.old_cost_supremum (P.alphabet he) b H (P.heightIntervals he H hM)
    (P.oldIntersections he b hM) x y

end PartitionConsistency.ProbeAlgebra.Path

end OAI
