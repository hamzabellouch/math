import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.PersistentProfiles

namespace OAI

/-! ## Conservative direct limits, profiles, and the exact real margin -/

noncomputable section

namespace PartitionConsistency.DiagramOrder.ConservativeLimit
universe u v
variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {M : ι → Type v} [∀ i, LeftCancelMonoid (M i)]
  (f : ∀ i j, i ≤ j → M i →* M j)
  [DirectedSystem M (f · · ·)]

/-- Canonical maps into the directed union, represented as a direct limit.
No ambient monoid or model-existence hypothesis is needed. -/
def of (i : ι) : M i →* DirectLimit M f where
  toFun x := Quotient.mk _ ⟨i, x⟩
  map_one' := (DirectLimit.one_def (f := f) i).symm
  map_mul' x y := (DirectLimit.mul_def (f := f) i x y).symm

@[simp] theorem of_apply (i : ι) (x : M i) :
    of f i x = (Quotient.mk _ ⟨i, x⟩ : DirectLimit M f) := rfl

@[simp] theorem of_map (i j : ι) (h : i ≤ j) (x : M i) :
    of f j (f i j h x) = of f i x := DirectLimit.mk_apply i j x h

/-- Left cancellation passes to a directed limit even without injective
transition maps: each equation can be tested at a common later stage. -/
instance : LeftCancelMonoid (DirectLimit M f) where
  mul_left_cancel := by
    intro x y z
    refine DirectLimit.induction₃ f (fun i a b c => ?_) x y z
    intro h
    change (Quotient.mk _ ⟨i,a⟩ : DirectLimit M f) * Quotient.mk _ ⟨i,b⟩ =
      Quotient.mk _ ⟨i,a⟩ * Quotient.mk _ ⟨i,c⟩ at h
    rw [DirectLimit.mul_def, DirectLimit.mul_def, Quotient.eq] at h
    obtain ⟨j, hij, hij', he⟩ := h
    simp only [map_mul] at he
    exact Quotient.sound ⟨j, hij, hij', mul_left_cancel he⟩

instance [∀ i, IsConical (M i)] : IsConical (DirectLimit M f) where
  eq_one_of_mul_eq_one := by
    intro x y
    refine DirectLimit.induction₂ f (fun i a b => ?_) x y
    intro h
    rw [DirectLimit.mul_def, DirectLimit.one_def i, Quotient.eq] at h
    obtain ⟨j, hij, hij', he⟩ := h
    simp only [map_mul, map_one] at he
    obtain ⟨ha, hb⟩ := IsConical.eq_one_of_mul_eq_one he
    constructor
    · rw [DirectLimit.one_def i, Quotient.eq]
      exact ⟨j, hij, hij, by simpa only [map_one] using ha⟩
    · rw [DirectLimit.one_def i, Quotient.eq]
      exact ⟨j, hij, hij, by simpa only [map_one] using hb⟩

variable (hf : ∀ i j h, Conservative (f i j h))
include hf

theorem of_injective (i : ι) : Function.Injective (of f i) :=
  DirectLimit.mk_injective f (fun i j h => (hf i j h).injective) i

theorem of_factors (i : ι) (x y : M i) (z : DirectLimit M f)
    (h : of f i x * z = of f i y) : ∃ t : M i, of f i t = z := by
  obtain ⟨j, z, rfl⟩ := DirectLimit.exists_eq_mk f z
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  change of f i x * of f j z = of f i y at h
  rw [← of_map f i k hik x, ← of_map f j k hjk z,
    ← of_map f i k hik y, ← map_mul] at h
  obtain ⟨t, ht⟩ := (hf i k hik).factors x y (f j k hjk z) (of_injective f hf k h)
  refine ⟨t, ?_⟩
  change of f i t = of f j z
  rw [← of_map f i k hik t, ht, of_map]

/-- Divisibility in the union between two elements of one stage is
exactly divisibility at that stage, with no new right factor. -/
theorem of_dvd_iff (i : ι) (x y : M i) : of f i x ∣ of f i y ↔ x ∣ y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨t, rfl⟩ := of_factors f hf i x y z hz.symm
    exact ⟨t, of_injective f hf i (by rw [map_mul]; exact hz)⟩
  · exact (of f i).map_dvd

theorem of_conservative (i : ι) : Conservative (of f i) where
  injective := of_injective f hf i
  factors := of_factors f hf i
  intersections x y a ha z := by
    obtain ⟨j,z,rfl⟩ := DirectLimit.exists_eq_mk f z
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    change (of f i x ∣ of f j z ∧ of f i y ∣ of f j z) ↔ of f i a ∣ of f j z
    rw [← of_map f i k hik x, ← of_map f i k hik y,
      ← of_map f i k hik a, ← of_map f j k hjk z,
      of_dvd_iff f hf, of_dvd_iff f hf, of_dvd_iff f hf]
    exact (hf i k hik).intersections x y a ha (f j k hjk z)
  common x y h := by
    obtain ⟨z,hxz,hyz⟩ := h
    obtain ⟨j,z,rfl⟩ := DirectLimit.exists_eq_mk f z
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    change of f i x ∣ of f j z at hxz
    change of f i y ∣ of f j z at hyz
    rw [← of_map f i k hik x, ← of_map f j k hjk z, of_dvd_iff f hf] at hxz
    rw [← of_map f i k hik y, ← of_map f j k hjk z, of_dvd_iff f hf] at hyz
    exact (hf i k hik).common x y ⟨f j k hjk z, hxz, hyz⟩

variable [∀ i, IsConical (M i)]

/-- Conditional joins in a conservative tower remain conditional joins
in the union; pairs that never had a common right multiple acquire none. -/
theorem conditionalJoins (hM : ∀ i, HasConditionalJoins (LeftDivOrder (M i))) :
    HasConditionalJoins (LeftDivOrder (DirectLimit M f)) := by
  intro x y a hx hy
  obtain ⟨i,x,y,a,rfl,rfl,rfl⟩ := DirectLimit.exists_eq_mk₃ f x y a
  obtain ⟨z,hz⟩ := exists_cone_join (hM i) x y a
    ((of_dvd_iff f hf i x a).1 ((LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).1 hx))
    ((of_dvd_iff f hf i y a).1 ((LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).1 hy))
  refine ⟨of f i z, ?_⟩
  apply (pair_lub_iff (α := LeftDivOrder (DirectLimit M f)) _ _ _).2
  intro w
  exact ((and_congr
      (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) (of f i x) w)
      (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) (of f i y) w)).trans
    ((of_conservative f hf i).intersections x y z hz w)).trans
    (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) (of f i z) w).symm

omit [∀ i, IsConical (M i)] in
/-- The successor persistence theorem passes to the full union. The path
remains the original path; its downward closure is taken in the final monoid. -/
theorem probeProfile (i : ι) (a b e m : M i) (n : ℕ → M i)
    (hP : ∀ j (hij : i ≤ j),
      ProbeProfile (f i j hij a) (f i j hij b) (f i j hij e)
        (f i j hij m) (fun k => f i j hij (n k))) :
    ProbeProfile (of f i a) (of f i b) (of f i e) (of f i m)
      (fun k => of f i (n k)) := by
  have hi : ProbeProfile a b e m n := by
    simpa only [DirectedSystem.map_self'] using hP i le_rfl
  refine ⟨?_,?_,?_,?_⟩
  · rw [← map_mul, hi.exit, map_mul]
  · intro h
    exact hi.not_divides ((of_dvd_iff f hf i m a).1 h)
  · intro x
    constructor
    · rintro ⟨hxa,hxm⟩
      obtain ⟨j,x,rfl⟩ := DirectLimit.exists_eq_mk f x
      obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
      have hxa' : f j k hjk x ∣ f i k hik a :=
        (of_dvd_iff f hf k _ _).1 (by simpa only [of_apply, DirectLimit.mk_apply] using hxa)
      have hxm' : f j k hjk x ∣ f i k hik m :=
        (of_dvd_iff f hf k _ _).1 (by simpa only [of_apply, DirectLimit.mk_apply] using hxm)
      obtain ⟨l,hl⟩ := ((hP k hik).divisors (f j k hjk x)).1 ⟨hxa',hxm'⟩
      exact ⟨l,by simpa only [of_apply, DirectLimit.mk_apply] using (of f k).map_dvd hl⟩
    · rintro ⟨l,hl⟩
      have hn := (hi.divisors (n l)).2 ⟨l,dvd_refl _⟩
      exact ⟨hl.trans ((of f i).map_dvd hn.1),hl.trans ((of f i).map_dvd hn.2)⟩
  · intro x hxa hxm z
    obtain ⟨j,x,rfl⟩ := DirectLimit.exists_eq_mk f x
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    have hxa' : f j k hjk x ∣ f i k hik a :=
      (of_dvd_iff f hf k _ _).1 (by simpa only [of_apply, DirectLimit.mk_apply] using hxa)
    have hxm' : ¬ f j k hjk x ∣ f i k hik m := by
      intro h
      exact hxm (by simpa only [of_apply, DirectLimit.mk_apply] using (of f k).map_dvd h)
    have h := (of_conservative f hf k).intersections
      (f j k hjk x) (f i k hik m) (f i k hik a * f i k hik e)
        ((hP k hik).joins _ hxa' hxm') z
    simpa only [map_mul, of_apply, DirectLimit.mk_apply] using h

end PartitionConsistency.DiagramOrder.ConservativeLimit

namespace PartitionConsistency.DiagramOrder.ConservativeLimit
universe u v
variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {M : ι → Type v} [∀ i, LeftCancelMonoid (M i)] [∀ i, IsConical (M i)]
  (f : ∀ i j, i ≤ j → M i →* M j)
  [DirectedSystem M (f · · ·)]
  (H : ∀ i, HeightCost (LeftDivOrder (M i)))
  (hρ : ∀ i j hij x, (H j).height (f i j hij x) = (H i).height x)
  (hε : ∀ i j hij x, (H j).cost (f i j hij x) = (H i).cost x)

def height : LeftDivOrder (DirectLimit M f) → ℝ :=
  DirectLimit.lift f (fun i => (H i).height) (fun i j h x => (hρ i j h x).symm)

def cost : LeftDivOrder (DirectLimit M f) → ℝ :=
  DirectLimit.lift f (fun i => (H i).cost) (fun i j h x => (hε i j h x).symm)

@[simp] theorem height_of (i : ι) (x : M i) :
    height f H hρ (of f i x) = (H i).height x := rfl

@[simp] theorem cost_of (i : ι) (x : M i) :
    cost f H hε (of f i x) = (H i).cost x := rfl

omit [Nonempty ι] in
theorem height_pos (x : LeftDivOrder (DirectLimit M f)) : 0 < height f H hρ x := by
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk f x
  exact (H i).height_pos x

omit [Nonempty ι] in
theorem height_lt_one (x : LeftDivOrder (DirectLimit M f)) : height f H hρ x < 1 := by
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk f x
  exact (H i).height_lt_one x

omit [Nonempty ι] in
theorem cost_pos (x : LeftDivOrder (DirectLimit M f)) : 0 < cost f H hε x := by
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk f x
  exact (H i).cost_pos x

omit [Nonempty ι] in
theorem cost_le_one (x : LeftDivOrder (DirectLimit M f)) : cost f H hε x ≤ 1 := by
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk f x
  exact (H i).cost_le_one x

variable (hf : ∀ i j h, Conservative (f i j h))
  (hSup : ∀ i j hij (x y : LeftDivOrder (M i)),
    sSup ((H j).cost '' {d : LeftDivOrder (M j) |
      d ≤ f i j hij y ∧ ¬ d ≤ f i j hij x}) =
        sSup ((H i).cost '' {d : LeftDivOrder (M i) | d ≤ y ∧ ¬ d ≤ x}))
include hf hSup

/-- Costs of all later divisors, including those not present at the old
stage, are uniformly bounded by the old missed-cost supremum. -/
theorem cost_le_old_sup (i : ι) (x y : LeftDivOrder (M i))
    (d : LeftDivOrder (DirectLimit M f))
    (hdy : d ≤ of f i y) (hdx : ¬ d ≤ of f i x) :
    cost f H hε d ≤ sSup ((H i).cost '' {a : LeftDivOrder (M i) | a ≤ y ∧ ¬ a ≤ x}) := by
  obtain ⟨j,d,rfl⟩ := DirectLimit.exists_eq_mk f d
  obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
  have hdy' : @LE.le (LeftDivOrder (M k)) _ (f j k hjk d) (f i k hik y) := by
    apply (LeftDivOrder.le_iff_dvd (M := M k) _ _).2
    apply (of_dvd_iff f hf k _ _).1
    erw [of_map f j k hjk d, of_map f i k hik y]
    exact (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).1 hdy
  have hdx' : ¬ @LE.le (LeftDivOrder (M k)) _ (f j k hjk d) (f i k hik x) := by
    intro h
    apply hdx
    have hdv := (LeftDivOrder.le_iff_dvd (M := M k) _ _).1 h
    have hv := (of f k).map_dvd hdv
    erw [of_map f j k hjk d, of_map f i k hik x] at hv
    exact (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).2 hv
  have hb : BddAbove ((H k).cost '' {a : LeftDivOrder (M k) |
      a ≤ f i k hik y ∧ ¬ a ≤ f i k hik x}) := by
    refine ⟨1,?_⟩
    rintro _ ⟨a,_,rfl⟩
    exact (H k).cost_le_one a
  have hc := le_csSup hb ⟨f j k hjk d,⟨hdy',hdx'⟩,rfl⟩
  rw [hSup i k hik x y, hε j k hjk d] at hc
  exact hc

/-- No supremum inflation occurs at limit stages. Merely preserving
pointwise strict inequalities would not imply this statement. -/
theorem old_cost_supremum (i : ι) (x y : LeftDivOrder (M i)) :
    sSup (cost f H hε '' {d : LeftDivOrder (DirectLimit M f) |
      d ≤ of f i y ∧ ¬ d ≤ of f i x}) =
        sSup ((H i).cost '' {d : LeftDivOrder (M i) | d ≤ y ∧ ¬ d ≤ x}) := by
  let S₀ := (H i).cost '' {d : LeftDivOrder (M i) | d ≤ y ∧ ¬ d ≤ x}
  let S₁ := cost f H hε '' {d : LeftDivOrder (DirectLimit M f) |
      d ≤ of f i y ∧ ¬ d ≤ of f i x}
  have hsubset : S₀ ⊆ S₁ := by
    rintro _ ⟨d,⟨hdy,hdx⟩,rfl⟩
    refine ⟨of f i d,⟨?_,?_⟩,rfl⟩
    · exact (LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).2
        ((of f i).map_dvd ((LeftDivOrder.le_iff_dvd (M := M i) _ _).1 hdy))
    · intro h
      apply hdx
      exact (LeftDivOrder.le_iff_dvd (M := M i) _ _).2
        ((of_dvd_iff f hf i d x).1
          ((LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).1 h))
  change sSup S₁ = sSup S₀
  by_cases hyx : y ≤ x
  · have hS₀ : S₀ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro _ ⟨d,⟨hdy,hdx⟩,_⟩
      exact hdx (hdy.trans hyx)
    have hS₁ : S₁ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      rintro _ ⟨d,⟨hdy,hdx⟩,_⟩
      apply hdx
      exact hdy.trans ((LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).2
        ((of f i).map_dvd ((LeftDivOrder.le_iff_dvd (M := M i) _ _).1 hyx)))
    rw [hS₀,hS₁]
  · have hS₀ : S₀.Nonempty := ⟨(H i).cost y,y,⟨le_rfl,hyx⟩,rfl⟩
    have hS₁ : S₁.Nonempty := hS₀.mono hsubset
    have hb₁ : BddAbove S₁ := by
      refine ⟨1,?_⟩
      rintro _ ⟨d,_,rfl⟩
      exact cost_le_one f H hε d
    apply le_antisymm
    · apply csSup_le hS₁
      rintro _ ⟨d,⟨hdy,hdx⟩,rfl⟩
      exact cost_le_old_sup f H hε hf hSup i x y d hdy hdx
    · exact csSup_le hS₀ (fun r hr => le_csSup hb₁ (hsubset hr))

/-- Limit-stage extension of the exact real height/cost margin, using
unchanged old suprema at every transition of the tower. -/
def heightCost : HeightCost (LeftDivOrder (DirectLimit M f)) where
  height := height f H hρ
  cost := cost f H hε
  height_pos := height_pos f H hρ
  height_lt_one := height_lt_one f H hρ
  cost_pos := cost_pos f H hε
  cost_le_one := cost_le_one f H hε
  margin {x y} hxy := by
    obtain ⟨i,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ f x y
    have hxy' : @LT.lt (LeftDivOrder (M i)) _ x y := by
      apply lt_iff_le_and_ne.2
      refine ⟨?_,?_⟩
      · apply (LeftDivOrder.le_iff_dvd (M := M i) _ _).2
        exact (of_dvd_iff f hf i x y).1
          ((LeftDivOrder.le_iff_dvd (M := DirectLimit M f) _ _).1 hxy.le)
      · exact fun he => hxy.ne (congrArg (of f i) he)
    change sSup (cost f H hε '' {d : LeftDivOrder (DirectLimit M f) |
      d ≤ of f i y ∧ ¬ d ≤ of f i x}) < (H i).height y - (H i).height x
    rw [old_cost_supremum f H hε hf hSup i x y]
    exact (H i).margin hxy'

@[simp] theorem heightCost_height_of (i : ι) (x : M i) :
    (heightCost f H hρ hε hf hSup).height (of f i x) = (H i).height x := rfl

@[simp] theorem heightCost_cost_of (i : ι) (x : M i) :
    (heightCost f H hρ hε hf hSup).cost (of f i x) = (H i).cost x := rfl

end PartitionConsistency.DiagramOrder.ConservativeLimit
end

namespace PartitionConsistency.DiagramOrder.ConservativeLimit
universe u v
variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
  {M : ι → Type u} {F : ∀ ⦃i j : ι⦄, i ≤ j → Sort v}
  (f : ∀ i j (h : i ≤ j), F h)
  [∀ ⦃i j : ι⦄ (h : i ≤ j), FunLike (F h) (M i) (M j)]
  [DirectedSystem M (f · · ·)]

/-- The cardinal bound used at the limit stages of the schedule. This does
not require injectivity, conservativity, or an algebraic structure. -/
theorem cardinal_le {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    (hι : Cardinal.mk ι ≤ μ) (hM : ∀ i, Cardinal.mk (M i) ≤ μ) :
    Cardinal.mk (DirectLimit M f) ≤ μ := by
  calc
    Cardinal.mk (DirectLimit M f) ≤ Cardinal.mk (Sigma M) := Cardinal.mk_quotient_le
    _ = Cardinal.sum (fun i => Cardinal.mk (M i)) := Cardinal.mk_sigma M
    _ ≤ Cardinal.sum (fun _ : ι => μ) := Cardinal.sum_le_sum _ _ hM
    _ = Cardinal.mk ι * μ := Cardinal.sum_const' ι μ
    _ ≤ μ * μ := by simpa only [mul_comm] using mul_le_mul_right hι μ
    _ = μ := Cardinal.mul_eq_self hμ

end PartitionConsistency.DiagramOrder.ConservativeLimit

end OAI
