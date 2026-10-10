import Mathlib

namespace OAI

namespace PartitionConsistency
namespace DiagramOrder

/-- Conicality is the condition from the source, not right cancellation. -/
class IsConical (M : Type*) [Monoid M] : Prop where
  eq_one_of_mul_eq_one {x y : M} : x * y = 1 → x = 1 ∧ y = 1

/-- The underlying monoid, equipped with the left-divisibility order below. -/
def LeftDivOrder (M : Type*) := M

namespace LeftDivOrder

instance {M : Type*} [Monoid M] : Monoid (LeftDivOrder M) :=
  inferInstanceAs (Monoid M)

instance {M : Type*} [LeftCancelMonoid M] : LeftCancelMonoid (LeftDivOrder M) :=
  inferInstanceAs (LeftCancelMonoid M)

instance {M : Type*} [Monoid M] [IsConical M] : IsConical (LeftDivOrder M) :=
  inferInstanceAs (IsConical M)

instance {M : Type*} [LeftCancelMonoid M] [IsConical M] : PartialOrder (LeftDivOrder M) where
  le x y := ∃ z, x * z = y
  le_refl x := ⟨1, mul_one x⟩
  le_trans x y z hxy hyz := by
    obtain ⟨u, hu⟩ := hxy
    obtain ⟨v, hv⟩ := hyz
    exact ⟨u * v, by rw [← mul_assoc, hu, hv]⟩
  le_antisymm x y hxy hyx := by
    obtain ⟨u, hu⟩ := hxy
    obtain ⟨v, hv⟩ := hyx
    have huv : u * v = 1 := by
      apply mul_left_cancel (a := x)
      rw [← mul_assoc, hu, hv, mul_one]
    have hu₁ := (IsConical.eq_one_of_mul_eq_one huv).1
    simpa only [hu₁, mul_one] using hu

instance {M : Type*} [LeftCancelMonoid M] [IsConical M] : OrderBot (LeftDivOrder M) where
  bot := 1
  bot_le x := ⟨x, one_mul x⟩

theorem le_iff {M : Type*} [LeftCancelMonoid M] [IsConical M]
    (x y : LeftDivOrder M) : x ≤ y ↔ ∃ z, x * z = y := Iff.rfl

theorem factor_unique {M : Type*} [LeftCancelMonoid M]
    {x y u v : LeftDivOrder M} (hu : x * u = y) (hv : x * v = y) : u = v :=
  mul_left_cancel (hu.trans hv.symm)

end LeftDivOrder

variable {α : Type*} [PartialOrder α]

/-- Exact height and cost hypotheses from equation (mono-margin). For the
strict comparisons used in that equation, the set of costs is nonempty
and bounded; the real conditional supremum is therefore the ordinary one. -/
structure HeightCost (α : Type*) [PartialOrder α] where
  height : α → ℝ
  cost : α → ℝ
  height_pos : ∀ x, 0 < height x
  height_lt_one : ∀ x, height x < 1
  cost_pos : ∀ x, 0 < cost x
  cost_le_one : ∀ x, cost x ≤ 1
  margin {x y : α} : x < y →
    sSup (cost '' {d | d ≤ y ∧ ¬ d ≤ x}) < height y - height x

namespace HeightCost
variable (H : HeightCost α)

/-- Each missing divisor's positive cost is paid by the height increase. -/
theorem point_margin {x y d : α} (hxy : x < y) (hdy : d ≤ y) (hdx : ¬ d ≤ x) :
    H.cost d < H.height y - H.height x := by
  have hb : BddAbove (H.cost '' {d | d ≤ y ∧ ¬ d ≤ x}) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, _, rfl⟩
    exact H.cost_le_one a
  exact (le_csSup hb ⟨d, ⟨hdy, hdx⟩, rfl⟩).trans_lt (H.margin hxy)

theorem strictMono_height : StrictMono H.height := by
  intro x y hxy
  have h := H.point_margin hxy le_rfl (not_le_of_gt hxy)
  have hp := H.cost_pos y
  linarith

include H in
/-- The central countability argument of `lem:mono-countable-ideal`.
In fact, only nonemptiness and directedness of the set are needed. No
cardinality assumption, inaccessible, or prechosen sequence is used. -/
theorem directed_cofinal_sequence {U : Set α} (hne : U.Nonempty)
    (hdir : DirectedOn (· ≤ ·) U) :
    ∃ f : ℕ → α, (∀ n, f n ∈ U) ∧ Monotone f ∧ ∀ d ∈ U, ∃ n, d ≤ f n := by
  classical
  let r := sSup (H.height '' U)
  have hb : BddAbove (H.height '' U) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    exact (H.height_lt_one x).le
  have approx : ∀ n : ℕ, ∃ u : U, r - 1 / (n + 1 : ℝ) < H.height u := by
    intro n
    have hpos : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
    have hr : r - 1 / (n + 1 : ℝ) < r := by linarith
    obtain ⟨_, ⟨u, hu, rfl⟩, hr'⟩ := (lt_csSup_iff hb (hne.image H.height)).1 hr
    exact ⟨⟨u, hu⟩, hr'⟩
  choose u hu using approx
  have upper : ∀ x y : U, ∃ z : U, x.val ≤ z.val ∧ y.val ≤ z.val := by
    intro x y
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x.val x.property y.val y.property
    exact ⟨⟨z, hz⟩, hxz, hyz⟩
  choose b hb₁ hb₂ using upper
  let f : ℕ → U := Nat.rec (u 0) (fun n prev => b prev (u (n + 1)))
  have hmono : Monotone (fun n => (f n).val) := by
    apply monotone_nat_of_le_succ
    intro n
    exact hb₁ (f n) (u (n + 1))
  have hu_le : ∀ n, (u n).val ≤ (f n).val := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact hb₂ (f n) (u (n + 1))
  have happrox : ∀ n : ℕ, r - 1 / (n + 1 : ℝ) < H.height (f n).val := by
    intro n
    exact (hu n).trans_le (H.strictMono_height.monotone (hu_le n))
  refine ⟨fun n => (f n).val, fun n => (f n).property, hmono, ?_⟩
  intro d hd
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (H.cost_pos d)
  refine ⟨n, ?_⟩
  by_contra hdn
  let z := b (f n) ⟨d, hd⟩
  have hxz : (f n).val ≤ z.val := hb₁ _ _
  have hdz : d ≤ z.val := hb₂ (f n) ⟨d, hd⟩
  have hlt : (f n).val < z.val := lt_of_le_not_ge hxz (fun h => hdn (hdz.trans h))
  have hgap := H.point_margin hlt hdz hdn
  have hbound : H.height z.val ≤ r := le_csSup hb ⟨z.val, z.property, rfl⟩
  have happ := happrox n
  linarith

end HeightCost

/-- A conditional join exists exactly for pairs possessing a common upper
bound. In the divisibility order this says that the intersection of two
principal right cones, when nonempty, is a principal right cone. -/
def HasConditionalJoins (α : Type*) [PartialOrder α] : Prop :=
  ∀ x y a : α, x ≤ a → y ≤ a → ∃ j, IsLUB {x, y} j

/-- An ideal in the source's bounded cone: nonempty and downward closed,
contained in the cone, and closed under its finite nonempty joins. Closure
under binary joins suffices, since singleton joins add no new condition. -/
structure ConeIdeal (a : α) where
  carrier : Set α
  nonempty : carrier.Nonempty
  bounded : carrier ⊆ Set.Iic a
  lower : IsLowerSet carrier
  join_closed {x y j : α} : x ∈ carrier → y ∈ carrier → IsLUB {x, y} j → j ∈ carrier

namespace ConeIdeal

theorem directed {a : α} (U : ConeIdeal a) (hj : HasConditionalJoins α) :
    DirectedOn (· ≤ ·) U.carrier := by
  intro x hx y hy
  obtain ⟨j, hxy⟩ := hj x y a (U.bounded hx) (U.bounded hy)
  exact ⟨j, U.join_closed hx hy hxy,
    hxy.1 (Set.mem_insert _ _), hxy.1 (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

/-- Source `lem:mono-countable-ideal`, including the stipulated first entry.
When `α = LeftDivOrder M`, the bottom element in this statement is `1`. -/
theorem countable_cofinal_sequence [OrderBot α] (H : HeightCost α)
    (hj : HasConditionalJoins α) {a : α} (U : ConeIdeal a) :
    ∃ f : ℕ → α, f 0 = ⊥ ∧ (∀ n, f n ∈ U.carrier) ∧ Monotone f ∧
      ∀ d ∈ U.carrier, ∃ n, d ≤ f n := by
  obtain ⟨g, hg, hmono, hcof⟩ := H.directed_cofinal_sequence U.nonempty (U.directed hj)
  let f : ℕ → α := fun n => match n with
    | 0 => ⊥
    | k + 1 => g k
  refine ⟨f, rfl, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
        obtain ⟨u, hu⟩ := U.nonempty
        exact U.lower bot_le hu
    | succ n => exact hg n
  · apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero => exact bot_le
    | succ n => exact hmono (Nat.le_succ n)
  · intro d hd
    obtain ⟨n, hn⟩ := hcof d hd
    exact ⟨n + 1, hn⟩

/-- Equality of bounded ideals is equality of their underlying subsets. -/
@[ext] theorem ext {a : α} {U V : ConeIdeal a} (h : U.carrier = V.carrier) : U = V := by
  cases U
  cases V
  cases h
  rfl

/-- A cofinal sequence determines an ideal without any choices of individual
lower elements: the ideal is exactly the lower closure of the sequence. -/
theorem carrier_of_cofinal {a : α} (U : ConeIdeal a) {f : ℕ → α}
    (hf : ∀ n, f n ∈ U.carrier) (hcof : ∀ d ∈ U.carrier, ∃ n, d ≤ f n) :
    U.carrier = {d | ∃ n, d ≤ f n} := by
  ext d
  constructor
  · exact hcof d
  · rintro ⟨n, hn⟩
    exact U.lower hn (hf n)

/-- The countable-cofinal-chain coding bound used when enumerating the monoid
requirements. This proves the cardinal bound, but does not construct a
monoid realizing those requirements. -/
theorem cardinal_bound [OrderBot α] (H : HeightCost α)
    (hj : HasConditionalJoins α) (a : α) :
    Cardinal.mk (ConeIdeal a) ≤ Cardinal.mk α ^ Cardinal.aleph0 := by
  classical
  have h : ∀ U : ConeIdeal a, ∃ f : ℕ → α, f 0 = ⊥ ∧
      (∀ n, f n ∈ U.carrier) ∧ Monotone f ∧ ∀ d ∈ U.carrier, ∃ n, d ≤ f n :=
    fun U => U.countable_cofinal_sequence H hj
  choose f hzero hmem hmono hcof using h
  have hinj : Function.Injective f := by
    intro U V heq
    apply ext
    rw [U.carrier_of_cofinal (hmem U) (hcof U),
      V.carrier_of_cofinal (hmem V) (hcof V), heq]
  simpa [Cardinal.mk_arrow] using Cardinal.mk_le_of_injective hinj

/-- Under the scheduling bound `μ^ℵ₀ = μ`, there are at most `μ` ideals
in each bounded cone of a monoid (or order) of size at most `μ`. -/
theorem cardinal_le [OrderBot α] (H : HeightCost α)
    (hj : HasConditionalJoins α) (a : α) {μ : Cardinal}
    (hα : Cardinal.mk α ≤ μ) (hμ : μ ^ Cardinal.aleph0 = μ) :
    Cardinal.mk (ConeIdeal a) ≤ μ := by
  calc
    Cardinal.mk (ConeIdeal a) ≤ Cardinal.mk α ^ Cardinal.aleph0 :=
      cardinal_bound H hj a
    _ ≤ μ ^ Cardinal.aleph0 := Cardinal.power_le_power_right hα
    _ = μ := hμ

end ConeIdeal
end DiagramOrder
end PartitionConsistency

end OAI
