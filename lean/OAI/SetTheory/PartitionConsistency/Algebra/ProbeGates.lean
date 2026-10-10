import Mathlib
import OAI.SetTheory.PartitionConsistency.Algebra.ProbeWords

namespace OAI

/-! ## Probe extension: all gates, conditional joins, and presentation -/

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder
namespace Raw

def head {M : Type u} {S : Type v} : Raw M S → Option S
  | .old _ => none
  | .cons s _ => some s

def length {M : Type u} {S : Type v} : Raw M S → ℕ
  | .old _ => 0
  | .cons _ w => w.length + 1

end Raw
namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] (A : Alphabet M S) (b : M)

def head (w : Word A b) : Option S := w.val.head

@[simp] theorem head_old (x : M) : head A b (old A b x) = none := rfl
@[simp] theorem head_cons (s : S) (w : Word A b) (hw) :
    head A b (cons A b s w hw) = some s := rfl

/-- The first-letter blocks and the old elements partition the irreducibles. -/
theorem head_eq_none_iff (w : Word A b) :
    head A b w = none ↔ ∃ x, w = old A b x := by
  obtain ⟨w, hw⟩ := w
  cases w with
  | old x => exact ⟨fun _ => ⟨x, rfl⟩, fun _ => rfl⟩
  | cons s w =>
    constructor
    · intro h; cases h
    · rintro ⟨x, hx⟩; cases congrArg Subtype.val hx

theorem head_eq_some_iff (w : Word A b) (s : S) :
    head A b w = some s ↔ ∃ v, ∃ hv, w = cons A b s v hv := by
  obtain ⟨w, hw⟩ := w
  cases w with
  | old x =>
    constructor
    · intro h; cases h
    · rintro ⟨v, hv, hx⟩; cases congrArg Subtype.val hx
  | cons t w =>
    change w.reduced A b ∧ ¬ w.headDiv A b at hw
    constructor
    · intro ht
      cases Option.some.inj ht
      exact ⟨⟨w, hw.1⟩, hw.2, rfl⟩
    · rintro ⟨v, hv, he⟩
      exact congrArg (head A b) he

/-- Membership in an old cone depends only on the head of a new form. -/
theorem headDiv_of_head_eq_some {x : M} {w : Word A b} {s : S}
    (hw : head A b w = some s) : headDiv A b x w ↔ ∃ t, A.act x t = s := by
  obtain ⟨v, hv, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  rfl

theorem headDiv_of_same_head {x : M} {w z : Word A b} {s : S}
    (hw : head A b w = some s) (hz : head A b z = some s) :
    headDiv A b x w ↔ headDiv A b x z :=
  (headDiv_of_head_eq_some A b hw).trans (headDiv_of_head_eq_some A b hz).symm

theorem head_oldAct_exit_ne (s : S) (w : Word A b) :
    head A b (oldAct A b (A.exit s) w) ≠ some s := by
  intro h
  exact A.separated s ((headDiv_of_head_eq_some A b h).1
    (headDiv_oldAct A b (A.exit s) w))

/-- A prepended letter exits its original block exactly when its input is
in the distinguished old `b`-cone. -/
theorem head_letterAct_ne_iff (s : S) (w : Word A b) :
    head A b (letterAct A b s w) ≠ some s ↔ headDiv A b b w := by
  classical
  by_cases h : headDiv A b b w
  · rw [letterAct_of_headDiv A b s w h]
    exact ⟨fun _ => h, fun _ => head_oldAct_exit_ne A b s _⟩
  · rw [letterAct_of_not_headDiv A b s w h, head_cons]
    exact ⟨fun h' => (h' rfl).elim, fun h' => (h h').elim⟩

/-- A gate is an old generator for precisely the part of a right cone
lying outside its word's first-letter block. -/
def Gate (w : Word A b) (s : S) (g : M) : Prop :=
  ∀ z : Word A b, (w ∣ z ∧ head A b z ≠ some s) ↔ old A b g ∣ z

theorem Gate.dvd {w : Word A b} {s : S} {g : M} (hg : Gate A b w s g) :
    w ∣ old A b g := ((hg _).2 (dvd_refl _)).1

theorem Gate.head_ne {w : Word A b} {s : S} {g : M}
    (hg : Gate A b w s g) {z : Word A b} (hz : old A b g ∣ z) :
    head A b z ≠ some s := ((hg z).2 hz).2

theorem Gate.dvd_old_iff {w : Word A b} {s : S} {g : M}
    (hg : Gate A b w s g) (y : M) : w ∣ old A b y ↔ g ∣ y := by
  rw [← old_dvd_old_iff A b g y, ← hg]
  exact ⟨fun h => ⟨h, by intro he; cases he⟩, And.left⟩

/-- An old cone either contains a whole first-letter block or is disjoint
from that block; in the latter case it sees only the gate of a word. -/
theorem Gate.old_intersection {w : Word A b} {s : S} {g x : M}
    (hg : Gate A b w s g) (hw : head A b w = some s)
    (hx : ¬ headDiv A b x w) (z : Word A b) :
    old A b x ∣ z ∧ w ∣ z ↔ old A b x ∣ z ∧ old A b g ∣ z := by
  constructor
  · rintro ⟨hxz, hwz⟩
    refine ⟨hxz, (hg z).1 ⟨hwz, ?_⟩⟩
    intro hz
    exact hx ((headDiv_of_same_head A b hw hz).2 ((old_dvd_iff_headDiv A b x z).1 hxz))
  · rintro ⟨hxz, hgz⟩
    exact ⟨hxz, hg.dvd.trans hgz⟩

/-- A principal old intersection for the suffix computes the exit cone
of the word. The quotient `u` is an old right factor of the intersection. -/
theorem gate_of_suffix_intersection (s : S) (Y : Word A b)
    (hY : ¬ headDiv A b b Y) (u : M)
    (hI : ∀ z : Word A b,
      Y ∣ z ∧ old A b b ∣ z ↔ old A b (b * u) ∣ z) :
    Gate A b (cons A b s Y hY) s (A.exit s * u) := by
  intro z
  constructor
  · rintro ⟨⟨v, hv⟩, hz⟩
    have hex : headDiv A b b (Y * v) := by
      apply (head_letterAct_ne_iff A b s _).1
      exact (congrArg (head A b) hv) ▸ hz
    have hbu : old A b (b * u) ∣ Y * v :=
      (hI _).1 ⟨dvd_mul_right _ _, (old_dvd_iff_headDiv A b b _).2 hex⟩
    obtain ⟨q, hq⟩ := hbu
    refine ⟨q, ?_⟩
    calc
      z = letterAct A b s (Y * v) := hv
      _ = letterAct A b s (oldAct A b b (oldAct A b u q)) := by
        exact congrArg (letterAct A b s) (hq.trans (oldAct_mul A b b u q))
      _ = oldAct A b (A.exit s) (oldAct A b u q) := letterAct_oldAct_b A b s _
      _ = old A b (A.exit s * u) * q := (oldAct_mul A b _ _ _).symm
  · intro hg
    obtain ⟨v, hv⟩ := ((hI (old A b (b * u))).2 (dvd_refl _)).1
    have hwg : cons A b s Y hY * v = old A b (A.exit s * u) := by
      change letterAct A b s (Y * v) = _
      rw [← hv]
      change letterAct A b s (oldAct A b b (old A b u)) = _
      rw [letterAct_oldAct_b]
      rfl
    refine ⟨(show cons A b s Y hY ∣ old A b (A.exit s * u) from ⟨v, hwg.symm⟩).trans hg, ?_⟩
    obtain ⟨q, rfl⟩ := hg
    change head A b (oldAct A b (A.exit s * u) q) ≠ some s
    rw [oldAct_mul]
    exact head_oldAct_exit_ne A b s _

/-- Only old cone intersections are required for the recursive gate
calculation. The path alphabet supplies this law from old conditional joins. -/
def OldIntersections : Prop :=
  ∀ x y : M, ∀ z : Word A b, old A b x ∣ z → old A b y ∣ z →
    ∃ j : M, ∀ v : Word A b, old A b x ∣ v ∧ old A b y ∣ v ↔ old A b j ∣ v

/-- Every genuine exit of a new word determines a least old right-multiple
cone. This induction is on literal suffix length, not on a presumed join
operation for new words. -/
theorem exists_gate_of_exit (hOld : OldIntersections A b) (w : Word A b)
    {s : S} (hs : head A b w = some s) {z : Word A b}
    (hwz : w ∣ z) (hz : head A b z ≠ some s) :
    ∃ g : M, Gate A b w s g := by
  obtain ⟨w, hw⟩ := w
  induction w generalizing s z with
  | old x => cases hs
  | cons t Y ih =>
    have hts : t = s := Option.some.inj hs
    subst t
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hw
    let Y' : Word A b := ⟨Y, hw.1⟩
    obtain ⟨v, hv⟩ := hwz
    have hbyv : old A b b ∣ Y' * v := by
      apply (old_dvd_iff_headDiv A b b _).2
      apply (head_letterAct_ne_iff A b s _).1
      exact (congrArg (head A b) hv) ▸ hz
    have hInt : ∃ j : M, ∀ q : Word A b,
        Y' ∣ q ∧ old A b b ∣ q ↔ old A b j ∣ q := by
      cases heY : Y with
      | old y =>
        have hYeq : Y' = old A b y := Subtype.ext heY
        rw [hYeq] at ⊢ hbyv
        exact hOld y b (old A b y * v) (dvd_mul_right _ _) hbyv
      | cons t Z =>
        have hY' : head A b Y' = some t := by change Y.head = some t; rw [heY]; rfl
        have hne : head A b (Y' * v) ≠ some t := by
          intro hh
          exact hw.2 ((headDiv_of_same_head A b hY' hh).2
            ((old_dvd_iff_headDiv A b b _).1 hbyv))
        obtain ⟨g, hg⟩ := ih hne hw.1 hY' (dvd_mul_right Y' v)
        have hgYv : old A b g ∣ Y' * v := (hg _).1 ⟨dvd_mul_right _ _, hne⟩
        obtain ⟨j, hj⟩ := hOld g b (Y' * v) hgYv hbyv
        refine ⟨j, fun q => ?_⟩
        calc
          Y' ∣ q ∧ old A b b ∣ q ↔ old A b b ∣ q ∧ Y' ∣ q := and_comm
          _ ↔ old A b b ∣ q ∧ old A b g ∣ q := Gate.old_intersection A b hg hY' hw.2 q
          _ ↔ old A b g ∣ q ∧ old A b b ∣ q := and_comm
          _ ↔ old A b j ∣ q := hj q
    obtain ⟨j, hj⟩ := hInt
    have hbj : b ∣ j := (old_dvd_old_iff A b b j).1 (((hj _).2 (dvd_refl _)).2)
    obtain ⟨u, rfl⟩ := hbj
    exact ⟨A.exit s * u, gate_of_suffix_intersection A b s Y' hw.2 u hj⟩

/-- An old right multiplier can leave the first-letter block only after
all the intervening letters have been consumed. Thus an exit obtained by
such a multiplier is itself old. -/
theorem append_old_exit_isOld (w : Word A b) {s : S}
    (hs : head A b w = some s) (d : M)
    (hex : head A b (w * old A b d) ≠ some s) :
    ∃ y : M, w * old A b d = old A b y := by
  obtain ⟨w, hw⟩ := w
  induction w generalizing s with
  | old x => cases hs
  | cons t Y ih =>
    have hts : t = s := Option.some.inj hs
    subst t
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hw
    let Y' : Word A b := ⟨Y, hw.1⟩
    have hby : headDiv A b b (Y' * old A b d) :=
      (head_letterAct_ne_iff A b s _).1 hex
    have hYold : ∃ y : M, Y' * old A b d = old A b y := by
      cases heY : Y with
      | old y =>
        have hYeq : Y' = old A b y := Subtype.ext heY
        exact ⟨y * d, congrArg (· * old A b d) hYeq⟩
      | cons t Z =>
        have hYhead : head A b Y' = some t := by change Y.head = some t; rw [heY]; rfl
        have hexY : head A b (Y' * old A b d) ≠ some t := by
          intro hhead
          exact hw.2 ((headDiv_of_same_head A b hYhead hhead).2 hby)
        exact ih hw.1 hYhead hexY
    obtain ⟨y, hy⟩ := hYold
    have hbyold : b ∣ y := by
      change headDiv A b b (old A b y)
      exact hy ▸ hby
    obtain ⟨q, rfl⟩ := hbyold
    refine ⟨A.exit s * q, ?_⟩
    change letterAct A b s (Y' * old A b d) = _
    rw [hy]
    change letterAct A b s (oldAct A b b (old A b q)) = _
    rw [letterAct_oldAct_b]
    rfl

/-- The actual least-old-multiple rule required for the later descending
birth-ordinal argument. -/
theorem Gate.append_old {w : Word A b} {s : S} {g : M}
    (hg : Gate A b w s g) (hs : head A b w = some s) (d : M)
    (hd : old A b g ∣ w * old A b d) :
    ∃ y : M, w * old A b d = old A b y :=
  append_old_exit_isOld A b w hs d (Gate.head_ne A b hg hd)

/-- A common multiple in one first-letter block forces every different-
headed divisor of that multiple to divide the entire block. -/
theorem dvd_of_different_head (hOld : OldIntersections A b)
    {w v z : Word A b} {s t : S}
    (hw : head A b w = some s) (hv : head A b v = some t) (hst : s ≠ t)
    (hvz : v ∣ z) (hz : head A b z = some s) : v ∣ w := by
  have hzt : head A b z ≠ some t := by rw [hz]; exact fun h => hst (Option.some.inj h)
  obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld v hv hvz hzt
  have hgz : old A b g ∣ z := (hg z).1 ⟨hvz, hzt⟩
  have hgw : old A b g ∣ w := by
    rw [old_dvd_iff_headDiv] at ⊢ hgz
    exact (headDiv_of_same_head A b hw hz).2 hgz
  exact (Gate.dvd A b hg).trans hgw

/-- Old divisors and differently headed new divisors both divide an
entire block as soon as they divide one member of that block. -/
theorem dvd_of_other_block (hOld : OldIntersections A b)
    {w v z : Word A b} {s : S}
    (hw : head A b w = some s) (hv : head A b v ≠ some s)
    (hvz : v ∣ z) (hz : head A b z = some s) : v ∣ w := by
  cases he : head A b v with
  | none =>
    obtain ⟨x, rfl⟩ := (head_eq_none_iff A b v).1 he
    rw [old_dvd_iff_headDiv] at ⊢ hvz
    exact (headDiv_of_same_head A b hw hz).2 hvz
  | some t =>
    exact dvd_of_different_head A b hOld hw he
      (fun hst => hv (hst ▸ he)) hvz hz

/-- The nonempty intersection of an old cone and any new cone is
computed by an old join, unless the old element already divides the word. -/
theorem old_word_cone_join (hOld : OldIntersections A b) (x : M) (w z : Word A b)
    (hxz : old A b x ∣ z) (hwz : w ∣ z) :
    ∃ j : Word A b, ∀ q : Word A b, old A b x ∣ q ∧ w ∣ q ↔ j ∣ q := by
  classical
  by_cases hxw : old A b x ∣ w
  · exact ⟨w, fun _ => ⟨And.right, fun h => ⟨hxw.trans h, h⟩⟩⟩
  cases he : head A b w with
  | none =>
    obtain ⟨y, rfl⟩ := (head_eq_none_iff A b w).1 he
    obtain ⟨j, hj⟩ := hOld x y z hxz hwz
    exact ⟨old A b j, hj⟩
  | some s =>
    have hx : ¬ headDiv A b x w := fun h => hxw ((old_dvd_iff_headDiv A b x w).2 h)
    have hzs : head A b z ≠ some s := by
      intro hz
      exact hx ((headDiv_of_same_head A b he hz).2 ((old_dvd_iff_headDiv A b x z).1 hxz))
    obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld w he hwz hzs
    obtain ⟨j, hj⟩ := hOld x g z hxz ((hg z).1 ⟨hwz, hzs⟩)
    exact ⟨old A b j, fun q => (Gate.old_intersection A b hg he hx q).trans (hj q)⟩

/-- Distinct incomparable first-letter blocks can meet only through both
of their gates, and the old cone law computes that intersection. -/
theorem different_head_cone_join (hOld : OldIntersections A b)
    {w v z : Word A b} {s t : S}
    (hw : head A b w = some s) (hv : head A b v = some t) (hst : s ≠ t)
    (hwz : w ∣ z) (hvz : v ∣ z) :
    ∃ j : Word A b, ∀ q, w ∣ q ∧ v ∣ q ↔ j ∣ q := by
  classical
  by_cases hwv : w ∣ v
  · exact ⟨v, fun _ => ⟨And.right, fun h => ⟨hwv.trans h, h⟩⟩⟩
  by_cases hvw : v ∣ w
  · exact ⟨w, fun _ => ⟨And.left, fun h => ⟨h, hvw.trans h⟩⟩⟩
  have hqs : ∀ q : Word A b, v ∣ q → head A b q ≠ some s := by
    intro q hvq hq
    exact hvw (dvd_of_different_head A b hOld hw hv hst hvq hq)
  have hqt : ∀ q : Word A b, w ∣ q → head A b q ≠ some t := by
    intro q hwq hq
    exact hwv (dvd_of_different_head A b hOld hv hw hst.symm hwq hq)
  obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld w hw hwz (hqs z hvz)
  obtain ⟨k, hk⟩ := exists_gate_of_exit A b hOld v hv hvz (hqt z hwz)
  obtain ⟨j, hj⟩ := hOld g k z ((hg z).1 ⟨hwz, hqs z hvz⟩) ((hk z).1 ⟨hvz, hqt z hwz⟩)
  refine ⟨old A b j, fun q => ?_⟩
  rw [← hj q]
  constructor
  · rintro ⟨hwq, hvq⟩
    exact ⟨(hg q).1 ⟨hwq, hqs q hvq⟩, (hk q).1 ⟨hvq, hqt q hwq⟩⟩
  · rintro ⟨hgq, hkq⟩
    exact ⟨(Gate.dvd A b hg).trans hgq, (Gate.dvd A b hk).trans hkq⟩

end Word

/-- Left translation preserves an exact cone-intersection equation in a
left-cancellative monoid. -/
theorem translate_cone_intersection {N : Type*} [LeftCancelMonoid N]
    (c x y j : N) (hj : ∀ q, x ∣ q ∧ y ∣ q ↔ j ∣ q) :
    ∀ q, c * x ∣ q ∧ c * y ∣ q ↔ c * j ∣ q := by
  intro q
  constructor
  · rintro ⟨⟨r, rfl⟩, hyr⟩
    rw [_root_.mul_assoc] at hyr ⊢
    apply (left_mul_dvd_iff c j (x * r)).2
    exact (hj _).1 ⟨dvd_mul_right _ _, (left_mul_dvd_iff c y (x * r)).1 hyr⟩
  · intro hq
    have hjxy := (hj j).2 (dvd_refl j)
    exact ⟨(mul_dvd_mul_left c hjxy.1).trans hq, (mul_dvd_mul_left c hjxy.2).trans hq⟩

namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (hb : b ≠ 1)

include hb in
/-- All new conditional joins exist. Only the old cone theorem was used
in constructing gates; no intermediate join theorem is assumed. -/
theorem cone_join (hOld : OldIntersections A b) (w v z : Word A b)
    (hwz : w ∣ z) (hvz : v ∣ z) :
    ∃ j : Word A b, ∀ q, w ∣ q ∧ v ∣ q ↔ j ∣ q := by
  classical
  obtain ⟨w, hw⟩ := w
  induction w generalizing v z with
  | old x => exact old_word_cone_join A b hOld x v z hwz hvz
  | cons s Y ih =>
    change Y.reduced A b ∧ ¬ Y.headDiv A b at hw
    let Y' : Word A b := ⟨Y, hw.1⟩
    change cons A b s Y' hw.2 ∣ z at hwz
    change ∃ j, ∀ q, cons A b s Y' hw.2 ∣ q ∧ v ∣ q ↔ j ∣ q
    obtain ⟨v, hv⟩ := v
    cases v with
    | old y =>
      obtain ⟨j, hj⟩ := old_word_cone_join A b hOld y (cons A b s Y' hw.2) z hvz hwz
      exact ⟨j, fun q => and_comm.trans (hj q)⟩
    | cons t Z =>
      change Z.reduced A b ∧ ¬ Z.headDiv A b at hv
      let Z' : Word A b := ⟨Z, hv.1⟩
      change cons A b t Z' hv.2 ∣ z at hvz
      change ∃ j, ∀ q, cons A b s Y' hw.2 ∣ q ∧ cons A b t Z' hv.2 ∣ q ↔ j ∣ q
      by_cases hst : s = t
      · subst t
        let c := generator A b hb s
        have hY : cons A b s Y' hw.2 = c * Y' :=
          (generator_mul_of_not_headDiv A b hb s Y' hw.2).symm
        have hZ : cons A b s Z' hv.2 = c * Z' :=
          (generator_mul_of_not_headDiv A b hb s Z' hv.2).symm
        rw [hY, hZ] at ⊢
        rw [hY] at hwz
        rw [hZ] at hvz
        obtain ⟨r, rfl⟩ := hwz
        have hZr : Z' ∣ Y' * r := by
          apply (left_mul_dvd_iff c Z' (Y' * r)).1
          exact (_root_.mul_assoc c Y' r) ▸ hvz
        obtain ⟨j, hj⟩ := ih Z' (Y' * r) hZr hw.1 (dvd_mul_right _ _)
        exact ⟨c * j, translate_cone_intersection c Y' Z' j hj⟩
      · exact different_head_cone_join A b hOld rfl rfl hst hwz hvz

end Word

namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M)

/-- The old cone law used above is realized by the path alphabet. -/
theorem oldIntersections (hM : HasConditionalJoins (LeftDivOrder M)) :
    Word.OldIntersections (P.alphabet he) b := by
  intro x y z hx hy
  obtain ⟨a', hxa, hya⟩ := P.common_multiple_reflection he b hx hy
  obtain ⟨j, hj⟩ := exists_cone_join hM x y a' hxa hya
  exact ⟨j, P.old_cone_intersection he b x y j hj⟩

/-- Conditional joins in the actual probe extension, not just in the
old monoid or in the direct-limit alphabet. -/
theorem extension_hasConditionalJoins (hM : HasConditionalJoins (LeftDivOrder M)) (hb : b ≠ 1) :
    HasConditionalJoins (LeftDivOrder (P.Extension he b)) := by
  intro x y z hx hy
  obtain ⟨j, hj⟩ := Word.cone_join (P.alphabet he) b hb (P.oldIntersections he b hM) x y z
    ((LeftDivOrder.le_iff_dvd _ _).1 hx) ((LeftDivOrder.le_iff_dvd _ _).1 hy)
  refine ⟨j, (pair_lub_iff (α := LeftDivOrder (P.Extension he b)) x y j).2 (fun q => ?_)⟩
  rw [LeftDivOrder.le_iff_dvd (M := P.Extension he b) x q,
    LeftDivOrder.le_iff_dvd (M := P.Extension he b) y q,
    LeftDivOrder.le_iff_dvd (M := P.Extension he b) j q]
  exact hj q

end Path
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra
universe u v
open DiagramOrder
namespace Word
variable {M : Type u} {S : Type v} [LeftCancelMonoid M] [IsConical M]
  (A : Alphabet M S) (b : M) (hb : b ≠ 1)

/-- The exit of a one-letter probe is not merely a lower bound on its
old multiples: the entire exit cone is its precise gate cone. -/
theorem generator_gate (s : S) : Gate A b (generator A b hb s) s (A.exit s) := by
  have h1 : ¬ headDiv A b b (old A b 1) := by
    rintro ⟨z, hz⟩
    exact hb (IsConical.eq_one_of_mul_eq_one hz.symm).1
  have h := gate_of_suffix_intersection A b s (old A b 1) h1 1 (fun z => by
    change (1 : Word A b) ∣ z ∧ old A b b ∣ z ↔ old A b (b * 1) ∣ z
    rw [_root_.mul_one]
    exact ⟨And.right, fun h => ⟨one_dvd z, h⟩⟩)
  simpa only [generator, _root_.mul_one] using h

theorem generator_dvd_of_head {w : Word A b} {s : S} (hw : head A b w = some s) :
    generator A b hb s ∣ w := by
  obtain ⟨v, hv, rfl⟩ := (head_eq_some_iff A b w s).1 hw
  exact ⟨v, (generator_mul_of_not_headDiv A b hb s v hv).symm⟩

omit [IsConical M] in
/-- Entering a differently headed block factors through one old element,
including the case where the entering divisor was old to begin with. -/
theorem old_factor_of_other_block (hOld : OldIntersections A b)
    {w z : Word A b} {s : S} (hw : head A b w ≠ some s)
    (hz : head A b z = some s) (hwz : w ∣ z) :
    ∃ g : M, w ∣ old A b g ∧ old A b g ∣ z := by
  cases he : head A b w with
  | none =>
    obtain ⟨x, rfl⟩ := (head_eq_none_iff A b w).1 he
    exact ⟨x, dvd_refl _, hwz⟩
  | some t =>
    have hzt : head A b z ≠ some t := by
      intro hzt
      have hts : t = s := Option.some.inj (hzt.symm.trans hz)
      exact hw (hts ▸ he)
    obtain ⟨g, hg⟩ := exists_gate_of_exit A b hOld w he hwz hzt
    exact ⟨g, Gate.dvd A b hg, (hg z).1 ⟨hwz, hzt⟩⟩

end Word
namespace Path
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M) (hb : b ≠ 1)

/-- The gate of the initial probe is exactly the specified old `ae`. -/
theorem probe_zero_gate : Word.Gate (P.alphabet he) b
    (P.probe he b hb 0) (P.letter 0 1) (a * e) := by
  have hg := Word.generator_gate (P.alphabet he) b hb (P.letter 0 1)
  simpa only [probe, alphabet, exit, target_letter, terminal_zero, one_mul] using hg

include hb in
/-- No divisor of `a`, whether old or newly created, belongs to the first-
letter block of the initial probe. -/
theorem head_ne_initial_of_dvd_a {w : P.Extension he b}
    (hwa : w ∣ Word.old (P.alphabet he) b a) :
    Word.head (P.alphabet he) b w ≠ some (P.letter 0 1) := by
  intro hh
  have hmw := Word.generator_dvd_of_head (P.alphabet he) b hb hh
  exact P.probe_not_dvd_a he b hb (hmw.trans hwa)

/-- The full divisor profile of the initial probe, including the newly
created divisors of `a`. This is equality of the actual two downsets in
the extension, not only agreement on the old submonoid. -/
theorem probe_full_profile (hM : HasConditionalJoins (LeftDivOrder M)) (w : P.Extension he b) :
    w ∣ P.probe he b hb 0 ∧ w ∣ Word.old (P.alphabet he) b a ↔
      ∃ i : ℕ, w ∣ Word.old (P.alphabet he) b (P.node i) := by
  constructor
  · rintro ⟨hwm, hwa⟩
    have hw := P.head_ne_initial_of_dvd_a he b hb hwa
    obtain ⟨g, hwg, hgm⟩ := Word.old_factor_of_other_block (P.alphabet he) b
      (P.oldIntersections he b hM) hw rfl hwm
    obtain ⟨i, hgi⟩ := (P.probe_old_profile he b hb g).1 hgm
    exact ⟨i, hwg.trans ((Word.old_dvd_old_iff _ _ _ _).2 hgi)⟩
  · rintro ⟨i, hwi⟩
    have him := (P.probe_old_profile he b hb (P.node i)).2 ⟨i, dvd_refl _⟩
    have hia := (Word.old_dvd_old_iff (P.alphabet he) b (P.node i) a).2 (P.bounded i)
    exact ⟨hwi.trans him, hwi.trans hia⟩

/-- Every divisor of `a` outside the probe's downset has join `ae` with
the probe. Both old and new divisors are covered. -/
theorem probe_join_profile (hM : HasConditionalJoins (LeftDivOrder M))
    {w : P.Extension he b} (hwa : w ∣ Word.old (P.alphabet he) b a)
    (hwm : ¬ w ∣ P.probe he b hb 0) (z : P.Extension he b) :
    w ∣ z ∧ P.probe he b hb 0 ∣ z ↔ Word.old (P.alphabet he) b (a * e) ∣ z := by
  have hg := P.probe_zero_gate he b hb
  have hwae : w ∣ Word.old (P.alphabet he) b (a * e) :=
    hwa.trans ((Word.old_dvd_old_iff _ _ _ _).2 (dvd_mul_right a e))
  constructor
  · rintro ⟨hwz, hmz⟩
    refine (hg z).1 ⟨hmz, ?_⟩
    intro hz
    exact hwm (Word.dvd_of_other_block (P.alphabet he) b (P.oldIntersections he b hM)
      rfl (P.head_ne_initial_of_dvd_a he b hb hwa) hwz hz)
  · intro hz
    exact ⟨hwae.trans hz, (Word.Gate.dvd _ _ hg).trans hz⟩

/-- Explicitly, `ae` is the order-theoretic least upper bound required by
the last line of the probe-algebra lemma. -/
theorem probe_join_isLUB (hM : HasConditionalJoins (LeftDivOrder M))
    {w : LeftDivOrder (P.Extension he b)} (hwa : w ∣ Word.old (P.alphabet he) b a)
    (hwm : ¬ w ∣ P.probe he b hb 0) :
    IsLUB (α := LeftDivOrder (P.Extension he b)) {w, P.probe he b hb 0} (Word.old (P.alphabet he) b (a * e)) := by
  apply (pair_lub_iff (α := LeftDivOrder (P.Extension he b)) _ _ _).2
  intro z
  rw [LeftDivOrder.le_iff_dvd (M := P.Extension he b) w z,
    LeftDivOrder.le_iff_dvd (M := P.Extension he b) (P.probe he b hb 0) z,
    LeftDivOrder.le_iff_dvd (M := P.Extension he b) (Word.old (P.alphabet he) b (a * e)) z]
  exact P.probe_join_profile he b hb hM hwa hwm z

/-- Every new word with an old right multiple has a least old right
multiple, and multiplication by an old element past its gate is old. -/
theorem least_old_multiple (hM : HasConditionalJoins (LeftDivOrder M))
    {w : P.Extension he b} (hw : ¬ ∃ y : M, w = Word.old (P.alphabet he) b y)
    {y : M} (hy : w ∣ Word.old (P.alphabet he) b y) :
    ∃ g : M, w ∣ Word.old (P.alphabet he) b g ∧
      (∀ z : M, w ∣ Word.old (P.alphabet he) b z ↔ g ∣ z) ∧
      (∀ d : M, Word.old (P.alphabet he) b g ∣ w * Word.old (P.alphabet he) b d →
        ∃ z : M, w * Word.old (P.alphabet he) b d = Word.old (P.alphabet he) b z) := by
  cases hs : Word.head (P.alphabet he) b w with
  | none => exact (hw ((Word.head_eq_none_iff _ _ w).1 hs)).elim
  | some s =>
    obtain ⟨g, hg⟩ := Word.exists_gate_of_exit (P.alphabet he) b (P.oldIntersections he b hM)
      w hs hy (by intro he; cases he)
    exact ⟨g, Word.Gate.dvd _ _ hg, Word.Gate.dvd_old_iff _ _ hg,
      Word.Gate.append_old _ _ hg hs⟩

end Path
end PartitionConsistency.ProbeAlgebra

namespace PartitionConsistency.ProbeAlgebra.Path
universe u v
open DiagramOrder
variable {M : Type u} [LeftCancelMonoid M] [IsConical M] {a e : M}
  (P : Path M a) (he : e ≠ 1) (b : M) {N : Type v} [Monoid N]
  (f : M →* N) (p : ℕ → N)

omit [IsConical M] in
/-- Adjacent transition relations imply every finite-stage transition
relation, without any right cancellation in either monoid. -/
theorem transitions_from_adjacent
    (hp : ∀ i, p i = f (P.factor i (i+1) (Nat.le_succ i)) * p (i+1))
    (i j : ℕ) (hij : i ≤ j) : p i = f (P.factor i j hij) * p j := by
  induction j, hij using Nat.le_induction with
  | base => simp only [factor_self, f.map_one, one_mul]
  | succ j hij ih =>
    calc
      p i = f (P.factor i j hij) * p j := ih
      _ = f (P.factor i j hij) * (f (P.factor j (j+1) (Nat.le_succ j)) * p (j+1)) :=
        congrArg (f (P.factor i j hij) * ·) (hp j)
      _ = f (P.factor i (j+1) (hij.trans (Nat.le_succ j))) * p (j+1) := by
        rw [← mul_assoc, ← f.map_mul, factor_trans]

variable (hp : ∀ i, p i = f (P.factor i (i+1) (Nat.le_succ i)) * p (i+1))
  (hbexit : ∀ i, p i * f b = f (P.terminal i * e))

/-- A family satisfying the original presentation's transition relations
induces its equivariant interpretation on direct-limit letters. -/
noncomputable def interpretedLetter : P.Letters → N :=
  DirectLimit.lift P.transition (fun i x => f x * p i)
    (fun i j hij x => by
      simp only [transition_apply, f.map_mul, mul_assoc]
      rw [← P.transitions_from_adjacent f p hp i j hij])

omit [IsConical M] in
@[simp] theorem interpretedLetter_mk (i : ℕ) (x : M) :
    P.interpretedLetter f p hp (P.letter i x) = f x * p i := rfl

omit [IsConical M] in
@[simp] theorem interpretedLetter_act (x : M) (s : P.Letters) :
    P.interpretedLetter f p hp (P.act x s) = f x * P.interpretedLetter f p hp s := by
  induction s using DirectLimit.induction with
  | ih i y =>
    change f (x * y) * p i = f x * (f y * p i)
    rw [f.map_mul, mul_assoc]

include hbexit in
omit [IsConical M] in
@[simp] theorem interpretedLetter_exit (s : P.Letters) :
    P.interpretedLetter f p hp s * f b = f (P.exit e s) := by
  induction s using DirectLimit.induction with
  | ih i x =>
    change (f x * p i) * f b = f ((x * P.terminal i) * e)
    rw [mul_assoc, hbexit]
    simp only [mul_assoc, f.map_mul]

/-- Universal evaluation for exactly the indexed probe presentation from
the source: no gate, join, normal-form, or height law is imposed on the
target monoid. -/
noncomputable def presentedLift : P.Extension he b →* N :=
  Word.liftHom (P.alphabet he) b f (P.interpretedLetter f p hp)
    (P.interpretedLetter_act f p hp) (P.interpretedLetter_exit b f p hp hbexit)

@[simp] theorem presentedLift_old (x : M) :
    P.presentedLift he b f p hp hbexit (Word.old (P.alphabet he) b x) = f x := rfl

@[simp] theorem presentedLift_probe (hb : b ≠ 1) (i : ℕ) :
    P.presentedLift he b f p hp hbexit (P.probe he b hb i) = p i := by
  change (P.interpretedLetter f p hp (P.letter i 1)) * f 1 = p i
  simp only [interpretedLetter_mk, f.map_one, one_mul, mul_one]

/-- Old elements and the displayed indexed generators determine every
homomorphism out of the actual extension. -/
theorem presentedHom_ext (hb : b ≠ 1) (F G : P.Extension he b →* N)
    (hOld : ∀ x : M, F (Word.old (P.alphabet he) b x) = G (Word.old (P.alphabet he) b x))
    (hNew : ∀ i : ℕ, F (P.probe he b hb i) = G (P.probe he b hb i)) : F = G := by
  apply Word.hom_ext (P.alphabet he) b hb F G hOld
  intro s
  induction s using DirectLimit.induction with
  | ih i x =>
    have hg : Word.generator (P.alphabet he) b hb (P.letter i x) =
        Word.old (P.alphabet he) b x * P.probe he b hb i := by
      apply Subtype.ext
      change Raw.cons (P.letter i x) (.old 1) =
        Raw.cons (P.act x (P.letter i 1)) (.old 1)
      rw [act_letter, mul_one]
    change F (Word.generator (P.alphabet he) b hb (P.letter i x)) =
      G (Word.generator (P.alphabet he) b hb (P.letter i x))
    rw [hg, F.map_mul, G.map_mul, hOld, hNew]

include hp hbexit in
/-- The actual extension has the universal property of the source's
monoid presentation over `M`. -/
theorem existsUnique_presentedHom (hb : b ≠ 1) :
    ∃! F : P.Extension he b →* N,
      (∀ x : M, F (Word.old (P.alphabet he) b x) = f x) ∧
      (∀ i : ℕ, F (P.probe he b hb i) = p i) := by
  refine ⟨P.presentedLift he b f p hp hbexit,
    ⟨P.presentedLift_old he b f p hp hbexit, P.presentedLift_probe he b f p hp hbexit hb⟩, ?_⟩
  intro F hF
  apply P.presentedHom_ext he b hb
  · intro x
    exact (hF.1 x).trans (P.presentedLift_old he b f p hp hbexit x).symm
  · intro i
    exact (hF.2 i).trans (P.presentedLift_probe he b f p hp hbexit hb i).symm

end PartitionConsistency.ProbeAlgebra.Path

end OAI
