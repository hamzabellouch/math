import OAI.RingTheory.DirectFiniteness.DetachmentGenus

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

structure Balanced (R : Ribbon α) (Inc : V → F → Prop)
    (ι : V → F → (A →+ B)) where
  blackLabel : α → V
  whiteLabel : α → F
  blackLabel_rot : ∀ a, blackLabel (R.black a) = blackLabel a
  whiteLabel_rot : ∀ a, whiteLabel (R.white a) = whiteLabel a
  incident : ∀ a, Inc (blackLabel a) (whiteLabel a)
  weight : α → A
  weight_ne : ∀ a, weight a ≠ 0
  exception : Cycles R.white
  black_sum : ∀ c : Cycles R.black,
    ∑ a ∈ cycleSet R.black c, ι (blackLabel a) (whiteLabel a) (weight a) = 0
  white_sum : ∀ c : Cycles R.white, c ≠ exception →
    ∑ a ∈ cycleSet R.white c, weight a = 0
  exceptional_sum : (∑ a ∈ cycleSet R.white exception, weight a) ≠ 0

def Balanced.Reduced {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}
    (D : Balanced R Inc ι) : Prop :=
  (∀ a, R.black a ≠ a → D.whiteLabel (R.black a) ≠ D.whiteLabel a) ∧
  (∀ a, R.white a ≠ a → D.blackLabel (R.white a) ≠ D.blackLabel a)

omit [Fintype α] in
lemma cycleClass_perm (p : Perm α) (a : α) : cycleClass p (p a) = cycleClass p a := by
  apply (cycleClass_eq p _ _).mpr
  exact (SameCycle.refl p a).apply_left

lemma mem_cycleSet_perm (p : Perm α) (c : Cycles p) {a : α}
    (ha : a ∈ cycleSet p c) : p a ∈ cycleSet p c := by
  rw [mem_cycleSet, cycleClass_perm]
  exact (mem_cycleSet p c a).mp ha

lemma cycleSet_pair_perm {p : Perm α} {c : Cycles p} {a b : α}
    (hab : a ≠ b) (hc : cycleSet p c = {a, b}) : p a = b := by
  have ha : a ∈ cycleSet p c := by simp [hc]
  have hb : b ∈ cycleSet p c := by simp [hc]
  have hcycle : p.SameCycle a b := by
    apply (cycleClass_eq p a b).mp
    exact ((mem_cycleSet p c a).mp ha).trans ((mem_cycleSet p c b).mp hb).symm
  have hnofix : p a ≠ a := fun h => hab (hcycle.eq_of_left h)
  have hh := mem_cycleSet_perm p c ha
  simpa [hc, hnofix] using hh

lemma Balanced.white_degree {R : Ribbon α} {Inc : V → F → Prop}
    {ι : V → F → (A →+ B)} (D : Balanced R Inc ι) (c : Cycles R.white) :
    2 ≤ (cycleSet R.white c).card + if c = D.exception then 1 else 0 := by
  classical
  have hpos := (cycleSet_nonempty R.white c).card_pos
  by_cases he : c = D.exception
  · rw [ite_eq_left he]
    omega
  · rw [ite_eq_right he, add_zero]
    by_contra! h
    have hc : (cycleSet R.white c).card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have hz := D.white_sum c he
    rw [ha] at hz
    simp only [Finset.sum_singleton] at hz
    exact D.weight_ne a hz

lemma Balanced.black_degree {R : Ribbon α} {Inc : V → F → Prop}
    {ι : V → F → (A →+ B)} (D : Balanced R Inc ι) (hred : D.Reduced)
    (hinj : ∀ v f, Inc v f → Function.Injective (ι v f))
    (hind : ∀ v f g, Inc v f → Inc v g → f ≠ g → ∀ x y,
      ι v f x + ι v g y = 0 → x = 0) (c : Cycles R.black) :
    3 ≤ (cycleSet R.black c).card := by
  classical
  have hpos := (cycleSet_nonempty R.black c).card_pos
  by_contra! h
  have hsmall : (cycleSet R.black c).card = 1 ∨ (cycleSet R.black c).card = 2 := by omega
  rcases hsmall with h1 | h2
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    have hz := D.black_sum c
    rw [ha] at hz
    simp only [Finset.sum_singleton] at hz
    exact D.weight_ne a (hinj _ _ (D.incident a) (hz.trans (map_zero _).symm))
  · obtain ⟨a, b, hab, hc⟩ := Finset.card_eq_two.mp h2
    have hp := cycleSet_pair_perm hab hc
    have hbl : D.blackLabel b = D.blackLabel a := by
      simpa only [hp] using D.blackLabel_rot a
    have hwl : D.whiteLabel a ≠ D.whiteLabel b := by
      have hn : R.black a ≠ a := by simpa [hp] using hab.symm
      have hh : D.whiteLabel b ≠ D.whiteLabel a := by simpa only [hp] using hred.1 a hn
      exact hh.symm
    have hiz : Inc (D.blackLabel a) (D.whiteLabel b) := by
      rw [← hbl]
      exact D.incident b
    have hz := D.black_sum c
    rw [hc] at hz
    simp only [Finset.sum_pair hab] at hz
    rw [hbl] at hz
    exact D.weight_ne a (hind _ _ _ (D.incident a) hiz hwl _ _ hz)

lemma cycleSet_singleton_of_fixed (p : Perm α) (a : α) (h : p a = a) :
    cycleSet p (cycleClass p a) = {a} := by
  classical
  ext b
  rw [mem_cycleSet, cycleClass_eq, Finset.mem_singleton]
  exact ⟨fun hb => hb.eq_of_right h, fun hb => hb ▸ SameCycle.refl p a⟩

lemma cycleSet_card_pow (p : Perm α) (a : α) :
    (p ^ (cycleSet p (cycleClass p a)).card) a = a := by
  classical
  by_cases h : p a = a
  · rw [cycleSet_singleton_of_fixed p a h, Finset.card_singleton, pow_one, h]
  · have heq : cycleSet p (cycleClass p a) = (p.cycleOf a).support := by
      ext b
      rw [mem_cycleSet, cycleClass_eq, mem_support_cycleOf_iff' h, sameCycle_comm]
    rw [heq, ← p.pow_mod_card_support_cycleOf_self_apply]
    simp

/-- The bipartite incidence graph; its extended girth is infinite for a forest. -/
def incidenceGraph (Inc : V → F → Prop) : SimpleGraph (Sum V F) where
  Adj x y := match x, y with
    | .inl v, .inr f => Inc v f
    | .inr f, .inl v => Inc v f
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

lemma Balanced.black_not_fixed (_D : Balanced R Inc ι)
    (hdeg : ∀ c, 3 ≤ (cycleSet R.black c).card) (a : α) : R.black a ≠ a := by
  intro ha
  have h := hdeg (cycleClass R.black a)
  rw [cycleSet_singleton_of_fixed R.black a ha, Finset.card_singleton] at h
  omega

lemma Balanced.white_fixed_exception (D : Balanced R Inc ι) (a : α)
    (ha : R.white a = a) : cycleClass R.white a = D.exception := by
  classical
  by_contra he
  have h := D.white_sum _ he
  rw [cycleSet_singleton_of_fixed R.white a ha, Finset.sum_singleton] at h
  exact D.weight_ne a h

noncomputable def Balanced.exceptionEdge (D : Balanced R Inc ι) : α :=
  (cycleSet_nonempty R.white D.exception).choose

lemma Balanced.exceptionEdge_mem (D : Balanced R Inc ι) :
    D.exceptionEdge ∈ cycleSet R.white D.exception :=
  (cycleSet_nonempty R.white D.exception).choose_spec

def Balanced.exceptionFace (D : Balanced R Inc ι) : Cycles R.face :=
  cycleClass R.face D.exceptionEdge

lemma Balanced.white_not_fixed_on_other_face (D : Balanced R Inc ι) {a : α}
    (ha : cycleClass R.face a ≠ D.exceptionFace) : R.white (R.black a) ≠ R.black a := by
  intro hf
  have hc := D.white_fixed_exception (R.black a) hf
  have he : D.exceptionEdge = R.black a := by
    have hm := D.exceptionEdge_mem
    rw [← hc, cycleSet_singleton_of_fixed R.white (R.black a) hf,
      Finset.mem_singleton] at hm
    exact hm
  apply ha
  unfold Balanced.exceptionFace
  rw [he, ← hf]
  exact (cycleClass_perm R.face a).symm

/-- Traversing one black turn and then the following white turn of a face. -/
def Balanced.halfStep (D : Balanced R Inc ι) (a : α) :
    (incidenceGraph Inc).Walk (.inr (D.whiteLabel a)) (.inr (D.whiteLabel (R.face a))) :=
  .cons (v := .inl (D.blackLabel a)) (by exact D.incident a) (.cons (by
    change Inc (D.blackLabel a) (D.whiteLabel (R.white (R.black a)))
    rw [D.whiteLabel_rot, ← D.blackLabel_rot a]
    exact D.incident (R.black a)) .nil)

lemma Balanced.halfStep_length (D : Balanced R Inc ι) (a : α) :
    (D.halfStep a).length = 2 := rfl

/-- An initial segment of the facial boundary, with two edge sides per step. -/
def Balanced.boundary (D : Balanced R Inc ι) (a : α) : (n : ℕ) →
    (incidenceGraph Inc).Walk (.inr (D.whiteLabel a))
      (.inr (D.whiteLabel ((R.face ^ n) a)))
  | 0 => .nil
  | n + 1 => (D.halfStep a).append ((D.boundary (R.face a) n).copy rfl (by
      simp only [pow_succ, Perm.mul_apply]))

lemma Balanced.boundary_length (D : Balanced R Inc ι) (a : α) (n : ℕ) :
    (D.boundary a n).length = 2 * n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [Balanced.boundary, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_copy, Balanced.halfStep_length, ih]
    omega

lemma Balanced.boundary_getVert_even (D : Balanced R Inc ι) (n k : ℕ) (hk : k ≤ n)
    (a : α) : (D.boundary a n).getVert (2 * k) =
      .inr (D.whiteLabel ((R.face ^ k) a)) := by
  induction n generalizing a k with
  | zero => have : k = 0 := Nat.le_zero.mp hk
            subst k
            rfl
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [Balanced.boundary, SimpleGraph.Walk.getVert_append]
      rw [ite_eq_right (by simp only [Balanced.halfStep_length]; omega),
        SimpleGraph.Walk.getVert_copy, Balanced.halfStep_length]
      have heq : 2 * (k + 1) - 2 = 2 * k := by omega
      rw [heq, ih k (by omega)]
      simp only [pow_succ, Perm.mul_apply]

lemma Balanced.boundary_getVert_odd (D : Balanced R Inc ι) (n k : ℕ) (hk : k < n)
    (a : α) : (D.boundary a n).getVert (2 * k + 1) =
      .inl (D.blackLabel ((R.face ^ k) a)) := by
  induction n generalizing a k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [Balanced.boundary, SimpleGraph.Walk.getVert_append]
      rw [ite_eq_right (by simp only [Balanced.halfStep_length]; omega),
        SimpleGraph.Walk.getVert_copy, Balanced.halfStep_length]
      have heq : 2 * (k + 1) + 1 - 2 = 2 * k + 1 := by omega
      rw [heq, ih k (by omega)]
      simp only [pow_succ, Perm.mul_apply]

omit [Fintype α] in
lemma cycleClass_pow (p : Perm α) (a : α) (n : ℕ) :
    cycleClass p ((p ^ n) a) = cycleClass p a :=
  (cycleClass_eq _ _ _).mpr ((SameCycle.refl p a).pow_left)

lemma Balanced.boundary_reduced (D : Balanced R Inc ι) (hred : D.Reduced)
    (hdeg : ∀ c, 3 ≤ (cycleSet R.black c).card) {a : α}
    (ha : cycleClass R.face a ≠ D.exceptionFace) (n : ℕ) :
    _root_.OAI.SimpleGraph.Walk.Reduced (D.boundary a n) := by
  apply SimpleGraph.Walk.reduced_of_getVert
  intro i hi
  rw [D.boundary_length] at hi
  have he : i = 2 * (i / 2) ∨ i = 2 * (i / 2) + 1 := by omega
  rcases he with he | he
  · rw [he, D.boundary_getVert_even n (i / 2) (by omega)]
    have hk : 2 * (i / 2) + 2 = 2 * (i / 2 + 1) := by omega
    rw [hk, D.boundary_getVert_even n (i / 2 + 1) (by omega)]
    intro h
    have hh := Sum.inr.inj h
    rw [pow_succ', Perm.mul_apply] at hh
    change D.whiteLabel ((R.face ^ (i / 2)) a) =
      D.whiteLabel (R.white (R.black ((R.face ^ (i / 2)) a))) at hh
    rw [D.whiteLabel_rot] at hh
    exact hred.1 _ (D.black_not_fixed hdeg _) hh.symm
  · rw [he, D.boundary_getVert_odd n (i / 2) (by omega)]
    have hk : 2 * (i / 2) + 1 + 2 = 2 * (i / 2 + 1) + 1 := by omega
    rw [hk, D.boundary_getVert_odd n (i / 2 + 1) (by omega)]
    intro h
    have hh := Sum.inl.inj h
    rw [pow_succ', Perm.mul_apply] at hh
    change D.blackLabel ((R.face ^ (i / 2)) a) =
      D.blackLabel (R.white (R.black ((R.face ^ (i / 2)) a))) at hh
    have hn : R.white (R.black ((R.face ^ (i / 2)) a)) ≠
        R.black ((R.face ^ (i / 2)) a) :=
      D.white_not_fixed_on_other_face (by rwa [cycleClass_pow])
    exact hred.2 _ hn (hh.symm.trans (D.blackLabel_rot _).symm)

lemma Balanced.face_degree (D : Balanced R Inc ι) (hred : D.Reduced)
    (hdeg : ∀ c, 3 ≤ (cycleSet R.black c).card)
    (hgirth : 12 ≤ (incidenceGraph Inc).egirth) (c : Cycles R.face) :
    6 ≤ (cycleSet R.face c).card + if c = D.exceptionFace then 6 else 0 := by
  classical
  by_cases hc : c = D.exceptionFace
  · rw [ite_eq_left hc]; omega
  rw [ite_eq_right hc, add_zero]
  obtain ⟨a, ha⟩ := cycleSet_nonempty R.face c
  have hac : cycleClass R.face a = c := (mem_cycleSet _ _ _).mp ha
  let n := (cycleSet R.face c).card
  have hpa : (R.face ^ n) a = a := by
    change (R.face ^ (cycleSet R.face c).card) a = a
    rw [← hac]
    exact cycleSet_card_pow R.face a
  let p : (incidenceGraph Inc).Walk (.inr (D.whiteLabel a)) (.inr (D.whiteLabel a)) :=
    (D.boundary a n).copy rfl (by rw [hpa])
  have hp : _root_.OAI.SimpleGraph.Walk.Reduced p := by
    exact (D.boundary_reduced hred hdeg (by rwa [hac]) n).copy _ _
  have hlen : p.length = 2 * n := by simp only [p, SimpleGraph.Walk.length_copy,
    D.boundary_length]
  have hne : ¬ p.Nil := by
    intro h
    have := SimpleGraph.Walk.Nil.length_eq_zero h
    have hn : 0 < n := (cycleSet_nonempty R.face c).card_pos
    omega
  have hg := hgirth.trans (hp.egirth_le hne)
  rw [hlen] at hg
  have hnat : 12 ≤ 2 * n := by exact_mod_cast hg
  change 6 ≤ n
  omega

/-- The curvature obstruction in the local-subgroup embedding proof, with every
facial girth bound derived rather than assumed. -/
theorem Balanced.not_spherical (D : Balanced R Inc ι) (hred : D.Reduced)
    (hinj : ∀ v f, Inc v f → Function.Injective (ι v f))
    (hind : ∀ v f g, Inc v f → Inc v g → f ≠ g → ∀ x y,
      ι v f x + ι v g y = 0 → x = 0)
    (hgirth : 12 ≤ (incidenceGraph Inc).egirth) : ¬ R.Spherical := by
  intro hR
  have hb := D.black_degree hred hinj hind
  exact euler_contradiction R hR D.exception D.exceptionFace hb D.white_degree
    (D.face_degree hred hb hgirth)

end KaplanskyCounterexample.Planar

end

end OAI
