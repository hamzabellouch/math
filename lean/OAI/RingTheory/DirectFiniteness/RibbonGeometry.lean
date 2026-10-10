import OAI.RingTheory.DirectFiniteness.ReducedWalks

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
attribute [local simp] SameCycle.rfl

variable {α : Type u_1} [Fintype α]

/-- Vertex cycles of a rotation, including the cycles of length one. -/
abbrev Cycles (p : Perm α) := Quotient (SameCycle.setoid p)

def cycleClass (p : Perm α) (x : α) : Cycles p := Quotient.mk _ x

def cycleSet (p : Perm α) (c : Cycles p) : Finset α :=
  Finset.univ.filter fun x => cycleClass p x = c

lemma mem_cycleSet (p : Perm α) (c : Cycles p) (x : α) :
    x ∈ cycleSet p c ↔ cycleClass p x = c := by simp [cycleSet]

omit [Fintype α] in
lemma cycleClass_eq (p : Perm α) (x y : α) :
    cycleClass p x = cycleClass p y ↔ p.SameCycle x y := Quotient.eq

lemma cycleSet_nonempty (p : Perm α) (c : Cycles p) : (cycleSet p c).Nonempty := by
  induction c using Quotient.inductionOn with
  | h x => exact ⟨x, (mem_cycleSet p _ x).mpr rfl⟩

lemma cycles_sum_card (p : Perm α) :
    ∑ c : Cycles p, (cycleSet p c).card = Fintype.card α := by
  classical
  simpa [cycleSet] using Finset.sum_card_fiberwise_eq_card_filter
    (s := Finset.univ) (t := Finset.univ) (g := cycleClass p)

/-- A bipartite rotation system. Each edge is oriented from black to white;
rotations at its two endpoints are permutations of the whole edge set. -/
structure Ribbon (α : Type u_2) where
  black : Perm α
  white : Perm α

def Ribbon.face (R : Ribbon α) : Perm α := R.white * R.black

def Ribbon.Spherical (R : Ribbon α) : Prop :=
  Nat.card (Cycles R.black) + Nat.card (Cycles R.white) +
    Nat.card (Cycles R.face) = Fintype.card α + 2

/-- Local surgery merging two white vertices along consecutive black edges.
The newly created digon is a one-cycle of the face permutation. -/
def Ribbon.mergeWhite (R : Ribbon α) (e : α) : Ribbon α where
  black := R.black
  white := swap e (R.face e) * R.white

omit [Fintype α] in
lemma mergeWhite_face (R : Ribbon α) (e : α) :
    (R.mergeWhite e).face = swap e (R.face e) * R.face := by
  simp [Ribbon.mergeWhite, Ribbon.face, mul_assoc]

omit [Fintype α] in
lemma mergeWhite_face_fixed (R : Ribbon α) (e : α) : (R.mergeWhite e).face e = e := by
  rw [mergeWhite_face]
  simp

/-- A map taking steps of one permutation to cycles of another takes whole
cycles to cycles. -/
lemma sameCycle_map {β : Type u_3} (p : Perm α) (q : Perm β) (f : α → β)
    (hstep : ∀ x, q.SameCycle (f x) (f (p x))) {x y : α}
    (hxy : p.SameCycle x y) : q.SameCycle (f x) (f y) := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (hstep _)

/-- Unplug an edge from its face cycle; the edge becomes a singleton cycle. -/
def unplug (p : Perm α) (a : α) : Perm α := swap a (p a) * p

def bypass (p : Perm α) (a x : α) : α := if x = a then p a else x

omit [Fintype α] in
lemma unplug_fixed (p : Perm α) (a : α) : unplug p a a = a := by
  simp [unplug]

lemma unplug_sameCycle (p : Perm α) (a : α) {x y : α}
    (h : (unplug p a).SameCycle x y) : p.SameCycle x y := by
  apply sameCycle_map (unplug p a) p id _ h
  intro x
  change p.SameCycle x (swap a (p a) (p x))
  by_cases hx : x = a
  · subst x
    simp
  · by_cases hxa : p x = a
    · simp only [hxa, swap_apply_left]
      exact (show p.SameCycle x a by rw [← hxa]; simp).trans (by simp)
    · have hxp : p x ≠ p a := p.injective.ne hx
      rw [swap_apply_of_ne_of_ne hxa hxp]
      simp

lemma sameCycle_bypass (p : Perm α) (a : α) (ha : p a ≠ a) {x y : α}
    (h : p.SameCycle x y) :
    (unplug p a).SameCycle (bypass p a x) (bypass p a y) := by
  apply sameCycle_map p (unplug p a) (bypass p a) _ h
  intro x
  by_cases hx : x = a
  · subst x
    simp [bypass, ha]
  · by_cases hxa : p x = a
    · have hq : unplug p a x = p a := by simp [unplug, hxa]
      simp only [bypass, hx, hxa, ite_false, ite_true]
      rw [← hq]
      simp
    · have hxp : p x ≠ p a := p.injective.ne hx
      have hq : unplug p a x = p x := by
        simp only [unplug, Perm.mul_apply]
        exact swap_apply_of_ne_of_ne hxa hxp
      simp only [bypass, hx, hxa, ite_false]
      rw [← hq]
      simp

lemma unplug_sameCycle_iff (p : Perm α) (a : α) (ha : p a ≠ a)
    {x y : α} (hx : x ≠ a) (hy : y ≠ a) :
    (unplug p a).SameCycle x y ↔ p.SameCycle x y := by
  refine ⟨unplug_sameCycle p a, fun h => ?_⟩
  simpa [bypass, hx, hy] using sameCycle_bypass p a ha h

omit [Fintype α] in
lemma bypass_ne (p : Perm α) (a : α) (ha : p a ≠ a) (x : α) :
    bypass p a x ≠ a := by
  by_cases hx : x = a <;> simp [bypass, hx, ha]

/-- Splicing a nontrivial cycle at a point adds exactly one singleton cycle. -/
def unplugCycleEquiv (p : Perm α) (a : α) (ha : p a ≠ a) :
    Cycles p ≃ {c : Cycles (unplug p a) // c ≠ cycleClass (unplug p a) a} where
  toFun := Quotient.lift (fun x =>
    ⟨cycleClass (unplug p a) (bypass p a x), by
      intro h
      have he := (cycleClass_eq _ _ _).mp h
      exact bypass_ne p a ha x (he.eq_of_right (unplug_fixed p a))⟩)
    (fun x y h => Subtype.ext ((cycleClass_eq _ _ _).mpr (sameCycle_bypass p a ha h)))
  invFun c := Quotient.map' id (fun _ _ h => unplug_sameCycle p a h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change cycleClass p (bypass p a x) = cycleClass p x
      apply (cycleClass_eq _ _ _).mpr
      by_cases hx : x = a <;> simp [bypass, hx]
  right_inv c := by
    rcases c with ⟨c, hc⟩
    apply Subtype.ext
    induction c using Quotient.inductionOn with
    | h x =>
      have hx : x ≠ a := by
        intro h
        apply hc
        exact congrArg (cycleClass _) h
      change cycleClass (unplug p a) (bypass p a x) = cycleClass (unplug p a) x
      simp [bypass, hx]

lemma unplug_cycles_card (p : Perm α) (a : α) (ha : p a ≠ a) :
    Nat.card (Cycles (unplug p a)) = Nat.card (Cycles p) + 1 := by
  have h := Fintype.card_congr (unplugCycleEquiv p a ha)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Cycles (unplug p a)) :=
    Fintype.card_pos_iff.mpr ⟨cycleClass (unplug p a) a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

/-- A transposition between two different cycles joins them. The orbit link is
proved directly by following the first return in one of the old cycles. -/
lemma swap_mul_sameCycle (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    (swap a b * p).SameCycle a b := by
  have hret : ∃ n : ℕ, 0 < n ∧ (p ^ n) b = b := by
    exact ⟨orderOf p, orderOf_pos p, by simp⟩
  let n := Nat.find hret
  have hn : 0 < n ∧ (p ^ n) b = b := Nat.find_spec hret
  have hmin : ∀ k, 0 < k → k < n → (p ^ k) b ≠ b := by
    intro k hk hkn heq
    exact Nat.find_min hret hkn ⟨hk, heq⟩
  have hneq : ∀ k : ℕ, (p ^ k) b ≠ a := by
    intro k heq
    apply hab
    exact (show p.SameCycle b a from ⟨k, by simpa using heq⟩).symm
  have hiter : ∀ k, k < n → ((swap a b * p) ^ k) b = (p ^ k) b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [pow_succ', Perm.mul_apply, ih (by omega), Perm.mul_apply]
      have heq : p ((p ^ k) b) = (p ^ (k + 1)) b := by
        rw [pow_succ', Perm.mul_apply]
      rw [heq, swap_apply_of_ne_of_ne (hneq _) (hmin _ (by omega) hk)]
  have hn' : n - 1 + 1 = n := by omega
  have hstep : ((swap a b * p) ^ n) b = a := by
    rw [← hn', pow_succ', Perm.mul_apply, hiter _ (by omega), Perm.mul_apply]
    have heq : p ((p ^ (n - 1)) b) = b := by
      calc
        p ((p ^ (n - 1)) b) = (p ^ (n - 1 + 1)) b := by rw [pow_succ', Perm.mul_apply]
        _ = b := by rw [hn']; exact hn.2
    rw [heq, swap_apply_right]
  exact (show (swap a b * p).SameCycle b a from ⟨n, by simpa using hstep⟩).symm

/-- Old cycles remain connected after a transposition joining distinct cycles. -/
lemma sameCycle_swap_mul (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b)
    {x y : α} (hxy : p.SameCycle x y) : (swap a b * p).SameCycle x y := by
  have hlink := swap_mul_sameCycle p a b hab
  apply sameCycle_map p (swap a b * p) id _ hxy
  intro x
  have hx : (swap a b * p).SameCycle x (swap a b (p x)) := by
    change (swap a b * p).SameCycle x ((swap a b * p) x)
    exact SameCycle.apply_right SameCycle.rfl
  by_cases hxa : p x = a
  · rw [hxa, swap_apply_left] at hx
    exact hx.trans (hxa ▸ hlink.symm)
  · by_cases hxb : p x = b
    · rw [hxb, swap_apply_right] at hx
      exact hx.trans (hxb ▸ hlink)
    · rwa [swap_apply_of_ne_of_ne hxa hxb] at hx

/-- The quotient of the old vertex set that identifies precisely the two
vertices joined by the transposition. -/
def mergedClass (p : Perm α) (a b : α) (x : α) : Cycles p :=
  if cycleClass p x = cycleClass p b then cycleClass p a else cycleClass p x

omit [Fintype α] in
lemma cycleClass_apply (p : Perm α) (x : α) : cycleClass p (p x) = cycleClass p x := by
  apply (cycleClass_eq _ _ _).mpr
  exact SameCycle.apply_left SameCycle.rfl

omit [Fintype α] in
lemma mergedClass_step (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) (x : α) :
    mergedClass p a b ((swap a b * p) x) = mergedClass p a b x := by
  have hne : cycleClass p a ≠ cycleClass p b := mt (cycleClass_eq p a b).mp hab
  change mergedClass p a b (swap a b (p x)) = _
  by_cases hxa : p x = a
  · have hx : cycleClass p x = cycleClass p a := by
      rw [← cycleClass_apply, hxa]
    simp [mergedClass, hxa, hx, hne]
  · by_cases hxb : p x = b
    · have hx : cycleClass p x = cycleClass p b := by
        rw [← cycleClass_apply, hxb]
      simp [mergedClass, hxb, hx, hne]
    · simp [swap_apply_of_ne_of_ne hxa hxb, mergedClass, cycleClass_apply]

lemma mergedClass_cycle (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b)
    {x y : α} (hxy : (swap a b * p).SameCycle x y) :
    mergedClass p a b x = mergedClass p a b y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, mergedClass_step p a b hab]
    exact ih

/-- Joining two different cycles deletes exactly one vertex. -/
def mergeCycleEquiv (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    Cycles (swap a b * p) ≃ {c : Cycles p // c ≠ cycleClass p b} where
  toFun := Quotient.lift (fun x => ⟨mergedClass p a b x, by
    have hne : cycleClass p a ≠ cycleClass p b := mt (cycleClass_eq p a b).mp hab
    simp only [mergedClass]
    split_ifs with h <;> assumption⟩)
    (fun _ _ h => Subtype.ext (mergedClass_cycle p a b hab h))
  invFun c := Quotient.map' id (fun _ _ h => sameCycle_swap_mul p a b hab h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change Quotient.map' id _ (mergedClass p a b x) = cycleClass (swap a b * p) x
      unfold mergedClass
      split_ifs with hx
      · apply (cycleClass_eq _ _ _).mpr
        exact (swap_mul_sameCycle p a b hab).trans
          (sameCycle_swap_mul p a b hab ((cycleClass_eq _ _ _).mp hx).symm)
      · rfl
  right_inv c := by
    apply Subtype.ext
    rcases c with ⟨c, hc⟩
    induction c using Quotient.inductionOn with
    | h x =>
      change mergedClass p a b x = cycleClass p x
      change cycleClass p x ≠ cycleClass p b at hc
      simp [mergedClass, hc]

lemma swap_mul_cycles_card (p : Perm α) (a b : α) (hab : ¬ p.SameCycle a b) :
    Nat.card (Cycles (swap a b * p)) + 1 = Nat.card (Cycles p) := by
  have h := Fintype.card_congr (mergeCycleEquiv p a b hab)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Cycles p) := Fintype.card_pos_iff.mpr ⟨cycleClass p a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

lemma mergeWhite_spherical (R : Ribbon α) (hR : R.Spherical) (e : α)
    (he : ¬ R.white.SameCycle e (R.black e)) : (R.mergeWhite e).Spherical := by
  have hn : ¬ R.white.SameCycle e (R.face e) := by
    simpa [Ribbon.face] using he
  have hne : R.face e ≠ e := by
    intro h
    apply hn
    rw [h]
  have hw := swap_mul_cycles_card R.white e (R.face e) hn
  have hf := unplug_cycles_card R.face e hne
  unfold Ribbon.Spherical at *
  change Nat.card (Cycles R.black) +
    Nat.card (Cycles (swap e (R.face e) * R.white)) + _ = _
  rw [mergeWhite_face]
  change Nat.card (Cycles R.black) +
    Nat.card (Cycles (swap e (R.face e) * R.white)) +
    Nat.card (Cycles (unplug R.face e)) = Fintype.card α + 2
  omega

theorem euler_contradiction (R : Ribbon α) (hR : R.Spherical)
    (w : Cycles R.white) (f : Cycles R.face)
    (hb : ∀ c : Cycles R.black, 3 ≤ (cycleSet R.black c).card)
    (hw : ∀ c : Cycles R.white, 2 ≤ (cycleSet R.white c).card + if c = w then 1 else 0)
    (hf : ∀ c : Cycles R.face, 6 ≤ (cycleSet R.face c).card + if c = f then 6 else 0) :
    False := by
  have hb' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.black))) => hb c)
  have hw' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.white))) => hw c)
  have hf' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.face))) => hf c)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, cycles_sum_card] at hb'
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_add_distrib,
    cycles_sum_card, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hw' hf'
  unfold Ribbon.Spherical at hR
  simp only [Nat.card_eq_fintype_card] at hR
  omega

end KaplanskyCounterexample.Planar

end

end OAI
