import OAI.RingTheory.DirectFiniteness.RibbonWheels

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2} {A : Type u_3} [Fintype α]

/-- The listed distinct edges constitute a whole rotation cycle. -/
def Follows (p : Perm α) (l : List α) : Prop := ∀ x ∈ l, p x = l.formPerm x

omit [Fintype α] in
lemma Follows.invariant {p : Perm α} {l : List α} (h : Follows p l) (x : α) :
    p x ∈ l ↔ x ∈ l := by
  classical
  constructor
  · intro hx
    let y := l.formPerm⁻¹ (p x)
    have hy : y ∈ l := by
      apply l.mem_of_formPerm_apply_mem
      simpa [y] using hx
    have he : p y = p x := by rw [h y hy]; simp [y]
    simpa [p.injective he] using hy
  · intro hx
    rw [h x hx]
    exact l.formPerm_apply_mem_of_mem hx

lemma Follows.sameCycle {p : Perm α} {l : List α} (h : Follows p l)
    (hd : l.Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) : p.SameCycle x y := by
  apply sameCycle_map l.formPerm p id _ (hd.isCycleOn_formPerm.2 hx hy)
  intro z
  by_cases hz : z ∈ l
  · change p.SameCycle z (l.formPerm z)
    rw [← h z hz]
    exact SameCycle.apply_right SameCycle.rfl
  · simp only [id_eq, List.formPerm_apply_of_notMem hz]
    exact SameCycle.rfl

lemma Follows.cycleSet {p : Perm α} {l : List α} (h : Follows p l)
    (hd : l.Nodup) {x : α} (hx : x ∈ l) :
    cycleSet p (cycleClass p x) = l.toFinset := by
  classical
  ext y
  rw [mem_cycleSet, cycleClass_eq, List.mem_toFinset]
  constructor
  · intro hy
    exact (perm_invariant_cycle p (fun z => z ∈ l) h.invariant hy).mpr hx
  · exact fun hy => h.sameCycle hd hy hx

lemma sameCycle_iff_of_eqOn_cycle (p q : Perm α) (x : α)
    (heq : ∀ z, p.SameCycle x z → q z = p z) (y : α) :
    q.SameCycle x y ↔ p.SameCycle x y := by
  have hp : ∀ n : ℕ, (q ^ n) x = (p ^ n) x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih]
      exact heq _ SameCycle.rfl.pow_right
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [hp] at hn
    exact ⟨n, by simpa only [zpow_natCast] using hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by simpa only [zpow_natCast, hp n] using hn⟩

lemma cycleSet_eq_of_eqOn_cycle (p q : Perm α) (x : α)
    (heq : ∀ z, p.SameCycle x z → q z = p z) :
    cycleSet q (cycleClass q x) = cycleSet p (cycleClass p x) := by
  ext y
  simp only [mem_cycleSet, cycleClass_eq, sameCycle_comm (x := y)]
  exact sameCycle_iff_of_eqOn_cycle p q x heq y

omit [Fintype α] in
lemma formPerm_map_apply [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (l : List α) (x : α) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      change swap (f a) (f b) (((b :: l).map f).formPerm (f x)) =
        f (swap a b ((b :: l).formPerm x))
      rw [ih]
      exact (hf.map_swap a b _).symm

omit [Fintype α] in
lemma Follows.map_sum_left {p : Perm α} {q : Perm β} {l : List α}
    (h : Follows p l) : Follows (Equiv.sumCongr p q) (l.map Sum.inl) := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simpa only [Equiv.sumCongr_apply, Sum.map_inl,
    formPerm_map_apply Sum.inl Sum.inl_injective] using congrArg Sum.inl (h x hx)

end KaplanskyCounterexample.Planar

end

end OAI
