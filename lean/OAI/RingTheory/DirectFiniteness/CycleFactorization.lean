import OAI.RingTheory.DirectFiniteness.RibbonGeometry

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type u_1} [Fintype α]

lemma sameCycle_map_quotient {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) :
    Nat.card (Cycles q) ≤ Nat.card (Cycles p) := by
  exact Nat.card_le_card_of_surjective (Quotient.map id (fun _ _ hxy => h hxy))
    (Quotient.map_surjective _ Function.surjective_id)

lemma swap_cycles_card_le (p : Perm α) (a b : α) :
    Nat.card (Cycles (swap a b * p)) ≤ Nat.card (Cycles p) + 1 := by
  let q := swap a b * p
  have hrev : swap a b * q = p := by simp [q, ← mul_assoc]
  by_cases hab : q.SameCycle a b
  · have href : ∀ {x y}, p.SameCycle x y → q.SameCycle x y := by
      intro x y h
      apply sameCycle_map p q id _ h
      intro x
      have hx : q.SameCycle x (q x) := SameCycle.rfl.apply_right
      have hp : p x = swap a b (q x) := by
        rw [← Perm.mul_apply, hrev]
      rw [hp]
      by_cases hxa : q x = a
      · rw [hxa] at hx
        simpa [hxa] using hx.trans hab
      · by_cases hxb : q x = b
        · rw [hxb] at hx
          simpa [hxb] using hx.trans hab.symm
        · rwa [swap_apply_of_ne_of_ne hxa hxb]
    exact (sameCycle_map_quotient href).trans (Nat.le_succ _)
  · have h := swap_mul_cycles_card q a b hab
    rw [hrev] at h
    change Nat.card (Cycles q) ≤ _
    omega

lemma cycles_card_le (p : Perm α) : Nat.card (Cycles p) ≤ Fintype.card α := by
  simpa using Nat.card_le_card_of_surjective (cycleClass p) Quotient.mk_surjective

lemma cycles_one_card : Nat.card (Cycles (1 : Perm α)) = Fintype.card α := by
  have heq : SameCycle.setoid (1 : Perm α) = ⊥ := by
    ext x y
    exact sameCycle_one
  rw [Cycles, heq]
  exact (Nat.card_congr Setoid.quotientBotEquiv).trans (Nat.card_eq_fintype_card)

/-- A minimal transposition factorization, with each transposition contained in
one of the original cycles. -/
lemma exists_cycle_factorization (p : Perm α) :
    ∃ l : List (α × α),
      (l.map fun ab => swap ab.1 ab.2).prod = p ∧
      l.length + Nat.card (Cycles p) = Fintype.card α ∧
      ∀ ab ∈ l, ab.1 ≠ ab.2 ∧ p.SameCycle ab.1 ab.2 := by
  have hmain : ∀ n : ℕ, ∀ p : Perm α,
      Fintype.card α - Nat.card (Cycles p) = n →
      ∃ l : List (α × α),
        (l.map fun ab => swap ab.1 ab.2).prod = p ∧
        l.length + Nat.card (Cycles p) = Fintype.card α ∧
        ∀ ab ∈ l, ab.1 ≠ ab.2 ∧ p.SameCycle ab.1 ab.2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hp : p = 1
      · subst p
        exact ⟨[], rfl, (Nat.zero_add _).trans (cycles_one_card (α := α)),
          fun _ membership => False.elim (List.not_mem_nil membership)⟩
      · have hex : ∃ a, p a ≠ a :=
          not_forall.mp (fun fixed => hp (Equiv.ext fixed))
        obtain ⟨a, ha⟩ := hex
        have hc := unplug_cycles_card p a ha
        have hle := cycles_card_le (unplug p a)
        have hlt : Fintype.card α - Nat.card (Cycles (unplug p a)) < n := by omega
        obtain ⟨l, hl, hlen, hmem⟩ := ih _ hlt (unplug p a) rfl
        refine ⟨(a, p a) :: l, ?_, ?_, ?_⟩
        · simp only [List.map_cons, List.prod_cons, hl]
          exact swap_mul_self_mul a (p a) p
        · simp only [List.length_cons]
          omega
        · intro ab hab
          rcases List.mem_cons.mp hab with rfl | hab
          · exact ⟨Ne.symm ha, SameCycle.rfl.apply_right⟩
          · exact ⟨(hmem ab hab).1, unplug_sameCycle p a (hmem ab hab).2⟩
  exact hmain _ p rfl

end KaplanskyCounterexample.Planar

end

end OAI
