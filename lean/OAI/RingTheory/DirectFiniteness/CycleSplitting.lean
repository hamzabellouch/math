import OAI.RingTheory.DirectFiniteness.BalanceObstruction

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} [Fintype α]

lemma sameCycle_after_swap {p : Perm α} {a b x y : α} (hab : p.SameCycle a b)
    (hxy : (swap a b * p).SameCycle x y) : p.SameCycle x y := by
  apply setoid_sameCycle_of_step (SameCycle.setoid p) (swap a b * p) _ hxy
  intro z
  exact (SameCycle.apply_right SameCycle.rfl).trans
    (setoid_swap_related (SameCycle.setoid p) hab (p z))

lemma sign_eq_cycles (p : Perm α) :
    sign p = (-1 : ℤˣ) ^ (Fintype.card α - Nat.card (Cycles p)) := by
  classical
  obtain ⟨l, hl, hlen, hmem⟩ := exists_cycle_factorization p
  have hs := sign_prod_list_swap (l := l.map fun ab => swap ab.1 ab.2) (by
    intro g hg
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hg
    exact ⟨ab.1, ab.2, (hmem ab hab).1, rfl⟩)
  rw [hl, List.length_map] at hs
  have hn : Fintype.card α - Nat.card (Cycles p) = l.length := by omega
  rwa [hn]

lemma not_sameCycle_swap_of_sameCycle (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) : ¬ (swap a b * p).SameCycle a b := by
  classical
  intro hq
  let q := swap a b * p
  have hrev : swap a b * q = p := by simp [q, ← mul_assoc]
  have heq : SameCycle.setoid p = SameCycle.setoid q := by
    ext x y
    constructor
    · intro h
      apply sameCycle_after_swap hq
      rwa [hrev]
    · exact sameCycle_after_swap hab
  have hc : Nat.card (Cycles p) = Nat.card (Cycles q) := by rw [Cycles, heq]
  have hs : sign p = sign q := by rw [sign_eq_cycles, sign_eq_cycles, hc]
  have hsign : (-1 : ℤˣ) = 1 := by
    have := hs
    change sign p = sign (swap a b * p) at this
    rw [Perm.sign_mul, sign_swap hne] at this
    exact mul_right_cancel (b := sign p) (by simpa using this.symm)
  norm_num at hsign

lemma swap_mul_cycles_card_split (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) :
    Nat.card (Cycles (swap a b * p)) = Nat.card (Cycles p) + 1 := by
  have h := swap_mul_cycles_card (swap a b * p) a b
    (not_sameCycle_swap_of_sameCycle p a b hne hab)
  simpa [← mul_assoc] using h.symm

end KaplanskyCounterexample.Planar

end

end OAI
