import OAI.RingTheory.DirectFiniteness.CycleFactorization

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1}

/-- Identify two classes of a partition, by redirecting the second to the first. -/
def mergeClass (s : Setoid α) (a b x : α) : Quotient s :=
  if Quotient.mk s x = Quotient.mk s b then Quotient.mk s a else Quotient.mk s x

def joinPair (s : Setoid α) (a b : α) : Setoid α := Setoid.ker (mergeClass s a b)

lemma le_joinPair (s : Setoid α) (a b : α) : s ≤ joinPair s a b := by
  intro x y hxy
  change mergeClass s a b x = mergeClass s a b y
  simp only [mergeClass, Quotient.sound hxy]

lemma joinPair_related (s : Setoid α) (a b : α) : (joinPair s a b).r a b := by
  change mergeClass s a b a = mergeClass s a b b
  simp [mergeClass]

lemma joinPair_eq_of_related (s : Setoid α) {a b : α} (hab : s.r a b) :
    joinPair s a b = s := by
  ext x y
  have h : ∀ x, mergeClass s a b x = Quotient.mk s x := by
    intro x
    simp only [mergeClass, ← Quotient.sound hab]
    split_ifs with hx
    · exact hx.symm
    · rfl
  change mergeClass s a b x = mergeClass s a b y ↔ s.r x y
  rw [h, h, Quotient.eq]

lemma joinPair_le (s t : Setoid α) (a b : α) (hst : s ≤ t) (hab : t.r a b) :
    joinPair s a b ≤ t := by
  intro x y hxy
  change mergeClass s a b x = mergeClass s a b y at hxy
  by_cases hx : Quotient.mk s x = Quotient.mk s b
  · by_cases hy : Quotient.mk s y = Quotient.mk s b
    · exact t.iseqv.trans (hst (Quotient.exact hx)) (t.iseqv.symm (hst (Quotient.exact hy)))
    · simp only [mergeClass, hx, hy, ite_true, ite_false] at hxy
      exact t.iseqv.trans (t.iseqv.trans (hst (Quotient.exact hx)) (t.iseqv.symm hab)) (hst (Quotient.exact hxy))
  · by_cases hy : Quotient.mk s y = Quotient.mk s b
    · simp only [mergeClass, hx, hy, ite_true, ite_false] at hxy
      exact t.iseqv.trans (t.iseqv.trans (hst (Quotient.exact hxy)) hab) (t.iseqv.symm (hst (Quotient.exact hy)))
    · simp only [mergeClass, hx, hy, ite_false] at hxy
      exact hst (Quotient.exact hxy)

/-- When the two old classes are distinct, joining them removes exactly one. -/
def joinPairEquiv (s : Setoid α) (a b : α) (hab : ¬ s.r a b) :
    Quotient (joinPair s a b) ≃ {c : Quotient s // c ≠ Quotient.mk s b} where
  toFun := Quotient.lift (fun x => ⟨mergeClass s a b x, by
    have hne : Quotient.mk s a ≠ Quotient.mk s b := fun h => hab (Quotient.exact h)
    simp only [mergeClass]
    split_ifs with hx <;> assumption⟩) (fun _ _ h => Subtype.ext h)
  invFun c := Quotient.map id (fun _ _ h => le_joinPair s a b h) c.val
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change Quotient.map id _ (mergeClass s a b x) = Quotient.mk _ x
      unfold mergeClass
      split_ifs with hx
      · apply Quotient.sound
        exact (joinPair s a b).iseqv.trans (joinPair_related s a b) (le_joinPair s a b (s.iseqv.symm (Quotient.exact hx)))
      · rfl
  right_inv c := by
    rcases c with ⟨c, hc⟩
    apply Subtype.ext
    induction c using Quotient.inductionOn with
    | h x =>
      change mergeClass s a b x = Quotient.mk s x
      simp [mergeClass, hc]

lemma joinPair_card [Fintype α] (s : Setoid α) (a b : α) (hab : ¬ s.r a b) :
    Nat.card (Quotient (joinPair s a b)) + 1 = Nat.card (Quotient s) := by
  have h := Fintype.card_congr (joinPairEquiv s a b hab)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have hp : 0 < Fintype.card (Quotient s) := Fintype.card_pos_iff.mpr ⟨Quotient.mk s a⟩
  simp only [Nat.card_eq_fintype_card]
  omega

lemma setoid_swap_related (s : Setoid α) {a b : α} (hab : s.r a b) (x : α) :
    s.r x (swap a b x) := by
  by_cases ha : x = a
  · subst x
    simpa using hab
  · by_cases hb : x = b
    · subst x
      simpa using s.iseqv.symm hab
    · rw [swap_apply_of_ne_of_ne ha hb]

lemma setoid_sameCycle_of_step [Fintype α] (s : Setoid α) (p : Perm α)
    (hstep : ∀ x, s.r x (p x)) {x y : α} (hxy : p.SameCycle x y) : s.r x y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact s.iseqv.refl _
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact s.iseqv.trans ih (hstep _)

/-- Connected components of a graph presented as a list of edges. -/
def edgePartition : List (α × α) → Setoid α
  | [] => ⊥
  | (a, b) :: l => joinPair (edgePartition l) a b

lemma edgePartition_le {l : List (α × α)} {s : Setoid α}
    (h : ∀ ab ∈ l, s.r ab.1 ab.2) : edgePartition l ≤ s := by
  induction l with
  | nil => exact bot_le
  | cons ab l ih =>
    exact joinPair_le _ _ _ _ (ih fun ab hab => h ab (List.mem_cons_of_mem _ hab))
      (h ab List.mem_cons_self)

lemma edgePartition_pair {l : List (α × α)} {ab : α × α} (h : ab ∈ l) :
    (edgePartition l).r ab.1 ab.2 := by
  induction l with
  | nil => simp at h
  | cons cd l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact joinPair_related _ _ _
    · exact le_joinPair _ _ _ (ih h)

lemma edgePartition_prod (l : List (α × α)) (x : α) :
    (edgePartition l).r x ((l.map fun ab => swap ab.1 ab.2).prod x) := by
  induction l with
  | nil => exact (⊥ : Setoid α).iseqv.refl x
  | cons ab l ih =>
    simp only [List.map_cons, List.prod_cons, Perm.mul_apply]
    exact (edgePartition (ab :: l)).iseqv.trans (le_joinPair _ _ _ ih)
      (setoid_swap_related (edgePartition (ab :: l)) (joinPair_related _ _ _) _)

lemma transposition_euler_bound [Fintype α] (l : List (α × α)) :
    Fintype.card α + Nat.card (Cycles (l.map fun ab => swap ab.1 ab.2).prod) ≤
      l.length + 2 * Nat.card (Quotient (edgePartition l)) := by
  induction l with
  | nil =>
    change Fintype.card α + Nat.card (Cycles (1 : Perm α)) ≤
      0 + 2 * Nat.card (Quotient (⊥ : Setoid α))
    rw [cycles_one_card, Nat.card_congr Setoid.quotientBotEquiv, Nat.card_eq_fintype_card]
    omega
  | cons ab l ih =>
    let p := (l.map fun ab => swap ab.1 ab.2).prod
    change Fintype.card α + Nat.card (Cycles (swap ab.1 ab.2 * p)) ≤
      (l.length + 1) + 2 * Nat.card (Quotient (joinPair (edgePartition l) ab.1 ab.2))
    by_cases h : (edgePartition l).r ab.1 ab.2
    · rw [joinPair_eq_of_related _ h]
      have hc := swap_cycles_card_le p ab.1 ab.2
      change Fintype.card α + Nat.card (Cycles p) ≤ _ at ih
      omega
    · have hab : ¬ p.SameCycle ab.1 ab.2 := by
        intro hc
        exact h (setoid_sameCycle_of_step (edgePartition l) p (edgePartition_prod l) hc)
      have hc := swap_mul_cycles_card p ab.1 ab.2 hab
      have hs := joinPair_card (edgePartition l) ab.1 ab.2 h
      change Fintype.card α + Nat.card (Cycles p) ≤ _ at ih
      omega

end KaplanskyCounterexample.Planar

end

end OAI
