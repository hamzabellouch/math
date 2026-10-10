import OAI.RingTheory.DirectFiniteness.SlabAvoidance

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
open KaplanskyCounterexample.FiniteLocalLemma
namespace KaplanskyCounterexample.FiniteGeometry

lemma sum_indicator_card {α : Type u_1} [Fintype α] (P : α → Prop) [DecidablePred P] (x : ℝ) :
    (∑ a : α, if P a then x else 0) = Fintype.card {a // P a} * x := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast (Fintype.card_subtype P).symm

variable {Q : Type u_2} {A : Type u_3} {R : Type u_4} {E : Type u_5} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]
namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)

lemma load_eq (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (p : ℝ) (v : SlabVariable F) :
    load (fun c : Candidate F T k => c.deps F T) (fun c => p^(c.deps F T).card) v =
    Fintype.card {c : Candidate F T k // c.labels.card=1 ∧ v ∈ c.deps F T} * p^2 +
    Fintype.card {c : Candidate F T k // c.labels.card=2 ∧ v ∈ c.deps F T} * p^4 := by
  rw [load]
  calc
    _ = ∑ c : Candidate F T k,
      ((if c.labels.card=1 ∧ v ∈ c.deps F T then p^2 else 0) +
       (if c.labels.card=2 ∧ v ∈ c.deps F T then p^4 else 0)) := by
      apply Finset.sum_congr rfl
      intro c _
      have hb := c.labels_card_bounds F T hk5
      have hc : c.labels.card=1 ∨ c.labels.card=2 := by
        rcases eq_or_lt_of_le hb.1 with hcount | hcount
        · exact Or.inl hcount.symm
        · exact Or.inr (Nat.le_antisymm hb.2 (Nat.succ_le_of_lt hcount))
      rw [c.deps_card F T hk3 hk5]
      rcases hc with hc | hc <;> by_cases hv : v ∈ c.deps F T <;> simp [hc,hv]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      exact congrArg₂ (· + ·)
        (sum_indicator_card (fun c : Candidate F T k => c.labels.card=1 ∧ v ∈ c.deps F T) (p^2))
        (sum_indicator_card (fun c : Candidate F T k => c.labels.card=2 ∧ v ∈ c.deps F T) (p^4))

lemma load_le (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (M : ℕ)
    (hM : ∀ j (C : AffineCoset (F.U j)) r, (C.val ∩ T r).card ≤ M) (p : ℝ) (v : SlabVariable F) :
    load (fun c : Candidate F T k => c.deps F T) (fun c => p^(c.deps F T).card) v ≤
    (Fintype.card R*k^2*2^k*M^2*Fintype.card Q^k : ℕ)*p^2 +
    ((Fintype.card R*Fintype.card Q)*k^4*3^k*(Fintype.card Q*Fintype.card E)*
      (Fintype.card Q*Fintype.card E)^2*Fintype.card Q^k : ℕ)*p^4 := by
  rw [load_eq F T k hk3 hk5 p v]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg p)
    exact_mod_cast local_one_card_le F T k v.1 v.2 hk3 hk5 M (hM v.1 v.2)
  · apply mul_le_mul_of_nonneg_right _ ((even_two.mul_right 2).pow_nonneg p)
    have h := local_two_card_le F T k v.1 v.2 hk5
    rw [AffineCoset.card,F.card_U] at h
    exact_mod_cast h

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
