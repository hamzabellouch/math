import OAI.RingTheory.DirectFiniteness.BalanceCoarsening

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2} {V : Type u_3} {F : Type u_4} {A : Type u_5} {B : Type u_6} [Fintype α] [AddCommGroup A] [AddCommGroup B]

lemma label_sameCycle (p : Perm α) (f : α → β) (hf : ∀ a, f (p a) = f a)
    {x y : α} (hxy : p.SameCycle x y) : f x = f y :=
  setoid_sameCycle_of_step (Setoid.ker f) p (fun x => (hf x).symm) hxy

lemma label_unplug (p : Perm α) (f : α → β) (hf : ∀ a, f (p a) = f a) (a x : α) :
    f (unplug p a x) = f x :=
  (label_sameCycle p f hf (unplug_sameCycle p a ((SameCycle.refl _ x).apply_right))).symm

lemma sameCycle_unplug_iff_of_ne (p : Perm α) (a : α) {x y : α}
    (hx : x ≠ a) (hy : y ≠ a) : (unplug p a).SameCycle x y ↔ p.SameCycle x y := by
  by_cases ha : p a = a
  · simp only [unplug, ha, swap_self]
    rfl
  · exact unplug_sameCycle_iff p a ha hx hy

lemma cycleSet_unplug (p : Perm α) (a x : α) (hx : x ≠ a) :
    cycleSet (unplug p a) (cycleClass (unplug p a) x) =
      (cycleSet p (cycleClass p x)).erase a := by
  classical
  ext y
  rw [mem_cycleSet, cycleClass_eq, Finset.mem_erase, mem_cycleSet, cycleClass_eq]
  constructor
  · intro hy
    refine ⟨?_, unplug_sameCycle p a hy⟩
    intro hya
    subst y
    exact hx (hy.symm.eq_of_right (unplug_fixed p a))
  · rintro ⟨hya, hy⟩
    exact (sameCycle_unplug_iff_of_ne p a hya hx).mpr hy

omit [Fintype α] in
lemma sum_erase_of_zero (s : Finset α) (a : α) (f : α → A) (ha : f a = 0) :
    ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x := by
  classical
  apply Finset.sum_subset (Finset.erase_subset _ _)
  intro x hx hxa
  have : x = a := by simpa [hx] using hxa
  simpa [this] using ha

lemma sum_cycle_unplug (p : Perm α) (a x : α) (hx : x ≠ a)
    (f : α → A) (ha : f a = 0) :
    ∑ y ∈ cycleSet (unplug p a) (cycleClass (unplug p a) x), f y =
      ∑ y ∈ cycleSet p (cycleClass p x), f y := by
  rw [cycleSet_unplug p a x hx]
  exact sum_erase_of_zero _ a f ha

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

lemma WeakBalanced.exists_exception_nonzero (D : WeakBalanced R Inc ι) :
    ∃ e ∈ cycleSet R.white D.exception, D.weight e ≠ 0 := by
  classical
  by_contra! h
  exact D.exceptional_sum (Finset.sum_eq_zero h)

/-- A zero-weight edge can be detached without changing any nonzero balance. -/
def WeakBalanced.detach (D : WeakBalanced R Inc ι) (a : α) (ha : D.weight a = 0) :
    WeakBalanced (R.detach a) Inc ι := by
  classical
  let e := D.exists_exception_nonzero.choose
  have he := D.exists_exception_nonzero.choose_spec.1
  have hwe := D.exists_exception_nonzero.choose_spec.2
  have hea : e ≠ a := by rintro rfl; exact hwe ha
  have hec := (mem_cycleSet R.white D.exception e).mp he
  refine {
    blackLabel := D.blackLabel
    whiteLabel := D.whiteLabel
    blackLabel_rot := label_unplug R.black D.blackLabel D.blackLabel_rot a
    whiteLabel_rot := label_unplug R.white D.whiteLabel D.whiteLabel_rot a
    incident := D.incident
    weight := D.weight
    exception := cycleClass (unplug R.white a) e
    black_sum := ?_
    white_sum := ?_
    exceptional_sum := ?_ }
  · dsimp only [Ribbon.detach]
    intro c
    induction c using Quotient.inductionOn with
    | h x =>
      change (∑ y ∈ cycleSet (unplug R.black a) (cycleClass (unplug R.black a) x),
        ι (D.blackLabel y) (D.whiteLabel y) (D.weight y)) = 0
      by_cases hx : x = a
      · subst x
        rw [cycleSet_singleton_of_fixed _ _ (unplug_fixed R.black a)]
        simp [ha]
      · rw [sum_cycle_unplug R.black a x hx
          (fun y => ι (D.blackLabel y) (D.whiteLabel y) (D.weight y)) (by simp [ha])]
        exact D.black_sum _
  · dsimp only [Ribbon.detach]
    intro c hc
    induction c using Quotient.inductionOn with
    | h x =>
      change (∑ y ∈ cycleSet (unplug R.white a) (cycleClass (unplug R.white a) x),
        D.weight y) = 0
      by_cases hx : x = a
      · subst x
        rw [cycleSet_singleton_of_fixed _ _ (unplug_fixed R.white a)]
        simpa using ha
      · rw [sum_cycle_unplug R.white a x hx _ ha]
        apply D.white_sum
        intro hxc
        apply hc
        apply (cycleClass_eq _ _ _).mpr
        apply (sameCycle_unplug_iff_of_ne R.white a hx hea).mpr
        exact (cycleClass_eq _ _ _).mp (hxc.trans hec.symm)
  · dsimp only [Ribbon.detach]
    rw [sum_cycle_unplug R.white a e hea _ ha, hec]
    exact D.exceptional_sum

end KaplanskyCounterexample.Planar
end

end OAI
