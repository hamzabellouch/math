import OAI.RingTheory.DirectFiniteness.DiagramDeletion

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

lemma cycleSet_wheel_white (p : Perm α) (x : α ⊕ α) :
    cycleSet (Ribbon.wheel p).white (cycleClass _ x) =
      {Sum.inl (sumIndex x), Sum.inr (sumIndex x)} := by
  ext y
  rw [mem_cycleSet, cycleClass_eq]
  change (SameCycle.setoid (Ribbon.wheel p).white).r y x ↔ _
  rw [wheel_white_setoid]
  cases x <;> cases y <;> simp [sumIndex]

variable {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def ZeroBalanced.wheel (p : Perm α) (v : V) (fl : α → F) (w : α → A)
    (hinc : ∀ x, Inc v (fl x))
    (hsum : ∀ c : Cycles p⁻¹, (∑ x ∈ cycleSet p⁻¹ c, ι v (fl x) (w x)) = 0) :
    ZeroBalanced (Ribbon.wheel p) (augInc Inc) (augMap ι) where
  blackLabel := Sum.elim (fun _ => none) (fun _ => some v)
  whiteLabel := Sum.elim fl fl
  blackLabel_rot := by rintro (x | x) <;> rfl
  whiteLabel_rot := by rintro (x | x) <;> rfl
  incident := by rintro (x | x); trivial; exact hinc x
  weight := Sum.elim w (fun x => -w x)
  black_sum c := by
    dsimp only [Ribbon.wheel] at c ⊢
    induction c using Quotient.inductionOn with
    | h x =>
      cases x with
      | inl x =>
        change (∑ y ∈ cycleSet (Equiv.sumCongr p p⁻¹) (cycleClass _ (.inl x)), _) = 0
        rw [sum_cycle_sum_left]
        simp [augMap]
      | inr x =>
        change (∑ y ∈ cycleSet (Equiv.sumCongr p p⁻¹) (cycleClass _ (.inr x)), _) = 0
        rw [sum_cycle_sum_right]
        simpa only [Sum.elim_inr, augMap, map_neg, Finset.sum_neg_distrib, neg_eq_zero] using hsum (cycleClass p⁻¹ x)
  white_sum c := by
    induction c using Quotient.inductionOn with
    | h x =>
      change (∑ y ∈ cycleSet (Ribbon.wheel p).white (cycleClass _ x), _) = 0
      rw [cycleSet_wheel_white, Finset.sum_pair (by simp)]
      simp only [Sum.elim_inl, Sum.elim_inr, add_neg_cancel]

lemma cycleSet_finRange_inv (n : ℕ) (c : Cycles (List.finRange n).formPerm⁻¹) :
    cycleSet (List.finRange n).formPerm⁻¹ c = Finset.univ := by
  induction c using Quotient.inductionOn with
  | h x =>
    ext y
    simp only [mem_cycleSet, Finset.mem_univ, iff_true]
    apply (cycleClass_eq _ _ _).mpr
    apply sameCycle_inv.mpr
    exact (List.nodup_finRange n).isCycleOn_formPerm.2 (by simp) (by simp)

omit [Fintype α] in
def wordWheel (r : List (F × A)) (v : V)
    (hinc : ∀ t ∈ r, Inc v t.1)
    (hsum : (r.map (fun t => ι v t.1 t.2)).sum = 0) :
    ZeroBalanced (Ribbon.wheel (List.finRange r.length).formPerm) (augInc Inc) (augMap ι) :=
  ZeroBalanced.wheel _ v (fun i => (r.get i).1) (fun i => (r.get i).2)
    (fun i => hinc _ (List.get_mem r i)) (by
      intro c
      rw [cycleSet_finRange_inv]
      rw [← List.sum_ofFn]
      change (List.ofFn ((fun t : F × A => ι v t.1 t.2) ∘ r.get)).sum = 0
      rw [← List.map_ofFn, List.ofFn_get]
      exact hsum)

end KaplanskyCounterexample.Planar

end

end OAI
