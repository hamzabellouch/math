import OAI.RingTheory.DirectFiniteness.WeightTransfer

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
attribute [local simp] SameCycle.rfl
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

lemma Ribbon.mergeWhite_components (R : Ribbon α) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a)) : (R.mergeWhite a).components = R.components := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa [Ribbon.face] using ha
  apply le_antisymm
  · apply (R.mergeWhite a).components_le_of_steps
    · exact R.black_step
    · intro x
      exact R.components.iseqv.trans (R.white_step x)
        (setoid_swap_related R.components (R.face_step a) (R.white x))
  · apply sup_le
    · exact le_sup_left
    · intro x y h
      exact (show SameCycle.setoid (R.mergeWhite a).white ≤ (R.mergeWhite a).components
        from le_sup_right) (sameCycle_swap_mul R.white a (R.face a) hn h)

lemma Ribbon.genusZero_mergeWhite (R : Ribbon α) (hR : R.GenusZero) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a)) : (R.mergeWhite a).GenusZero := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa [Ribbon.face] using ha
  have hne : R.face a ≠ a := by intro h; exact hn (by rw [h])
  have hw := swap_mul_cycles_card R.white a (R.face a) hn
  have hf := unplug_cycles_card R.face a hne
  unfold Ribbon.GenusZero at *
  rw [R.mergeWhite_components a ha, mergeWhite_face]
  change Nat.card (Cycles R.black) + Nat.card (Cycles (swap a (R.face a) * R.white)) +
    Nat.card (Cycles (unplug R.face a)) = _
  rw [hf, Nat.add_comm (Nat.card (Cycles R.face)) 1, ← Nat.add_assoc,
    Nat.add_assoc _ _ 1, hw]
  exact hR

/-- The color-reversed local surgery. -/
def Ribbon.mergeBlack (R : Ribbon α) (a : α) : Ribbon α where
  black := swap a (R.black (R.white a)) * R.black
  white := R.white

omit [Fintype α] in
lemma Ribbon.mergeBlack_face (R : Ribbon α) (a : α) :
    (R.mergeBlack a).face = unplug R.face (R.white a) := by
  change R.white * (swap a (R.black (R.white a)) * R.black) =
    swap (R.white a) (R.white (R.black (R.white a))) * (R.white * R.black)
  rw [← mul_assoc, mul_swap_eq_swap_mul, mul_assoc]

lemma Ribbon.mergeBlack_components (R : Ribbon α) (a : α)
    (ha : ¬ R.black.SameCycle a (R.white a)) : (R.mergeBlack a).components = R.components := by
  have hn : ¬ R.black.SameCycle a (R.black (R.white a)) := by simpa using ha
  apply le_antisymm
  · apply (R.mergeBlack a).components_le_of_steps
    · intro x
      exact R.components.iseqv.trans (R.black_step x)
        (setoid_swap_related R.components
          (R.components.iseqv.trans (R.white_step a) (R.black_step (R.white a))) (R.black x))
    · exact R.white_step
  · apply sup_le
    · intro x y h
      exact (show SameCycle.setoid (R.mergeBlack a).black ≤ (R.mergeBlack a).components
        from le_sup_left) (sameCycle_swap_mul R.black a (R.black (R.white a)) hn h)
    · exact le_sup_right

lemma Ribbon.genusZero_mergeBlack (R : Ribbon α) (hR : R.GenusZero) (a : α)
    (ha : ¬ R.black.SameCycle a (R.white a)) : (R.mergeBlack a).GenusZero := by
  have hn : ¬ R.black.SameCycle a (R.black (R.white a)) := by simpa using ha
  have hne : R.face (R.white a) ≠ R.white a := by
    intro h
    have h' : R.black (R.white a) = a := R.white.injective h
    exact hn (by rw [h'])
  have hb := swap_mul_cycles_card R.black a (R.black (R.white a)) hn
  have hf := unplug_cycles_card R.face (R.white a) hne
  unfold Ribbon.GenusZero at *
  rw [R.mergeBlack_components a ha, R.mergeBlack_face]
  change Nat.card (Cycles (swap a (R.black (R.white a)) * R.black)) +
    Nat.card (Cycles R.white) + Nat.card (Cycles (unplug R.face (R.white a))) = _
  omega

omit [Fintype α] in
lemma label_swap (f : α → V) (a b : α) (hab : f a = f b) (x : α) :
    f (swap a b x) = f x := by
  by_cases hxa : x = a
  · subst x
    simpa using hab.symm
  · by_cases hxb : x = b
    · subst x
      simpa using hab
    · rw [swap_apply_of_ne_of_ne hxa hxb]

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def WeakBalanced.mergeWhite (D : WeakBalanced R Inc ι) (a : α)
    (ha : ¬ R.white.SameCycle a (R.black a))
    (hl : D.whiteLabel (R.black a) = D.whiteLabel a) :
    WeakBalanced (R.mergeWhite a) Inc ι := by
  have hn : ¬ R.white.SameCycle a (R.face a) := by simpa [Ribbon.face] using ha
  apply D.coarsen (R.mergeWhite a) (fun h => h) (sameCycle_swap_mul _ _ _ hn)
    D.blackLabel_rot
  intro x
  change D.whiteLabel (swap a (R.face a) (R.white x)) = D.whiteLabel x
  rw [label_swap D.whiteLabel a (R.face a)]
  · exact D.whiteLabel_rot x
  · exact (hl.symm).trans (D.whiteLabel_rot (R.black a)).symm

def WeakBalanced.mergeBlack (D : WeakBalanced R Inc ι) (a : α)
    (ha : ¬ R.black.SameCycle a (R.white a))
    (hl : D.blackLabel (R.white a) = D.blackLabel a) :
    WeakBalanced (R.mergeBlack a) Inc ι := by
  have hn : ¬ R.black.SameCycle a (R.black (R.white a)) := by simpa using ha
  apply D.coarsen (R.mergeBlack a) (sameCycle_swap_mul _ _ _ hn) (fun h => h)
    _ D.whiteLabel_rot
  intro x
  change D.blackLabel (swap a (R.black (R.white a)) (R.black x)) = D.blackLabel x
  rw [label_swap D.blackLabel a (R.black (R.white a))]
  · exact D.blackLabel_rot x
  · exact (hl.symm).trans (D.blackLabel_rot (R.white a)).symm

end KaplanskyCounterexample.Planar
end

end OAI
