import OAI.RingTheory.DirectFiniteness.BalanceDetachment

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

/-- The inclusion of the cycles of an invariant subset. -/
def cycleSubtypeMap (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Cycles (p.subtypePerm hP) → Cycles p :=
  Quotient.map Subtype.val (fun _ _ h => (sameCycle_subtypePerm (h := hP)).mp h)

omit [Fintype α] in
lemma cycleSubtypeMap_injective (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x) :
    Function.Injective (cycleSubtypeMap p P hP) := by
  intro c d
  induction c using Quotient.inductionOn with
  | h x =>
    induction d using Quotient.inductionOn with
    | h y =>
      intro h
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mpr (Quotient.exact h))

lemma sum_cycle_subtype (p : Perm α) (P : α → Prop) (hP : ∀ x, P (p x) ↔ P x)
    (c : Cycles (p.subtypePerm hP)) (f : α → A) :
    ∑ a ∈ cycleSet (p.subtypePerm hP) c, f a.val =
      ∑ a ∈ cycleSet p (cycleSubtypeMap p P hP c), f a := by
  classical
  induction c using Quotient.inductionOn with
  | h x =>
    apply Finset.sum_bij (fun y _ => y.val)
    · intro y hy
      apply (mem_cycleSet _ _ _).mpr
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mp
        (Quotient.exact ((mem_cycleSet _ _ _).mp hy)))
    · intro y _ z _ h
      exact Subtype.ext h
    · intro y hy
      have hcycle : p.SameCycle y x.val := (cycleClass_eq _ _ _).mp ((mem_cycleSet _ _ _).mp hy)
      have hPy : P y := (perm_invariant_cycle p P hP hcycle).mpr x.property
      refine ⟨⟨y, hPy⟩, ?_, rfl⟩
      apply (mem_cycleSet _ _ _).mpr
      exact Quotient.sound ((sameCycle_subtypePerm (h := hP)).mpr hcycle)
    · intro _ _
      rfl

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

/-- Discard components not containing the exception. -/
def WeakBalanced.restrict (D : WeakBalanced R Inc ι) (P : α → Prop)
    (hb : ∀ x, P (R.black x) ↔ P x) (hw : ∀ x, P (R.white x) ↔ P x)
    (e : α) (he : cycleClass R.white e = D.exception) (hPe : P e) :
    WeakBalanced (R.restrict P hb hw) Inc ι where
  blackLabel a := D.blackLabel a.val
  whiteLabel a := D.whiteLabel a.val
  blackLabel_rot a := D.blackLabel_rot a.val
  whiteLabel_rot a := D.whiteLabel_rot a.val
  incident a := D.incident a.val
  weight a := D.weight a.val
  exception := cycleClass (R.white.subtypePerm hw) ⟨e, hPe⟩
  black_sum c := by
    dsimp only [Ribbon.restrict] at c ⊢
    rw [sum_cycle_subtype R.black P hb c
      (fun x => ι (D.blackLabel x) (D.whiteLabel x) (D.weight x))]
    exact D.black_sum _
  white_sum c hc := by
    dsimp only [Ribbon.restrict] at c hc ⊢
    rw [sum_cycle_subtype]
    apply D.white_sum
    intro h
    apply hc
    apply cycleSubtypeMap_injective R.white P hw
    exact h.trans he.symm
  exceptional_sum := by
    change (∑ a ∈ cycleSet (R.white.subtypePerm hw)
      (cycleClass (R.white.subtypePerm hw) ⟨e, hPe⟩), D.weight a.val) ≠ 0
    rw [sum_cycle_subtype]
    change (∑ a ∈ cycleSet R.white (cycleClass R.white e), D.weight a) ≠ 0
    rw [he]
    exact D.exceptional_sum

end KaplanskyCounterexample.Planar
end

end OAI
