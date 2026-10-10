import OAI.RingTheory.DirectFiniteness.CycleSums

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {β : Type u_2} {V : Type u_3} {F : Type u_4} {A : Type u_5} {B : Type u_6} [Fintype α] [Fintype β]
variable [AddCommGroup A] [AddCommGroup B]

/-- An auxiliary balanced component, without an exceptional white vertex. -/
structure ZeroBalanced (R : Ribbon α) (Inc : V → F → Prop)
    (ι : V → F → (A →+ B)) where
  blackLabel : α → V
  whiteLabel : α → F
  blackLabel_rot : ∀ a, blackLabel (R.black a) = blackLabel a
  whiteLabel_rot : ∀ a, whiteLabel (R.white a) = whiteLabel a
  incident : ∀ a, Inc (blackLabel a) (whiteLabel a)
  weight : α → A
  black_sum : ∀ c : Cycles R.black,
    ∑ a ∈ cycleSet R.black c, ι (blackLabel a) (whiteLabel a) (weight a) = 0
  white_sum : ∀ c : Cycles R.white, ∑ a ∈ cycleSet R.white c, weight a = 0

variable {R : Ribbon α} {S : Ribbon β} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def WeakBalanced.sumZero (D : WeakBalanced R Inc ι) (E : ZeroBalanced S Inc ι) :
    WeakBalanced (R.sum S) Inc ι where
  blackLabel := Sum.elim D.blackLabel E.blackLabel
  whiteLabel := Sum.elim D.whiteLabel E.whiteLabel
  blackLabel_rot := by rintro (x | x); exact D.blackLabel_rot x; exact E.blackLabel_rot x
  whiteLabel_rot := by rintro (x | x); exact D.whiteLabel_rot x; exact E.whiteLabel_rot x
  incident := by rintro (x | x); exact D.incident x; exact E.incident x
  weight := Sum.elim D.weight E.weight
  exception := cycleInl R.white S.white D.exception
  black_sum c := by
    dsimp only [Ribbon.sum] at c ⊢
    induction c using Quotient.inductionOn with
    | h x =>
      cases x with
      | inl x =>
        change (∑ a ∈ cycleSet (Equiv.sumCongr R.black S.black) (cycleClass _ (.inl x)), _) = 0
        rw [sum_cycle_sum_left]
        exact D.black_sum _
      | inr x =>
        change (∑ a ∈ cycleSet (Equiv.sumCongr R.black S.black) (cycleClass _ (.inr x)), _) = 0
        rw [sum_cycle_sum_right]
        exact E.black_sum _
  white_sum c hc := by
    dsimp only [Ribbon.sum] at c hc ⊢
    induction c using Quotient.inductionOn with
    | h x =>
      cases x with
      | inl x =>
        have hne : cycleClass R.white x ≠ D.exception := by
          intro he
          exact hc (congrArg (cycleInl R.white S.white) he)
        change (∑ a ∈ cycleSet (Equiv.sumCongr R.white S.white) (cycleClass _ (.inl x)), _) = 0
        rw [sum_cycle_sum_left]
        exact D.white_sum _ hne
      | inr x =>
        change (∑ a ∈ cycleSet (Equiv.sumCongr R.white S.white) (cycleClass _ (.inr x)), _) = 0
        rw [sum_cycle_sum_right]
        exact E.white_sum _
  exceptional_sum := by
    generalize he : D.exception = e at *
    induction e using Quotient.inductionOn with
    | h x =>
      change (∑ a ∈ cycleSet (Equiv.sumCongr R.white S.white)
        (cycleClass _ (.inl x)), Sum.elim D.weight E.weight a) ≠ 0
      rw [sum_cycle_sum_left]
      change (∑ y ∈ cycleSet R.white ⟦x⟧, D.weight y) ≠ 0
      rw [← he]
      exact D.exceptional_sum

/-- The temporary boundary is an unlabelled black vertex. -/
def augInc (Inc : V → F → Prop) : Option V → F → Prop
  | none, _ => True
  | some v, f => Inc v f

def augMap (ι : V → F → (A →+ B)) : Option V → F → (A →+ B)
  | none, _ => 0
  | some v, f => ι v f

/-- A planar partially exposed lifetime diagram. The anchor has zero weight
and merely keeps a distinguished boundary rotation available at the empty word. -/
structure OpenDiagram (Inc : V → F → Prop) (ι : V → F → (A →+ B))
    (f₀ : F) (w : List (F × A)) where
  Edge : Type
  fintype : Fintype Edge
  ribbon : Ribbon Edge
  balanced : @WeakBalanced Edge (Option V) F A B fintype _ _ ribbon (augInc Inc) (augMap ι)
  planar : @Ribbon.GenusZero Edge fintype ribbon
  anchor : Edge
  boundary : List Edge
  nodup : (anchor :: boundary).Nodup
  rotation : Follows ribbon.black (anchor :: boundary)
  exposed : ∀ x, balanced.blackLabel x = none ↔ x ∈ anchor :: boundary
  anchor_weight : balanced.weight anchor = 0
  anchor_label : balanced.whiteLabel anchor = f₀
  word : boundary.map (fun x => (balanced.whiteLabel x, balanced.weight x)) = w

attribute [instance] OpenDiagram.fintype

end KaplanskyCounterexample.Planar

end

end OAI
