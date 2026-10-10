import OAI.RingTheory.DirectFiniteness.PlanarBalance

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} {V : Type u_2} {F : Type u_3} {A : Type u_4} {B : Type u_5} [Fintype α] [AddCommGroup A] [AddCommGroup B]

/-- Cycles map under a coarsening of the orbit partition. -/
def cycleMap {p q : Perm α} (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) :
    Cycles p → Cycles q := Quotient.map id (fun _ _ hxy => h hxy)

omit [Fintype α] in
lemma cycleMap_class {p q : Perm α} (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y)
    (a : α) : cycleMap h (cycleClass p a) = cycleClass q a := rfl

lemma sum_cycle_coarsen {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) (c : Cycles q) (f : α → A) :
    ∑ a ∈ cycleSet q c, f a =
      ∑ d ∈ Finset.univ.filter (fun d : Cycles p => cycleMap h d = c),
        ∑ a ∈ cycleSet p d, f a := by
  classical
  have hh := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset α)
    (Finset.univ.filter (fun d : Cycles p => cycleMap h d = c)) (cycleClass p) f
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, cycleMap_class, cycleSet]
    using hh.symm

lemma sum_cycle_coarsen_zero {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) (f : α → A)
    (hf : ∀ c : Cycles p, ∑ a ∈ cycleSet p c, f a = 0) (c : Cycles q) :
    ∑ a ∈ cycleSet q c, f a = 0 := by
  rw [sum_cycle_coarsen h]
  simp only [hf, Finset.sum_const_zero]

lemma sum_cycle_coarsen_exception {p q : Perm α}
    (h : ∀ {x y}, p.SameCycle x y → q.SameCycle x y) (f : α → A)
    (e : Cycles p) (hf : ∀ c : Cycles p, c ≠ e → ∑ a ∈ cycleSet p c, f a = 0)
    (c : Cycles q) :
    ∑ a ∈ cycleSet q c, f a =
      if cycleMap h e = c then ∑ a ∈ cycleSet p e, f a else 0 := by
  classical
  rw [sum_cycle_coarsen h]
  have hz : ∀ d : Cycles p, (∑ a ∈ cycleSet p d, f a) =
      if d = e then ∑ a ∈ cycleSet p e, f a else 0 := by
    intro d
    split_ifs with hd
    · rw [hd]
    · exact hf d hd
  calc
    _ = ∑ d ∈ Finset.univ.filter (fun d : Cycles p => cycleMap h d = c),
        if d = e then ∑ a ∈ cycleSet p e, f a else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      exact hz d
    _ = _ := by simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]

/-- The same balances, allowing temporary zero edges during cancellation. -/
structure WeakBalanced (R : Ribbon α) (Inc : V → F → Prop)
    (ι : V → F → (A →+ B)) where
  blackLabel : α → V
  whiteLabel : α → F
  blackLabel_rot : ∀ a, blackLabel (R.black a) = blackLabel a
  whiteLabel_rot : ∀ a, whiteLabel (R.white a) = whiteLabel a
  incident : ∀ a, Inc (blackLabel a) (whiteLabel a)
  weight : α → A
  exception : Cycles R.white
  black_sum : ∀ c : Cycles R.black,
    ∑ a ∈ cycleSet R.black c, ι (blackLabel a) (whiteLabel a) (weight a) = 0
  white_sum : ∀ c : Cycles R.white, c ≠ exception →
    ∑ a ∈ cycleSet R.white c, weight a = 0
  exceptional_sum : (∑ a ∈ cycleSet R.white exception, weight a) ≠ 0

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

def Balanced.weak (D : Balanced R Inc ι) : WeakBalanced R Inc ι where
  blackLabel := D.blackLabel
  whiteLabel := D.whiteLabel
  blackLabel_rot := D.blackLabel_rot
  whiteLabel_rot := D.whiteLabel_rot
  incident := D.incident
  weight := D.weight
  exception := D.exception
  black_sum := D.black_sum
  white_sum := D.white_sum
  exceptional_sum := D.exceptional_sum

def WeakBalanced.strong (D : WeakBalanced R Inc ι) (h : ∀ a, D.weight a ≠ 0) :
    Balanced R Inc ι where
  blackLabel := D.blackLabel
  whiteLabel := D.whiteLabel
  blackLabel_rot := D.blackLabel_rot
  whiteLabel_rot := D.whiteLabel_rot
  incident := D.incident
  weight := D.weight
  weight_ne := h
  exception := D.exception
  black_sum := D.black_sum
  white_sum := D.white_sum
  exceptional_sum := D.exceptional_sum

def WeakBalanced.coarsen (D : WeakBalanced R Inc ι) (S : Ribbon α)
    (hb : ∀ {x y}, R.black.SameCycle x y → S.black.SameCycle x y)
    (hw : ∀ {x y}, R.white.SameCycle x y → S.white.SameCycle x y)
    (hbl : ∀ a, D.blackLabel (S.black a) = D.blackLabel a)
    (hwl : ∀ a, D.whiteLabel (S.white a) = D.whiteLabel a) :
    WeakBalanced S Inc ι where
  blackLabel := D.blackLabel
  whiteLabel := D.whiteLabel
  blackLabel_rot := hbl
  whiteLabel_rot := hwl
  incident := D.incident
  weight := D.weight
  exception := cycleMap hw D.exception
  black_sum := sum_cycle_coarsen_zero hb _ D.black_sum
  white_sum c hc := by
    rw [sum_cycle_coarsen_exception hw _ D.exception D.white_sum, ite_eq_right (Ne.symm hc)]
  exceptional_sum := by
    rw [sum_cycle_coarsen_exception hw _ D.exception D.white_sum, ite_eq_left rfl]
    exact D.exceptional_sum

end KaplanskyCounterexample.Planar
end

end OAI
