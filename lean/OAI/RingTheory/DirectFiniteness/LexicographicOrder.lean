import OAI.RingTheory.DirectFiniteness.PrescribedParameters

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

/-- First successful element of a finite, linearly ordered search space. -/
def first {α : Type u_1} [Fintype α] [LinearOrder α] (P : α → Prop) (h : ∃ x, P x) : α :=
  (Finset.univ.filter P).min' (by simpa [Finset.Nonempty] using h)

lemma first_spec {α : Type u_2} [Fintype α] [LinearOrder α] (P : α → Prop) (h : ∃ x, P x) :
    P (first P h) := by
  have hh := Finset.min'_mem (Finset.univ.filter P) (by simpa [Finset.Nonempty] using h)
  exact (Finset.mem_filter.mp hh).2

lemma first_le {α : Type u_3} [Fintype α] [LinearOrder α] (P : α → Prop) (h : ∃ x, P x)
    (y : α) (hy : P y) : first P h ≤ y :=
  Finset.min'_le _ y (by simp [hy])

/-- Lexicographic order on coefficient/coordinate vectors, increasing index first. -/
@[instance_reducible] def vectorOrder {ι : Type u_4} [LinearOrder ι] [WellFoundedLT ι]
    {α : Type u_5} [LinearOrder α] : LinearOrder (ι → α) :=
  LinearOrder.lift' (toLex : (ι → α) → Lex (ι → α)) (fun _ _ h => h)

@[instance_reducible] def subsetOrder (α : Type u_6) [Fintype α] [LinearOrder α] : LinearOrder (Finset α) :=
  @LinearOrder.lift' (Finset α) (Lex (α → Bool)) inferInstance
    (fun S => toLex (fun x => decide (x ∈ S))) (by
      intro S T h
      apply Finset.ext
      intro x
      have hx := congrFun (congrArg ofLex h) x
      simpa using congrArg (fun b => b=true) hx)

/-- Residues are ordered 0,...,p-1, independently of their field operations. -/
@[instance_reducible] def residueOrder (p : ℕ) [NeZero p] : LinearOrder (ZMod p) :=
  LinearOrder.lift' ZMod.val (ZMod.val_injective p)

end KaplanskyCounterexample.Prescription
end

end OAI
