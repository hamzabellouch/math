import Mathlib.Data.List.Basic
import Mathlib.Tactic.Group

namespace OAI

/-!
# The group calculation for a charged closed walk

In §3, left Cayley moves commute with the right holonomy. Recording a step
as `(s,m)` means `z ↦ s * z * g^m`; a pure Cayley step has `m=0`, and a
pure base step has `s=1`. The accumulated endpoint formula and conjugacy
obstruction are expressed using an actual finite list of steps.
-/

namespace CoarseAssembly

variable {Q : Type*} [Group Q]

/-- Successively apply left Cayley moves and right integral holonomies. -/
def holonomyEndpoint (g : Q) : List (Q × ℤ) → Q → Q
  | [], z => z
  | s :: steps, z => holonomyEndpoint g steps (s.1 * z * g ^ s.2)

/-- Product of the left moves, in the order in which they act. -/
def holonomyWord : List (Q × ℤ) → Q
  | [] => 1
  | s :: steps => holonomyWord steps * s.1

/-- Total signed crossing count. -/
def holonomyCharge : List (Q × ℤ) → ℤ
  | [] => 0
  | s :: steps => s.2 + holonomyCharge steps

/-- Left multiplication and right holonomy accumulate independently. -/
theorem holonomyEndpoint_eq (g z : Q) (steps : List (Q × ℤ)) :
    holonomyEndpoint g steps z = holonomyWord steps * z * g ^ holonomyCharge steps := by
  induction steps generalizing z with
  | nil => simp [holonomyEndpoint, holonomyWord, holonomyCharge]
  | cons s steps ih =>
    simp only [holonomyEndpoint, holonomyWord, holonomyCharge, ih, zpow_add]
    group

/-- A closed walk forces its right holonomy to be conjugate to the inverse
of its left word. No commutativity of the finite quotient is assumed. -/
theorem holonomy_conjugacy (g z : Q) (steps : List (Q × ℤ))
    (hclosed : holonomyEndpoint g steps z = z) :
    g ^ holonomyCharge steps = z⁻¹ * (holonomyWord steps)⁻¹ * z := by
  rw [holonomyEndpoint_eq] at hclosed
  calc
    g ^ holonomyCharge steps =
        (z⁻¹ * (holonomyWord steps)⁻¹) *
          (holonomyWord steps * z * g ^ holonomyCharge steps) := by group
    _ = z⁻¹ * (holonomyWord steps)⁻¹ * z := by rw [hclosed]

/-- Any conjugacy invariant, in particular matrix trace, detects the
obstruction supplied by a closed charged walk. -/
theorem holonomy_invariant_eq {T : Type*} (tr : Q → T)
    (htr : ∀ q z, tr (z⁻¹ * q * z) = tr q)
    (g z : Q) (steps : List (Q × ℤ))
    (hclosed : holonomyEndpoint g steps z = z) :
    tr (g ^ holonomyCharge steps) = tr (holonomyWord steps)⁻¹ := by
  rw [holonomy_conjugacy g z steps hclosed, htr]

/-- If a conjugacy invariant separates all the nonzero possible charges
from the inverse left word, a closed walk has charge zero. This is the
algebraic contradiction used after reducing to the minimum-depth quotient. -/
theorem holonomyCharge_eq_zero {T : Type*} (tr : Q → T)
    (htr : ∀ q z, tr (z⁻¹ * q * z) = tr q)
    (g z : Q) (steps : List (Q × ℤ))
    (hclosed : holonomyEndpoint g steps z = z)
    (hsep : holonomyCharge steps ≠ 0 →
      tr (g ^ holonomyCharge steps) ≠ tr (holonomyWord steps)⁻¹) :
    holonomyCharge steps = 0 := by
  by_contra hn
  exact hsep hn (holonomy_invariant_eq tr htr g z steps hclosed)

end CoarseAssembly

end OAI
