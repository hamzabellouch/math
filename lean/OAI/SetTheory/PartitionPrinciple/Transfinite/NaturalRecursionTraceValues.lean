import OAI.SetTheory.PartitionPrinciple.Geometry.FiniteIterationTraces

namespace OAI

section

namespace PartitionPilot.Forcing.OrdinalRecursionTrace

universe u v
variable {B : Type v} {R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
variable (encode : B → ZFSet.{u}) (step : B → B) (base : B)
variable (zero : ∀ p y, R (natSetCode 0) p y → y = encode base)
variable (successor : ∀ n p b y,
  ZFSet.pair (natSetCode n) (encode b) ∈ p → R (natSetCode (n + 1)) p y →
    y = encode (step b))

include zero successor

theorem natural_entry_value {N t : ZFSet.{u}} (ordinal : ordinalSetProperty N)
    (trace : OrdinalRecursionTrace R N t) :
    ∀ n, natSetCode n ∈ N → ∀ y, ZFSet.pair (natSetCode n) y ∈ t →
      y = encode (natIterate step base n) := by
  intro n
  induction n with
  | zero =>
    intro hn y entry
    exact zero _ y (trace.2 _ hn y entry)
  | succ n ih =>
    intro hn y entry
    have previous : natSetCode n ∈ natSetCode (n + 1) :=
      (natSetCode_mem_iff n (n + 1)).2 (Nat.lt_succ_self n)
    have hnN := ordinal.1 (natSetCode (n + 1)) hn (natSetCode n) previous
    obtain ⟨b, oldEntry⟩ := trace.1.total hnN
    have equal := ih hnN b oldEntry
    exact successor n (graphRestriction (natSetCode (n + 1)) t)
      (natIterate step base n) y
      (pair_mem_graphRestriction.2 ⟨equal ▸ oldEntry, previous⟩)
      (trace.2 _ hn y entry)

theorem natural_entry_iff {N t : ZFSet.{u}} (ordinal : ordinalSetProperty N)
    (trace : OrdinalRecursionTrace R N t) (n : Nat) (hn : natSetCode n ∈ N) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode n) y ∈ t ↔ y = encode (natIterate step base n) := by
  constructor
  · exact natural_entry_value encode step base zero successor ordinal trace n hn y
  · intro equal
    obtain ⟨z, entry⟩ := trace.1.total hn
    have value := natural_entry_value encode step base zero successor ordinal trace n hn z entry
    exact equal.symm ▸ (value ▸ entry)

end PartitionPilot.Forcing.OrdinalRecursionTrace

end

end OAI
