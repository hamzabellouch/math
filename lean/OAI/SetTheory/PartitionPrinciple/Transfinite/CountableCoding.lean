import OAI.SetTheory.PartitionPrinciple.Geometry.NodeCoding

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u

def natPair (a b : Nat) : Nat := (a + b) * (a + b) + a

theorem natPair_upper (a b : Nat) : natPair a b < (a + b + 1) * (a + b + 1) := by
  unfold natPair
  rw [Nat.succ_mul_succ]
  omega

theorem natPair_sum_lt {a b c d : Nat} (less : a + b < c + d) : natPair a b < natPair c d := by
  have step : a + b + 1 ≤ c + d := by omega
  have sq := Nat.mul_le_mul step step
  have bound := natPair_upper a b
  unfold natPair at *
  omega

theorem natPair_injective {a b c d : Nat} (eq : natPair a b = natPair c d) : a = c ∧ b = d := by
  have sums : a + b = c + d := by
    have h₁ : ¬ a + b < c + d := fun h => Nat.ne_of_lt (natPair_sum_lt h) eq
    have h₂ : ¬ c + d < a + b := fun h => Nat.ne_of_lt (natPair_sum_lt h) eq.symm
    omega
  unfold natPair at eq
  rw [sums] at eq
  omega

def listCode {A : Type u} (encode : A → Nat) : List A → Nat
  | [] => 0
  | a :: xs => natPair (encode a) (listCode encode xs) + 1

theorem listCode_injective {A : Type u} (encode : A → Nat)
    (injective : ∀ a b, encode a = encode b → a = b)
    (xs ys : List A) (eq : listCode encode xs = listCode encode ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => exact False.elim (Nat.zero_ne_add_one _ eq)
  | cons x xs ih =>
    cases ys with
    | nil => exact False.elim (Nat.zero_ne_add_one _ eq.symm)
    | cons y ys =>
      have parts := natPair_injective (Nat.add_right_cancel eq)
      have head := injective x y parts.1
      have tail := ih ys parts.2
      cases head
      cases tail
      rfl

namespace TaskSystem

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)

theorem union_countable (encodeA : A → Nat)
    (injectiveA : ∀ a b, encodeA a = encodeA b → a = b)
    (encodeTask : Task → Nat)
    (injectiveTask : ∀ i j, encodeTask i = encodeTask j → i = j) :
    ∃ encode : f.Union → Nat, ∀ x y, encode x = encode y → x = y := by
  apply f.union_size_transfer (fun p => natPair (listCode encodeTask p.1) (encodeA p.2))
  intro x y eq
  have parts := natPair_injective eq
  exact Prod.ext (listCode_injective encodeTask injectiveTask _ _ parts.1)
    (injectiveA _ _ parts.2)

end TaskSystem
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
