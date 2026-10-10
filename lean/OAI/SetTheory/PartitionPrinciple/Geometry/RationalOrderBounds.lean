import OAI.SetTheory.PartitionPrinciple.Forcing.DenseInterpolation

namespace OAI

namespace PartitionPilot.Compression.RecursiveMaps.RationalHeights

structure Fraction where
  num : Int
  den : Nat
  positive : 0 < den

namespace Fraction

def Lt (a b : Fraction) : Prop := a.num * (b.den : Int) < b.num * (a.den : Int)
def Equiv (a b : Fraction) : Prop := a.num * (b.den : Int) = b.num * (a.den : Int)

theorem den_pos (a : Fraction) : 0 < (a.den : Int) := Int.natCast_pos.mpr a.positive

theorem cancel_lt {a b c : Int} (pos : 0 < c) (h : a * c < b * c) : a < b := by
  apply Classical.byContradiction
  intro hn
  have ba : b ≤ a := by omega
  have hc : 0 ≤ c := by omega
  have hb := Int.mul_le_mul_of_nonneg_right ba hc
  omega

theorem equiv_trans {a b c : Fraction} (ab : Equiv a b) (bc : Equiv b c) : Equiv a c := by
  apply Int.eq_of_mul_eq_mul_right (a := (b.den : Int)) (by have := b.den_pos; omega)
  change (a.num * (c.den : Int)) * b.den = (c.num * (a.den : Int)) * b.den
  calc
    _ = (a.num * (b.den : Int)) * c.den := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (b.num * (a.den : Int)) * c.den := congrArg (fun x => x * (c.den : Int)) ab
    _ = (b.num * (c.den : Int)) * a.den := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (c.num * (b.den : Int)) * a.den := congrArg (fun x => x * (a.den : Int)) bc
    _ = _ := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem lt_trans {a b c : Fraction} (ab : Lt a b) (bc : Lt b c) : Lt a c := by
  apply cancel_lt b.den_pos
  have h₁ := Int.mul_lt_mul_of_pos_right ab c.den_pos
  have h₂ := Int.mul_lt_mul_of_pos_right bc a.den_pos
  have eq : (b.num * (a.den : Int)) * c.den = (b.num * (c.den : Int)) * a.den := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [eq] at h₁
  have h := Int.lt_trans h₁ h₂
  simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using h

theorem lt_left {a b c : Fraction} (eq : Equiv a b) (h : Lt a c) : Lt b c := by
  have scaled := Int.mul_lt_mul_of_pos_right h b.den_pos
  have lhs : (a.num * (c.den : Int)) * b.den = (b.num * (c.den : Int)) * a.den := by
    calc
      _ = (a.num * (b.den : Int)) * c.den := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (b.num * (a.den : Int)) * c.den := congrArg (fun x => x * (c.den : Int)) eq
      _ = _ := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have rhs : (c.num * (a.den : Int)) * b.den = (c.num * (b.den : Int)) * a.den := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [lhs, rhs] at scaled
  exact cancel_lt a.den_pos scaled

theorem lt_right {a b c : Fraction} (eq : Equiv b c) (h : Lt a b) : Lt a c := by
  have scaled := Int.mul_lt_mul_of_pos_right h c.den_pos
  have lhs : (a.num * (b.den : Int)) * c.den = (a.num * (c.den : Int)) * b.den := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have rhs : (b.num * (a.den : Int)) * c.den = (c.num * (a.den : Int)) * b.den := by
    calc
      _ = (b.num * (c.den : Int)) * a.den := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (c.num * (b.den : Int)) * a.den := congrArg (fun x => x * (a.den : Int)) eq
      _ = _ := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [lhs, rhs] at scaled
  exact cancel_lt b.den_pos scaled

def setoid : Setoid Fraction where
  r := Equiv
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => equiv_trans h h'⟩

def mediant (a b : Fraction) : Fraction :=
  ⟨a.num + b.num, a.den + b.den, by have := a.positive; omega⟩

theorem mediant_between (a b : Fraction) (h : Lt a b) :
    Lt a (mediant a b) ∧ Lt (mediant a b) b := by
  change a.num * (b.den : Int) < b.num * (a.den : Int) at h
  constructor
  · change a.num * ((a.den + b.den : Nat) : Int) < (a.num + b.num) * (a.den : Int)
    rw [Int.natCast_add, Int.mul_add, Int.add_mul]
    omega
  · change (a.num + b.num) * (b.den : Int) < b.num * ((a.den + b.den : Nat) : Int)
    rw [Int.natCast_add, Int.mul_add, Int.add_mul]
    omega

def above (a : Fraction) : Fraction := ⟨a.num + a.den, a.den, a.positive⟩

theorem lt_above (a : Fraction) : Lt a (above a) := by
  have pos := Int.mul_pos a.den_pos a.den_pos
  change a.num * (a.den : Int) < (a.num + (a.den : Int)) * a.den
  rw [Int.add_mul]
  omega

def intCode : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

theorem intCode_injective (a b : Int) (h : intCode a = intCode b) : a = b := by
  cases a <;> cases b <;> simp only [intCode] at h <;> congr 1 <;> omega

def code (a : Fraction) : Nat := natPair (intCode a.num) a.den

theorem code_injective (a b : Fraction) (h : code a = code b) : a = b := by
  have parts := natPair_injective h
  have hn := intCode_injective a.num b.num parts.1
  rcases a with ⟨an, ad, ha⟩
  rcases b with ⟨bn, bd, hb⟩
  dsimp at hn
  have hd : ad = bd := parts.2
  cases hn
  cases hd
  rfl

end Fraction

def Rational := Quotient Fraction.setoid

namespace Rational

def mk (a : Fraction) : Rational := Quotient.mk Fraction.setoid a

def lt : Rational → Rational → Prop :=
  Quotient.lift₂ Fraction.Lt (fun _ _ _ _ ha hb =>
    propext ⟨fun h => Fraction.lt_right hb (Fraction.lt_left ha h),
      fun h => Fraction.lt_right hb.symm (Fraction.lt_left ha.symm h)⟩)

theorem irrefl (a : Rational) : ¬ lt a a := by
  induction a using Quotient.ind with
  | _ a => exact Int.lt_irrefl _

theorem trans {a b c : Rational} (h : lt a b) (h' : lt b c) : lt a c := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ a b c => exact Fraction.lt_trans h h'

theorem compare (a b : Rational) : lt a b ∨ a = b ∨ lt b a := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    have h : a.num * (b.den : Int) < b.num * (a.den : Int) ∨
        a.num * (b.den : Int) = b.num * (a.den : Int) ∨
        b.num * (a.den : Int) < a.num * (b.den : Int) := by omega
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Quotient.sound h))
    · exact Or.inr (Or.inr h)

theorem between (a b : Rational) (h : lt a b) : ∃ c, lt a c ∧ lt c b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b => exact ⟨mk (a.mediant b), Fraction.mediant_between a b h⟩

theorem unbounded_above (a : Rational) : ∃ b, lt a b := by
  induction a using Quotient.ind with
  | _ a => exact ⟨mk a.above, a.lt_above⟩

def order : DenseHeightOrder Rational where
  lt := lt
  irrefl := irrefl
  trans := trans
  compare := compare
  between := between

noncomputable def representative (a : Rational) : Fraction :=
  Classical.choose (Quotient.exists_rep a)

theorem representative_eq (a : Rational) : mk (representative a) = a :=
  Classical.choose_spec (Quotient.exists_rep a)

noncomputable def code (a : Rational) : Nat := (representative a).code

theorem code_injective (a b : Rational) (h : code a = code b) : a = b := by
  have eq := Fraction.code_injective (representative a) (representative b) h
  exact (representative_eq a).symm.trans ((congrArg mk eq).trans (representative_eq b))

end Rational

namespace Fraction

def below (a : Fraction) : Fraction := ⟨a.num - a.den, a.den, a.positive⟩

theorem below_lt (a : Fraction) : Lt (below a) a := by
  have positive := Int.mul_pos a.den_pos a.den_pos
  change (a.num - (a.den : Int)) * a.den < a.num * (a.den : Int)
  rw [Int.sub_mul]
  omega

end Fraction

namespace Rational

theorem mk_eq_iff (a b : Fraction) : mk a = mk b ↔ Fraction.Equiv a b := by
  exact ⟨fun h => Quotient.exact h, fun h => @Quotient.sound Fraction Fraction.setoid a b h⟩

theorem mk_lt_iff (a b : Fraction) : lt (mk a) (mk b) ↔ Fraction.Lt a b := Iff.rfl

theorem unbounded_below (a : Rational) : ∃ b, lt b a := by
  induction a using Quotient.ind with
  | _ a => exact ⟨mk a.below, a.below_lt⟩

theorem representative_equiv (a : Fraction) :
    Fraction.Equiv (representative (mk a)) a :=
  (mk_eq_iff _ _).1 (representative_eq (mk a))

end Rational

end PartitionPilot.Compression.RecursiveMaps.RationalHeights

end OAI
