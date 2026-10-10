import OAI.RingTheory.DirectFiniteness.TranslatedUnits

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.MatrixBlock
variable {S : Type u_1} {R : Type u_2} {m : Type u_3} [Ring S] [Ring R] [Fintype m]
variable (f : S →+* R) (q : m → m → R)

def block (X : Matrix m m S) : R := ∑ i, ∑ j, f (X i j) * q i j

lemma block_zero : block f q 0 = 0 := by simp [block]
lemma block_add (X Y : Matrix m m S) : block f q (X + Y) = block f q X + block f q Y := by
  simp [block, add_mul, Finset.sum_add_distrib]
lemma block_sub (X Y : Matrix m m S) : block f q (X - Y) = block f q X - block f q Y := by
  simp [block, sub_mul, Finset.sum_sub_distrib]
lemma block_one : block f q 1 = ∑ i, q i i := by
  simp [block, Matrix.one_apply, apply_ite]

variable (hqq : ∀ i j k r, q i j * q k r = if j = k then q i r else 0)
variable (hcomm : ∀ x i j, Commute (f x) (q i j))
include hqq hcomm

lemma block_mul (X Y : Matrix m m S) : block f q (X * Y) = block f q X * block f q Y := by
  have hterm (i j k r : m) :
      (f (X i j) * q i j) * (f (Y k r) * q k r) =
        if j = k then f (X i j * Y k r) * q i r else 0 := by
    calc
      _ = f (X i j * Y k r) * (q i j * q k r) := by
        rw [map_mul, ← mul_assoc, mul_assoc (f (X i j)),
          (hcomm (Y k r) i j).eq.symm]
        simp only [mul_assoc]
      _ = _ := by rw [hqq]; split_ifs <;> simp
  have hmulij (i j : m) : (f (X i j) * q i j) * block f q Y =
      ∑ r, f (X i j * Y j r) * q i r := by
    simp only [block, Finset.mul_sum, hterm]
    rw [Finset.sum_comm]
    simp
  symm
  calc
    block f q X * block f q Y = ∑ i, ∑ j, (f (X i j) * q i j) * block f q Y := by
      change (∑ i, ∑ j, f (X i j) * q i j) * block f q Y = _
      simp only [Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ r, f (X i j * Y j r) * q i r := by simp_rw [hmulij]
    _ = block f q (X * Y) := by
      simp only [block, Matrix.mul_apply, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

lemma block_sandwich (X : Matrix m m S) (i j : m) :
    q i i * block f q X * q j j = f (X i j) * q i j := by
  have hterm (k r : m) : q i i * (f (X k r) * q k r) * q j j =
      if i = k then if r = j then f (X k r) * q i j else 0 else 0 := by
    calc
      _ = f (X k r) * (q i i * q k r * q j j) := by
        rw [← mul_assoc, (hcomm (X k r) i i).eq.symm]
        simp only [mul_assoc]
      _ = _ := by
        by_cases hik : i = k <;> by_cases hrj : r = j <;>
          simp [hqq, hik, hrj]

  simp only [block, Finset.mul_sum, Finset.sum_mul, hterm]
  simp

lemma block_injective (hpure : ∀ x i j, f x * q i j = 0 → x = 0) :
    Function.Injective (block f q) := by
  intro X Y h
  have hz : block f q (X - Y) = 0 := by rw [block_sub, h, sub_self]
  have hXY : X - Y = 0 := by
    ext i j
    apply hpure _ i j
    rw [← block_sandwich f q hqq hcomm, hz, mul_zero, zero_mul]
  exact sub_eq_zero.mp hXY

/-- A (possibly nonunital) injective matrix block carries one-sided inverses to
one-sided inverses in the ambient ring using the complementary idempotent. -/
theorem scalar_witnesses
    (hpure : ∀ x i j, f x * q i j = 0 → x = 0)
    (a b : Matrix m m S) (hab : a * b = 1) (hba : b * a ≠ 1) :
    ∃ a' b' : R, a' * b' = 1 ∧ b' * a' ≠ 1 := by
  let e := block f q 1
  let a' := 1 - e + block f q a
  let b' := 1 - e + block f q b
  have he : e * e = e := by rw [← block_mul f q hqq hcomm, mul_one]
  have hea : e * block f q a = block f q a := by rw [← block_mul f q hqq hcomm, one_mul]
  have hae : block f q a * e = block f q a := by rw [← block_mul f q hqq hcomm, mul_one]
  have heb : e * block f q b = block f q b := by rw [← block_mul f q hqq hcomm, one_mul]
  have hbe : block f q b * e = block f q b := by rw [← block_mul f q hqq hcomm, mul_one]
  have hab' : block f q a * block f q b = e := by rw [← block_mul f q hqq hcomm, hab]
  refine ⟨a',b',?_,?_⟩
  · dsimp [a',b']
    noncomm_ring [he, hea, hae, heb, hbe, hab']
  · intro h
    have h' : block f q b * block f q a = e := by
      apply add_left_cancel (a := 1 - e)
      calc
        1 - e + block f q b * block f q a =
            (1 - e + block f q b) * (1 - e + block f q a) := by
          noncomm_ring [he, hea, hae, heb, hbe]
        _ = 1 := h
        _ = 1 - e + e := by abel
    apply hba
    apply block_injective f q hqq hcomm hpure
    rw [block_mul f q hqq hcomm]
    exact h'

end KaplanskyCounterexample.MatrixBlock
end

end OAI
