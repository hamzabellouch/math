import OAI.RingTheory.DirectFiniteness.ScalarWitnesses

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.MatrixBlock
variable {S : Type u_1} {R : Type u_2} {m : Type u_3} [Ring S] [Ring R] [Fintype m]
variable (f : S →+* R) (q : m → m → R)

def output (X : Matrix m m S) : R := 1 - block f q 1 + block f q X

lemma output_formula (X : Matrix m m S) :
    output f q X = 1 - ∑ i, q i i + ∑ i, ∑ j, f (X i j)*q i j := by
  rw [output,block_one,block]

variable (hqq : ∀ i j k r, q i j * q k r = if j = k then q i r else 0)
variable (hcomm : ∀ x i j, Commute (f x) (q i j))

include hqq hcomm in
theorem prescribed_scalar_products
    (hpure : ∀ x i j, f x * q i j = 0 → x = 0)
    (a b : Matrix m m S) (hab : a * b = 1) (hba : b * a ≠ 1) :
    output f q a * output f q b = 1 ∧ output f q b * output f q a ≠ 1 := by
  let e := block f q 1
  let a' := 1 - e + block f q a
  let b' := 1 - e + block f q b
  have he : e * e = e := by rw [← block_mul f q hqq hcomm, mul_one]
  have hea : e * block f q a = block f q a := by rw [← block_mul f q hqq hcomm, one_mul]
  have hae : block f q a * e = block f q a := by rw [← block_mul f q hqq hcomm, mul_one]
  have heb : e * block f q b = block f q b := by rw [← block_mul f q hqq hcomm, one_mul]
  have hbe : block f q b * e = block f q b := by rw [← block_mul f q hqq hcomm, mul_one]
  have hab' : block f q a * block f q b = e := by rw [← block_mul f q hqq hcomm, hab]
  change a' * b' = 1 ∧ b' * a' ≠ 1
  refine ⟨?_,?_⟩
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

namespace KaplanskyCounterexample.FiniteBlock
variable {K : Type u_4} {C : Type u_5} {m : Type u_6} {L : Type u_7} [Field K] [CommGroup C] [Group L]
variable [Fintype m] [Fintype C]
variable (ξ : C →* Kˣ) (i₀ : m)

def output (a : Matrix m m (MonoidAlgebra K L)) : MonoidAlgebra K (L × Auxiliary m C) :=
  MatrixBlock.output (ProductAlgebras.leftMap (K := K) (G := L) (H := Auxiliary m C)).toRingHom
    (fun i j => ProductAlgebras.rightMap (G := L) (matrixUnit ξ i₀ i j)) a

theorem output_products (hc : (Fintype.card (m → C) : K) ≠ 0) (hξ : ξ ≠ 1)
    (a b : Matrix m m (MonoidAlgebra K L)) (hab : a * b = 1) (hba : b * a ≠ 1) :
    output ξ i₀ a * output ξ i₀ b=1 ∧ output ξ i₀ b*output ξ i₀ a≠1 := by
  let f := (ProductAlgebras.leftMap (K := K) (G := L) (H := Auxiliary m C)).toRingHom
  let q (i j : m) := ProductAlgebras.rightMap (G := L) (matrixUnit ξ i₀ i j)
  have hqq (i j k r : m) : q i j * q k r = if j = k then q i r else 0 := by
    dsimp [q]
    rw [← map_mul, matrixUnit_mul ξ i₀ hc hξ]
    split_ifs <;> simp
  have hcomm (x : MonoidAlgebra K L) (i j : m) : Commute (f x) (q i j) :=
    ProductAlgebras.left_right_commute x _
  have hpure (x : MonoidAlgebra K L) (i j : m) : f x * q i j = 0 → x = 0 := by
    intro he
    by_contra hx
    exact ProductAlgebras.product_ne_zero hx (matrixUnit_ne_zero ξ i₀ hc i j) he
  exact MatrixBlock.prescribed_scalar_products f q hqq hcomm hpure a b hab hba

end KaplanskyCounterexample.FiniteBlock
end

end OAI
