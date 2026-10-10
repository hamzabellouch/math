import OAI.RingTheory.DirectFiniteness.ProductAlgebras

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteBlock
variable {K : Type u_1} {C : Type u_2} {m : Type u_3} {L : Type u_4} [Field K] [CommGroup C] [Group L]
variable [Fintype m] [Fintype C]
variable (ξ : C →* Kˣ) (i₀ : m)

def matrixUnit (i j : m) : MonoidAlgebra K (Auxiliary m C) :=
  TranslatedUnits.unit (fun i => permElt (Equiv.swap i₀ i))
    (fun i => permElt (Equiv.swap i₀ i)⁻¹) (p ξ i₀) i j

lemma matrixUnit_diag (i : m) : matrixUnit ξ i₀ i i = p ξ i := by
  simpa only [matrixUnit, TranslatedUnits.unit, Equiv.swap_apply_left] using
    translated ξ (Equiv.swap i₀ i) i₀

lemma matrixUnit_mul (hc : (Fintype.card (m → C) : K) ≠ 0) (hξ : ξ ≠ 1)
    (i j k r : m) :
    matrixUnit ξ i₀ i j * matrixUnit ξ i₀ k r =
      if j = k then matrixUnit ξ i₀ i r else 0 := by
  apply TranslatedUnits.products _ _ _
    (fun i => permElt_inv_mul (Equiv.swap i₀ i)) (p_idem ξ hc i₀)
  intro j k hjk
  change matrixUnit ξ i₀ j j * matrixUnit ξ i₀ k k = 0
  rw [matrixUnit_diag, matrixUnit_diag]
  exact p_orth ξ hξ hjk

lemma matrixUnit_ne_zero (hc : (Fintype.card (m → C) : K) ≠ 0) (i j : m) :
    matrixUnit ξ i₀ i j ≠ 0 :=
  TranslatedUnits.unit_ne_zero _ _ _ (fun i => permElt_inv_mul (Equiv.swap i₀ i))
    (p_ne_zero ξ hc i₀) i j

include i₀ in

theorem scalar_witnesses (hc : (Fintype.card (m → C) : K) ≠ 0) (hξ : ξ ≠ 1)
    (a b : Matrix m m (MonoidAlgebra K L)) (hab : a * b = 1) (hba : b * a ≠ 1) :
    ∃ a' b' : MonoidAlgebra K (L × Auxiliary m C), a' * b' = 1 ∧ b' * a' ≠ 1 := by
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
  exact MatrixBlock.scalar_witnesses f q hqq hcomm hpure a b hab hba

end KaplanskyCounterexample.FiniteBlock
end

end OAI
