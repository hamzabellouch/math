import OAI.RepresentationTheory.RestrictedTilting.TorusWeightProjection

namespace OAI

namespace FiberFunctorProof
open scoped TensorProduct BigOperators
universe u
variable {k : Type u} [Field k] [Infinite k]
variable {V W : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W]

 
lemma hasWeightsBetween_tensor (ρ : Representation k (SL2 k) V)
    (σ : Representation k (SL2 k) W) (hρ : IsRational k ρ) (hσ : IsRational k σ)
    (a b : ℕ) (hA : HasWeightsBetween ρ (-(a : ℤ)) a)
    (hB : HasWeightsBetween σ (-(b : ℤ)) b) :
    HasWeightsBetween (Representation.tprod ρ σ) (-((a+b : ℕ) : ℤ)) (a+b) := by
  let τ := Representation.tprod ρ σ
  have hτ := IsRational.tensor k ρ σ hρ hσ
  intro n z hn hz
  have hzero (v : V) (w : W) : torusWeightProjection τ hτ n (v ⊗ₜ[k] w) = 0 := by
    obtain ⟨c, hc⟩ := rational_torus_integerExpansions k ρ hρ v
    obtain ⟨d, hd⟩ := rational_torus_integerExpansions k σ hσ w
    have hv : v = ∑ i ∈ c.support, c i := by
      simpa [Finsupp.sum, integerCharacter] using hc 1
    have hw : w = ∑ i ∈ d.support, d i := by
      simpa [Finsupp.sum, integerCharacter] using hd 1
    rw [hv, hw, TensorProduct.sum_tmul]
    simp only [TensorProduct.tmul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hci : c i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hdj : d j ≠ 0 := Finsupp.mem_support_iff.mp hj
    have hciw := integer_coefficient_eigen k ρ v c hc i
    have hdjw := integer_coefficient_eigen k σ w d hd j
    have hiB : -(a : ℤ) ≤ i ∧ i ≤ a := by
      constructor <;> by_contra h <;> apply hci
      · exact hA i (c i) (Or.inl (by omega)) hciw
      · exact hA i (c i) (Or.inr (by omega)) hciw
    have hjB : -(b : ℤ) ≤ j ∧ j ≤ b := by
      constructor <;> by_contra h <;> apply hdj
      · exact hB j (d j) (Or.inl (by omega)) hdjw
      · exact hB j (d j) (Or.inr (by omega)) hdjw
    have hij : ∀ t, τ (diagonalTorus k t) (c i ⊗ₜ[k] d j) =
        integerCharacter k (i+j) t • (c i ⊗ₜ[k] d j) := by
      intro t
      simp only [τ, Representation.tprod_apply, TensorProduct.map_tmul, hciw, hdjw,
        TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
      congr 1
      simp [integerCharacter, zpow_add, mul_comm]
    rw [torusWeightProjection_eigen τ hτ n (i+j) _ hij, ite_eq_right (by omega)]
  have hp (z : V ⊗[k] W) : torusWeightProjection τ hτ n z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul v w => exact hzero v w
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  simpa only [torusWeightProjection_eigen τ hτ n n z hz, ite_true] using hp z
end FiberFunctorProof

end OAI
