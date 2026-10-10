import OAI.RingTheory.DirectFiniteness.CharacterFormulas

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteBlock
variable {m : Type u_1} {C : Type u_2} [CommGroup C]

/-- The coordinate permutation action in the exact finite auxiliary group. -/
def permAction : Equiv.Perm m →* MulAut (m → C) where
  toFun σ :=
    { toFun := fun w i => w (σ.symm i)
      invFun := fun w i => w (σ i)
      left_inv := by intro w; funext i; simp
      right_inv := by intro w; funext i; simp
      map_mul' := by intro w z; rfl }
  map_one' := by ext w i; rfl
  map_mul' σ τ := by ext w i; rfl

abbrev Auxiliary (m : Type u_3) (C : Type u_4) [CommGroup C] :=
  SemidirectProduct (m → C) (Equiv.Perm m) permAction

instance [Fintype m] [Fintype C] : Fintype (Auxiliary m C) :=
  Fintype.ofEquiv ((m → C) × Equiv.Perm m) SemidirectProduct.equivProd.symm

variable {K : Type u_5} [Field K] [Fintype m] [Fintype C]
variable (ξ : C →* Kˣ)

def coordinate (i : m) : (m → C) →* Kˣ := ξ.comp (Pi.evalMonoidHom _ i)

omit [Fintype m] in
lemma coordinate_ne (hξ : ξ ≠ 1) {i j : m} (hij : i ≠ j) :
    coordinate ξ i ≠ coordinate ξ j := by
  obtain ⟨c,hc⟩ : ∃ c, ξ c ≠ 1 := by
    by_contra! h
    exact hξ (MonoidHom.ext h)
  intro h
  have hh := congrArg (fun χ : (m → C) →* Kˣ => χ (Function.update 1 i c)) h
  simp [coordinate, Function.update_of_ne hij.symm] at hh
  exact hc hh

open CharacterIdempotents

def p (i : m) : MonoidAlgebra K (Auxiliary m C) :=
  pushed SemidirectProduct.inl (coordinate ξ i)

def permElt (σ : Equiv.Perm m) : MonoidAlgebra K (Auxiliary m C) :=
  MonoidAlgebra.of K _ (SemidirectProduct.inr σ)

omit [Fintype m] [Fintype C] in
lemma permElt_inv_mul (σ : Equiv.Perm m) :
    permElt (K := K) (C := C) σ⁻¹ * permElt σ = 1 := by
  simp [permElt, ← MonoidAlgebra.one_def]
omit [Fintype m] [Fintype C] in
lemma permElt_mul_inv (σ : Equiv.Perm m) :
    permElt (K := K) (C := C) σ * permElt σ⁻¹ = 1 := by
  simp [permElt, ← MonoidAlgebra.one_def]

lemma p_ne_zero (hc : (Fintype.card (m → C) : K) ≠ 0) (i : m) : p ξ i ≠ 0 :=
  pushed_ne_zero _ SemidirectProduct.inl_injective _ hc
lemma p_idem (hc : (Fintype.card (m → C) : K) ≠ 0) (i : m) : p ξ i * p ξ i = p ξ i :=
  pushed_idempotent _ _ hc
lemma p_orth (hξ : ξ ≠ 1) {i j : m} (hij : i ≠ j) : p ξ i * p ξ j = 0 :=
  pushed_orthogonal _ _ _ (coordinate_ne ξ hξ hij)

lemma translated (σ : Equiv.Perm m) (i : m) :
    permElt σ * p ξ i * permElt σ⁻¹ = p ξ (σ i) := by
  unfold p
  rw [pushed_eq_sum, pushed_eq_sum]
  simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  calc
    _ = ∑ w : m → C, MonoidAlgebra.single (SemidirectProduct.inl (permAction σ w))
        ((coordinate ξ (σ i) (permAction σ w) : K)⁻¹) := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [permElt, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
        one_mul, mul_one]
      rw [← SemidirectProduct.inl_aut]
      congr 1
      simp [coordinate, permAction]
    _ = _ := Equiv.sum_comp (permAction σ).toEquiv (fun w : m → C =>
      (MonoidAlgebra.single (SemidirectProduct.inl w : Auxiliary m C)
        ((coordinate ξ (σ i) w : K)⁻¹)))

end KaplanskyCounterexample.FiniteBlock
end

end OAI
