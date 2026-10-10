import Mathlib
import OAI.RingTheory.Multiplicity.TensorConductor

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech.NormalizedLength.Tower
variable {R : Type*} [CommRing R] (T : Tower R)

section Bound
variable {B N : Type*} [CommRing B] [Algebra R B]
  [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]

lemma length_le_quotient_mul (I : Ideal B) (hI : I ≤ Module.annihilator B N)
    {b : ℕ} (f : (Fin b → B) →ₗ[B] N) (hf : Function.Surjective f) :
    T.length N ≤ (b : ℝ≥0∞) * T.length (B ⧸ I) := by
  classical
  let P := Submodule.pi Set.univ (fun _ : Fin b => I)
  have hP : P ≤ f.ker := by
    intro x hx
    change f x = 0
    rw [pi_eq_sum_univ x, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    exact Module.mem_annihilator.mp (hI (hx i (Set.mem_univ i))) _
  let q := P.liftQ f hP
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y,rfl⟩ := hf x
    exact ⟨P.mkQ y,rfl⟩
  calc
    T.length N ≤ T.length ((Fin b → B) ⧸ P) :=
      T.length_le_of_surjective (q.restrictScalars R) hq
    _ = T.length (Fin b → B ⧸ I) :=
      T.length_eq_of_equiv ((Submodule.quotientPi (fun _ : Fin b => I)).restrictScalars R)
    _ = _ := by
      suffices hlength : ∀ count : ℕ,
          T.length (Fin count → B ⧸ I) = count * T.length (B ⧸ I) from hlength b
      intro count
      induction count with
      | zero => simp [T.length_zero]
      | succ count ih =>
        rw [T.length_eq_of_equiv
          (Fin.consLinearEquiv R (fun _ : Fin (count + 1) => B ⧸ I)).symm,
          T.length_prod, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

lemma length_scalar_cokernel_eq (g : R) :
    T.length (N ⧸ (LinearMap.lsmul R N g).range) =
      T.length (N ⧸ (LinearMap.lsmul B N (algebraMap R B g)).range) := by
  let P := (LinearMap.lsmul B N (algebraMap R B g)).range
  have hp : (LinearMap.lsmul R N g).range = P.restrictScalars R := by
    ext x
    dsimp [P]
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.restrictScalars_mem]
    simp only [IsScalarTower.algebraMap_smul]
  exact T.length_eq_of_equiv ((Submodule.quotEquivOfEq _ _ hp).trans
    (Submodule.Quotient.restrictScalarsEquiv R P))

lemma length_scalar_cokernel_le (I : Ideal B) (hI : I ≤ Module.annihilator B N)
    {b : ℕ} (f : (Fin b → B) →ₗ[B] N) (hf : Function.Surjective f) (g : R) :
    T.length (N ⧸ (LinearMap.lsmul R N g).range) ≤
      (b : ℝ≥0∞) * T.length (B ⧸ (I ⊔ Ideal.span {algebraMap R B g})) := by
  rw [T.length_scalar_cokernel_eq (B := B)]
  let P := (LinearMap.lsmul B N (algebraMap R B g)).range
  let q := P.mkQ.comp f
  have hq : Function.Surjective q := P.mkQ_surjective.comp hf
  apply T.length_le_quotient_mul (I ⊔ Ideal.span {algebraMap R B g}) _ q hq
  apply sup_le
  · intro a ha
    apply Module.mem_annihilator.mpr
    intro x
    obtain ⟨y,rfl⟩ := P.mkQ_surjective x
    rw [← map_smul, Module.mem_annihilator.mp (hI ha) y, map_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    apply Module.mem_annihilator.mpr
    intro x
    obtain ⟨y,rfl⟩ := P.mkQ_surjective x
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    exact ⟨y,rfl⟩
end Bound
end Lech.NormalizedLength.Tower

end

end OAI
