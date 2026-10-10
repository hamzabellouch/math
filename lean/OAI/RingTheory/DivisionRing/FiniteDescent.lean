import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Algebra.Ring.Subring.Basic

namespace OAI

/-! Finite-dimensional descent over algebraic central scalar extensions.
This does not construct the Kurosh counterexample.
All coefficient fields and finite spanning spaces below are constructed.
No assumption supplies a descended multiplication table or generating span. -/
noncomputable section
open scoped BigOperators

namespace Kurosh022

/-- Finite descent over an algebraic central scalar extension. The target
algebra may be noncommutative. Coordinates of one are included explicitly,
so the chosen finite basis need not have first vector one. -/
theorem finite_descent_two_generators
    (K F D : Type*) [Field K] [Field F] [Ring D]
    [Algebra K F] [Algebra F D] [Algebra K D] [IsScalarTower K F D]
    [Algebra.IsAlgebraic K F] [FiniteDimensional F D]
    (x y : D) (hgen : Algebra.adjoin K ({x, y} : Set D) = ⊤) :
    FiniteDimensional K D := by
  classical
  let ι := Fin (Module.finrank F D)
  let b : Module.Basis ι F D := Module.finBasis F D
  let C : Finset F :=
    (Finset.univ.image (fun t : ι × ι × ι => b.repr (b t.1 * b t.2.1) t.2.2)) ∪
    (Finset.univ.image (fun i : ι => b.repr (1 : D) i)) ∪
    (Finset.univ.image (fun i : ι => b.repr x i)) ∪
    (Finset.univ.image (fun i : ι => b.repr y i))
  let E : IntermediateField K F := IntermediateField.adjoin K (C : Set F)
  let : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin
    (fun z _ => (Algebra.IsAlgebraic.isAlgebraic (R := K) z).isIntegral)
  have hC (z : F) (hz : z ∈ C) : z ∈ E :=
    IntermediateField.subset_adjoin K (C : Set F) hz
  let V : Submodule E D := Submodule.span E (Set.range b)
  have hb (i : ι) : b i ∈ V := Submodule.subset_span ⟨i, rfl⟩
  have hcoords (z : D) (hz : ∀ i, b.repr z i ∈ E) : z ∈ V := by
    rw [← b.sum_repr z]
    apply V.sum_mem
    intro i _
    change ((⟨b.repr z i, hz i⟩ : E) • b i) ∈ V
    exact V.smul_mem _ (hb i)
  have h1 : (1 : D) ∈ V := hcoords 1 (fun i => hC _ (by simp [C]))
  have hx : x ∈ V := hcoords x (fun i => hC _ (by simp [C]))
  have hy : y ∈ V := hcoords y (fun i => hC _ (by simp [C]))
  have hbb (i j : ι) : b i * b j ∈ V := by
    apply hcoords
    intro k
    apply hC
    simp only [C, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inl ⟨(i, j, k), rfl⟩))
  have hmul (v w : D) (hv : v ∈ V) (hw : w ∈ V) : v * w ∈ V := by
    apply Submodule.span_induction₂
      (p := fun v w _ _ => v * w ∈ V) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hv hw
    · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
      exact hbb i j
    · intro w _
      simp
    · intro v _
      simp
    · intro v w z _ _ _ hvz hwz
      simpa only [add_mul] using V.add_mem hvz hwz
    · intro v w z _ _ _ hvw hvz
      simpa only [mul_add] using V.add_mem hvw hvz
    · intro c v w _ _ hvw
      simpa only [smul_mul_assoc] using V.smul_mem c hvw
    · intro c v w _ _ hvw
      simpa only [mul_smul_comm] using V.smul_mem c hvw
  let B : Subalgebra E D := V.toSubalgebra h1 hmul
  have htop : (⊤ : Subalgebra K D) ≤ B.restrictScalars K := by
    rw [← hgen]
    apply Algebra.adjoin_le
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hx
    · have hzy : z = y := Set.mem_singleton_iff.mp hz
      subst z
      exact hy
  have hV : ∀ z : D, z ∈ V := fun z => htop (show z ∈ (⊤ : Subalgebra K D) from trivial)
  let : Module.Finite E V := Module.Finite.span_of_finite E (Set.finite_range b)
  let : Module.Finite K V := Module.Finite.trans E V
  exact Module.Finite.of_surjective (V.subtype.restrictScalars K)
    (fun z => ⟨⟨z, hV z⟩, rfl⟩)

/-- The actual-center specialization; `Subring.center D` is the native center,
not an abstract nominated scalar field or an assumed finite descent witness. -/
theorem finite_over_actual_center_descends
    (K D : Type*) [Field K] [DivisionRing D] [Algebra K D]
    [Algebra.IsAlgebraic K D] [FiniteDimensional (Subring.center D) D]
    (x y : D) (hgen : Algebra.adjoin K ({x, y} : Set D) = ⊤) :
    FiniteDimensional K D := by
  let : Algebra K (Subring.center D) :=
    inferInstanceAs (Algebra K (Subalgebra.center K D))
  let : IsScalarTower K (Subring.center D) D :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let inclusion : Subring.center D →ₐ[K] D :=
    { (Subring.center D).subtype with commutes' := fun _ => rfl }
  let : Algebra.IsAlgebraic K (Subring.center D) :=
    Algebra.IsAlgebraic.of_injective inclusion Subtype.val_injective
  exact finite_descent_two_generators K (Subring.center D) D x y hgen

end Kurosh022

end

end OAI
