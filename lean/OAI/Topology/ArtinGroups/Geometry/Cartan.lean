import Mathlib
import OAI.Topology.ArtinGroups.Geometry.TrigPhasePower

namespace OAI

namespace HarmonicArtin.Geometric

open scoped Classical

variable {S W : Type*} [DecidableEq S] [Group W]

noncomputable def cartan (M : CoxeterMatrix S) : Matrix S S ℝ := fun i j =>
  if i=j then 2 else if M i j=0 then -2 else -2*Real.cos (Real.pi/(M i j:ℝ))

@[simp] lemma cartan_diag (M : CoxeterMatrix S) (i : S) : cartan M i i=2 := by
  simp [cartan]

lemma cartan_symm (M : CoxeterMatrix S) (i j : S) : cartan M i j=cartan M j i := by
  simp only [cartan, M.symmetric i j, eq_comm]

variable [Fintype S]

noncomputable def rootRow (M : CoxeterMatrix S) (i : S) : (S → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp (Matrix.mulVecLin (cartan M))

@[simp] lemma rootRow_apply (M : CoxeterMatrix S) (i : S) (x : S → ℝ) :
    rootRow M i x = (Matrix.mulVec (cartan M) x) i := rfl

@[simp] lemma rootRow_single (M : CoxeterMatrix S) (i j : S) :
    rootRow M i (Pi.single j 1) = cartan M i j := by
  simp [Matrix.mulVec_single]

noncomputable def simpleReflection (M : CoxeterMatrix S) (i : S) :
    (S → ℝ) ≃ₗ[ℝ] (S → ℝ) :=
  reflection (Pi.single i 1) (rootRow M i) (by simp)

@[simp] lemma simpleReflection_apply (M : CoxeterMatrix S) (i : S) (x : S → ℝ) :
    simpleReflection M i x = x - (Matrix.mulVec (cartan M) x) i • Pi.single i 1 := rfl

lemma simpleReflection_squared (M : CoxeterMatrix S) (i : S) :
    simpleReflection M i * simpleReflection M i = 1 := by
  apply LinearEquiv.ext
  intro x
  exact reflect_involutive (Pi.single i 1) (rootRow M i) (by simp) x

lemma simpleReflection_isLiftable (M : CoxeterMatrix S) :
    CoxeterMatrix.IsLiftable M (simpleReflection M) := by
  intro i j
  by_cases hij : i=j
  · subst j
    rw [M.diagonal, pow_one, simpleReflection_squared]
  by_cases hm0 : M i j=0
  · rw [hm0,pow_zero]
  have hm : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
  exact reflection_pair_order (Pi.single i 1) (Pi.single j 1) (rootRow M i) (rootRow M j)
    (by simp) (by simp) (M i j) hm
    (by simp [cartan,hij,hm0])
    (by simp [cartan,Ne.symm hij,← M.symmetric i j,hm0])

noncomputable def representation {M : CoxeterMatrix S} (cs : CoxeterSystem M W) :
    W →* ((S → ℝ) ≃ₗ[ℝ] (S → ℝ)) :=
  cs.lift ⟨simpleReflection M, simpleReflection_isLiftable M⟩

@[simp] lemma representation_simple {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (i : S) :
    representation cs (cs.simple i)=simpleReflection M i := cs.lift_apply_simple _ i

lemma simple_injective {M : CoxeterMatrix S} (cs : CoxeterSystem M W) :
    Function.Injective cs.simple := by
  intro i j h
  by_contra hij
  have hh := congrArg (fun w => representation cs w (Pi.single i 1) i) h
  simp only [representation_simple,simpleReflection_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Pi.single_eq_same] at hh
  have hji : (Pi.single j (1:ℝ) : S → ℝ) i = 0 := Pi.single_eq_of_ne hij 1
  have hrow : (Matrix.mulVec (cartan M) (Pi.single i (1:ℝ))) i=2 := by simp [Matrix.mulVec_single]
  rw [hji,hrow] at hh
  norm_num at hh

end HarmonicArtin.Geometric

end OAI
