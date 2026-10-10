import Mathlib

namespace OAI

/-! Scalar extension of free algebras and finite support over increasing fields. -/

namespace KuroshConstruction

section ScalarChange

variable {K L M I : Type*} [CommSemiring K] [CommSemiring L] [CommSemiring M]

noncomputable def freeScalarChange (f : K →+* L) : FreeAlgebra K I →+* FreeAlgebra L I := by
  letI := Algebra.compHom (FreeAlgebra L I) f
  exact (FreeAlgebra.lift K (FreeAlgebra.ι L)).toRingHom

@[simp] lemma freeScalarChange_ι (f : K →+* L) (i : I) :
    freeScalarChange f (FreeAlgebra.ι K i) = FreeAlgebra.ι L i := by
  let := Algebra.compHom (FreeAlgebra L I) f
  exact FreeAlgebra.lift_ι_apply (R := K) _ i

@[simp] lemma freeScalarChange_algebraMap (f : K →+* L) (c : K) :
    freeScalarChange (I := I) f (algebraMap K (FreeAlgebra K I) c) =
      algebraMap L (FreeAlgebra L I) (f c) := by
  let := Algebra.compHom (FreeAlgebra L I) f
  exact (FreeAlgebra.lift K (FreeAlgebra.ι L)).commutes c

lemma freeScalarChange_comp (f : K →+* L) (g : L →+* M) (p : FreeAlgebra K I) :
    freeScalarChange g (freeScalarChange f p) = freeScalarChange (g.comp f) p := by
  induction p using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 i => simp
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

lemma freeScalarChange_id (p : FreeAlgebra K I) : freeScalarChange (RingHom.id K) p = p := by
  induction p using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 i => simp
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

end ScalarChange

section LimitScalars

variable (K : ℕ → Type*) [∀ i, CommSemiring (K i)]
  (f : ∀ i j, i ≤ j → K i →+* K j) [DirectedSystem K (fun i j h => f i j h)]
  {I : Type*}

lemma freeScalarChange_limit_compatible (i j : ℕ) (h : i ≤ j) (p : FreeAlgebra (K i) I) :
    freeScalarChange (DirectLimit.Ring.of K f j) (freeScalarChange (f i j h) p) =
      freeScalarChange (DirectLimit.Ring.of K f i) p := by
  rw [freeScalarChange_comp]
  have he : (DirectLimit.Ring.of K f j).comp (f i j h) = DirectLimit.Ring.of K f i := by
    ext x
    exact DirectLimit.Ring.of_f h x
  rw [he]

lemma freePolynomial_finite_stage (p : FreeAlgebra (DirectLimit K f) I) :
    ∃ i, ∃ q : FreeAlgebra (K i) I,
      freeScalarChange (DirectLimit.Ring.of K f i) q = p := by
  induction p using FreeAlgebra.induction with
  | grade0 c =>
    obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk f c
    exact ⟨i, algebraMap _ _ x, freeScalarChange_algebraMap _ x⟩
  | grade1 i => exact ⟨0, FreeAlgebra.ι (K 0) i, freeScalarChange_ι _ i⟩
  | mul p q hp hq =>
    obtain ⟨i, p, rfl⟩ := hp
    obtain ⟨j, q, rfl⟩ := hq
    refine ⟨max i j, freeScalarChange (f i (max i j) (le_max_left _ _)) p *
      freeScalarChange (f j (max i j) (le_max_right _ _)) q, ?_⟩
    rw [map_mul, freeScalarChange_limit_compatible, freeScalarChange_limit_compatible]
  | add p q hp hq =>
    obtain ⟨i, p, rfl⟩ := hp
    obtain ⟨j, q, rfl⟩ := hq
    refine ⟨max i j, freeScalarChange (f i (max i j) (le_max_left _ _)) p +
      freeScalarChange (f j (max i j) (le_max_right _ _)) q, ?_⟩
    rw [map_add, freeScalarChange_limit_compatible, freeScalarChange_limit_compatible]

lemma limit_finite_tuple {J : Type*} [Fintype J] (c : J → DirectLimit K f) :
    ∃ n, ∃ a : J → K n, ∀ j, DirectLimit.Ring.of K f n (a j) = c j := by
  classical
  choose i x hx using fun j => DirectLimit.exists_eq_mk f (c j)
  let n := Finset.univ.sup i
  have hin (j : J) : i j ≤ n := Finset.le_sup (f := i) (Finset.mem_univ j)
  refine ⟨n, fun j => f (i j) n (hin j) (x j), fun j => ?_⟩
  rw [DirectLimit.Ring.of_f]
  exact (hx j).symm

end LimitScalars

end KuroshConstruction

end OAI
