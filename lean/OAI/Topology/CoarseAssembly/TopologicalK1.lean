import OAI.Topology.CoarseAssembly.Definitions
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.CStarAlgebra.Unitization
import OAI.Topology.CoarseAssembly.FredholmModule

namespace OAI

/-!
# Topological K₁ from stable invertible matrices

The unital group is presented by invertible finite matrices, with the actual
matrix-product, stabilization and continuous-path relations. The nonunital
group will be the kernel of the scalar-quotient map on the unitization.
These definitions keep the analytic assembly target tied to its algebra.
-/

noncomputable section

namespace CoarseAssembly.TopologicalK1

open CoarseAssembly.Analytic (Interval start finish)

universe u v w

variable (R : Type u) [Ring R] [TopologicalSpace R]

variable {R}

theorem relation_zero {z : FreeAbelianGroup (StableGL R)} (h : Relation R z) :
    (QuotientAddGroup.mk z : Group R) = 0 :=
  (QuotientAddGroup.eq_zero_iff z).2 (AddSubgroup.subset_closure h)

theorem matrixClass_mul {n : ℕ} (g h : InvertibleMatrix R n) :
    matrixClass R (g * h) = matrixClass R g + matrixClass R h := by
  apply sub_eq_zero.mp
  simpa only [matrixClass, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add] using
    relation_zero (.mul g h)

theorem matrixClass_stabilize {n : ℕ} (g : InvertibleMatrix R n) (h : InvertibleMatrix R (n + 1))
    (hs : IsStabilization R g h) : matrixClass R g = matrixClass R h := by
  apply sub_eq_zero.mp
  simpa only [matrixClass, QuotientAddGroup.mk_sub] using relation_zero (.stabilize g h hs)

theorem matrixClass_homotopy {n : ℕ} (c : Interval → InvertibleMatrix R n) (hc : Continuous c) :
    matrixClass R (c start) = matrixClass R (c finish) := by
  apply sub_eq_zero.mp
  simpa only [matrixClass, QuotientAddGroup.mk_sub] using relation_zero (.homotopy c hc)

@[simp] theorem matrixClass_one (n : ℕ) : matrixClass R (1 : InvertibleMatrix R n) = 0 := by
  have h := matrixClass_mul (1 : InvertibleMatrix R n) 1
  simp only [one_mul] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

variable {S : Type v} {T : Type w} [Ring S] [TopologicalSpace S] [Ring T] [TopologicalSpace T]

theorem continuous_mapGL (φ : R →+* S) (hφ : Continuous φ) (n : ℕ) :
    Continuous (mapGL φ n) := by
  apply Continuous.units_map
  exact continuous_pi (fun i => continuous_pi (fun j =>
    hφ.comp ((continuous_apply j).comp (continuous_apply i))))

omit [TopologicalSpace R] [TopologicalSpace S] in
theorem mapGL_stabilize (φ : R →+* S) {n : ℕ} (g : InvertibleMatrix R n) (h : InvertibleMatrix R (n + 1))
    (hs : IsStabilization R g h) : IsStabilization S (mapGL φ n g) (mapGL φ (n + 1) h) := by
  have heq := congrArg (fun M => Matrix.map M φ) hs
  simpa [IsStabilization, mapGL, Matrix.fromBlocks_map, Matrix.submatrix_map] using heq

theorem mapFree_relation (φ : R →+* S) (hφ : Continuous φ)
    {z : FreeAbelianGroup (StableGL R)} (hz : Relation R z) : mapFree φ z = 0 := by
  cases hz with
  | mul g h =>
    simpa [mapFree] using sub_eq_zero.mpr (matrixClass_mul (mapGL φ _ g) (mapGL φ _ h))
  | stabilize g h hs =>
    simpa [mapFree] using sub_eq_zero.mpr
      (matrixClass_stabilize _ _ (mapGL_stabilize φ g h hs))
  | homotopy c hc =>
    simpa [mapFree] using sub_eq_zero.mpr
      (matrixClass_homotopy (fun t => mapGL φ _ (c t)) ((continuous_mapGL φ hφ _).comp hc))

@[simp] theorem map_matrixClass (φ : R →+* S) (hφ : Continuous φ) {n : ℕ} (g : InvertibleMatrix R n) :
    map φ hφ (matrixClass R g) = matrixClass S (mapGL φ n g) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem hom_ext {D : Type*} [AddCommGroup D] (f g : Group R →+ D)
    (h : ∀ n (a : InvertibleMatrix R n), f (matrixClass R a) = g (matrixClass R a)) : f = g := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  rintro ⟨n, a⟩
  exact h n a

omit [TopologicalSpace R] in
@[simp] theorem mapGL_id {n : ℕ} (g : InvertibleMatrix R n) : mapGL (RingHom.id R) n g = g := by
  apply Units.ext
  rfl

@[simp] theorem map_id : map (RingHom.id R) continuous_id = AddMonoidHom.id (Group R) := by
  apply hom_ext
  intro n a
  simp

omit [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace T] in
theorem mapGL_comp (φ : R →+* S) (ψ : S →+* T) {n : ℕ} (g : InvertibleMatrix R n) :
    mapGL (ψ.comp φ) n g = mapGL ψ n (mapGL φ n g) := by
  apply Units.ext
  rfl

theorem map_comp (φ : R →+* S) (ψ : S →+* T) (hφ : Continuous φ) (hψ : Continuous ψ) :
    map (ψ.comp φ) (hψ.comp hφ) = (map ψ hψ).comp (map φ hφ) := by
  apply hom_ext
  intro n a
  simp [mapGL_comp]

end CoarseAssembly.TopologicalK1

end

end OAI
