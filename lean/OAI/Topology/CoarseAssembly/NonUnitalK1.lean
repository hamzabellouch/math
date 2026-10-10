import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.TopologicalK1
import Mathlib.Analysis.CStarAlgebra.Spectrum

namespace OAI

/-!
# K₁ of nonunital C*-algebras

The group is the kernel of the scalar projection from the unitization.
Nonunital star homomorphisms induce actual maps of these kernels, preserving
composition. This is the target functor for the reduced Roe assembly map.
-/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

open scoped CStarAlgebra

universe u v w

variable (A : Type u) [NonUnitalCStarAlgebra A]

variable {A} {B : Type v} [NonUnitalCStarAlgebra B]
variable {C : Type w} [NonUnitalCStarAlgebra C]

@[simp] theorem scalarMap_matrixClass {n : ℕ}
    (g : TopologicalK1.InvertibleMatrix (Unitization ℂ A) n) :
    scalarMap A (TopologicalK1.matrixClass (Unitization ℂ A) g) =
      TopologicalK1.matrixClass ℂ
        (TopologicalK1.mapGL (Unitization.fstHom ℂ A).toRingHom n g) :=
  TopologicalK1.map_matrixClass _ _ _

@[simp] theorem unitizationMap_matrixClass (φ : A →⋆ₙₐ[ℂ] B) {n : ℕ}
    (g : TopologicalK1.InvertibleMatrix (Unitization ℂ A) n) :
    unitizationMap φ (TopologicalK1.matrixClass (Unitization ℂ A) g) =
      TopologicalK1.matrixClass (Unitization ℂ B)
        (TopologicalK1.mapGL (Unitization.starMap φ).toRingHom n g) :=
  TopologicalK1.map_matrixClass _ _ _

theorem scalarMap_natural (φ : A →⋆ₙₐ[ℂ] B) :
    (scalarMap B).comp (unitizationMap φ) = scalarMap A := by
  apply TopologicalK1.hom_ext
  intro n g
  simp only [AddMonoidHom.comp_apply, unitizationMap_matrixClass, scalarMap_matrixClass]
  congr 1
  apply Units.ext
  apply Matrix.ext
  intro i j
  change (Unitization.starMap φ ((g : Matrix (Fin n) (Fin n) (Unitization ℂ A)) i j)).fst =
    ((g : Matrix (Fin n) (Fin n) (Unitization ℂ A)) i j).fst
  simp [Unitization.starMap_apply, Unitization.algebraMap_eq_inl]

@[simp] theorem map_coe (φ : A →⋆ₙₐ[ℂ] B) (x : K1 A) :
    (map φ x : TopologicalK1.Group (Unitization ℂ B)) = unitizationMap φ x := rfl

theorem unitizationMap_comp (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] C) :
    unitizationMap (ψ.comp φ) = (unitizationMap ψ).comp (unitizationMap φ) := by
  apply TopologicalK1.hom_ext
  intro n g
  simp only [AddMonoidHom.comp_apply, unitizationMap_matrixClass]
  congr 1
  apply Units.ext
  apply Matrix.ext
  intro i j
  change Unitization.starMap (ψ.comp φ) ((g : Matrix (Fin n) (Fin n) (Unitization ℂ A)) i j) =
    Unitization.starMap ψ (Unitization.starMap φ ((g : Matrix (Fin n) (Fin n) (Unitization ℂ A)) i j))
  exact DFunLike.congr_fun (Unitization.starMap_comp (φ := φ) (ψ := ψ)) _

theorem map_comp (φ : A →⋆ₙₐ[ℂ] B) (ψ : B →⋆ₙₐ[ℂ] C) :
    map (ψ.comp φ) = (map ψ).comp (map φ) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (unitizationMap_comp φ ψ) (x : TopologicalK1.Group (Unitization ℂ A))

@[simp] theorem unitizationMap_id :
    unitizationMap (NonUnitalStarAlgHom.id ℂ A) =
      AddMonoidHom.id (TopologicalK1.Group (Unitization ℂ A)) := by
  apply TopologicalK1.hom_ext
  intro n g
  simp only [unitizationMap_matrixClass, AddMonoidHom.id_apply]
  congr 1
  apply Units.ext
  apply Matrix.ext
  intro i j
  change Unitization.starMap (NonUnitalStarAlgHom.id ℂ A) ((g : Matrix (Fin n) (Fin n) (Unitization ℂ A)) i j) = _
  simp

@[simp] theorem map_id : map (NonUnitalStarAlgHom.id ℂ A) = AddMonoidHom.id (K1 A) := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (unitizationMap_id (A := A)) (x : TopologicalK1.Group (Unitization ℂ A))

end CoarseAssembly.OperatorKTheory

end

end OAI
