import OAI.Topology.CoarseAssembly.RelativeTwoByTwo

namespace OAI

/-! # Relative two-by-two classes and their actual norm homotopies -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

open Analytic

variable {R : Type*} [CStarAlgebra R]
variable (S : NonUnitalStarSubalgebra ℂ R) [hS : IsClosed (S : Set R)]

def relativeTwoMatrix (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) :
    TopologicalK1.InvertibleMatrix (Unitization ℂ S) 2 :=
  Unitary.toUnits (relativeTwoUnitary S u hu)

theorem relativeTwoMatrix_scalar (u : unitary (Matrix (Fin 2) (Fin 2) R)) (hu) :
    TopologicalK1.mapGL (Unitization.fstHom ℂ S).toRingHom 2 (relativeTwoMatrix S u hu) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [TopologicalK1.mapGL, relativeTwoMatrix, relativeTwoUnitary, matrixTwoStarHom]
  · simp [TopologicalK1.mapGL, relativeTwoMatrix, relativeTwoUnitary, matrixTwoStarHom,
      hij]

def relativeTwoClass (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) : K1 S :=
  ⟨TopologicalK1.matrixClass (Unitization ℂ S) (relativeTwoMatrix S u hu), by
    rw [AddMonoidHom.mem_ker, scalarMap_matrixClass, relativeTwoMatrix_scalar,
      TopologicalK1.matrixClass_one]⟩

variable {P : Type*} [TopologicalSpace P]

theorem continuous_relativeTwoUnitary (u : P → unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ p i j, ((u p : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S)
    (hc : Continuous (fun p => (u p : Matrix (Fin 2) (Fin 2) R))) :
    Continuous (fun p => (relativeTwoUnitary S (u p) (hu p)).val) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hp : Continuous (fun p => relativeTwoPart S (u p) (hu p) i j) :=
    (((continuous_apply j).comp ((continuous_apply i).comp hc)).sub continuous_const).subtype_mk
      (fun p => hu p i j)
  exact continuous_const.add (Unitization.continuous_inr.comp hp)

theorem continuous_relativeTwoMatrix (u : P → unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ p i j, ((u p : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S)
    (hc : Continuous (fun p => (u p : Matrix (Fin 2) (Fin 2) R))) :
    Continuous (fun p => relativeTwoMatrix S (u p) (hu p)) := by
  apply Units.continuous_iff.mpr
  have hv := continuous_relativeTwoUnitary S u hu hc
  exact ⟨hv, hv.star⟩

theorem relativeTwoClass_homotopy (u : Interval → unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ t i j, ((u t : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S)
    (hc : Continuous (fun t => (u t : Matrix (Fin 2) (Fin 2) R))) :
    relativeTwoClass S (u start) (hu start) = relativeTwoClass S (u finish) (hu finish) := by
  apply Subtype.ext
  exact TopologicalK1.matrixClass_homotopy (fun t => relativeTwoMatrix S (u t) (hu t))
    (continuous_relativeTwoMatrix S u hu hc)

end CoarseAssembly.OperatorKTheory

end

end OAI
