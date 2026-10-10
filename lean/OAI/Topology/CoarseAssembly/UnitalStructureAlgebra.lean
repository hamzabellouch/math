import OAI.Topology.CoarseAssembly.StructureQuotient
import Mathlib.Analysis.CStarAlgebra.Spectrum

namespace OAI

/-! # The unit of the controlled pseudolocal algebra -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp
local instance : ContinuousStar (Operator X H) := ⟨operator_star_continuous⟩

omit [CompleteSpace H] in
theorem propagationLE_one : PropagationLE 0 (1 : Operator X H) := by
  intro x y hxy
  have hne : x ≠ y := by intro h; simp [h] at hxy
  ext v
  simp [entry_apply, lp.single_apply, hne]

theorem structureGenerator_one : StructureGenerator (1 : Operator X H) := by
  refine ⟨⟨0, le_rfl, propagationLE_one⟩, ?_, ?_⟩
  · intro f
    simp only [one_mul, mul_one, sub_self]
    exact isCompactOperator_zero
  · rw [star_one (Operator X H)]
    intro f
    simp only [one_mul, mul_one, sub_self]
    exact isCompactOperator_zero

theorem structureAlgebra_one : (1 : Operator X H) ∈ structureAlgebra (X := X) (H := H) :=
  (NonUnitalStarSubalgebra.le_topologicalClosure _)
    (NonUnitalStarAlgebra.subset_adjoin ℂ _ (structureGenerator_one (X := X) (H := H)))

/-- The controlled structure algebra with its actual identity operator. -/
def unitalStructureAlgebra : StarSubalgebra ℂ (Operator X H) where
  carrier := structureAlgebra (X := X) (H := H)
  add_mem' := (structureAlgebra (X := X) (H := H)).add_mem
  mul_mem' := (structureAlgebra (X := X) (H := H)).mul_mem
  star_mem' := fun h => star_mem h
  algebraMap_mem' z := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (structureAlgebra (X := X) (H := H)).smul_mem z structureAlgebra_one

theorem unitalStructureAlgebra_closed :
    IsClosed (unitalStructureAlgebra (X := X) (H := H) : Set (Operator X H)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

instance : CompleteSpace (unitalStructureAlgebra (X := X) (H := H)) :=
  unitalStructureAlgebra_closed.completeSpace_coe

instance : CStarAlgebra (unitalStructureAlgebra (X := X) (H := H)) :=
  StarSubalgebra.cstarAlgebra _ (h_closed := unitalStructureAlgebra_closed)

end CoarseAssembly.DiscreteRoe

end

end OAI
