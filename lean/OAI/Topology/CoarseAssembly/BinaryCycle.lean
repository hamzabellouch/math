import OAI.Topology.CoarseAssembly.BinaryHilbertSum
import OAI.Topology.CoarseAssembly.AnalyticKHomology

namespace OAI

/-! # Actual direct sums of odd Fredholm modules -/

noncomputable section

namespace CoarseAssembly.Analytic

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

def OddCycle.binarySum (c d : OddCycle A) : OddCycle A where
  space := binaryHilbertSpace c.space d.space
  representation := (binaryBlockHom c.space d.space).toNonUnitalStarAlgHom.comp
    (c.representation.prod d.representation)
  operator := binaryBlock c.space d.space c.operator d.operator
  commutator_compact a := by
    change IsCompactOperator
      (binaryBlock c.space d.space c.operator d.operator *
        binaryBlock c.space d.space (c.representation a) (d.representation a) -
      binaryBlock c.space d.space (c.representation a) (d.representation a) *
        binaryBlock c.space d.space c.operator d.operator)
    rw [← binaryBlock_mul, ← binaryBlock_mul, ← binaryBlock_sub]
    exact binaryBlock_compact _ _ (c.commutator_compact a) (d.commutator_compact a)
  square_compact a := by
    change IsCompactOperator
      ((binaryBlock c.space d.space c.operator d.operator *
          binaryBlock c.space d.space c.operator d.operator - 1) *
        binaryBlock c.space d.space (c.representation a) (d.representation a) :
        End (binaryHilbertSpace c.space d.space))
    rw [← binaryBlock_mul, ← binaryBlock_one c.space d.space, ← binaryBlock_sub,
      ← binaryBlock_mul]
    exact binaryBlock_compact _ _ (c.square_compact a) (d.square_compact a)
  adjoint_compact a := by
    change IsCompactOperator
      ((star (binaryBlock c.space d.space c.operator d.operator) -
        binaryBlock c.space d.space c.operator d.operator) *
      binaryBlock c.space d.space (c.representation a) (d.representation a))
    rw [← binaryBlock_star, ← binaryBlock_sub, ← binaryBlock_mul]
    exact binaryBlock_compact _ _ (c.adjoint_compact a) (d.adjoint_compact a)

def OddCycle.binarySum_decomposition (c d : OddCycle A) : c.IsDirectSum d (c.binarySum d) where
  left := binaryLeft c.space d.space
  right := binaryRight c.space d.space
  orthogonal := binaryLeft_right c.space d.space
  exhaustive := binary_exhaustive c.space d.space
  representation_eq _ := rfl
  operator_eq := rfl

theorem binarySum_class (c d : OddCycle A) :
    cycleClass A (c.binarySum d) = cycleClass A c + cycleClass A d :=
  directSum_eq c d _ (c.binarySum_decomposition d)

end CoarseAssembly.Analytic

end

end OAI
