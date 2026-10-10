import OAI.Topology.CoarseAssembly.OrthogonalCoordinates

namespace OAI

/-! # The operator algebra of an orthogonal direct sum -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A] {c d e : OddCycle A}

def OddCycle.IsDirectSum.block (h : c.IsDirectSum d e) (T : End c.space) (S : End d.space) :
    End e.space := operatorConjugation h.left T + operatorConjugation h.right S

theorem OddCycle.IsDirectSum.cross_left (h : c.IsDirectSum d e) (T : End c.space) (S : End d.space) :
    operatorConjugation h.left T * operatorConjugation h.right S = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change h.left (T (h.left.toContinuousLinearMap.adjoint
    (h.right (S (h.right.toContinuousLinearMap.adjoint x))))) = 0
  have hz := DFunLike.congr_fun h.orthogonal (S (h.right.toContinuousLinearMap.adjoint x))
  change h.left.toContinuousLinearMap.adjoint (h.right (S (h.right.toContinuousLinearMap.adjoint x))) = 0 at hz
  rw [hz, map_zero, map_zero]

theorem OddCycle.IsDirectSum.cross_right (h : c.IsDirectSum d e) (T : End c.space) (S : End d.space) :
    operatorConjugation h.right S * operatorConjugation h.left T = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change h.right (S (h.right.toContinuousLinearMap.adjoint
    (h.left (T (h.left.toContinuousLinearMap.adjoint x))))) = 0
  have hz := DFunLike.congr_fun h.orthogonal_reverse (T (h.left.toContinuousLinearMap.adjoint x))
  change h.right.toContinuousLinearMap.adjoint (h.left (T (h.left.toContinuousLinearMap.adjoint x))) = 0 at hz
  rw [hz, map_zero, map_zero]

theorem OddCycle.IsDirectSum.block_mul (h : c.IsDirectSum d e)
    (T T' : End c.space) (S S' : End d.space) :
    h.block T S * h.block T' S' = h.block (T * T') (S * S') := by
  unfold block
  rw [add_mul, mul_add, mul_add, h.cross_left T S', h.cross_right T' S,
    add_zero, zero_add, ← operatorConjugation_mul, ← operatorConjugation_mul]

theorem OddCycle.IsDirectSum.block_add (h : c.IsDirectSum d e)
    (T T' : End c.space) (S S' : End d.space) :
    h.block (T + T') (S + S') = h.block T S + h.block T' S' := by
  change operatorConjugationHom h.left (T + T') + operatorConjugationHom h.right (S + S') = _
  rw [map_add, map_add]
  change (operatorConjugationHom h.left T + operatorConjugationHom h.left T') +
    (operatorConjugationHom h.right S + operatorConjugationHom h.right S') =
    (operatorConjugationHom h.left T + operatorConjugationHom h.right S) +
    (operatorConjugationHom h.left T' + operatorConjugationHom h.right S')
  abel

theorem OddCycle.IsDirectSum.block_smul (h : c.IsDirectSum d e) (z : ℂ)
    (T : End c.space) (S : End d.space) : h.block (z • T) (z • S) = z • h.block T S := by
  change operatorConjugationHom h.left (z • T) + operatorConjugationHom h.right (z • S) = _
  change operatorConjugationHom h.left (z • T) + operatorConjugationHom h.right (z • S) =
    z • (operatorConjugationHom h.left T + operatorConjugationHom h.right S)
  rw [map_smul, map_smul, smul_add]

theorem OddCycle.IsDirectSum.block_one (h : c.IsDirectSum d e) : h.block 1 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun h.exhaustive x

def OddCycle.IsDirectSum.blockHom (h : c.IsDirectSum d e) :
    (End c.space × End d.space) →⋆ₐ[ℂ] End e.space where
  toFun p := h.block p.1 p.2
  map_zero' := by
    change operatorConjugationHom h.left 0 + operatorConjugationHom h.right 0 = 0
    rw [map_zero, map_zero, add_zero]
  map_one' := h.block_one
  map_add' p q := h.block_add p.1 q.1 p.2 q.2
  map_mul' p q := (h.block_mul p.1 q.1 p.2 q.2).symm
  map_star' p := by
    simp only [block, star_add, ← operatorConjugation_star, Prod.fst_star, Prod.snd_star]
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change h.block (z • 1) (z • 1) = z • 1
    rw [h.block_smul, h.block_one]

end CoarseAssembly.Analytic

end

end OAI
