import OAI.Topology.CoarseAssembly.CountableHilbertSum

namespace OAI

/-! # The orthogonal complement of one countable Hilbert summand -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : ℕ → HilbertSpace) (j : ℕ)

def summandComplement : Submodule ℂ (countableHilbertSpace H) :=
  (lp.evalCLM ℂ (fun k => H k) 2 j).ker

instance summandComplement_complete : CompleteSpace (summandComplement H j) :=
  (lp.evalCLM ℂ (fun k => H k) 2 j).isClosed_ker.completeSpace_coe

abbrev complementHilbertSpace : HilbertSpace where
  Carrier := summandComplement H j
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := inferInstance

def complementIsometry : complementHilbertSpace H j →ₗᵢ[ℂ] countableHilbertSpace H :=
  (summandComplement H j).subtypeₗᵢ

def complementProjection : countableHilbertSpace H →L[ℂ] complementHilbertSpace H j :=
  ((1 : End (countableHilbertSpace H)) -
    (summandIsometry H j).toContinuousLinearMap.comp (lp.evalCLM ℂ (fun k => H k) 2 j)).codRestrict
      (summandComplement H j) (by
        intro x
        change (x - lp.single (E := fun k => H k) 2 j (x j)) j = 0
        simp)

theorem complementProjection_coe (x : countableHilbertSpace H) :
    (complementProjection H j x : countableHilbertSpace H) =
      x - summandIsometry H j (x j) := rfl

theorem complementIsometry_adjoint :
    (complementIsometry H j).toContinuousLinearMap.adjoint = complementProjection H j := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  symm
  change inner ℂ (x - lp.single (E := fun k => H k) 2 j (x j))
    (y : countableHilbertSpace H) = inner ℂ x (y : countableHilbertSpace H)
  rw [inner_sub_left, lp.inner_single_left]
  have hy : (y : countableHilbertSpace H) j = 0 := y.property
  rw [hy, inner_zero_right, sub_zero]

theorem summand_complement_orthogonal :
    (summandIsometry H j).toContinuousLinearMap.adjoint.comp
      (complementIsometry H j).toContinuousLinearMap = 0 := by
  rw [summandIsometry_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  exact x.property

theorem summand_complement_exhaustive :
    (summandIsometry H j).toContinuousLinearMap.comp
        (summandIsometry H j).toContinuousLinearMap.adjoint +
      (complementIsometry H j).toContinuousLinearMap.comp
        (complementIsometry H j).toContinuousLinearMap.adjoint = 1 := by
  rw [summandIsometry_adjoint, complementIsometry_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  change summandIsometry H j (x j) +
    (complementProjection H j x : countableHilbertSpace H) = x
  rw [complementProjection_coe]
  abel

end CoarseAssembly.Analytic

end

end OAI
