import Mathlib.Algebra.Group.Hom.Basic

namespace OAI

/-!
# The boundary index diagram

The algebraic final calculation in §6 of the coarse Novikov manuscript.
This is a diagram lemma, not a definition or construction of coarse assembly.
The two naturality equations are the precise consequences of Willett--Yu,
*Higher Index Theory*, §§5.1, 6.7, 7.1--7.2 used in that calculation.
The geometric filling and operator factorization remain separate obligations.
-/

namespace CoarseAssembly

variable {HB HD HX KB KD KX : Type*}
variable [AddCommGroup HB] [AddCommGroup HD] [AddCommGroup HX]
variable [AddCommGroup KB] [AddCommGroup KD] [AddCommGroup KX]

/-- Naturality and an actual factorization through a filling annihilate the
index of the included boundary. `filled` is the conclusion of the geometric
filling argument, and `factor` is induced by the proved operator identity
`V E = I`. Neither is being declared to be a published input. -/
theorem boundary_index_zero
    (e : HB →+ HD) (i : HB →+ HX)
    (μB : HB →+ KB) (μD : HD →+ KD) (μX : HX →+ KX)
    (eRoe : KB →+ KD) (iRoe : KB →+ KX) (transfer : KD →+ KX)
    (natural_e : μD.comp e = eRoe.comp μB)
    (natural_i : μX.comp i = iRoe.comp μB)
    (factor : transfer.comp eRoe = iRoe)
    (β : HB) (filled : e β = 0) : μX (i β) = 0 := by
  calc
    μX (i β) = iRoe (μB β) := DFunLike.congr_fun natural_i β
    _ = transfer (eRoe (μB β)) := (DFunLike.congr_fun factor (μB β)).symm
    _ = transfer (μD (e β)) := congrArg transfer (DFunLike.congr_fun natural_e β).symm
    _ = 0 := by rw [filled, map_zero, map_zero]

/-- A filling through a group which is zero makes every boundary class vanish.
In the manuscript the middle group is locally finite K-homology of the
countable union of compact discs, using Blackadar Theorem 19.7.1,
Proposition 17.9.1, and §19.8.3. -/
theorem boundary_filling_zero {HW : Type*} [AddCommGroup HW] [Subsingleton HW]
    (boundary : HB →+ HW) (inclusion : HW →+ HD) (β : HB) :
    (inclusion.comp boundary) β = 0 := by
  have h : boundary β = 0 := Subsingleton.elim _ _
  simp [h]

end CoarseAssembly

end OAI
