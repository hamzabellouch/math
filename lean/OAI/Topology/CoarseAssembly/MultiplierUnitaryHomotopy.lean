import OAI.Topology.CoarseAssembly.MultiplierBoundaryHomotopy
import OAI.Topology.CoarseAssembly.InvolutionUnitaryPath

namespace OAI

/-! # Unitary homotopies preserve the Roe multiplier boundary

This is the conjugation step in descent through changes of cycle
coordinates. The path is an actual norm-continuous path of unitaries in
the Roe multiplier algebra.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def conjugatedMultiplier (u : unitary (multiplierAlgebra (X := X) (H := H)))
    (F : multiplierAlgebra (X := X) (H := H)) : multiplierAlgebra (X := X) (H := H) :=
  (u : multiplierAlgebra (X := X) (H := H)) * F * star (u : multiplierAlgebra (X := X) (H := H))

theorem conjugatedMultiplier_selfAdjoint
    (u : unitary (multiplierAlgebra (X := X) (H := H)))
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F) :
    IsSelfAdjoint (conjugatedMultiplier u F) := by
  change star ((u : multiplierAlgebra (X := X) (H := H)) * F * star (u : multiplierAlgebra (X := X) (H := H))) = _
  rw [star_mul, star_mul, star_star, hF.star_eq]
  rfl

theorem conjugatedMultiplier_square_defect
    (u : unitary (multiplierAlgebra (X := X) (H := H)))
    (F : multiplierAlgebra (X := X) (H := H)) :
    (conjugatedMultiplier u F) ^ 2 - 1 =
      (u : multiplierAlgebra (X := X) (H := H)) * (F ^ 2 - 1) * star (u : multiplierAlgebra (X := X) (H := H)) := by
  let U : multiplierAlgebra (X := X) (H := H) := u
  have hleft : star U * U = 1 := Unitary.coe_star_mul_self u
  have hright : U * star U = 1 := Unitary.coe_mul_star_self u
  change (U * F * star U) ^ 2 - 1 = U * (F ^ 2 - 1) * star U
  calc
    _ = U * F * (star U * U) * F * star U - 1 := by noncomm_ring
    _ = U * (F * F) * star U - 1 := by rw [hleft]; simp only [mul_one, mul_assoc]
    _ = _ := by rw [pow_two, mul_sub, sub_mul, mul_one, hright]

theorem conjugatedMultiplier_defect_mem
    (u : unitary (multiplierAlgebra (X := X) (H := H)))
    (F : multiplierAlgebra (X := X) (H := H))
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) :
    (conjugatedMultiplier u F).val ^ 2 - 1 ∈ algebra (X := X) (H := H) := by
  let U : multiplierAlgebra (X := X) (H := H) := u
  have he := congrArg (fun T : multiplierAlgebra (X := X) (H := H) => T.val)
    (conjugatedMultiplier_square_defect u F)
  change (conjugatedMultiplier u F).val ^ 2 - 1 = U.val * (F.val ^ 2 - 1) *
    (star U).val at he
  rw [he]
  have hleft : U.val * (F.val ^ 2 - 1) ∈ algebra (X := X) (H := H) :=
    (U.property ⟨_, hFd⟩).1
  exact ((star U).property ⟨_, hleft⟩).2

theorem multiplierBoundaryClass_unitaryHomotopy
    (U : Interval → unitary (multiplierAlgebra (X := X) (H := H)))
    (hU : Continuous U) (F : multiplierAlgebra (X := X) (H := H))
    (hF : IsSelfAdjoint F) (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) :
    multiplierBoundaryClass (conjugatedMultiplier (U start) F)
      (conjugatedMultiplier_selfAdjoint (U start) F hF)
      (conjugatedMultiplier_defect_mem (U start) F hFd) =
    multiplierBoundaryClass (conjugatedMultiplier (U finish) F)
      (conjugatedMultiplier_selfAdjoint (U finish) F hF)
      (conjugatedMultiplier_defect_mem (U finish) F hFd) := by
  apply multiplierBoundaryClass_homotopy
    (fun t => conjugatedMultiplier (U t) F)
    (fun t => conjugatedMultiplier_selfAdjoint (U t) F hF)
    (fun t => conjugatedMultiplier_defect_mem (U t) F hFd)
  exact ((continuous_subtype_val.comp hU).mul continuous_const).mul
    ((continuous_subtype_val.comp hU).star)

theorem multiplierBoundaryClass_involutionConjugation
    (u : unitary (multiplierAlgebra (X := X) (H := H)))
    (hu : IsSelfAdjoint (u : multiplierAlgebra (X := X) (H := H)))
    (F : multiplierAlgebra (X := X) (H := H))
    (hF : IsSelfAdjoint F) (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) :
    multiplierBoundaryClass F hF hFd =
      multiplierBoundaryClass (conjugatedMultiplier u F)
        (conjugatedMultiplier_selfAdjoint u F hF)
        (conjugatedMultiplier_defect_mem u F hFd) := by
  have huu : (u : multiplierAlgebra (X := X) (H := H)) * u = 1 := by
    calc
      _ = star (u : multiplierAlgebra (X := X) (H := H)) * u := by rw [hu.star_eq]
      _ = 1 := Unitary.coe_star_mul_self u
  let W : Interval → unitary (multiplierAlgebra (X := X) (H := H)) :=
    involutionUnitaryPath (u : multiplierAlgebra (X := X) (H := H)) hu huu
  have hw0 : W start = 1 :=
    involutionUnitaryPath_start (u : multiplierAlgebra (X := X) (H := H)) hu huu
  have h0 : conjugatedMultiplier (W start) F = F := by
    rw [hw0]
    simp [conjugatedMultiplier]
  have h1 : W finish = u := by
    apply Subtype.ext
    exact involutionUnitaryPath_finish (u : multiplierAlgebra (X := X) (H := H)) hu huu
  have hwc : Continuous W :=
    involutionUnitaryPath_continuous (u : multiplierAlgebra (X := X) (H := H)) hu huu
  have h := multiplierBoundaryClass_unitaryHomotopy W hwc F hF hFd
  simpa only [h0, h1] using h

end CoarseAssembly.DiscreteRoe

end

end OAI
