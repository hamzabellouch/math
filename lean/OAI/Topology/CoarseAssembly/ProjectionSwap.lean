import OAI.Topology.CoarseAssembly.BinaryHilbertSum
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # The unitary which exchanges complementary represented subspaces -/

noncomputable section

namespace CoarseAssembly.Analytic

variable (H : HilbertSpace)

def binaryFlip : End (binaryHilbertSpace H H) :=
  (LinearIsometryEquiv.withLpProdComm 2 ℂ H H).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem binaryFlip_apply (x : binaryHilbertSpace H H) :
    binaryFlip H x = WithLp.toLp 2 (x.snd, x.fst) := rfl

theorem binaryFlip_selfAdjoint : IsSelfAdjoint (binaryFlip H) := by
  change ContinuousLinearMap.adjoint
    (LinearIsometryEquiv.withLpProdComm 2 ℂ H H).toContinuousLinearEquiv.toContinuousLinearMap = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  rfl

theorem binaryFlip_block (T : End H) :
    binaryFlip H * binaryBlock H H T T = binaryBlock H H T T * binaryFlip H := by
  apply ContinuousLinearMap.ext
  intro x
  change binaryFlip H (binaryBlock H H T T x) = binaryBlock H H T T (binaryFlip H x)
  rw [binaryBlock_apply H H, binaryFlip_apply, binaryFlip_apply, binaryBlock_apply H H]
  rfl

def projectionSwap (P : End H) : End (binaryHilbertSpace H H) :=
  binaryBlock H H P P + binaryBlock H H (1 - P) (1 - P) * binaryFlip H

@[simp] theorem projectionSwap_apply (P : End H) (x : binaryHilbertSpace H H) :
    projectionSwap H P x =
      WithLp.toLp 2 (P x.fst + (1 - P) x.snd, (1 - P) x.fst + P x.snd) := by
  change binaryBlock H H P P x + binaryBlock H H (1 - P) (1 - P) (binaryFlip H x) = _
  rw [binaryBlock_apply H H, binaryFlip_apply, binaryBlock_apply H H]
  apply (WithLp.ofLp_injective 2)
  change (P x.fst + (1 - P) x.snd, P x.snd + (1 - P) x.fst) = _
  rw [add_comm (P x.snd)]

theorem projectionSwap_selfAdjoint (P : End H) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (projectionSwap H P) := by
  change star (projectionSwap H P) = projectionSwap H P
  unfold projectionSwap
  rw [star_add, star_mul, ← binaryBlock_star, ← binaryBlock_star,
    hP.star_eq, star_sub, star_one, hP.star_eq, (binaryFlip_selfAdjoint H).star_eq,
    binaryFlip_block]

theorem projectionSwap_sq (P : End H) (hPP : P * P = P) :
    projectionSwap H P * projectionSwap H P = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change projectionSwap H P (projectionSwap H P x) = x
  rw [projectionSwap_apply H, projectionSwap_apply H]
  apply (WithLp.ofLp_injective 2)
  have hp (y : H) : P (P y) = P y := DFunLike.congr_fun hPP y
  change
    (P (P x.fst + (1 - P) x.snd) + (1 - P) ((1 - P) x.fst + P x.snd),
     (1 - P) (P x.fst + (1 - P) x.snd) + P ((1 - P) x.fst + P x.snd)) = (x.fst, x.snd)
  simp only [map_add, sub_apply, one_apply_eq_self, map_sub, hp]
  ext <;> abel_nf

def projectionSwapUnitary (P : End H) (hP : IsStarProjection P) :
    binaryHilbertSpace H H ≃ₗᵢ[ℂ] binaryHilbertSpace H H :=
  Unitary.linearIsometryEquiv ⟨projectionSwap H P, by
    rw [Unitary.mem_iff, (projectionSwap_selfAdjoint H P hP.isSelfAdjoint).star_eq]
    exact ⟨projectionSwap_sq H P hP.isIdempotentElem,
      projectionSwap_sq H P hP.isIdempotentElem⟩⟩

@[simp] theorem projectionSwapUnitary_clm (P : End H) (hP : IsStarProjection P) :
    (projectionSwapUnitary H P hP).toLinearIsometry.toContinuousLinearMap = projectionSwap H P := rfl

theorem projectionSwapUnitary_conjugation (P : End H) (hP : IsStarProjection P)
    (T : End (binaryHilbertSpace H H)) :
    operatorConjugation (projectionSwapUnitary H P hP).toLinearIsometry T =
      projectionSwap H P * T * projectionSwap H P := by
  unfold operatorConjugation
  rw [projectionSwapUnitary_clm]
  change projectionSwap H P * T * star (projectionSwap H P) = _
  rw [(projectionSwap_selfAdjoint H P hP.isSelfAdjoint).star_eq]

end CoarseAssembly.Analytic

end

end OAI
