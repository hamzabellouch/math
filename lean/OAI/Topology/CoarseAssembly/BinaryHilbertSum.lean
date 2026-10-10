import OAI.Topology.CoarseAssembly.FredholmModule
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace OAI

/-! # Concrete binary sums of the Hilbert spaces of analytic cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

universe u

abbrev binaryHilbertSpace (H K : HilbertSpace.{u}) : HilbertSpace.{u} where
  Carrier := WithLp 2 (H × K)
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := inferInstance

variable (H K : HilbertSpace.{u})

def binaryLeft : H →ₗᵢ[ℂ] binaryHilbertSpace H K where
  toFun x := WithLp.toLp 2 (x, 0)
  map_add' _ _ := by simp [← WithLp.toLp_add]
  map_smul' _ _ := by simp [← WithLp.toLp_smul]
  norm_map' x := WithLp.norm_toLp_fst 2 H K x

def binaryRight : K →ₗᵢ[ℂ] binaryHilbertSpace H K where
  toFun x := WithLp.toLp 2 (0, x)
  map_add' _ _ := by simp [← WithLp.toLp_add]
  map_smul' _ _ := by simp [← WithLp.toLp_smul]
  norm_map' x := WithLp.norm_toLp_snd 2 H K x

@[simp] theorem binaryLeft_adjoint :
    (binaryLeft H K).toContinuousLinearMap.adjoint = WithLp.fstL 2 ℂ H K := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [binaryLeft, WithLp.prod_inner_apply]

@[simp] theorem binaryRight_adjoint :
    (binaryRight H K).toContinuousLinearMap.adjoint = WithLp.sndL 2 ℂ H K := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [binaryRight, WithLp.prod_inner_apply]

theorem binaryLeft_right :
    (binaryLeft H K).toContinuousLinearMap.adjoint ∘L
      (binaryRight H K).toContinuousLinearMap = 0 := by
  rw [binaryLeft_adjoint]
  ext x
  simp [binaryRight]

theorem binary_exhaustive :
    (binaryLeft H K).toContinuousLinearMap.comp (binaryLeft H K).toContinuousLinearMap.adjoint +
      (binaryRight H K).toContinuousLinearMap.comp (binaryRight H K).toContinuousLinearMap.adjoint = 1 := by
  rw [binaryLeft_adjoint, binaryRight_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.ofLp_injective 2)
  simp [binaryLeft, binaryRight]
  rfl

/-- Block diagonal operators, on the actual Hilbert sum. -/
def binaryBlock (T : End H) (S : End K) : End (binaryHilbertSpace H K) :=
  operatorConjugation (binaryLeft H K) T + operatorConjugation (binaryRight H K) S

@[simp] theorem binaryBlock_apply (T : End H) (S : End K)
    (x : binaryHilbertSpace H K) :
    binaryBlock H K T S x = WithLp.toLp 2 (T x.fst, S x.snd) := by
  unfold binaryBlock operatorConjugation
  rw [binaryLeft_adjoint, binaryRight_adjoint]
  apply (WithLp.ofLp_injective 2)
  simp [binaryLeft, binaryRight]

theorem binaryBlock_add (T T' : End H) (S S' : End K) :
    binaryBlock H K (T + T') (S + S') = binaryBlock H K T S + binaryBlock H K T' S' := by
  ext x
  rw [add_apply, binaryBlock_apply H K, binaryBlock_apply H K,
    binaryBlock_apply H K]
  rfl

theorem binaryBlock_sub (T T' : End H) (S S' : End K) :
    binaryBlock H K (T - T') (S - S') = binaryBlock H K T S - binaryBlock H K T' S' := by
  ext x
  rw [sub_apply, binaryBlock_apply H K, binaryBlock_apply H K,
    binaryBlock_apply H K]
  rfl

theorem binaryBlock_mul (T T' : End H) (S S' : End K) :
    binaryBlock H K (T * T') (S * S') = binaryBlock H K T S * binaryBlock H K T' S' := by
  ext x
  change binaryBlock H K (T * T') (S * S') x =
    binaryBlock H K T S (binaryBlock H K T' S' x)
  rw [binaryBlock_apply H K, binaryBlock_apply H K, binaryBlock_apply H K]
  rfl

@[simp] theorem binaryBlock_one : binaryBlock H K 1 1 = 1 := by
  ext x
  rw [binaryBlock_apply H K]
  rfl

@[simp] theorem binaryBlock_zero : binaryBlock H K 0 0 = 0 := by
  ext x
  rw [binaryBlock_apply H K]
  rfl

theorem binaryBlock_star (T : End H) (S : End K) :
    binaryBlock H K (star T) (star S) = star (binaryBlock H K T S) := by
  simp only [binaryBlock, star_add, ← operatorConjugation_star]

theorem binaryBlock_smul (z : ℂ) (T : End H) (S : End K) :
    binaryBlock H K (z • T) (z • S) = z • binaryBlock H K T S := by
  ext x
  rw [smul_apply, binaryBlock_apply H K, binaryBlock_apply H K]
  rfl

def binaryBlockHom : (End H × End K) →⋆ₐ[ℂ] End (binaryHilbertSpace H K) where
  toFun p := binaryBlock H K p.1 p.2
  map_zero' := binaryBlock_zero H K
  map_one' := binaryBlock_one H K
  map_add' p q := binaryBlock_add H K p.1 q.1 p.2 q.2
  map_mul' p q := binaryBlock_mul H K p.1 q.1 p.2 q.2
  map_star' p := binaryBlock_star H K p.1 p.2
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one]
    exact (binaryBlock_smul H K z 1 1).trans (by rw [binaryBlock_one])

theorem binaryBlock_compact {T : End H} {S : End K}
    (hT : IsCompactOperator T) (hS : IsCompactOperator S) :
    IsCompactOperator (binaryBlock H K T S) := by
  unfold binaryBlock operatorConjugation
  exact ((hT.clm_comp (binaryLeft H K).toContinuousLinearMap).comp_clm
    (binaryLeft H K).toContinuousLinearMap.adjoint).add
      ((hS.clm_comp (binaryRight H K).toContinuousLinearMap).comp_clm
        (binaryRight H K).toContinuousLinearMap.adjoint)

end CoarseAssembly.Analytic

end

end OAI
