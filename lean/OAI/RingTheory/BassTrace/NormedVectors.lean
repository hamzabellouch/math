import OAI.RingTheory.BassTrace.AffinePotentials

namespace OAI

noncomputable section

/-! A normed ambient space for finitely supported real vectors. The ℓ² norm controls affine
topology and triangulations; balls use the separately defined transport metric. -/

namespace BassTrace.Sparse

section

variable {Y : Type*}

private def vectorEmbedding : (Y →₀ ℝ) →ₗ[ℝ] lp (fun _ : Y => ℝ) 2 := by
  classical
  exact Finsupp.linearCombination ℝ (fun y => lp.single 2 y 1)

private lemma vectorEmbedding_apply (v : Y →₀ ℝ) (y : Y) :
    vectorEmbedding v y = v y := by
  classical
  simp only [vectorEmbedding,Finsupp.linearCombination_apply, Finsupp.sum,
    lp.coeFn_sum,lp.coeFn_smul,Finset.sum_apply,Pi.smul_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]

private lemma vectorEmbedding_injective :
    Function.Injective (vectorEmbedding (Y := Y)) := by
  intro v w h
  ext y
  simpa only [vectorEmbedding_apply] using congrArg (fun f : lp (fun _ : Y => ℝ) 2 => f y) h

scoped instance realFinsuppNormedAddCommGroup : NormedAddCommGroup (Y →₀ ℝ) :=
  NormedAddCommGroup.induced _ _ vectorEmbedding vectorEmbedding_injective

scoped instance realFinsuppNormedSpace : NormedSpace ℝ (Y →₀ ℝ) :=
  NormedSpace.induced ℝ _ _ vectorEmbedding

open scoped BassTrace.Sparse

lemma coordinate_norm_le (v : Y →₀ ℝ) (y : Y) : ‖v y‖ ≤ ‖v‖ := by
  change ‖v y‖ ≤ ‖vectorEmbedding v‖
  rw [← vectorEmbedding_apply v y]
  exact lp.norm_apply_le_norm (by norm_num) _ _

def coordinateCLM (y : Y) : (Y →₀ ℝ) →L[ℝ] ℝ :=
  (Finsupp.lapply y).mkContinuous 1 (fun v => by simpa using coordinate_norm_le v y)

@[simp] lemma coordinateCLM_apply (y : Y) (v : Y →₀ ℝ) : coordinateCLM y v = v y := rfl

def finitePairingCLM (S : Finset Y) (a : Y → ℝ) : (Y →₀ ℝ) →L[ℝ] ℝ :=
  ∑ y ∈ S, a y • coordinateCLM (y : Y)

@[simp] lemma finitePairingCLM_apply (S : Finset Y) (a : Y → ℝ) (v : Y →₀ ℝ) :
    finitePairingCLM S a v = ∑ y ∈ S, a y * v y := by
  simp [finitePairingCLM]

lemma finitePairingCLM_vanish (S : Finset Y) (a : Y → ℝ) (v : Y →₀ ℝ)
    (hv : Disjoint S v.support) : finitePairingCLM S a v = 0 := by
  classical
  rw [finitePairingCLM_apply]
  apply Finset.sum_eq_zero
  intro y hy
  have hnot : y ∉ v.support := fun h => Finset.disjoint_left.mp hv hy h
  rw [Finsupp.notMem_support_iff.mp hnot,mul_zero]

end

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

def finsuppRelabelIsometry (e : Y ≃ Z) : (Y →₀ ℝ) ≃ₗᵢ[ℝ] (Z →₀ ℝ) where
  __ := Finsupp.domLCongr (R := ℝ) e
  norm_map' v := by
    change ‖vectorEmbedding (Finsupp.domLCongr (R := ℝ) e v)‖ = ‖vectorEmbedding v‖
    rw [lp.norm_eq_tsum_rpow (by norm_num),lp.norm_eq_tsum_rpow (by norm_num)]
    simp only [vectorEmbedding_apply]
    congr 1
    change (∑' z,‖v (e.symm z)‖ ^ (2 : ℝ)) = ∑' y,‖v y‖ ^ (2 : ℝ)
    exact e.symm.tsum_eq (fun y : Y => ‖v y‖ ^ (2 : ℝ))

end BassTrace.Sparse

end

end OAI
