import OAI.Topology.CoarseAssembly.BilateralShift
import Mathlib.Topology.DenseEmbedding

namespace OAI

/-! # Separable countable sums of the Hilbert spaces in analytic cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

open TopologicalSpace

variable (H : ℕ → HilbertSpace)

abbrev HilbertSum := lp (fun j => H j) 2

instance hilbertSum_secondCountable : SecondCountableTopology (HilbertSum H) := by
  let v : ℕ × ℕ → HilbertSum H := fun p => lp.single 2 p.1 (denseSeq (H p.1) p.2)
  let P : Submodule ℂ (HilbertSum H) := (Submodule.span ℂ (Set.range v)).topologicalClosure
  have hc : IsClosed (P : Set (HilbertSum H)) := Submodule.isClosed_topologicalClosure _
  have hsingle (j : ℕ) (x : H j) : lp.single 2 j x ∈ P := by
    refine (denseRange_denseSeq (H j)).induction_on x
      (hc.preimage (lp.singleContinuousLinearMap ℂ (fun j => H j) 2 j).continuous) ?_
    intro n
    apply Submodule.le_topologicalClosure
    exact Submodule.subset_span ⟨(j, n), rfl⟩
  have htop : P = ⊤ := by
    apply top_unique
    intro x _
    apply hc.mem_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top x)
    exact Filter.Eventually.of_forall (fun s => Submodule.sum_mem P (fun j _ => hsingle j (x j)))
  have hs := ((Set.countable_range v).isSeparable.span (R := ℂ)).closure
  change IsSeparable (P : Set (HilbertSum H)) at hs
  rw [htop] at hs
  have : SeparableSpace (HilbertSum H) := isSeparable_univ_iff.mp hs
  infer_instance

abbrev countableHilbertSpace : HilbertSpace where
  Carrier := HilbertSum H
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance
  secondCountable := inferInstance

/-- The inclusion of an individual Hilbert summand. -/
def summandIsometry (j : ℕ) : H j →ₗᵢ[ℂ] countableHilbertSpace H where
  toFun x := lp.single (E := fun j => H j) 2 j x
  map_add' x y := lp.single_add (E := fun j => H j) 2 j x y
  map_smul' z x := by
    simpa only [RingHom.id_apply] using
      (lp.single_smul (𝕜 := ℂ) (E := fun j => H j) 2 j z x)
  norm_map' x := lp.norm_single (E := fun j => H j) (by norm_num : (0 : ENNReal) < 2) j x

@[simp] theorem summandIsometry_apply (j : ℕ) (x : H j) :
    summandIsometry H j x = lp.single (E := fun j => H j) 2 j x := rfl

/-- Coordinate evaluation is the adjoint of summand inclusion. -/
theorem summandIsometry_adjoint (j : ℕ) :
    (summandIsometry H j).toContinuousLinearMap.adjoint = lp.evalCLM ℂ (fun j => H j) 2 j := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact lp.inner_single_left (𝕜 := ℂ) (G := fun j => H j) j y x

end CoarseAssembly.Analytic

end

end OAI
