import OAI.RingTheory.BassTrace.ZeroCarriers

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace BassTrace.FiniteAverage

open Set Finset MeasureTheory

open scoped Classical

noncomputable section

section AlgebraicNorm

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

private abbrev BIndex := Module.Free.ChooseBasisIndex ℝ V

private def embedding : V →ₗ[ℝ] lp (fun _ : BIndex V=>ℝ) 2 :=
  (Finsupp.linearCombination ℝ (fun i=>lp.single 2 i 1)).comp
    (Module.Free.chooseBasis ℝ V).repr.toLinearMap

private lemma embedding_apply (v : V) (i : BIndex V) :
    embedding V v i=(Module.Free.chooseBasis ℝ V).repr v i := by
  simp only [embedding,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    Finsupp.linearCombination_apply,Finsupp.sum,lp.coeFn_sum,lp.coeFn_smul,
    Finset.sum_apply,Pi.smul_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]

private lemma embedding_injective : Function.Injective (embedding V) := by
  intro v w h
  apply (Module.Free.chooseBasis ℝ V).repr.injective
  ext i
  simpa only [embedding_apply] using congrArg (fun f : lp (fun _ : BIndex V=>ℝ) 2=>f i) h

private abbrev algebraicNormedGroup : NormedAddCommGroup V :=
  NormedAddCommGroup.induced _ _ (embedding V) (embedding_injective V)

private abbrev algebraicNormedSpace : letI := algebraicNormedGroup V; NormedSpace ℝ V :=
  NormedSpace.induced ℝ _ _ (embedding V)

end AlgebraicNorm

variable {X V W : Type*} [MeasurableSpace X]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

variable (μ : Measure X)

def average (f : SimpleFunc X V) : V :=
  ∑v∈f.range, μ.real (f⁻¹' {v}) • v

lemma average_add [IsFiniteMeasure μ] (f g : SimpleFunc X V) :
    average μ (f+g)=average μ f+average μ g := by
  let :=  algebraicNormedGroup V
  let :=  algebraicNormedSpace V
  simpa only [average,SimpleFunc.integral_eq] using
    SimpleFunc.integral_add (f.integrable_of_isFiniteMeasure) (g.integrable_of_isFiniteMeasure)

lemma average_map [IsFiniteMeasure μ] (L : V →ₗ[ℝ] W) (f : SimpleFunc X V) :
    average μ (f.map L)=L (average μ f) := by
  let :=  algebraicNormedGroup V
  let :=  algebraicNormedSpace V
  let :=  algebraicNormedGroup W
  let :=  algebraicNormedSpace W
  rw [average,← SimpleFunc.integral_eq,
    SimpleFunc.map_integral f L f.integrable_of_isFiniteMeasure L.map_zero]
  simp only [average,map_sum,map_smul]

lemma average_const [IsProbabilityMeasure μ] (v : V) :
    average μ (SimpleFunc.const X v)=v := by
  let :=  algebraicNormedGroup V
  let :=  algebraicNormedSpace V
  rw [average,← SimpleFunc.integral_eq,SimpleFunc.integral_const]
  simp

lemma average_precomp {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    (h : Z → X) (hh : MeasurePreserving h ν μ) (hs : Function.Surjective h)
    (f : SimpleFunc X V) :
    average ν (f.comp h hh.measurable)=average μ f := by
  have he : (f.comp h hh.measurable).range=f.range := by
    ext v
    simp only [SimpleFunc.mem_range,Set.mem_range]
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨h z,rfl⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨z,rfl⟩ := hs x
      exact ⟨z,rfl⟩
  unfold average
  rw [he]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  exact hh.measureReal_preimage (f.measurableSet_fiber v).nullMeasurableSet

section LocallyConstant

variable [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X]

variable {A : Type*}

def ofLocallyConstant (f : X → A) (hf : IsLocallyConstant f) : SimpleFunc X A where
  toFun := f
  measurableSet_fiber' v := (hf.isClopen_fiber v).isOpen.measurableSet
  finite_range' := hf.range_finite

@[simp] lemma ofLocallyConstant_apply (f : X → A) (hf : IsLocallyConstant f) (x : X) :
    ofLocallyConstant f hf x=f x := rfl

end LocallyConstant

variable [IsFiniteMeasure μ]

lemma average_complex_eq_integral (f : SimpleFunc X ℂ) :
    average μ f=∫x,f x∂μ := by
  rw [average,← SimpleFunc.integral_eq]
  exact f.integral_eq_integral f.integrable_of_isFiniteMeasure

lemma norm_average_le_integral_norm (f : SimpleFunc X ℂ) :
    ‖average μ f‖≤∫x,‖f x‖∂μ := by
  rw [average_complex_eq_integral]
  exact norm_integral_le_integral_norm _

end

end BassTrace.FiniteAverage

end OAI
