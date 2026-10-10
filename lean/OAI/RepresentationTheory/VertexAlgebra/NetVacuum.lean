import OAI.RepresentationTheory.VertexAlgebra.NetAxioms
import OAI.RepresentationTheory.VertexAlgebra.MobiusRepresentation

namespace OAI

noncomputable section
open UniformSpace Set TopologicalSpace
namespace StronglyRationalVOA
lemma globalCyclicSpace_contains {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : ProperCircleArc → VonNeumannAlgebra H) (Ω : H) : Ω ∈ globalCyclicSpace N Ω := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1,one_mem _,rfl⟩
lemma globalCyclicSpace_invariant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (N : ProperCircleArc → VonNeumannAlgebra H) (Ω : H)
    (I : ProperCircleArc) (B : H →L[ℂ] H) (hB : B ∈ N I) :
    ∀ x ∈ globalCyclicSpace N Ω, B x ∈ globalCyclicSpace N Ω := by
  let S := Submodule.span ℂ {x | ∃ C ∈ globalObservableAlgebra N, x=C Ω}
  have hBs : B ∈ globalObservableAlgebra N := Algebra.subset_adjoin (mem_iUnion.mpr ⟨I,hB⟩)
  have hinv : Set.MapsTo B (S : Set H) (S : Set H) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨C,hC,rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨B*C,mul_mem hBs hC,rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      change B (x+y) ∈ S
      rw [map_add]
      exact S.add_mem ihx ihy
    | smul c x hx ih =>
      change B (c • x) ∈ S
      rw [map_smul]
      exact S.smul_mem c ih
  exact hinv.closure B.continuous
end StronglyRationalVOA
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma hilbertCompletion_separable (_U : A.UnitaryStructure) : SeparableSpace (Completion V) := by
  have hv : SeparableSpace V := by
    have hg (d : ℕ) : IsSeparable (A.grade d : Set V) := by
      let : FiniteDimensional ℂ (A.grade d) := A.grade_finite d
      exact IsSeparable.of_subtype _
    have hs := (IsSeparable.iUnion hg).span (R := ℂ)
    have he : Submodule.span ℂ (⋃ d, (A.grade d : Set V))=⊤ := by
      apply top_unique
      intro x _
      apply A.homogeneous_induction (P := fun x => x ∈ Submodule.span ℂ (⋃ d, (A.grade d : Set V)))
      · exact (Submodule.span ℂ _).zero_mem
      · intro d x hx; exact Submodule.subset_span (mem_iUnion.mpr ⟨d,hx⟩)
      · intro x y hx hy; exact Submodule.add_mem _ hx hy
    rw [he,Submodule.top_coe] at hs
    exact isSeparable_univ_iff.mp hs
  let := hv
  exact Completion.denseRange_coe.separableSpace (Completion.continuous_coe V)
 

lemma interval_vacuum_cyclic (hc : A.toVertexAlgebra.C2Cofinite) :
    globalCyclicSpace (U.intervalAlgebra hc) (A.vacuum:Completion V)=⊤ := by
  have h := U.interval_invariant_subspace hc
    (globalCyclicSpace (U.intervalAlgebra hc) (A.vacuum:Completion V))
    (Submodule.isClosed_topologicalClosure _) (globalCyclicSpace_invariant _ _)
  rcases h with h | h
  · have hh := globalCyclicSpace_contains (U.intervalAlgebra hc) (A.vacuum:Completion V)
    rw [h,Submodule.mem_bot] at hh
    exact (U.completion_vacuum_ne_zero hh).elim
  · exact h
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
