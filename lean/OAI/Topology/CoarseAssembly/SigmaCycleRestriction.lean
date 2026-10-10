import OAI.Topology.CoarseAssembly.BlockSumDecomposition
import OAI.Topology.CoarseAssembly.SigmaCycle
import OAI.Topology.CoarseAssembly.CircleCoefficient

namespace OAI

/-! # The coordinates of an actual countable Fredholm cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

variable {A : Type} [NonUnitalCStarAlgebra A]

def zeroRepresentationCycle (H : HilbertSpace) (F : End H) : OddCycle A where
  space := H
  representation := 0
  operator := F
  commutator_compact _ := by simp; exact isCompactOperator_zero
  square_compact _ := by simp; exact isCompactOperator_zero
  adjoint_compact _ := by simp; exact isCompactOperator_zero

theorem zeroRepresentationCycle_degenerate (H : HilbertSpace) (F : End H) :
    (zeroRepresentationCycle (A := A) H F).Degenerate := by
  constructor
  · intro a
    change F * (0 : End H) - 0 * F = 0
    simp
  constructor
  · intro a
    change (F * F - 1) * (0 : End H) = 0
    simp
  · intro a
    change (star F - F) * (0 : End H) = 0
    simp

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]
  [∀ j, T2Space (Y j)]

theorem sigmaRestriction_extension_same (j : ℕ) (f : C₀(Y j, ℂ)) :
    sigmaFunctionRestriction Y j
      (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j) f) =
      compactFunctionForget f := by
  ext x
  exact zeroExtension_apply (sigmaComponent Y j) (sigmaComponent_open Y j) f x

theorem sigmaRestriction_extension_ne (j k : ℕ) (hjk : j ≠ k) (f : C₀(Y j, ℂ)) :
    sigmaFunctionRestriction Y k
      (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j) f) = 0 := by
  ext x
  apply zeroExtension_apply_outside (sigmaComponent Y j) (sigmaComponent_open Y j) f
  rintro ⟨y, hy⟩
  exact hjk (congrArg Sigma.fst hy)

variable (c : ∀ j, OddCycle C(Y j, ℂ))
variable (M : ℝ) (hM : 0 ≤ M) (hF : ∀ j, ‖(c j).operator‖ ≤ M)

theorem sigmaCycleRepresentation_extension (j : ℕ) (f : C₀(Y j, ℂ)) :
    sigmaCycleRepresentation Y c
      (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j) f) =
      operatorConjugation (summandIsometry (cycleHilbertFamily Y c) j)
        ((c j).representation (compactFunctionForget f)) := by
  unfold operatorConjugation
  rw [summandIsometry_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext k
  change (c k).representation (sigmaFunctionRestriction Y k
    (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j) f)) (x k) =
      lp.single (E := fun k => (c k).space) 2 j
        ((c j).representation (compactFunctionForget f) (x j)) k
  by_cases hjk : j = k
  · subst k
    rw [sigmaRestriction_extension_same]
    simp
  · rw [sigmaRestriction_extension_ne Y j k hjk, map_zero]
    simp [Pi.single_eq_of_ne (Ne.symm hjk)]

def sigmaComplementCycle (j : ℕ) : OddCycle C₀(Y j, ℂ) :=
  zeroRepresentationCycle (complementHilbertSpace (cycleHilbertFamily Y c) j)
    (complementBlockOperator (cycleHilbertFamily Y c) (fun k => (c k).operator) M hM hF j)

def sigmaCycle_directSum (hself : ∀ j, IsSelfAdjoint (c j).operator)
    (hsq : ∀ j, (c j).operator * (c j).operator = 1) (j : ℕ) :
    ((c j).precomp compactFunctionForget).IsDirectSum (sigmaComplementCycle Y c M hM hF j)
      ((sigmaCycle Y c M hM hF hself hsq).precomp
        (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j))) where
  left := summandIsometry (cycleHilbertFamily Y c) j
  right := complementIsometry (cycleHilbertFamily Y c) j
  orthogonal := summand_complement_orthogonal (cycleHilbertFamily Y c) j
  exhaustive := summand_complement_exhaustive (cycleHilbertFamily Y c) j
  representation_eq f := by
    change sigmaCycleRepresentation Y c
      (zeroExtensionHom (sigmaComponent Y j) (sigmaComponent_open Y j) f) =
        operatorConjugation (summandIsometry (cycleHilbertFamily Y c) j)
          ((c j).representation (compactFunctionForget f)) +
        operatorConjugation (complementIsometry (cycleHilbertFamily Y c) j)
          (0 : End (complementHilbertSpace (cycleHilbertFamily Y c) j))
    rw [sigmaCycleRepresentation_extension]
    simp [operatorConjugation]
  operator_eq := blockOperator_decomposition (cycleHilbertFamily Y c)
    (fun k => (c k).operator) M hM hF j

theorem sigmaCycle_coordinate (hself : ∀ j, IsSelfAdjoint (c j).operator)
    (hsq : ∀ j, (c j).operator * (c j).operator = 1) (j : ℕ) :
    restrictComponent (sigmaComponent Y j) (sigmaComponent_open Y j)
      (cycleClass C₀(Sigma Y, ℂ) (sigmaCycle Y c M hM hF hself hsq)) =
      cycleClass C₀(Y j, ℂ) ((c j).precomp compactFunctionForget) := by
  rw [restrictComponent, precomp_cycleClass]
  rw [directSum_eq _ _ _ (sigmaCycle_directSum Y c M hM hF hself hsq j)]
  have hz : cycleClass C₀(Y j, ℂ) (sigmaComplementCycle Y c M hM hF j) = 0 :=
    degenerate_zero _ (zeroRepresentationCycle_degenerate _ _)
  rw [hz, add_zero]

end CoarseAssembly.Analytic

end

end OAI
