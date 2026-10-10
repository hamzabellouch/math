import OAI.Topology.CoarseAssembly.IndexPairing
import OAI.Topology.CoarseAssembly.CompactHomotopy

namespace OAI

/-! # The scalar-unitary pairing for compact spaces -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y]

/-- A circle-valued map as a unitary in the compact continuous-function algebra. -/
def compactUnitary (f : C(X, Circle)) : C(X, ℂ) :=
  ⟨fun x => (f x : ℂ), continuous_subtype_val.comp f.continuous⟩

omit [CompactSpace X] in
theorem compactUnitary_star_mul (f : C(X, Circle)) : star (compactUnitary f) * compactUnitary f = 1 := by
  ext x
  change star (f x : ℂ) * (f x : ℂ) = 1
  simp only [Complex.star_def, Complex.conj_mul', Circle.norm_coe, one_pow, Complex.ofReal_one]

omit [CompactSpace X] in
theorem compactUnitary_mul_star (f : C(X, Circle)) : compactUnitary f * star (compactUnitary f) = 1 := by
  rw [mul_comm]
  exact compactUnitary_star_mul f

/-- The index pairing on the actual locally finite K-homology group. -/
def compactIndexPairing (f : C(X, Circle)) : LocallyFiniteK1 X →+ ℤ :=
  (indexPairing (compactUnitary f) (compactUnitary_star_mul f)
    (compactUnitary_mul_star f)).comp (precomp compactFunctionLift)

@[simp] theorem compactIndexPairing_cycleClass (f : C(X, Circle)) (c : OddCycle C₀(X, ℂ)) :
    compactIndexPairing f (cycleClass C₀(X, ℂ) c) =
      rawCycleIndex (c.precomp compactFunctionLift) (compactUnitary f) := by
  simp only [compactIndexPairing, AddMonoidHom.comp_apply, precomp_cycleClass,
    indexPairing_cycleClass]

theorem compactFunctionLift_pullback (γ : C(X, Y)) :
    (pullback (compactMap γ)).comp (compactFunctionLift (X := Y)) =
      (compactFunctionLift (X := X)).comp
        (ContinuousMap.compStarAlgHom' ℂ ℂ γ).toNonUnitalStarAlgHom := by
  ext a x
  rfl

theorem compactIndexPairing_natural (f : C(Y, Circle)) (γ : C(X, Y)) :
    (compactIndexPairing f).comp (pushforward (compactMap γ)) =
      compactIndexPairing (f.comp γ) := by
  apply hom_ext
  intro c
  simp only [AddMonoidHom.comp_apply, pushforward, precomp_cycleClass,
    compactIndexPairing_cycleClass, OddCycle.precomp_comp, compactFunctionLift_pullback]
  let φ := (ContinuousMap.compStarAlgHom' ℂ ℂ γ).toNonUnitalStarAlgHom
  have hφ : φ 1 = 1 := map_one (ContinuousMap.compStarAlgHom' ℂ ℂ γ)
  exact rawCycleIndex_precomp (c.precomp compactFunctionLift) φ hφ (compactUnitary f)

end CoarseAssembly.Analytic

end

end OAI
