import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RegularizedRipsRelations

namespace OAI

/-! # A whole-union index on the actual analytic K-homology domain

Restriction homomorphisms into a family of finite Rips function algebras
are explicit parameters. The map descends through every relation of the
original Fredholm-module group, without a countable-additivity assumption.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ} {A : Type} [NonUnitalCStarAlgebra A]

theorem analyticFamilyIndexFree_relation (o : ∀ i, Q i) (hr : 0 ≤ r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (η : ∀ i, C(Point (Q i) r, ℂ) →⋆ₙₐ[ℂ] A)
    {z : FreeAbelianGroup (OddCycle A)} (hz : CycleRelation A z) :
    analyticFamilyIndexFree o hr χ η z = 0 := by
  let := separatedMetric o
  cases hz with
  | degenerate c h =>
    simpa only [analyticFamilyIndexFree, FreeAbelianGroup.lift_apply_of] using
      regularizedFamily_degenerate (fun i => c.precomp (η i))
        (fun i => h.precomp (η i)) χ o hr
  | unitary c d h =>
    simp only [analyticFamilyIndexFree, map_sub, FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (regularizedFamily_unitary _ _ (fun i => h.precomp (η i)) χ o hr)
  | directSum c d e h =>
    simp only [analyticFamilyIndexFree, map_sub, map_add, FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (regularizedFamily_directSum _ _ _ (fun i => h.precomp (η i)) χ o hr)
  | homotopy h =>
    simp only [analyticFamilyIndexFree, map_sub, FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (regularizedFamily_homotopy (fun i => h.precomp (η i)) χ o hr)

theorem analyticFamilyIndex_eq_lift (o : ∀ i, Q i) (hr : 0 ≤ r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (η : ∀ i, C(Point (Q i) r, ℂ) →⋆ₙₐ[ℂ] A) :
    letI := separatedMetric o
    letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    analyticFamilyIndex o hr χ η =
      QuotientAddGroup.lift (relations A) (analyticFamilyIndexFree o hr χ η)
        ((AddSubgroup.closure_le _).2 (fun _ hz => analyticFamilyIndexFree_relation o hr χ η hz)) := by
  classical
  let := separatedMetric o
  let : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
    inferInstance
  dsimp only [analyticFamilyIndex]
  split_ifs with h
  · rfl
  · exact (h ((AddSubgroup.closure_le _).2
      (fun _ hz => analyticFamilyIndexFree_relation o hr χ η hz))).elim

@[simp] theorem analyticFamilyIndex_class (o : ∀ i, Q i) (hr : 0 ≤ r)
    (χ : ∀ i, C(Point (Q i) r, ℂ) →⋆ₐ[ℂ] ℂ)
    (η : ∀ i, C(Point (Q i) r, ℂ) →⋆ₙₐ[ℂ] A) (c : OddCycle A) :
    letI := separatedMetric o
    letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    analyticFamilyIndex o hr χ η (cycleClass A c) =
      (regularizedFamily (fun i => c.precomp (η i)) χ).boundary o hr :=
  by
    let := separatedMetric o
    let : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    have h := DFunLike.congr_fun (analyticFamilyIndex_eq_lift o hr χ η) (cycleClass A c)
    exact h.trans (FreeAbelianGroup.lift_apply_of _ _)

end CoarseAssembly.Rips

end

end OAI
