import OAI.Topology.CoarseAssembly.DirectSumIndex

namespace OAI

/-! # The scalar-unitary index pairing on odd analytic K-homology

All four defining Fredholm-cycle relations are respected by the explicit
Toeplitz index. Hence it descends to the existing quotient group.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

def indexFree (u : A) : FreeAbelianGroup (OddCycle A) →+ ℤ :=
  FreeAbelianGroup.lift (fun c => rawCycleIndex c u)

theorem indexFree_relation (u : A) (hul : star u * u = 1) (hur : u * star u = 1)
    {z : FreeAbelianGroup (OddCycle A)} (hz : CycleRelation A z) : indexFree u z = 0 := by
  cases hz with
  | degenerate c h =>
    simpa [indexFree] using rawCycleIndex_degenerate c u h hul hur
  | unitary c d h =>
    simpa [indexFree] using sub_eq_zero.mpr (rawCycleIndex_unitary c d h u hul hur).symm
  | directSum c d e h =>
    simpa [indexFree] using sub_eq_zero.mpr (rawCycleIndex_directSum h u hul hur)
  | homotopy h =>
    simpa [indexFree] using sub_eq_zero.mpr (rawCycleIndex_homotopy h u hul hur)

/-- Pairing an odd analytic class with an actual scalar unitary. -/
def indexPairing (u : A) (hul : star u * u = 1) (hur : u * star u = 1) : OddK A →+ ℤ :=
  QuotientAddGroup.lift (relations A) (indexFree u)
    ((AddSubgroup.closure_le _).2 (fun _ hz => indexFree_relation u hul hur hz))

@[simp] theorem indexPairing_cycleClass (u : A) (hul : star u * u = 1)
    (hur : u * star u = 1) (c : OddCycle A) :
    indexPairing u hul hur (cycleClass A c) = rawCycleIndex c u :=
  FreeAbelianGroup.lift_apply_of _ _

variable {B : Type} [CStarAlgebra B]

theorem indexPairing_precomp (φ : B →⋆ₙₐ[ℂ] A) (hφ : φ 1 = 1) (u : B)
    (hul : star u * u = 1) (hur : u * star u = 1) :
    (indexPairing u hul hur).comp (precomp φ) = indexPairing (φ u)
      (by rw [← map_star, ← map_mul, hul, hφ])
      (by rw [← map_star, ← map_mul, hur, hφ]) := by
  apply hom_ext
  intro c
  simp only [AddMonoidHom.comp_apply, precomp_cycleClass, indexPairing_cycleClass]
  exact rawCycleIndex_precomp c φ hφ u

end CoarseAssembly.Analytic

end

end OAI
