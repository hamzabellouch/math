import OAI.Topology.CoarseAssembly.SeparatedRipsIndex
import OAI.Topology.CoarseAssembly.ClopenNaturality
import OAI.Topology.CoarseAssembly.RipsScaleCompatibility

namespace OAI

/-! # Coarsening commutes with restriction to every sufficiently late component -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic
open scoped ZeroAtInfty

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r s : ℝ}

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
theorem separatedRips_coarsen_preimage (o : ∀ i, Q i) (hrs : r ≤ s) (i : ℕ) :
    letI := separatedMetric o
    ∀ x : Point (Sigma Q) r,
      coarsen hrs x ∈ Set.range (separatedRipsEmbedding o s i) ↔
        x ∈ Set.range (separatedRipsEmbedding o r i) := by
  let := separatedMetric o
  intro x
  change coarsen hrs x ∈ Set.range (mapPoint (separatedComponent i)
    (fun a b => ((separatedComponent_isometry o i).dist_eq a b).le)) ↔
      x ∈ Set.range (mapPoint (separatedComponent i)
        (fun a b => ((separatedComponent_isometry o i).dist_eq a b).le))
  rw [mapPoint_range (separatedComponent i) (separatedComponent_isometry o i),
    mapPoint_range (separatedComponent i) (separatedComponent_isometry o i)]
  rfl

omit [∀ i, DecidableEq (Q i)] in
theorem lateRipsFunctionHom_coarsen (o : ∀ i, Q i) (hrs : r ≤ s)
    (i : ℕ) (hi : s < i) :
    letI := separatedMetric o
    (pullback (inclusion (X := Sigma Q) hrs)).comp (lateRipsFunctionHom o s i) =
      (lateRipsFunctionHom o r i).comp (scaleFunctionHom hrs).toNonUnitalStarAlgHom := by
  let := separatedMetric o
  have hir : r < i := hrs.trans_lt hi
  have heq := pullback_zeroExtension
    (separatedRipsEmbedding o r i) (separatedRipsEmbedding_open o r i hir)
    (separatedRipsEmbedding o s i) (separatedRipsEmbedding_open o s i hi)
    (inclusion (X := Sigma Q) hrs) (inclusion (X := Q i) hrs)
    (fun a => coarsen_mapPoint hrs (separatedComponent i)
      (fun x y => ((separatedComponent_isometry o i).dist_eq x y).le) a)
    (separatedRips_coarsen_preimage o hrs i)
  ext f x
  have hx := congrArg (fun g : C₀(Point (Sigma Q) r, ℂ) => g x)
    (DFunLike.congr_fun heq (compactFunctionLift f))
  have hc : pullback (inclusion (X := Q i) hrs) (compactFunctionLift f) =
      compactFunctionLift ((scaleFunctionHom hrs) f) := by
    ext p
    rfl
  simp only [NonUnitalStarAlgHom.comp_apply] at hx
  rw [hc] at hx
  simpa only [lateRipsFunctionHom, dite_eq_left hi, dite_eq_left hir,
    NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom] using hx

end CoarseAssembly.Rips

end

end OAI
