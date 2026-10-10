import OAI.Topology.CoarseAssembly.ComponentRipsPreimage
import OAI.Topology.CoarseAssembly.LateRipsCoarsening
import OAI.Topology.CoarseAssembly.CoefficientInclusion

namespace OAI

/-! # Exact restriction identity for a component-preserving geometric inclusion -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic
open scoped ZeroAtInfty

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)]

omit [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem componentRips_commutes (o : ∀ i, Q i) (p : ∀ i, P i)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y)
    (r : ℝ) (i : ℕ) :
    letI := separatedMetric o
    letI := separatedMetric p
    ∀ x, mapPoint (componentEmbedding e) he (separatedRipsEmbedding o r i x) =
      separatedRipsEmbedding p r i (mapPoint (e i) (hei i) x) := by
  let := separatedMetric o
  let := separatedMetric p
  intro x
  apply Point.ext
  change (x.weight.embDomain (separatedComponent i)).embDomain (componentEmbedding e) =
    (x.weight.embDomain (e i)).embDomain (separatedComponent i)
  rw [← Finsupp.embDomain_trans_apply, ← Finsupp.embDomain_trans_apply]
  rfl

omit [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem lateRipsFunctionHom_inclusion (o : ∀ i, Q i) (p : ∀ i, P i)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y)
    (r : ℝ) (i : ℕ) (hi : r < i) :
    letI := separatedMetric o
    letI := separatedMetric p
    (pullback (embeddingMap (componentEmbedding e) he r)).comp (lateRipsFunctionHom p r i) =
      (lateRipsFunctionHom o r i).comp (inclusionFunctionHom r (e i) (hei i)).toNonUnitalStarAlgHom := by
  let := separatedMetric o
  let := separatedMetric p
  have heq := pullback_zeroExtension
    (separatedRipsEmbedding o r i) (separatedRipsEmbedding_open o r i hi)
    (separatedRipsEmbedding p r i) (separatedRipsEmbedding_open p r i hi)
    (embeddingMap (componentEmbedding e) he r) (embeddingMap (e i) (hei i) r)
    (componentRips_commutes o p e hei he r i)
    (componentRips_preimage o p e r he i)
  ext f x
  have hx := congrArg (fun g : C₀(Point (Sigma Q) r, ℂ) => g x)
    (DFunLike.congr_fun heq (compactFunctionLift f))
  simp only [NonUnitalStarAlgHom.comp_apply] at hx
  have hc : pullback (embeddingMap (e i) (hei i) r) (compactFunctionLift f) =
      compactFunctionLift (inclusionFunctionHom r (e i) (hei i) f) := by
    ext a
    rfl
  rw [hc] at hx
  simpa only [lateRipsFunctionHom, dite_eq_left hi, NonUnitalStarAlgHom.comp_apply,
    StarAlgHom.coe_toNonUnitalStarAlgHom] using hx

end CoarseAssembly.Rips

end

end OAI
