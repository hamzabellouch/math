import OAI.Topology.CoarseAssembly.ComponentRestrictionNaturality
import OAI.Topology.CoarseAssembly.RipsFamilyInclusion
import OAI.Topology.CoarseAssembly.SeparatedIndexCoarsening

namespace OAI

/-! # Geometric naturality on the actual locally finite analytic domain -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe
open scoped ZeroAtInfty

variable {Q P : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, MetricSpace (P i)]
  [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] {r : ℝ}

omit [∀ i, Fintype (Q i)] [∀ i, Fintype (P i)]
  [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem ripsPointCharacter_included (o : ∀ i, Q i) (p : ∀ i, P i) (hr : 0 ≤ r)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (hroot : ∀ i, e i (o i) = p i) (i : ℕ) :
    ripsPointCharacter p r hr i =
      (ripsPointCharacter o r hr i).comp (inclusionFunctionHom r (e i) (hei i)) := by
  ext f
  change f (vertex (p i) hr) = f (mapPoint (e i) (hei i) (vertex (o i) hr))
  rw [mapPoint_vertex, hroot i]

omit [∀ i, DecidableEq (Q i)] [∀ i, DecidableEq (P i)] in
theorem late_regularizedCycle_included (o : ∀ i, Q i) (p : ∀ i, P i) (hr : 0 ≤ r)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (hroot : ∀ i, e i (o i) = p i)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y)
    (c : letI := separatedMetric o; OddCycle C₀(Point (Sigma Q) r, ℂ)) (i : ℕ) (hi : r < i) :
    letI := separatedMetric o
    letI := separatedMetric p
    ((c.precomp (pullback (embeddingMap (componentEmbedding e) he r))).precomp
      (lateRipsFunctionHom p r i)).regularize (ripsPointCharacter p r hr i) =
      includedCycle r (e i) (hei i)
        ((c.precomp (lateRipsFunctionHom o r i)).regularize (ripsPointCharacter o r hr i)) := by
  let := separatedMetric o
  let := separatedMetric p
  have hp : (c.precomp (pullback (embeddingMap (componentEmbedding e) he r))).precomp
      (lateRipsFunctionHom p r i) =
      (c.precomp (lateRipsFunctionHom o r i)).precomp
        (inclusionFunctionHom r (e i) (hei i)).toNonUnitalStarAlgHom :=
    congrArg (fun η => c.precomp η) (lateRipsFunctionHom_inclusion o p e hei he r i hi)
  rw [hp, ripsPointCharacter_included o p hr e hei hroot i]
  exact (c.precomp (lateRipsFunctionHom o r i)).regularize_precomp_eq
    (inclusionFunctionHom r (e i) (hei i)) (ripsPointCharacter o r hr i)

private theorem ampleRipsOperator_eq_of_cycle_eq {X : Type} [MetricSpace X] [Fintype X] [DecidableEq X]
    (r : ℝ) (c d : OddCycle C(Point X r, ℂ)) (h : c = d)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1) :
    ampleRipsOperator r c hc = ampleRipsOperator r d hd := by
  subst d
  rfl

theorem separatedRipsIndex_inclusion (o : ∀ i, Q i) (p : ∀ i, P i) (hr : 0 ≤ r)
    (e : ∀ i, Q i ↪ P i) (hei : ∀ i x y, dist (e i x) (e i y) ≤ dist x y)
    (hroot : ∀ i, e i (o i) = p i)
    (he : letI := separatedMetric o; letI := separatedMetric p
      ∀ x y, dist (componentEmbedding e x) (componentEmbedding e y) ≤ dist x y) :
    letI := separatedMetric o
    letI := separatedMetric p
    letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    letI : Ring (Unitization ℂ (algebra (X := Sigma P) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    (separatedRipsIndex p r hr).comp (pushforward (embeddingMap (componentEmbedding e) he r)) =
      (OperatorKTheory.map (inclusionHom (X := Sigma Q) (Y := Sigma P) (H := lp (fun _ : ℕ => ℂ) 2)
      (componentEmbedding e) he)).comp (separatedRipsIndex o r hr) := by
  let := separatedMetric o
  let := separatedMetric p
  let : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
    inferInstance
  let : Ring (Unitization ℂ (algebra (X := Sigma P) (H := lp (fun _ : ℕ => ℂ) 2))) :=
    inferInstance
  apply Analytic.hom_ext
  intro c
  let K := OperatorKTheory.map (inclusionHom (X := Sigma Q) (Y := Sigma P) (H := lp (fun _ : ℕ => ℂ) 2)
      (componentEmbedding e) he)
  let C := regularizedFamily (fun i => c.precomp (lateRipsFunctionHom o r i)) (ripsPointCharacter o r hr)
  let D := regularizedFamily
    (fun i => (c.precomp (pullback (embeddingMap (componentEmbedding e) he r))).precomp
      (lateRipsFunctionHom p r i)) (ripsPointCharacter p r hr)
  let J : Finset ℕ := Finset.range (Nat.ceil r + 1)
  have ht := D.boundary_eq_of_tail (C.included e hei) p hr hr J (by
    intro i hi
    have hni : Nat.ceil r < i := Nat.lt_of_succ_le (Nat.le_of_not_lt (by
      simpa only [J, Finset.mem_range] using hi))
    have hil : r < i := (Nat.le_ceil r).trans_lt (by exact_mod_cast hni)
    exact ampleRipsOperator_eq_of_cycle_eq r _ _
      (late_regularizedCycle_included o p hr e hei hroot he c i hil) _ _)
  have hbd : D.boundary p hr = K (C.boundary o hr) :=
    ht.trans (C.boundary_included o p hr e hei he).symm
  have hp := congrArg (separatedRipsIndex p r hr)
    (Analytic.precomp_cycleClass (pullback (embeddingMap (componentEmbedding e) he r)) c)
  have hsource := congrArg K (separatedRipsIndex_class o r hr c)
  exact hp.trans ((separatedRipsIndex_class p r hr
    (c.precomp (pullback (embeddingMap (componentEmbedding e) he r)))).trans
      (hbd.trans hsource.symm))

end CoarseAssembly.Rips

end

end OAI
