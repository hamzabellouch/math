import OAI.Topology.CoarseAssembly.LateRipsCoarsening
import OAI.Topology.CoarseAssembly.RegularizedCoarsening
import OAI.Topology.CoarseAssembly.RipsFiniteTail

namespace OAI

/-! # Coarsening compatibility of the index on the full analytic domain -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe
open scoped ZeroAtInfty

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r s : ℝ}

omit [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] in
theorem ripsPointCharacter_coarsen (o : ∀ i, Q i) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r ≤ s) (i : ℕ) :
    ripsPointCharacter o s hs i = (ripsPointCharacter o r hr i).comp (scaleFunctionHom hrs) := by
  ext f
  change f (vertex (o i) hs) = f (coarsen hrs (vertex (o i) hr))
  rfl

omit [∀ i, DecidableEq (Q i)] in
theorem late_regularizedCycle_coarsen (o : ∀ i, Q i) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r ≤ s) (c : letI := separatedMetric o; OddCycle C₀(Point (Sigma Q) r, ℂ))
    (i : ℕ) (hi : s < i) :
    letI := separatedMetric o
    ((c.precomp (pullback (inclusion hrs))).precomp (lateRipsFunctionHom o s i)).regularize
      (ripsPointCharacter o s hs i) =
    coarsenedCycle hrs ((c.precomp (lateRipsFunctionHom o r i)).regularize
      (ripsPointCharacter o r hr i)) := by
  let := separatedMetric o
  have hp : (c.precomp (pullback (inclusion hrs))).precomp (lateRipsFunctionHom o s i) =
      (c.precomp (lateRipsFunctionHom o r i)).precomp (scaleFunctionHom hrs).toNonUnitalStarAlgHom :=
    congrArg (fun η => c.precomp η) (lateRipsFunctionHom_coarsen o hrs i hi)
  rw [hp, ripsPointCharacter_coarsen o hr hs hrs i]
  exact (c.precomp (lateRipsFunctionHom o r i)).regularize_precomp_eq
    (scaleFunctionHom hrs) (ripsPointCharacter o r hr i)

theorem ampleRipsOperator_congr {X : Type} [MetricSpace X] [Fintype X] [DecidableEq X]
    (r : ℝ) (c d : OddCycle C(Point X r, ℂ)) (h : c = d)
    (hc : c.representation 1 = 1) (hd : d.representation 1 = 1) :
    ampleRipsOperator r c hc = ampleRipsOperator r d hd := by
  subst d
  rfl

theorem separatedRipsIndex_coarsen (o : ∀ i, Q i) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    letI := separatedMetric o
    letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    (separatedRipsIndex o s hs).comp (pushforward (inclusion (X := Sigma Q) hrs)) =
      separatedRipsIndex o r hr := by
  let := separatedMetric o
  let : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
    inferInstance
  apply Analytic.hom_ext
  intro c
  let C := regularizedFamily (fun i => c.precomp (lateRipsFunctionHom o r i))
    (ripsPointCharacter o r hr)
  let D := regularizedFamily
    (fun i => (c.precomp (pullback (inclusion hrs))).precomp (lateRipsFunctionHom o s i))
    (ripsPointCharacter o s hs)
  let J : Finset ℕ := Finset.range (Nat.ceil s + 1)
  have ht := D.boundary_eq_of_tail (C.coarsen hrs) o hs hs J (by
    intro i hi
    have hni : Nat.ceil s < i := Nat.lt_of_succ_le (Nat.le_of_not_lt (by
      simpa only [J, Finset.mem_range] using hi))
    have hil : s < i := (Nat.le_ceil s).trans_lt (by exact_mod_cast hni)
    exact ampleRipsOperator_congr s _ _ (late_regularizedCycle_coarsen o hr hs hrs c i hil) _ _)
  have hbd : D.boundary o hs = C.boundary o hr :=
    ht.trans (ampleRipsFamilyBoundary_scale hrs o hr hs C.cycle C.unital C.selfAdjoint
      C.bound C.bound_nonneg C.norm_le)
  have hp := congrArg (separatedRipsIndex o s hs)
    (Analytic.precomp_cycleClass (pullback (inclusion (X := Sigma Q) hrs)) c)
  exact hp.trans ((separatedRipsIndex_class o s hs (c.precomp (pullback (inclusion hrs)))).trans
    (hbd.trans (separatedRipsIndex_class o r hr c).symm))

end CoarseAssembly.Rips

end

end OAI
