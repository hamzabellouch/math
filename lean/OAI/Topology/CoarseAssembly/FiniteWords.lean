import OAI.Topology.CoarseAssembly.TraceObstruction

namespace OAI

/-!
# Uniform exclusion of short charged closed words

This is the algebraic part of the small-loop lemma in §3, specialized to
`SL₃(ℤ)` and its actual congruence quotients. The finite family of possible
word traces is constructed, rather than postulated as an extra input.
-/

namespace CoarseAssembly.Congruence

/-- Words of length at most `n` in a finite set of left moves. -/
def wordBall (S : Finset ArithmeticGroup) : ℕ → Finset ArithmeticGroup
  | 0 => {1}
  | n + 1 => wordBall S n ∪ (wordBall S n).biUnion (fun w => S.image (w * ·))

theorem wordBall_mono (S : Finset ArithmeticGroup) {n m : ℕ} (h : n ≤ m) :
    wordBall S n ⊆ wordBall S m := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step h ih => exact ih.trans Finset.subset_union_left

theorem holonomyWord_mem (S : Finset ArithmeticGroup) (steps : List (ArithmeticGroup × ℤ))
    (hS : ∀ s ∈ steps, s.1 ∈ S) : holonomyWord steps ∈ wordBall S steps.length := by
  induction steps with
  | nil => simp [holonomyWord, wordBall]
  | cons s steps ih =>
    have hs : s.1 ∈ S := hS s (by simp)
    have ht : ∀ q ∈ steps, q.1 ∈ S := fun q hq => hS q (by simp [hq])
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨holonomyWord steps, ih ht,
      Finset.mem_image.mpr ⟨s.1, hs, rfl⟩⟩

theorem holonomyCharge_natAbs_le (steps : List (ArithmeticGroup × ℤ))
    (hs : ∀ s ∈ steps, s.2.natAbs ≤ 1) : (holonomyCharge steps).natAbs ≤ steps.length := by
  induction steps with
  | nil => simp [holonomyCharge]
  | cons s steps ih =>
    have hhead : s.2.natAbs ≤ 1 := hs s (by simp)
    have htail : (holonomyCharge steps).natAbs ≤ steps.length :=
      ih (fun q hq => hs q (by simp [hq]))
    exact (Int.natAbs_add_le _ _).trans (by simpa [Nat.add_comm] using Nat.add_le_add hhead htail)

/-- Reduction of each left move, preserving its signed base charge. -/
def reduceSteps (k : ℕ) (steps : List (ArithmeticGroup × ℤ)) : List (Quotient k × ℤ) :=
  steps.map (fun s => (reduce k s.1, s.2))

@[simp] theorem holonomyCharge_reduceSteps (k : ℕ) (steps : List (ArithmeticGroup × ℤ)) :
    holonomyCharge (reduceSteps k steps) = holonomyCharge steps := by
  induction steps with
  | nil => rfl
  | cons s steps ih => simpa only [reduceSteps, List.map_cons, holonomyCharge] using congrArg (s.2 + ·) ih

@[simp] theorem holonomyWord_reduceSteps (k : ℕ) (steps : List (ArithmeticGroup × ℤ)) :
    holonomyWord (reduceSteps k steps) = reduce k (holonomyWord steps) := by
  induction steps with
  | nil => simp [reduceSteps, holonomyWord]
  | cons s steps ih =>
    simpa only [reduceSteps, List.map_cons, holonomyWord, map_mul] using
      congrArg (· * reduce k s.1) ih

/-- At a sufficiently deep quotient, no bounded list of allowed Cayley/base
moves can close with nonzero charge. This conclusion does not assume a
spectral gap, a property-(T) theorem, or an analytic K-homology fact. -/
theorem bounded_closed_lifts_have_zero_charge (t : ℤ_[2]ˣ)
    (ht : Transcendental ℤ (t : ℤ_[2])) (S : Finset ArithmeticGroup) (A : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k, N ≤ k → ∀ z : Quotient k,
      ∀ steps : List (ArithmeticGroup × ℤ), steps.length ≤ A →
        (∀ s ∈ steps, s.1 ∈ S ∧ s.2.natAbs ≤ 1) →
        holonomyEndpoint (holonomy t k) (reduceSteps k steps) z = z →
        holonomyCharge steps = 0 := by
  let traces := (wordBall S A).image
    (fun w => Matrix.trace ((w⁻¹ : ArithmeticGroup) : Matrix (Fin 3) (Fin 3) ℤ))
  obtain ⟨N, hN, hsep⟩ := matrix_trace_separation t ht A traces
  refine ⟨N, hN, ?_⟩
  intro k hk z steps hlen hsteps hclosed
  by_contra hcharge
  have hpos : 1 ≤ (holonomyCharge steps).natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hcharge)
  have hbound : (holonomyCharge steps).natAbs ≤ A :=
    (holonomyCharge_natAbs_le steps (fun s hs => (hsteps s hs).2)).trans hlen
  have hword : holonomyWord steps ∈ wordBall S A :=
    wordBall_mono S hlen (holonomyWord_mem S steps (fun s hs => (hsteps s hs).1))
  have htrace : Matrix.trace (((holonomyWord steps)⁻¹ : ArithmeticGroup) :
      Matrix (Fin 3) (Fin 3) ℤ) ∈ traces :=
    Finset.mem_image.mpr ⟨holonomyWord steps, hword, rfl⟩
  have hne := hsep k hk (holonomyCharge steps).natAbs
    (Finset.mem_Icc.mpr ⟨hpos, hbound⟩) (holonomyWord steps)⁻¹ htrace
  apply hne
  rw [← trace_holonomy_natAbs]
  simpa only [holonomyCharge_reduceSteps, holonomyWord_reduceSteps, map_inv] using
    closed_walk_trace t k z (reduceSteps k steps) hclosed

end CoarseAssembly.Congruence

end OAI
