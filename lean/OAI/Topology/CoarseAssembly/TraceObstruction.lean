import OAI.Topology.CoarseAssembly.CongruenceQuotients
import OAI.Topology.CoarseAssembly.TraceSeparation
import OAI.Topology.CoarseAssembly.Holonomy

namespace OAI

/-!
# Matrix trace separation in the congruence quotients

The elementary p-adic separation result is connected here to the actual
`SL₃` matrices and to the closed-walk holonomy identity.
-/

namespace CoarseAssembly.Congruence

/-- The finite matrix trace is the reduction of the p-adic Laurent trace. -/
theorem trace_holonomy_pow (t : ℤ_[2]ˣ) (k m : ℕ) :
    Matrix.trace ((holonomy t k ^ m : Quotient k) : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) =
      PadicInt.toZModPow k (diagonalTrace t m) := by
  rw [holonomy, trace_diagonal_pow]
  simp [diagonalTrace]

/-- The two nontrivial diagonal entries are exchanged when the charge is
negated, so the trace only depends on its absolute value. -/
theorem trace_holonomy_natAbs (t : ℤ_[2]ˣ) (k : ℕ) (m : ℤ) :
    Matrix.trace ((holonomy t k ^ m : Quotient k) : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) =
    Matrix.trace ((holonomy t k ^ m.natAbs : Quotient k) :
      Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) := by
  cases m with
  | ofNat n =>
    exact congrArg
      (fun q : Quotient k => Matrix.trace (q : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))))
      (zpow_natCast (holonomy t k) n)
  | negSucc n =>
    change Matrix.trace ((holonomy t k ^ (-((n + 1 : ℕ) : ℤ)) : Quotient k) :
      Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) = _
    calc
      _ = Matrix.trace ((holonomy t k ^ (((n + 1 : ℕ) : ℤ)) : Quotient k) :
          Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :=
        trace_diagonal_neg _ _
      _ = _ := congrArg
        (fun q : Quotient k => Matrix.trace (q : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))))
        (zpow_natCast (holonomy t k) (n + 1))

/-- Simultaneous trace separation from a finite set of integral word traces,
now stated for the actual finite special linear groups. -/
theorem matrix_trace_separation (t : ℤ_[2]ˣ)
    (ht : Transcendental ℤ (t : ℤ_[2])) (A : ℕ) (traces : Finset ℤ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k, N ≤ k → ∀ m ∈ Finset.Icc 1 A,
      ∀ w : ArithmeticGroup, Matrix.trace (w : Matrix (Fin 3) (Fin 3) ℤ) ∈ traces →
        Matrix.trace ((holonomy t k ^ m : Quotient k) : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) ≠
          Matrix.trace (reduce k w : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) := by
  obtain ⟨N, hN, hsep⟩ := finite_trace_separation t ht A traces
  refine ⟨N, hN, ?_⟩
  intro k hk m hm w hw
  rw [trace_holonomy_pow, trace_reduce]
  exact hsep k hk m hm _ hw

/-- A closed word in a finite quotient forces equality of the concrete
matrix traces. This is the contradiction paired with separation above. -/
theorem closed_walk_trace (t : ℤ_[2]ˣ) (k : ℕ) (z : Quotient k)
    (steps : List (Quotient k × ℤ))
    (hclosed : holonomyEndpoint (holonomy t k) steps z = z) :
    Matrix.trace ((holonomy t k ^ holonomyCharge steps : Quotient k) :
      Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) =
    Matrix.trace (((holonomyWord steps)⁻¹ : Quotient k) : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :=
  holonomy_invariant_eq
    (fun q : Quotient k => Matrix.trace (q : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))))
    (fun q z => trace_conjugate q z) (holonomy t k) z steps hclosed

end CoarseAssembly.Congruence

end OAI
