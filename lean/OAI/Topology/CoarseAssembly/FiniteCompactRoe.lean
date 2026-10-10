import OAI.Topology.CoarseAssembly.Roe

namespace OAI

/-! # Compact self-adjoint operators on a finite component lie in its Roe algebra -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem finite_propagation_bound (T : Operator X H) :
    ∃ r : ℝ, 0 ≤ r ∧ PropagationLE r T := by
  let r : ℝ := ∑ x : X, ∑ y : X, dist x y
  have hr : 0 ≤ r := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  refine ⟨r, hr, ?_⟩
  intro x y hxy
  have h1 : dist x y ≤ ∑ z : X, dist x z :=
    Finset.single_le_sum (f := fun z : X => dist x z)
      (fun _ _ => dist_nonneg) (Finset.mem_univ y)
  have h2 : (∑ z : X, dist x z) ≤ r :=
    Finset.single_le_sum (f := fun z : X => ∑ w : X, dist z w)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
      (Finset.mem_univ x)
  exact False.elim ((not_lt_of_ge (h1.trans h2)) hxy)

omit [Fintype X] [PseudoMetricSpace X] [CompleteSpace H] in
theorem compact_entries_of_compact {T : Operator X H} (hT : IsCompactOperator T) :
    CompactEntries T := fun x y => (hT.comp_clm (insert y)).clm_comp (coordinate x)

theorem compact_selfAdjoint_mem_roe {T : Operator X H}
    (hT : IsCompactOperator T) (hself : IsSelfAdjoint T) :
    T ∈ algebra (X := X) (H := H) := by
  apply generator_mem
  refine ⟨finite_propagation_bound T, compact_entries_of_compact hT, ?_⟩
  rw [hself.star_eq]
  exact compact_entries_of_compact hT

end CoarseAssembly.DiscreteRoe

end

end OAI
