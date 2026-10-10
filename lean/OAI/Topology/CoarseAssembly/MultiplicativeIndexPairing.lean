import OAI.Topology.CoarseAssembly.EssentialToeplitzIndex
import OAI.Topology.CoarseAssembly.UnitaryHomotopyIndex

namespace OAI

/-! # Additivity of the scalar-unitary pairing under multiplication -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem rawCycleIndex_mul (c : OddCycle A) (u v : A)
    (hul : star u * u = 1) (hur : u * star u = 1)
    (hvl : star v * v = 1) (hvr : v * star v = 1) :
    rawCycleIndex c (u * v) = rawCycleIndex c u + rawCycleIndex c v := by
  have hc : Commute c.cutDown.operator (c.cutDown.representation 1) :=
    commute_of_complement _ _ (cutDown_selfAdjoint c)
      (representation_unit_selfAdjoint c.cutDown) (cutDown_complement c)
  have hcomm (a : A) : IsCompactOperator
      (c.cutDown.operator * unitaryExtension c.cutDown a -
        unitaryExtension c.cutDown a * c.cutDown.operator : End c.cutDown.space) := by
    rw [unitaryExtension_commutator c.cutDown a hc]
    exact c.cutDown.commutator_compact a
  obtain ⟨hUl, hUr⟩ := unitaryExtension_unitary c.cutDown u hul hur
  obtain ⟨hVl, hVr⟩ := unitaryExtension_unitary c.cutDown v hvl hvr
  have hi := essentialToeplitz_index_mul c.cutDown.operator
    (unitaryExtension c.cutDown u) (unitaryExtension c.cutDown v)
    (cutDown_selfAdjoint c) (cutDown_square_compact c) hUl hUr hVl hVr (hcomm u) (hcomm v)
  rw [unitaryExtension_mul] at hi
  simp only [rawCycleIndex, rawCycleToeplitz_eq_cutDown, representedToeplitz]
  exact hi

open scoped ZeroAtInfty

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

theorem compactIndexPairing_mul (f g : C(X, Circle)) :
    compactIndexPairing (f * g) = compactIndexPairing f + compactIndexPairing g := by
  apply hom_ext
  intro c
  simp only [AddMonoidHom.add_apply, compactIndexPairing_cycleClass]
  have he : compactUnitary (f * g) = compactUnitary f * compactUnitary g := rfl
  rw [he]
  exact rawCycleIndex_mul _ _ _ (compactUnitary_star_mul f) (compactUnitary_mul_star f)
    (compactUnitary_star_mul g) (compactUnitary_mul_star g)

theorem compactIndexPairing_one : compactIndexPairing (1 : C(X, Circle)) = 0 := by
  have h := compactIndexPairing_mul (1 : C(X, Circle)) 1
  rw [one_mul] at h
  exact add_eq_left.mp h.symm

theorem compactIndexPairing_pow (f : C(X, Circle)) (n : ℕ) :
    compactIndexPairing (f ^ n) = n • compactIndexPairing f := by
  induction n with
  | zero => simp only [pow_zero, compactIndexPairing_one, zero_smul]
  | succ n ih => rw [pow_succ, compactIndexPairing_mul, ih, succ_nsmul]

theorem compactIndexPairing_inv (f : C(X, Circle)) :
    compactIndexPairing f⁻¹ = -compactIndexPairing f := by
  have h := compactIndexPairing_mul f f⁻¹
  rw [mul_inv_cancel, compactIndexPairing_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem compactIndexPairing_zpow (f : C(X, Circle)) (n : ℤ) :
    compactIndexPairing (f ^ n) = n • compactIndexPairing f := by
  cases n with
  | ofNat n => simpa using compactIndexPairing_pow f n
  | negSucc n =>
    rw [zpow_negSucc, compactIndexPairing_inv, compactIndexPairing_pow]
    simp only [Int.negSucc_eq, neg_smul]
    rw [← Nat.cast_add_one, natCast_zsmul]

end CoarseAssembly.Analytic

end

end OAI
