import Mathlib
import OAI.RingTheory.Kurosh.LiftingStages

namespace OAI

/-! Independent tangent directions at the universal pair of formal variables. -/

namespace KuroshConstruction

lemma letterTuple_liftingInput (K : Type) [Field K] :
    LiftingInput K (FreeSeries.letter : Fin 2 → FreeSeries K) := by
  have hzero : constantTuple (FreeSeries.letter : Fin 2 → FreeSeries K) = 0 := by
    ext i
    simp [constantTuple]
  have hinter : innerTangent K (constantTuple
      (FreeSeries.letter : Fin 2 → FreeSeries K)) = ⊥ := by
    rw [hzero]
    apply LinearMap.range_eq_bot.mpr
    ext t
    simp [innerDirection]
  constructor
  · apply top_unique
    intro x _
    exact (Algebra.adjoin K (Set.range (constantTuple
      (FreeSeries.letter : Fin 2 → FreeSeries K)))).algebraMap_mem x
  · have hletter : (letterTuple (FreeSeries.letter : Fin 2 → FreeSeries K)) =
        fun j => Pi.basisFun K (Fin 2) j := by
      ext j i
      simp [letterTuple, Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rw [hletter]
    apply (Pi.basisFun K (Fin 2)).linearIndependent.map'
    rw [Submodule.ker_mkQ, hinter]

noncomputable def seedStage : LiftingStage := by
  let K := AlgebraicClosure ℚ
  let : Algebra.IsAlgebraic ℚ K := AlgebraicClosure.isAlgebraic ℚ
  have hc : Set.Countable (Set.univ : Set K) := by
    convert Algebraic.countable ℚ K using 1
    ext a
    simp only [Set.mem_univ, Set.mem_ofPred_eq, true_iff]
    exact Algebra.IsAlgebraic.isAlgebraic a
  let : Countable K := Set.countable_univ_iff.mp hc
  refine ⟨K, K, ?_, FreeSeries.letter, letterTuple_liftingInput K⟩
  intro n hn
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot K n

end KuroshConstruction

end OAI
