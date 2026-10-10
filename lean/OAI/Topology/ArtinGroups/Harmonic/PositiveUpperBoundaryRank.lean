import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.EarlierLinkSubtypeIso
import OAI.Topology.ArtinGroups.Harmonic.PositiveUpperBoundaryRestriction

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable

theorem positiveUpperBoundary_rank (n : ℕ) :
    ∀ {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
      (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
      (inj : Function.Injective (positiveToArtin M)) (a : NoncriticalPositiveCell M)
      (_ : matchingLetter M z hz a ∈ a.val.2.val) (_ : a.val.2.val.ncard = n),
    ContractibleSpace (OrderWeights {b : PositiveCellPoset M inj //
      positiveCellToLifted M b < positiveCellToLifted M a.val ∧
      b ≠ (positiveMatch M z hz inj a).val}) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S _ _ M z hz inj a hs hn
    let N := restrictedMatrix M a.val.2.val
    let : Finite N.Group := restricted_finite M a.val.2.val a.val.2.property
    obtain ⟨q,hq⟩ := exists_longest N.toCoxeterSystem
    let injN := spherical_positiveToArtin_injective M a.val.2.val a.val.2.property
    have hc : positiveCellTop N (positiveFullCell N) ≠ 1 :=
      positiveFullCell_noncritical N ⟨matchingLetter M z hz a,hs⟩
    let c : NoncriticalPositiveCell N := ⟨positiveFullCell N,hc⟩
    let D : Set (PositiveCellPoset N injN) := {b |
      positiveCellToLifted N b < fullSphericalCell N ∧ b ≠ (positiveMatch N q hq injN c).val}
    have hD : ContractibleSpace (OrderWeights D) := by
      apply invariantPositive_contractible N q hq injN D
        (positiveFullBoundary_root N q hq injN hc)
        (positiveFullBoundary_down N q hq injN hc)
        (positiveFullBoundary_match N q hq injN hc)
      intro b hb hbs
      have hk : b.val.2.val.ncard < n := by
        have hh := lifted_rank_strict N hb.1
        change b.val.2.val.ncard < (Set.univ : Set a.val.2.val).ncard at hh
        simpa only [Set.ncard_univ,Nat.card_coe_set_eq,hn] using hh
      exact ih b.val.2.val.ncard hk N q hq injN b hbs rfl
    let e := positiveUpperBoundaryRestrictionIso M z hz inj a hs q hq injN hc
    rw [positiveFullCell_lifted] at e
    exact (weightHomeomorph e).contractibleSpace_iff.mp hD

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

theorem positiveUpperBoundary_contractible (a : NoncriticalPositiveCell M)
    (hs : matchingLetter M z hz a ∈ a.val.2.val) :
    ContractibleSpace (OrderWeights {b : PositiveCellPoset M inj //
      positiveCellToLifted M b < positiveCellToLifted M a.val ∧
      b ≠ (positiveMatch M z hz inj a).val}) :=
  positiveUpperBoundary_rank a.val.2.val.ncard M z hz inj a hs rfl

include z hz

theorem positiveCellPoset_contractible : ContractibleSpace (OrderWeights (PositiveCellPoset M inj)) := by
  apply orderWeights_contractible_of_earlier_links (PositiveEarlier M z hz inj)
    (positiveEarlier_wf M z hz inj) (positiveEarlier_total M z hz inj)
    (positiveRootCell M) (positiveEarlier_root M z hz inj)
  intro a ha
  have hn : positiveCellTop M a ≠ 1 := fun h => ha ((positiveCellTop_eq_one_iff M a).mp h)
  let c : NoncriticalPositiveCell M := ⟨a,hn⟩
  by_cases hs : matchingLetter M z hz c ∈ c.val.2.val
  · exact (weightHomeomorph (positiveEarlierLink_upper_iso M z hz inj c hs)).contractibleSpace_iff.mpr
      (positiveUpperBoundary_contractible M z hz inj c hs)
  · exact positiveEarlierLink_lower_contractible M z hz inj c hs

end HarmonicArtin

end OAI
