import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveLiftSimple

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

theorem finiteArtin_positive_left_fraction [Finite M.Group] (g:Artin M) :
    ∃ u v:List S,g=(wordArtin M u)⁻¹*wordArtin M v := by
  obtain ⟨z,hz⟩:=exists_longest M.toCoxeterSystem
  obtain ⟨n,u,hu⟩:=positive_fraction_longest M z hz g
  obtain ⟨v,hv⟩:=positiveLift_longest_square_positive M z
  obtain ⟨v',hv'⟩:=wordArtin_positive_power M v n
  refine ⟨v',u,?_⟩
  rw [hu,hv',hv,zpow_neg,zpow_natCast]
  exact ((positiveLift_longest_square_central M z hz (wordArtin M u)).pow_left n).inv_left.eq.symm

end HarmonicArtin

end OAI
