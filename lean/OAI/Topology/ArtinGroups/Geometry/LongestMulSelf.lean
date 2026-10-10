import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RootNonposDescent

namespace OAI

namespace HarmonicArtin.Geometric
open CoxeterExchange

variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

lemma longest_mul_self (z:W) (hz:∀w,cs.length w≤cs.length z) : z*z=1 := by
  have h:=length_mul_of_all_descents cs z (all_descents_of_longest cs z hz) z
  exact cs.length_eq_zero_iff.mp (by omega)

lemma longest_conjugates_simple (z:W) (hz:∀w,cs.length w≤cs.length z) (s:S) :
    ∃ t:S,z*cs.simple s*z=cs.simple t := by
  apply cs.length_eq_one_iff.mp
  have h:=length_mul_of_all_descents cs z (all_descents_of_longest cs z hz) (cs.simple s*z)
  have h':=all_left_descents_of_longest cs z hz s
  rw [← mul_assoc] at h
  omega

end HarmonicArtin.Geometric

end OAI
