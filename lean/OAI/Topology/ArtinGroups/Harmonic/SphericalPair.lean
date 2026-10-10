import Mathlib
import OAI.Topology.ArtinGroups.Model
import OAI.Topology.ArtinGroups.Coxeter.AltListReduced

namespace OAI

namespace HarmonicArtin
variable {S : Type*} [Fintype S]
lemma spherical_pair (M : CoxeterMatrix S) (i j : S) (hm : 2≤M i j) :
    IsSpherical M ({i,j} : Set S) :=
  CoxeterExchange.finite_parabolic_pair M.toCoxeterSystem i j hm
end HarmonicArtin

end OAI
