import Mathlib
import OAI.Topology.ArtinGroups.Realizations.NerveOrderMap
import OAI.Topology.ArtinGroups.Harmonic.EarlierUpper

namespace OAI

namespace HarmonicArtin
open Simplicial CategoryTheory

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

theorem sourceEarlierUpper_contractible (P:Deligne M)
    (h:Nonempty (SourceEarlierUpper M P)) :
    ContractibleSpace |nerve (SourceEarlierUpper M P)| := by
  have ha:=(sourceEarlierUpper_nonempty_iff M P).mp h
  exact nerve_contractible_of_order_clip (sourceUpperRetraction M P)
    (sourceUpperCenter M P ha) (sourceUpperRetraction_le M P)
    (sourceUpperRetraction_le_center M P ha)

end HarmonicArtin

end OAI
