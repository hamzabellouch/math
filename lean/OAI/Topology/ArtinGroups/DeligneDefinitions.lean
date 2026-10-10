import Mathlib
import OAI.Topology.ArtinGroups.Model

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}
def artinParabolic (M : CoxeterMatrix S) (T : Set S) : Subgroup (Artin M) :=
  Subgroup.closure (generator M '' T)

def rightCoset (M : CoxeterMatrix S) (T : Set S) (x : Artin M) : Set (Artin M) :=
  {g | g * x⁻¹ ∈ artinParabolic M T}

abbrev Deligne (M : CoxeterMatrix S) :=
  {c : Set S × Set (Artin M) //
    IsSpherical M c.1 ∧ ∃ x : Artin M, c.2 = rightCoset M c.1 x}

noncomputable def DeligneRealization (M : CoxeterMatrix S) : TopCat :=
  SSet.toTop.obj (CategoryTheory.nerve (Deligne M))

end HarmonicArtin

end OAI
