import Mathlib
import OAI.RingTheory.Multiplicity.RootCechProjective
import OAI.RingTheory.Multiplicity.RootRestriction

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
variable {s t v : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty) (hv : v.Nonempty)
  (m : Fin n → ℤ)

def sectionsRestrictionBase (hst : s ⊆ t) :
    Sections R n s hs m →ₗ[R] Sections R n t ht m where
  toFun := sectionsRestriction R n hs ht m hst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma sectionsRestrictionBase_apply (hst : s ⊆ t) (x : Sections R n s hs m) :
    sectionsRestrictionBase R n hs ht m hst x = sectionsRestriction R n hs ht m hst x := rfl

lemma sectionsRestrictionBase_self (x : Sections R n s hs m) :
    sectionsRestrictionBase R n hs hs m (Finset.Subset.refl s) x=x := rfl

lemma sectionsRestrictionBase_comp (hst : s ⊆ t) (htv : t ⊆ v) (x : Sections R n s hs m) :
    sectionsRestrictionBase R n ht hv m htv (sectionsRestrictionBase R n hs ht m hst x)=
      sectionsRestrictionBase R n hs hv m (hst.trans htv) x := rfl

lemma gridSectionsEquiv_restriction (hst : s ⊆ t) (x : grid R n m s ∅) :
    gridSectionsEquiv R n t ht m (Submodule.inclusion (grid_target_mono R n m ∅ hst) x) =
      sectionsRestrictionBase R n hs ht m hst (gridSectionsEquiv R n s hs m x) := rfl

end Lech.ProjectiveRoot

end

end OAI
