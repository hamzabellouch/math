import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomDimension
import OAI.Topology.ArtinGroups.Harmonic.InjectiveFinrankOne

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma boundary_of_homDimension_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (hd : homDimension Q E F n v = 0)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homCycles Q E F n v) :
    f ∈ homBoundaries Q E F n v := by
  have : Subsingleton (homCohomology Q E F n v) :=
    (Module.finrank_zero_iff.mp hd)
  have hz : (Submodule.Quotient.mk (⟨f, hf⟩ : homCycles Q E F n v) :
      homCohomology Q E F n v) = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero
    ((homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype)).mp hz

noncomputable def homDetector (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (L : Matrix I J (Q.Zigzag K) →ₗ[K] K)
    (hL : ∀ f ∈ homBoundaries Q E F n v, L f = 0) :
    homCohomology Q E F n v →ₗ[K] K :=
  Submodule.liftQ _ (L.comp (homCycles Q E F n v).subtype) (by
    intro f hf
    exact hL f hf)

lemma boundary_of_homDimension_le_one (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ)
    (hd : homDimension Q E F n v ≤ 1)
    (L : Matrix I J (Q.Zigzag K) →ₗ[K] K)
    (hL : ∀ f ∈ homBoundaries Q E F n v, L f = 0)
    {u : Matrix I J (Q.Zigzag K)} (hu : u ∈ homCycles Q E F n v) (huL : L u ≠ 0)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homCycles Q E F n v) (hfL : L f = 0) :
    f ∈ homBoundaries Q E F n v := by
  let T := homDetector Q E F n v L hL
  have hin := injective_of_finrank_le_one hd T
    (Submodule.Quotient.mk (⟨u, hu⟩ : homCycles Q E F n v)) huL
  have hz : (Submodule.Quotient.mk (⟨f, hf⟩ : homCycles Q E F n v) :
      homCohomology Q E F n v) = 0 := by
    apply hin
    change L f = T 0
    rw [map_zero]
    exact hfL
  exact (Submodule.Quotient.mk_eq_zero
    ((homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype)).mp hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
