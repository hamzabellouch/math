import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomDimensionDual
import OAI.Topology.ArtinGroups.Harmonic.PlacementLevelFiberSum

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A:Type} {K:Type*} [Field K] [Fintype V] [Fintype A]
  (Q:ReversibleQuiver V A) (hn:∀a,Q.source a≠Q.target a)
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

lemma probeOrbit_level_dual (w:List (V×Bool)) (α β:V) (d:ℤ) :
    classLevelArray R (probeOrbit Q (K:=K) hn w α false) (.inl β,d)=
      classLevelArray R
        (probeOrbit Q (K:=K) hn (w.reverse.map fun a=>(a.1,!a.2)) β false) (.inl α,-d) := by
  have h:=placementLevel_dual
    (classGeneratorArray R (probeOrbit Q (K:=K) hn w α false))
    (classGeneratorArray R (probeOrbit Q (K:=K) hn (w.reverse.map fun a=>(a.1,!a.2)) β true))
    (.inl β) (.inl α) (probeOrbit_generator_dual Q hn w α β) d
  change classLevelArray R _ _=classLevelArray R _ _ at h
  have hs:=probeOrbit_level_swap Q (K:=K) hn (w.reverse.map fun a=>(a.1,!a.2)) β α false (-d)
  exact h.trans hs

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
