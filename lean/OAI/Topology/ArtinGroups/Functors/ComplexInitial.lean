import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Initial
import OAI.Topology.ArtinGroups.Quivers.Iso
import OAI.Topology.ArtinGroups.Complexes.BasedComplexComplex
import OAI.Topology.ArtinGroups.Functors.ReversibleQuiverMap

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W]

lemma complex_initial (α:V) :
    e.complex (initialProjective Q (K:=K) α : BasedComplex Q PUnit.{u+1}) =
      initialProjective R (e.vertex α) := by
  apply ext_placement_differential R
  · rfl
  · exact e.matrix_zero

lemma classMap_initial (α:V) :
    e.classMap (initialClass Q (K:=K) α) = initialClass R (e.vertex α) := by
  change classOfComplex R (e.complex (initialProjective Q α : BasedComplex Q PUnit.{u+1})) = _
  rw [e.complex_initial]
  rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
