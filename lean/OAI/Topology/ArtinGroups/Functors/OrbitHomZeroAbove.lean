import Mathlib
import OAI.Topology.ArtinGroups.Functors.SignedPerm
import OAI.Topology.ArtinGroups.Complexes.GeneratorArrayZeroCap

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.ProbeEmbedding
open Zigzag Zigzag.BasedComplex

variable {V A:Type} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q
variable (hn:∀a,Q.source a≠Q.target a)

lemma orbit_classHom_zero_above_cap (w:List (V×Bool)) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hx:ClassCapOn Q (wordPerm Q hn w x) U q)
    (α:V) (hα:α∈U) (b:Bool) (n v:ℤ) (hd:q+1<n+v) :
    classHomDimension R n v
      (probeOrbit Q hn (w.reverse.map fun a=>(a.1,!a.2)) α b) (classMap Q x)=0 := by
  rw [orbit_classHom_dimension]
  apply classGeneratorArray_zero_of_cap Q _ U q hx _ hα
  change q<n+(v-1)
  omega

lemma minimal_orbit_homDimension (w:List (V×Bool)) (x:FiniteHomotopyClass Q (K:=K))
    (α:V) (b:Bool) (n v:ℤ) :
    homDimension R
      (minimalClassModel R (probeOrbit Q hn (w.reverse.map fun a=>(a.1,!a.2)) α b)).complex
      (complex Q (minimalClassModel Q x).complex) n v=
      classGeneratorArray Q (wordPerm Q hn w x) ⟨α,n,v-1⟩ := by
  have hE:classOfComplex R (K:=K)
      (minimalClassModel R (probeOrbit Q hn (w.reverse.map fun a=>(a.1,!a.2)) α b)).complex=
      probeOrbit Q hn (w.reverse.map fun a=>(a.1,!a.2)) α b:=minimalClassModel_class R _
  have hF:classOfComplex R (complex Q (minimalClassModel Q x).complex)=classMap Q x := by
    rw [← classMap_complex]
    exact congrArg (classMap Q) (minimalClassModel_class Q x)
  change classHomDimension R n v (classOfComplex R _) (classOfComplex R _)=_
  erw [hE,hF,orbit_classHom_dimension]

end HarmonicArtin.ReversibleQuiver.ProbeEmbedding

end OAI
