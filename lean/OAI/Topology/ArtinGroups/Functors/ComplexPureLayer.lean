import Mathlib
import OAI.Topology.ArtinGroups.Functors.SupportedCycles
import OAI.Topology.ArtinGroups.Functors.Placement
import OAI.Topology.ArtinGroups.Functors.ReversibleQuiverMap
import OAI.Topology.ArtinGroups.Complexes.MinimalModelEquivalence
import OAI.Topology.ArtinGroups.Complexes.LevelArrayComplexMinimal

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

universe u
attribute [local instance] Classical.propDecidable
variable {V A W B : Type u} {K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype V] [Fintype W] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq W] [DecidableEq A] [DecidableEq B]
  {I : Type u} [Fintype I] [DecidableEq I]

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] [DecidableEq I] in
lemma complex_pureLayer (E:BasedComplex Q (K := K) I) (hE:E.IsMinimal Q) (d:ℤ) :
    e.complex (E.pureLayer Q hE d) =
      (e.complex E).pureLayer R (e.complex_minimal hE) d := rfl

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] in
lemma classMap_layer (x:FiniteHomotopyClass Q (K := K)) (d:ℤ) :
    e.classMap (classLayer Q d x) = classLayer R d (e.classMap x) := by
  let E := (minimalClassModel Q x).complex
  have hE := minimalClassModel_minimal Q x
  have hx : classOfComplex Q E = x := minimalClassModel_class Q x
  rw [← hx,classMap_complex,classLayer_minimal Q E hE d,
    classLayer_minimal R (e.complex E) (e.complex_minimal hE) d,classMap_complex,e.complex_pureLayer]
  rfl

lemma classMap_socleDimension (x:FiniteHomotopyClass Q (K := K)) (d:ℤ) (α:V) (c:ℤ) :
    classLayerSocleDimension R d (e.vertex α) c (e.classMap x) =
      classLayerSocleDimension Q d α c x := by
  let E := (minimalClassModel Q x).complex
  have hE := minimalClassModel_minimal Q x
  have hx : classOfComplex Q E = x := minimalClassModel_class Q x
  rw [← hx,classMap_complex,classLayerSocleDimension_minimal Q E hE,
    classLayerSocleDimension_minimal R (e.complex E) (e.complex_minimal hE),← e.complex_pureLayer]
  exact (e.coefficientSocle (E.pureLayer Q hE d) (fun i => i.property) α c).finrank_eq.symm

lemma classMap_topDimension (x:FiniteHomotopyClass Q (K := K)) (d:ℤ) (α:V) (c:ℤ) :
    classLayerTopDimension R d (e.vertex α) c (e.classMap x) =
      classLayerTopDimension Q d α c x := by
  let E := (minimalClassModel Q x).complex
  have hE := minimalClassModel_minimal Q x
  have hx : classOfComplex Q E = x := minimalClassModel_class Q x
  rw [← hx,classMap_complex,classLayerTopDimension_minimal Q E hE,
    classLayerTopDimension_minimal R (e.complex E) (e.complex_minimal hE),← e.complex_pureLayer]
  exact (e.coefficientTopDual (E.pureLayer Q hE d) (fun i => i.property) α c).finrank_eq.symm

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] [DecidableEq I] in
lemma levelArray_complex (E:BasedComplex Q (K := K) I) (α:V) (d:ℤ) :
    (e.complex E).levelArray R (e.vertex α,d) = E.levelArray Q (α,d) := by
  simp only [levelArray_apply]
  have hP : {i:I | ((e.complex E).placement i).color=e.vertex α ∧ ((e.complex E).placement i).level=d} =
      {i:I | (E.placement i).color=α ∧ (E.placement i).level=d} := by
    ext i
    change (e.vertex (E.placement i).color=e.vertex α ∧ (E.placement i).level=d) ↔ _
    rw [e.vertex.injective.eq_iff]
    rfl
  exact congrArg (fun U:Set I => Nat.card U) hP

omit [Fintype V] [Fintype W] [DecidableEq A] [DecidableEq B] in
lemma classMap_levelArray (x:FiniteHomotopyClass Q (K := K)) (α:V) (d:ℤ) :
    classLevelArray R (e.classMap x) (e.vertex α,d) = classLevelArray Q x (α,d) := by
  let E := (minimalClassModel Q x).complex
  have hE := minimalClassModel_minimal Q x
  have hx : classOfComplex Q E = x := minimalClassModel_class Q x
  rw [← hx,classMap_complex,classLevelArray_complex_minimal Q E hE,
    classLevelArray_complex_minimal R (e.complex E) (e.complex_minimal hE)]
  exact e.levelArray_complex E α d

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
