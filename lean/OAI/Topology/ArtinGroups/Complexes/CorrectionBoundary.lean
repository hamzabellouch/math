import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ReindexHomOperator
import OAI.Topology.ArtinGroups.Complexes.HomSpaceMul

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J I' J' : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V] [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
  [DecidableEq I] [DecidableEq J] [DecidableEq I'] [DecidableEq J']

lemma HomotopyEquivalence.sourceCorrection_boundary {E : BasedComplex Q (K := K) I}
    {E' : BasedComplex Q (K := K) I'} (e : HomotopyEquivalence Q E E') :
    e.forward.matrix * e.backward.matrix - projectiveIdentity Q E.placement ∈
      homBoundaries Q E E 0 0 := by
  apply homotopyEquation_boundary Q ⟨e.sourceEntries, e.sourceDegree⟩
  rw [e.sourceEquation]
  abel

lemma HomotopyEquivalence.sandwichCorrection_boundary {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {E' : BasedComplex Q (K := K) I'}
    {F' : BasedComplex Q (K := K) J'}
    (e : HomotopyEquivalence Q E E') (f : HomotopyEquivalence Q F F')
    (n v : ℤ) {g : Matrix I J (Q.Zigzag K)} (hg : g ∈ homCycles Q E F n v) :
    e.forward.matrix * (e.backward.matrix * g * f.forward.matrix) * f.backward.matrix - g ∈
      homBoundaries Q E F n v := by
  have hl := homBoundary_mul_cycle Q (e.sourceCorrection_boundary Q) hg
  have hr := homCycle_mul_boundary Q hg (f.sourceCorrection_boundary Q)
  have hc := homCycles_mul Q (map_mem_homCycles Q f.forward) (map_mem_homCycles Q f.backward)
  have hll := homBoundary_mul_cycle Q hl hc
  simp only [zero_add, add_zero] at hll hr
  have hb := (homBoundaries Q E F n v).add_mem hll hr
  have heq : (e.forward.matrix * e.backward.matrix - projectiveIdentity Q E.placement) *
      g * (f.forward.matrix * f.backward.matrix) +
      g * (f.forward.matrix * f.backward.matrix - projectiveIdentity Q F.placement) =
      e.forward.matrix * (e.backward.matrix * g * f.forward.matrix) * f.backward.matrix - g := by
    have hi : projectiveIdentity Q E.placement * g = g := projectiveIdentity_mul Q hg.1.1
    have hj : g * projectiveIdentity Q F.placement = g := mul_projectiveIdentity Q hg.1.1
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub]
    erw [hi, hj]
    simp only [Matrix.mul_assoc]
    abel
  rw [heq] at hb
  exact hb

lemma HomotopyEquivalence.sandwich_injective {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {E' : BasedComplex Q (K := K) I'}
    {F' : BasedComplex Q (K := K) J'}
    (e : HomotopyEquivalence Q E E') (f : HomotopyEquivalence Q F F') (n v : ℤ) :
    Function.Injective ((sandwichHomOperator Q e.backward f.forward).onCohomology n v) := by
  apply HomOperator.onCohomology_injective
  intro g hg hb
  have hb' := (sandwichHomOperator Q e.forward f.backward).map_boundaries n v hb
  have hc := e.sandwichCorrection_boundary Q f n v hg
  have hd := (homBoundaries Q E F n v).sub_mem hb' hc
  change e.forward.matrix * (e.backward.matrix * g * f.forward.matrix) * f.backward.matrix -
    (e.forward.matrix * (e.backward.matrix * g * f.forward.matrix) * f.backward.matrix - g) ∈
      homBoundaries Q E F n v at hd
  simpa only [sub_sub_cancel] using hd

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
