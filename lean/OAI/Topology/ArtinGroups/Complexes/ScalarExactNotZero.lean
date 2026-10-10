import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Initial
import OAI.Topology.ArtinGroups.Complexes.BasedComplexComplex
import OAI.Topology.ArtinGroups.Complexes.TestExact

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma scalarExact_not_of_zero_differential {I:Type u} [Fintype I]
    (E:BasedComplex Q (K:=K) I) (α:V) (hd:E.differential=0) (i:I) :
    ¬ScalarExactAt Q E α (E.placement i).level (E.placement i).cochain := by
  intro h
  have hdm:E.differential.map (vertexHom Q α)=0 := by rw [hd]; ext a b; exact map_zero (vertexHom Q (K:=K) α)
  let x:I→K:=Pi.single i 1
  have hx:ScalarSupported Q E (E.placement i).level (E.placement i).cochain x := by
    intro j hj
    have hji:j≠i:=by rintro rfl; exact hj ⟨rfl,rfl⟩
    exact Pi.single_eq_of_ne hji _
  obtain ⟨y,_,hy⟩:=h x hx (by rw [hdm,Matrix.vecMul_zero])
  rw [hdm,Matrix.vecMul_zero] at hy
  have hh:=congrFun hy i
  simp [x] at hh

lemma initialClass_test_not_exact (α β:V) (p:Zigzag.CornerPath Q α β) :
    ¬ClassTestExact Q α (Path.length p.val) 0 (initialClass Q (K:=K) β) := by
  let E:=initialProjective Q (K:=K) β
  change ¬ScalarExactAt Q (E.testComplex Q α) α _ _
  have hd:(E.testComplex Q α).differential=0 := by
    change scalarCornerMatrix Q α (testMatrix Q E.placement E.placement α 0)=0
    rw [testMatrix_zero,scalarCornerMatrix_zero]
  simpa only [E,testComplex,testPlacement,initialProjective,GeneratorPlacement.level,
    zero_add] using scalarExact_not_of_zero_differential Q (E.testComplex Q α) α hd ⟨PUnit.unit,p⟩

lemma classPositiveTwist_initial_orthogonal {α β:V} (h:OrthogonalVertices Q α β) :
    classPositiveTwist Q α (initialClass Q (K:=K) β)=initialClass Q β := by
  let E:=initialProjective Q (K:=K) β
  let :IsEmpty (TestIndex Q E.placement α):=⟨fun i=>by
    rcases i with ⟨i,⟨p,hs,ht⟩⟩
    change Path.source Q p=α at hs
    change Path.target Q p=β at ht
    rcases p with a|a|a
    · exact h.1 (hs.symm.trans ht)
    · exact h.2 a hs ht
    · exact h.1 (hs.symm.trans ht)⟩
  change classOfComplex Q (E.positiveTwist Q α)=classOfComplex Q E
  rw [classOfComplex_reindex Q _ (Equiv.emptySum (TestIndex Q E.placement α) PUnit).symm]
  congr 1

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
