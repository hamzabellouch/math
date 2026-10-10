import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomDimensionZeroCycles
import OAI.Topology.ArtinGroups.Complexes.LowerTruncation

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def targetLow (_E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J) (d:ℤ) :
    Matrix I J (Q.Zigzag K)→ₗ[K] Matrix I (lowerLevelSet Q F d) (Q.Zigzag K) where
  toFun M i j:=M i j
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma targetLow_inclusion (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hF:F.IsMinimal Q) (d:ℤ) (f:Matrix I (lowerLevelSet Q F d) (Q.Zigzag K))
    (hf:ProjectiveEntries Q E.placement (lowerTruncation Q F hF d).placement f) :
    targetLow Q E F d (f*blockInclusion Q F (lowerLevelSet Q F d))=f := by
  apply Matrix.ext
  intro i j
  change (∑ k:lowerLevelSet Q F d,f i k*
    (if (k:J)=(j:J) then vertexId Q (K:=K) (F.placement k).color else 0))=f i j
  simp only [Subtype.val_inj,mul_ite,MulZeroClass.mul_zero,Fintype.sum_ite_eq']
  exact hf.2 i j

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma targetLow_homSpace (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hF:F.IsMinimal Q) (d n v:ℤ) {g:Matrix I J (Q.Zigzag K)}
    (hg:g∈homSpace Q E F n v) :
    targetLow Q E F d g∈homSpace Q E (lowerTruncation Q F hF d) n v :=
  ⟨⟨fun i j=>hg.1.1 i j,fun i j=>hg.1.2 i j⟩,fun i j=>hg.2 i j⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J] in
lemma targetLow_differential (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (hF:F.IsMinimal Q) (d n:ℤ) (g:Matrix I J (Q.Zigzag K))
    (hg:∀ i j,j∉lowerLevelSet Q F d → g i j=0) :
    targetLow Q E F d (homDifferential Q E F n g)=
      homDifferential Q E (lowerTruncation Q F hF d) n (targetLow Q E F d g) := by
  have hmul:targetLow Q E F d (g*F.differential)=
      targetLow Q E F d g*(lowerTruncation Q F hF d).differential := by
    apply Matrix.ext
    intro i j
    change (∑ k:J,g i k*F.differential k j)=
      ∑ k:lowerLevelSet Q F d,g i k*F.differential k j
    symm
    apply Fintype.sum_of_injective (Subtype.val:lowerLevelSet Q F d→J) Subtype.val_injective
    · intro k hk
      have hn:k∉lowerLevelSet Q F d:=fun hh=>hk ⟨⟨k,hh⟩,rfl⟩
      rw [hg i k hn,zero_mul]
    · intro k; rfl
  change targetLow Q E F d (E.differential*g-cochainSign (K:=K) n • (g*F.differential))=_
  rw [map_sub,map_smul,hmul]
  rfl

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
theorem low_boundary_of_inclusion_boundary (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hF:F.IsMinimal Q) (d:ℤ)
    (hE:∀ i,(E.placement i).level≤d+1)
    {f:Matrix I (lowerLevelSet Q F d) (Q.Zigzag K)}
    (hf:ProjectiveEntries Q E.placement (lowerTruncation Q F hF d).placement f)
    (hb:f*blockInclusion Q F (lowerLevelSet Q F d)∈homBoundaries Q E F 0 0) :
    f∈homBoundaries Q E (lowerTruncation Q F hF d) 0 0 := by
  obtain ⟨g,hg,he⟩:=hb
  have hs:∀ i j,j∉lowerLevelSet Q F d → g i j=0 := by
    intro i j hj
    by_contra hn
    have hh:=mapDegree_level_bound Q hg.2 hn
    have hhE:=hE i
    exact hj (by change (F.placement j).level≤d; omega)
  refine ⟨targetLow Q E F d g,targetLow_homSpace Q E F hF d _ _ hg,?_⟩
  have h:=congrArg (targetLow Q E F d) he
  rw [targetLow_differential Q E F hF d _ _ hs,targetLow_inclusion Q E F hF d f hf] at h
  exact h

omit [DecidableEq A] [DecidableEq I] in
lemma lowerTruncation_homDimension_zero (E:BasedComplex Q (K:=K) I)
    (F:BasedComplex Q (K:=K) J) (hF:F.IsMinimal Q) (d:ℤ)
    (hE:∀ i,(E.placement i).level≤d+1) (hz:homDimension Q E F 0 0=0) :
    homDimension Q E (lowerTruncation Q F hF d) 0 0=0 := by
  apply homDimension_zero_of_cycles_boundary Q
  intro f hf
  apply low_boundary_of_inclusion_boundary Q E F hF d hE hf.1.1
  apply boundary_of_homDimension_zero Q E F 0 0 hz
  simpa only [add_zero,lowInclusion] using homCycles_mul Q hf
    (map_mem_homCycles Q (lowInclusion Q F (lowerLevelSet Q F d) (levelDownClosed Q F hF d)))

omit [DecidableEq A] in
lemma classLowerTruncation_homDimension_zero (x y:FiniteHomotopyClass Q (K:=K))
    (d:ℤ) (hx:ClassUpperBound Q (d+1) x) (hz:classHomDimension Q 0 0 x y=0) :
    classHomDimension Q 0 0 x (classLowerTruncation Q d y)=0 := by
  let E:=minimalClassModel Q x
  let F:=minimalClassModel Q y
  have hx':classOfComplex Q E.complex=x:=minimalClassModel_class Q x
  rw [← hx']
  change homDimension Q E.complex (lowerTruncation Q F.complex (minimalClassModel_minimal Q y) d) 0 0=0
  apply lowerTruncation_homDimension_zero Q E.complex F.complex (minimalClassModel_minimal Q y) d hx
  rw [minimalClassModel_homDimension]
  exact hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
