import Mathlib
import OAI.Topology.ArtinGroups.Quivers.UnitTestVector
import OAI.Topology.ArtinGroups.Complexes.BottomScalarCycleZero

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def layerVector (E:BasedComplex Q (K:=K) I) (d:ℤ)
    (x:{i // (E.placement i).level=d}→K) : I→K := by
  classical
  exact fun i=>if h:(E.placement i).level=d then x ⟨i,h⟩ else 0

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma layerVector_support (E:BasedComplex Q (K:=K) I) (d:ℤ)
    (x:{i // (E.placement i).level=d}→K) (i:I)
    (h:(E.placement i).level≠d) : layerVector Q E d x i=0 := by
  classical
  simp [layerVector,h]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma layerVector_socle (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (d:ℤ) (α:V) (c:ℤ) {x:{i // (E.placement i).level=d}→K}
    (hx:x∈coefficientSocle Q (E.pureLayer Q hE d) α c) :
    layerVector Q E d x∈coefficientSocle Q E α c := by
  classical
  constructor
  · intro i hi
    by_cases hid:(E.placement i).level=d
    · simpa [layerVector,hid] using hx.1 ⟨i,hid⟩ hi
    · exact layerVector_support Q E d x i hid
  · intro j a ha
    by_cases hj:(E.placement j).level=d
    · rw [← hx.2 ⟨j,hj⟩ a ha]
      symm
      apply Fintype.sum_of_injective
        (Subtype.val : {i // (E.placement i).level=d}→I) Subtype.val_injective
      · intro i hi
        rw [layerVector_support Q E d x i (fun h=>hi ⟨⟨i,h⟩,rfl⟩),MulZeroClass.zero_mul]
      · intro i
        change x i * (E.differential i.val j).arrow a =
          layerVector Q E d x i.val * (E.differential i.val j).arrow a
        simp only [layerVector,dite_eq_left i.property]
    · apply Finset.sum_eq_zero
      intro i hi
      by_cases hid:(E.placement i).level=d
      · have hd:(E.differential i j).arrow a=0 := by
          exact congrFun (differential_arrow_level Q E (fun h=>hj (h.trans hid))) a
        rw [hd,MulZeroClass.mul_zero]
      · rw [layerVector_support Q E d x i hid,MulZeroClass.zero_mul]

omit [DecidableEq I] in
lemma unitTestVector_bottom_cycle (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (d:ℤ) (hfloor:∀ i,d≤(E.placement i).level) (α:V) (c:ℤ)
    {x:I→K} (hx:x∈coefficientSocle Q E α c)
    (hs:∀ i,(E.placement i).level≠d→x i=0) :
    Matrix.vecMul (unitTestVector Q E.placement α x)
      ((E.testComplex Q α).differential.map (vertexHom Q α))=0 := by
  have hd:((E.testComplex Q α).differential.map (vertexHom Q α))=
      testMatrix Q E.placement E.placement α E.differential := by
    apply Matrix.ext
    intro i j
    change ((testMatrix Q E.placement E.placement α E.differential i j) • vertexId Q α).vertex α = _
    simp
  rw [hd]
  funext j
  rw [unitTestVector_differential Q E α x (fun i h=>hx.1 i (Or.inl h))]
  rcases j with ⟨j,⟨p,hp,hq⟩⟩
  rcases p with v|a|v
  · apply Finset.sum_eq_zero
    intro i hi
    change x i * (E.differential i j).vertex v=0
    simp only [hE i j,Pi.zero_apply,MulZeroClass.mul_zero]
  · exact hx.2 j a hp
  · apply Finset.sum_eq_zero
    intro i hi
    change x i * (E.differential i j).token v=0
    by_cases hxi:x i=0
    · rw [hxi,MulZeroClass.zero_mul]
    have hi:(E.placement i).level=d := Classical.not_not.mp (fun h=>hxi (hs i h))
    have hz:(E.differential i j).token v=0 := by
      by_contra hn
      obtain ⟨_,_,hc,hu⟩:=degree_token_support Q E.entries E.degree i j v hn
      have hj:=hfloor j
      dsimp only [GeneratorPlacement.level] at hi hj
      omega
    rw [hz,MulZeroClass.mul_zero]

omit [DecidableEq I] in
theorem bottomSocle_zero_of_test_equiv_above
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) {d:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α:V)
    (F:BasedComplex Q (K:=K) J) (e:HomotopyEquivalence Q (E.testComplex Q α) F)
    (hF:∀ j,d<(F.placement j).level) (c:ℤ) :
    coefficientSocle Q (E.pureLayer Q hE d) α c=⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro x hx
  change x=0
  let y:=layerVector Q E d x
  have hy:y∈coefficientSocle Q E α c:=layerVector_socle Q E hE d α c hx
  have hs:∀ i,(E.placement i).level≠d→y i=0:=layerVector_support Q E d x
  have htf:∀ i,d≤((E.testComplex Q α).placement i).level := by
    intro i
    have hi:=hfloor i.1
    have hl:0≤Path.length i.2.val := by
      rcases i.2.val with v|a|v <;> norm_num [Path.length]
    dsimp only [testComplex,testPlacement,GeneratorPlacement.level] at *
    omega
  have hts:∀ i,((E.testComplex Q α).placement i).level≠d→
      unitTestVector Q E.placement α y i=0 := by
    intro i hi
    change y i.1 * pathCoordinates Q (vertexId Q α) i.2.val=0
    by_cases hp:Sum.inl α=i.2.val
    · rw [vertex_coordinates,ite_eq_left hp,_root_.mul_one]
      apply hs
      intro hc
      apply hi
      change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=d
      rw [← hp]
      simpa [Path.length,GeneratorPlacement.level] using hc
    · rw [vertex_coordinates,ite_eq_right hp,MulZeroClass.mul_zero]
  have hz:=bottom_scalar_cycle_zero Q (E.testComplex Q α) F e α (fun _=>rfl) htf hF
    (unitTestVector Q E.placement α y) hts (unitTestVector_bottom_cycle Q E hE d hfloor α c hy hs)
  have hy0:y=0 := by
    have hh:=congrArg (sumUnitTest Q E.placement α) hz
    rw [sumUnitTest_unit Q E.placement α y (fun i h=>hy.1 i (Or.inl h)),map_zero] at hh
    exact hh
  funext i
  have hh:=congrFun hy0 i.val
  change (if h:(E.placement i.val).level=d then x ⟨i.val,h⟩ else 0)=0 at hh
  split_ifs at hh with hi
  · exact hh
  · exact (hi i.property).elim

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
