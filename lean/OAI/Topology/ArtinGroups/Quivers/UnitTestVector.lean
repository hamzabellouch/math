import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CornerPath
import OAI.Topology.ArtinGroups.Complexes.CoefficientTopDual
import OAI.Topology.ArtinGroups.Diagrams.SupportedKernel

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma corner_length_zero {α β : V} (p : CornerPath Q α β) (h : Path.length p.val=0) :
    p.val = Sum.inl α := by
  rcases p with ⟨p,hs,ht⟩
  rcases p with v|a|v
  · exact congrArg Sum.inl hs
  · norm_num [Path.length] at h
  · norm_num [Path.length] at h

lemma vertex_coordinates (α : V) (p : Path V A) :
    pathCoordinates Q (vertexId Q (K := K) α) p = if Sum.inl α=p then 1 else 0 := by
  rw [← pathBasis_vertex,pathBasis_coordinates]

noncomputable def unitTestVector (p : I → GeneratorPlacement V) (α : V) :
    (I → K) →ₗ[K] (TestIndex Q p α → K) where
  toFun x i := x i.1 * pathCoordinates Q (vertexId Q α) i.2.val
  map_add' x y := by funext i; exact _root_.add_mul _ _ _
  map_smul' r x := by funext i; exact _root_.mul_assoc _ _ _

noncomputable def sumUnitTest (p : I → GeneratorPlacement V) (α : V) :
    (TestIndex Q p α → K) →ₗ[K] (I → K) where
  toFun x i := ∑ z : CornerPath Q α (p i).color, x ⟨i,z⟩
  map_add' x y := by funext i; exact Finset.sum_add_distrib
  map_smul' r x := by funext i; exact (Finset.mul_sum _ _ _).symm

omit [Fintype I] [DecidableEq A] in
lemma sumUnitTest_support (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=0) → x i=0) :
    ∀ i, (p i).color ≠ α ∨ (p i).cochain ≠ c → sumUnitTest Q p α x i=0 := by
  intro i hi
  apply Finset.sum_eq_zero
  intro z hz
  apply hx
  rintro ⟨hc,hl⟩
  rcases hi with hi|hi
  · apply hi
    have he := corner_length_zero Q z hl
    have ht := z.property.2
    rw [he] at ht
    exact ht.symm
  · exact hi hc

omit [Fintype I] in
lemma unitTestVector_sum (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=0) → x i=0) :
    unitTestVector Q p α (sumUnitTest Q p α x) = x := by
  funext i
  change (∑ z : CornerPath Q α (p i.1).color, x ⟨i.1,z⟩) *
    pathCoordinates Q (vertexId Q α) i.2.val = x i
  by_cases hl : Path.length i.2.val=0
  · have he := corner_length_zero Q i.2 hl
    rw [vertex_coordinates,ite_eq_left he.symm,_root_.mul_one]
    apply Finset.sum_eq_single i.2
    · intro z hz hzi
      apply hx
      rintro ⟨hc,hzlen⟩
      apply hzi
      apply Subtype.ext
      exact (corner_length_zero Q z hzlen).trans he.symm
    · simp
  · rw [hx i (fun h => hl h.2)]
    rw [vertex_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]

omit [Fintype I] in
lemma sumUnitTest_unit (p : I → GeneratorPlacement V) (α : V)
    (x : I → K) (hx : ∀ i, (p i).color≠α → x i=0) :
    sumUnitTest Q p α (unitTestVector Q p α x)=x := by
  funext i
  by_cases hi : (p i).color=α
  · let z : CornerPath Q α (p i).color := ⟨Sum.inl α,rfl,hi.symm⟩
    change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (vertexId Q α) w.val)=x i
    rw [Finset.sum_eq_single z]
    · rw [vertex_coordinates,ite_eq_left rfl,_root_.mul_one]
    · intro w hw hwz
      rw [vertex_coordinates,ite_eq_right (fun he => hwz (Subtype.ext he.symm)),MulZeroClass.mul_zero]
    · simp
  · change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (vertexId Q α) w.val)=x i
    rw [hx i hi]
    simp

omit [DecidableEq A] in
lemma unitTestVector_differential (E : BasedComplex Q (K := K) I) (α:V)
    (x : I → K) (hx : ∀ i, (E.placement i).color≠α → x i=0)
    (j : TestIndex Q E.placement α) :
    Matrix.vecMul (unitTestVector Q E.placement α x)
      (testMatrix Q E.placement E.placement α E.differential) j =
      ∑ i, x i * pathCoordinates Q (E.differential i j.1) j.2.val := by
  change (∑ z : TestIndex Q E.placement α, x z.1 * pathCoordinates Q (vertexId Q α) z.2.val *
    pathCoordinates Q (pathBasis Q z.2.val * E.differential z.1 j.1) j.2.val)=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : (E.placement i).color=α
  · simp only [_root_.mul_assoc,← Finset.mul_sum]
    rw [coordinates_mul_expansion Q (vertexId Q α) (E.differential i j.1)
      (vertexId_mul_self Q α) (by rw [hc]; exact vertexId_mul_self Q α)]
    have heq := E.entries.1 i j.1
    rw [hc] at heq
    rw [heq]
  · simp only [hx i hc,MulZeroClass.zero_mul,Finset.sum_const_zero]

namespace BasedComplex

noncomputable def socleTestCycles (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ) :=
  ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential)
    (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=0)

lemma unitTestVector_socle (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientSocle Q E α c) :
    unitTestVector Q E.placement α x ∈ socleTestCycles Q E α c := by
  constructor
  · intro i hi
    change x i.1 * pathCoordinates Q (vertexId Q α) i.2.val=0
    by_cases hc : (E.placement i.1).cochain=c
    · have hl : Path.length i.2.val≠0 := fun h => hi ⟨hc,h⟩
      rw [vertex_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]
    · rw [hx.1 i.1 (Or.inr hc),MulZeroClass.zero_mul]
  · funext j
    rw [unitTestVector_differential Q E α x (fun i h => hx.1 i (Or.inl h))]
    rcases j with ⟨j,⟨p,hs,ht⟩⟩
    rcases p with v|a|v
    · apply Finset.sum_eq_zero
      intro i hi
      change x i * (E.differential i j).vertex v=0
      rw [(pure_differential_linear Q E hE i j).1]
      simp
    · exact hx.2 j a hs
    · apply Finset.sum_eq_zero
      intro i hi
      change x i * (E.differential i j).token v=0
      rw [(pure_differential_linear Q E hE i j).2]
      simp

lemma sumUnitTest_socle (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ)
    {x : TestIndex Q E.placement α → K} (hx : x ∈ socleTestCycles Q E α c) :
    sumUnitTest Q E.placement α x ∈ coefficientSocle Q E α c := by
  have hs := sumUnitTest_support Q E.placement α c x hx.1
  constructor
  · exact hs
  · intro j a ha
    by_cases ht : Q.target a=(E.placement j).color
    · let z : TestIndex Q E.placement α := ⟨j,Sum.inr (Sum.inl a),ha,ht⟩
      have hh := unitTestVector_differential Q E α (sumUnitTest Q E.placement α x)
        (fun i h => hs i (Or.inl h)) z
      rw [unitTestVector_sum Q E.placement α c x hx.1,hx.2] at hh
      exact hh.symm
    · apply Finset.sum_eq_zero
      intro i hi
      have hz : (E.differential i j).arrow a=0 := by
        by_contra hn
        exact ht (coordinates_corner Q (p := Sum.inr (Sum.inl a)) (E.entries.1 i j) (E.entries.2 i j) hn).2
      rw [hz,MulZeroClass.mul_zero]

noncomputable def coefficientSocleTestEquiv (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ) :
    coefficientSocle Q E α c ≃ₗ[K] socleTestCycles Q E α c where
  toFun x := ⟨unitTestVector Q E.placement α x.val,unitTestVector_socle Q E hE α c x.property⟩
  invFun y := ⟨sumUnitTest Q E.placement α y.val,sumUnitTest_socle Q E α c y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact sumUnitTest_unit Q E.placement α x.val (fun i h => x.property.1 i (Or.inl h))
  right_inv y := by
    apply Subtype.ext
    exact unitTestVector_sum Q E.placement α c y.val y.property.1
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r x := by apply Subtype.ext; exact map_smul _ _ _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
