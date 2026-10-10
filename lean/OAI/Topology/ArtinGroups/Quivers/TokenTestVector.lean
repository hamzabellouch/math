import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CornerPath
import OAI.Topology.ArtinGroups.Complexes.CoefficientTopDual
import OAI.Topology.ArtinGroups.Diagrams.SupportedKernel

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K I : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma corner_length_two {α β : V} (p : CornerPath Q α β) (h : Path.length p.val=2) :
    p.val = Sum.inr (Sum.inr α) := by
  rcases p with ⟨p,hs,ht⟩
  rcases p with v|a|v
  · norm_num [Path.length] at h
  · norm_num [Path.length] at h
  · exact congrArg (fun v => Sum.inr (Sum.inr v)) hs

lemma token_coordinates (α : V) (p : Path V A) :
    pathCoordinates Q (tokenBasis Q (K := K) α) p = if Sum.inr (Sum.inr α)=p then 1 else 0 := by
  rw [← pathBasis_token,pathBasis_coordinates]

noncomputable def tokenTestVector (p : I → GeneratorPlacement V) (α : V) :
    (I → K) →ₗ[K] (TestIndex Q p α → K) where
  toFun x i := x i.1 * pathCoordinates Q (tokenBasis Q α) i.2.val
  map_add' x y := by funext i; exact _root_.add_mul _ _ _
  map_smul' r x := by funext i; exact _root_.mul_assoc _ _ _

noncomputable def sumTokenTest (p : I → GeneratorPlacement V) (α : V) :
    (TestIndex Q p α → K) →ₗ[K] (I → K) where
  toFun x i := ∑ z : CornerPath Q α (p i).color, x ⟨i,z⟩
  map_add' x y := by funext i; exact Finset.sum_add_distrib
  map_smul' r x := by funext i; exact (Finset.mul_sum _ _ _).symm

omit [Fintype I] [DecidableEq A] in
lemma sumTokenTest_support (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=2) → x i=0) :
    ∀ i, (p i).color ≠ α ∨ (p i).cochain ≠ c → sumTokenTest Q p α x i=0 := by
  intro i hi
  apply Finset.sum_eq_zero
  intro z hz
  apply hx
  rintro ⟨hc,hl⟩
  rcases hi with hi|hi
  · apply hi
    have he := corner_length_two Q z hl
    have ht := z.property.2
    rw [he] at ht
    exact ht.symm
  · exact hi hc

omit [Fintype I] in
lemma tokenTestVector_sum (p : I → GeneratorPlacement V) (α : V) (c : ℤ)
    (x : TestIndex Q p α → K)
    (hx : ∀ i, ¬ ((p i.1).cochain=c ∧ Path.length i.2.val=2) → x i=0) :
    tokenTestVector Q p α (sumTokenTest Q p α x) = x := by
  funext i
  change (∑ z : CornerPath Q α (p i.1).color, x ⟨i.1,z⟩) *
    pathCoordinates Q (tokenBasis Q α) i.2.val = x i
  by_cases hl : Path.length i.2.val=2
  · have he := corner_length_two Q i.2 hl
    rw [token_coordinates,ite_eq_left he.symm,_root_.mul_one]
    apply Finset.sum_eq_single i.2
    · intro z hz hzi
      apply hx
      rintro ⟨hc,hzlen⟩
      apply hzi
      apply Subtype.ext
      exact (corner_length_two Q z hzlen).trans he.symm
    · simp
  · rw [hx i (fun h => hl h.2)]
    rw [token_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]

omit [Fintype I] in
lemma sumTokenTest_unit (p : I → GeneratorPlacement V) (α : V)
    (x : I → K) (hx : ∀ i, (p i).color≠α → x i=0) :
    sumTokenTest Q p α (tokenTestVector Q p α x)=x := by
  funext i
  by_cases hi : (p i).color=α
  · let z : CornerPath Q α (p i).color := ⟨Sum.inr (Sum.inr α),rfl,hi.symm⟩
    change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (tokenBasis Q α) w.val)=x i
    rw [Finset.sum_eq_single z]
    · rw [token_coordinates,ite_eq_left rfl,_root_.mul_one]
    · intro w hw hwz
      rw [token_coordinates,ite_eq_right (fun he => hwz (Subtype.ext he.symm)),MulZeroClass.mul_zero]
    · simp
  · change (∑ w : CornerPath Q α (p i).color, x i * pathCoordinates Q (tokenBasis Q α) w.val)=x i
    rw [hx i hi]
    simp

omit [DecidableEq A] in
lemma trace_left_corner {α : V} (x : Zigzag Q K) (hx : vertexId Q α * x=x) :
    trace Q x=x.token α := by
  unfold trace
  apply Finset.sum_eq_single α
  · intro β hβ hβα
    have hh := coordinates_vertexId_left Q α x (Sum.inr (Sum.inr β))
    rw [hx] at hh
    simpa [Path.source,pathCoordinates_token,hβα,Ne.symm hβα] using hh
  · simp

lemma token_path_mul {α β : V} (p : CornerPath Q α β) (x : Zigzag Q K) :
    (pathBasis Q p.val*x).token α=pathCoordinates Q x (Path.dual Q p.val) := by
  rw [coordinates_trace,Path.dual_dual,trace_mul_comm]
  symm
  apply trace_left_corner
  rw [← _root_.mul_assoc,cornerPath_left]

lemma tokenTestVector_differential (E : BasedComplex Q (K := K) I) (α:V)
    (x : I → K) (hx : ∀ i, (E.placement i).color≠α → x i=0)
    (i : TestIndex Q E.placement α) :
    Matrix.vecMul (tokenTestVector Q E.placement α x)
      (testMatrix Q E.placement E.placement α E.differential).transpose i =
      ∑ j, x j * pathCoordinates Q (E.differential i.1 j) (Path.dual Q i.2.val) := by
  change (∑ z : TestIndex Q E.placement α, x z.1 * pathCoordinates Q (tokenBasis Q α) z.2.val *
    pathCoordinates Q (pathBasis Q i.2.val * E.differential i.1 z.1) z.2.val)=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : (E.placement j).color=α
  · let z : CornerPath Q α (E.placement j).color := ⟨Sum.inr (Sum.inr α),rfl,hc.symm⟩
    rw [Finset.sum_eq_single z]
    · rw [token_coordinates,ite_eq_left rfl,_root_.mul_one]
      change x j * (pathBasis Q i.2.val * E.differential i.1 j).token α = _
      rw [token_path_mul]
    · intro w hw hwz
      rw [token_coordinates,ite_eq_right (fun he => hwz (Subtype.ext he.symm)),
        MulZeroClass.mul_zero,MulZeroClass.zero_mul]
    · simp
  · simp only [hx j hc,MulZeroClass.zero_mul,Finset.sum_const_zero]

namespace BasedComplex

noncomputable def topTestCycles (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ) :=
  ScalarCycles.supportedKernel (testMatrix Q E.placement E.placement α E.differential).transpose
    (fun i => (E.placement i.1).cochain=c ∧ Path.length i.2.val=2)

lemma tokenTestVector_top (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ)
    {x : I → K} (hx : x ∈ coefficientTopDual Q E α c) :
    tokenTestVector Q E.placement α x ∈ topTestCycles Q E α c := by
  constructor
  · intro i hi
    change x i.1 * pathCoordinates Q (tokenBasis Q α) i.2.val=0
    by_cases hc : (E.placement i.1).cochain=c
    · have hl : Path.length i.2.val≠2 := fun h => hi ⟨hc,h⟩
      rw [token_coordinates,ite_eq_right (fun he => hl (by rw [← he]; rfl)),MulZeroClass.mul_zero]
    · rw [hx.1 i.1 (Or.inr hc),MulZeroClass.zero_mul]
  · funext i
    rw [tokenTestVector_differential Q E α x (fun i h => hx.1 i (Or.inl h))]
    rcases i with ⟨i,⟨p,hs,ht⟩⟩
    rcases p with v|a|v
    · apply Finset.sum_eq_zero
      intro j hj
      change x j * (E.differential i j).token v=0
      rw [(pure_differential_linear Q E hE i j).2]
      simp
    · simpa only [Path.dual,pathCoordinates_arrow,mul_comm,Pi.zero_apply] using hx.2 i (Q.reverse a)
    · apply Finset.sum_eq_zero
      intro j hj
      change x j * (E.differential i j).vertex v=0
      rw [(pure_differential_linear Q E hE i j).1]
      simp

lemma sumTokenTest_top (E : BasedComplex Q (K := K) I) (α:V) (c:ℤ)
    {x : TestIndex Q E.placement α → K} (hx : x ∈ topTestCycles Q E α c) :
    sumTokenTest Q E.placement α x ∈ coefficientTopDual Q E α c := by
  have hs := sumTokenTest_support Q E.placement α c x hx.1
  constructor
  · exact hs
  · intro i a
    by_cases ha : Q.target a=α
    · by_cases ht : Q.source a=(E.placement i).color
      · let z : TestIndex Q E.placement α := ⟨i,Sum.inr (Sum.inl (Q.reverse a)),
          (Q.source_reverse a).trans ha,(Q.target_reverse a).trans ht⟩
        have hh := tokenTestVector_differential Q E α (sumTokenTest Q E.placement α x)
          (fun j h => hs j (Or.inl h)) z
        rw [tokenTestVector_sum Q E.placement α c x hx.1,hx.2] at hh
        simpa only [z,Path.dual,Q.reverse_reverse,pathCoordinates_arrow,mul_comm,Pi.zero_apply] using hh.symm
      · apply Finset.sum_eq_zero
        intro j hj
        have hz : (E.differential i j).arrow a=0 := by
          by_contra hn
          exact ht (coordinates_corner Q (p := Sum.inr (Sum.inl a))
            (E.entries.1 i j) (E.entries.2 i j) hn).1
        rw [hz,MulZeroClass.zero_mul]
    · apply Finset.sum_eq_zero
      intro j hj
      by_cases hjc : (E.placement j).color=α
      · have hz : (E.differential i j).arrow a=0 := by
          by_contra hn
          exact ha ((coordinates_corner Q (p := Sum.inr (Sum.inl a))
            (E.entries.1 i j) (E.entries.2 i j) hn).2.trans hjc)
        rw [hz,MulZeroClass.zero_mul]
      · rw [hs j (Or.inl hjc),MulZeroClass.mul_zero]

noncomputable def coefficientTopTestEquiv (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level=l) (α:V) (c:ℤ) :
    coefficientTopDual Q E α c ≃ₗ[K] topTestCycles Q E α c where
  toFun x := ⟨tokenTestVector Q E.placement α x.val,tokenTestVector_top Q E hE α c x.property⟩
  invFun y := ⟨sumTokenTest Q E.placement α y.val,sumTokenTest_top Q E α c y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact sumTokenTest_unit Q E.placement α x.val (fun i h => x.property.1 i (Or.inl h))
  right_inv y := by
    apply Subtype.ext
    exact tokenTestVector_sum Q E.placement α c y.val y.property.1
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' r x := by apply Subtype.ext; exact map_smul _ _ _

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
