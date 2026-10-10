import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Harmonic.Level

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma mapDegree_level_bound {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} {n v : ℤ} (h : MapDegree Q p q n v M)
    {i : I} {j : J} (hne : M i j ≠ 0) :
    (q j).level ≤ (p i).level + n + v := by
  have hc : (q j).cochain = (p i).cochain + n := by
    by_contra hc
    exact hne ((h i j).1 hc)
  have ha := homogeneous_nonzero_degree Q (h i j).2 hne
  dsimp only [GeneratorPlacement.level]
  omega

def atLevel (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) (d : ℤ) :
    Matrix {i // (p i).level = d} {j // (q j).level = d} (Q.Zigzag K) :=
  fun i j => M i.val j.val

lemma atLevel_mul [Fintype J]
    (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (r : L → GeneratorPlacement V) (M : Matrix I J (Q.Zigzag K))
    (N : Matrix J L (Q.Zigzag K)) (d : ℤ)
    [Fintype {j // (q j).level = d}]
    (hM : ∀ i j, M i j ≠ 0 → (q j).level ≤ (p i).level)
    (hN : ∀ j k, N j k ≠ 0 → (r k).level ≤ (q j).level) :
    atLevel Q p r (M * N) d = atLevel Q p q M d * atLevel Q q r N d := by
  classical
  apply Matrix.ext
  intro i k
  change (∑ j, M i.val j * N j k.val) =
    ∑ j : {j // (q j).level = d}, M i.val j.val * N j.val k.val
  symm
  apply Fintype.sum_of_injective (Subtype.val : {j // (q j).level = d} → J)
    Subtype.val_injective
  · intro j hj
    by_cases h₁ : M i.val j = 0
    · rw [h₁]
      exact MulZeroClass.zero_mul _
    by_cases h₂ : N j k.val = 0
    · rw [h₂]
      exact MulZeroClass.mul_zero _
    have hle := hM i.val j h₁
    have hge := hN j k.val h₂
    have hq : (q j).level = d := by
      rw [i.property] at hle
      rw [k.property] at hge
      exact le_antisymm hle hge
    exact (hj ⟨⟨j, hq⟩, rfl⟩).elim
  · intro j
    rfl

lemma atLevel_add (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M N : Matrix I J (Q.Zigzag K)) (d : ℤ) :
    atLevel Q p q (M + N) d = atLevel Q p q M d + atLevel Q p q N d := rfl

lemma atLevel_zero (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (d : ℤ) : atLevel Q p q (0 : Matrix I J (Q.Zigzag K)) d = 0 := rfl

lemma atLevel_identity [DecidableEq I] (p : I → GeneratorPlacement V) (d : ℤ) :
    atLevel Q p p (projectiveIdentity Q (K := K) p) d =
      projectiveIdentity Q (fun i : {i // (p i).level = d} => p i.val) := by
  apply Matrix.ext
  intro i j
  change (if i.val = j.val then vertexId Q (p i.val).color else 0) =
    (if i = j then vertexId Q (p i.val).color else 0)
  simp only [Subtype.val_inj]

lemma atLevel_degree_neg (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) (d : ℤ) (hM : MapDegree Q p q (-1) 0 M) :
    atLevel Q p q M d = 0 := by
  apply Matrix.ext
  intro i j
  change M i.val j.val = 0
  by_contra hne
  have h := mapDegree_level_bound Q hM hne
  rw [i.property, j.property] at h
  omega

namespace BasedComplex

variable [Fintype I] [Fintype J] [Fintype L]

lemma map_level_bound {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (f : Map Q E F) (i : I) (j : J) (h : f.matrix i j ≠ 0) :
    (F.placement j).level ≤ (E.placement i).level := by
  simpa only [add_zero] using mapDegree_level_bound Q f.degree h

lemma minimal_differential_level_bound (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (i j : I) (h : E.differential i j ≠ 0) :
    (E.placement j).level ≤ (E.placement i).level := by
  have h := E.differential_level Q hE h
  omega

noncomputable def Map.pureLayer {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (d : ℤ) :
    Map Q (E.pureLayer Q hE d) (F.pureLayer Q hF d) where
  matrix := atLevel Q E.placement F.placement f.matrix d
  entries := ⟨fun i j => f.entries.1 i.val j.val, fun i j => f.entries.2 i.val j.val⟩
  degree := fun i j => f.degree i.val j.val
  commute := by
    change atLevel Q E.placement E.placement E.differential d *
        atLevel Q E.placement F.placement f.matrix d =
      atLevel Q E.placement F.placement f.matrix d *
        atLevel Q F.placement F.placement F.differential d
    rw [← atLevel_mul Q _ _ _ _ _ d (E.minimal_differential_level_bound Q hE)
      (map_level_bound Q f), ← atLevel_mul Q _ _ _ _ _ d (map_level_bound Q f)
      (F.minimal_differential_level_bound Q hF), f.commute]

structure ChainIsomorphism [DecidableEq I] [DecidableEq J]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) where
  forward : Map Q E F
  backward : Map Q F E
  sourceEquation : forward.matrix * backward.matrix = projectiveIdentity Q E.placement
  targetEquation : backward.matrix * forward.matrix = projectiveIdentity Q F.placement

lemma atLevel_homotopy_boundary (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (H : Matrix I I (Q.Zigzag K)) (hH : MapDegree Q E.placement E.placement (-1) 0 H)
    (d : ℤ) : atLevel Q E.placement E.placement
      (E.differential * H + H * E.differential) d = 0 := by
  classical
  have hbound (i j : I) (h : H i j ≠ 0) :
      (E.placement j).level ≤ (E.placement i).level := by
    have hb := mapDegree_level_bound Q hH h
    omega
  rw [atLevel_add, atLevel_mul Q _ _ _ _ _ d
      (E.minimal_differential_level_bound Q hE) hbound,
    atLevel_mul Q _ _ _ _ _ d hbound (E.minimal_differential_level_bound Q hE),
    atLevel_degree_neg Q _ _ _ _ hH, Matrix.zero_mul, Matrix.mul_zero, add_zero]

noncomputable def HomotopyEquivalence.pureLayer [DecidableEq I] [DecidableEq J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    (h : HomotopyEquivalence Q E F) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (d : ℤ) :
    ChainIsomorphism Q (E.pureLayer Q hE d) (F.pureLayer Q hF d) where
  forward := h.forward.pureLayer Q hE hF d
  backward := h.backward.pureLayer Q hF hE d
  sourceEquation := by
    change atLevel Q _ _ h.forward.matrix d * atLevel Q _ _ h.backward.matrix d = _
    rw [← atLevel_mul Q _ _ _ _ _ d (map_level_bound Q h.forward)
      (map_level_bound Q h.backward), h.sourceEquation, atLevel_add,
      E.atLevel_homotopy_boundary Q hE h.sourceHomotopy h.sourceDegree,
      add_zero, atLevel_identity]
    rfl
  targetEquation := by
    change atLevel Q _ _ h.backward.matrix d * atLevel Q _ _ h.forward.matrix d = _
    rw [← atLevel_mul Q _ _ _ _ _ d (map_level_bound Q h.backward)
      (map_level_bound Q h.forward), h.targetEquation, atLevel_add,
      F.atLevel_homotopy_boundary Q hF h.targetHomotopy h.targetDegree,
      add_zero, atLevel_identity]
    rfl

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
