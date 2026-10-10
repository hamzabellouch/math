import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.GeneratorPlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

def reductionAt (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) (a : GeneratorPlacement V) :
    Matrix {i // p i = a} {j // q j = a} K :=
  fun i j => (M i.1 j.1).vertex a.color

lemma reductionAt_add (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M N : Matrix I J (Q.Zigzag K)) (a : GeneratorPlacement V) :
    reductionAt Q p q (M + N) a = reductionAt Q p q M a + reductionAt Q p q N a := rfl

omit [Fintype A] [DecidableEq V] in
lemma reductionAt_positive (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) (a : GeneratorPlacement V) (hM : PositiveMatrix Q M) :
    reductionAt Q p q M a = 0 := by
  funext i j
  change (M i.1 j.1).vertex a.color = 0
  rw [hM i.1 j.1]
  rfl

lemma reductionAt_identity [DecidableEq I] (p : I → GeneratorPlacement V)
    (a : GeneratorPlacement V) :
    reductionAt Q p p (projectiveIdentity Q (K := K) p) a = 1 := by
  classical
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [reductionAt, projectiveIdentity, i.property]
  · have h' : (i : I) ≠ (j : I) := fun he => h (Subtype.ext he)
    simp [reductionAt, projectiveIdentity, h, h']

lemma reductionAt_mul [Fintype J]
    (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (r : L → GeneratorPlacement V) (M : Matrix I J (Q.Zigzag K))
    (N : Matrix J L (Q.Zigzag K)) (a : GeneratorPlacement V)
    (hc : ProjectiveEntries Q p q M) (hd : MapDegree Q p q 0 0 M) :
    reductionAt Q p r (M * N) a =
      reductionAt Q p q M a * reductionAt Q q r N a := by
  classical
  apply Matrix.ext
  intro i l
  change (vertexHom Q (K := K) a.color) ((M * N) i.1 l.1) = _
  simp only [Matrix.mul_apply, map_sum, map_mul]
  apply Finset.sum_congr_set {j | q j = a}
  · intro j hj
    rfl
  · intro j hj
    have hz : (M i.1 j).vertex a.color = 0 := by
      by_contra hn
      have hs := (reduction_support Q hc hd i.1 j a.color hn).1
      exact hj (hs.symm.trans i.property)
    change (M i.1 j).vertex a.color * (N j l.1).vertex a.color = 0
    rw [hz]
    exact MulZeroClass.zero_mul _

namespace BasedComplex

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

structure HomotopyEquivalence (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) where
  forward : Map Q E F
  backward : Map Q F E
  sourceHomotopy : Matrix I I (Q.Zigzag K)
  targetHomotopy : Matrix J J (Q.Zigzag K)
  sourceEntries : ProjectiveEntries Q E.placement E.placement sourceHomotopy
  targetEntries : ProjectiveEntries Q F.placement F.placement targetHomotopy
  sourceDegree : MapDegree Q E.placement E.placement (-1) 0 sourceHomotopy
  targetDegree : MapDegree Q F.placement F.placement (-1) 0 targetHomotopy
  sourceEquation : forward.matrix * backward.matrix = projectiveIdentity Q E.placement +
    (E.differential * sourceHomotopy + sourceHomotopy * E.differential)
  targetEquation : backward.matrix * forward.matrix = projectiveIdentity Q F.placement +
    (F.differential * targetHomotopy + targetHomotopy * F.differential)

theorem multiplicity_eq_of_minimal_homotopyEquivalence
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (h : HomotopyEquivalence Q E F) (a : GeneratorPlacement V) :
    E.multiplicity Q a = F.multiplicity Q a := by
  classical
  let f := reductionAt Q E.placement F.placement h.forward.matrix a
  let g := reductionAt Q F.placement E.placement h.backward.matrix a
  have hfg : f * g = 1 := by
    dsimp only [f, g]
    rw [← reductionAt_mul Q _ _ _ _ _ a h.forward.entries h.forward.degree,
      h.sourceEquation, reductionAt_add, reductionAt_identity,
      reductionAt_positive Q _ _ _ a]
    · exact add_zero _
    · exact positiveMatrix_add Q
        (positiveMatrix_mul_right Q hE h.sourceHomotopy)
        (positiveMatrix_mul_left Q h.sourceHomotopy hE)
  have hgf : g * f = 1 := by
    dsimp only [f, g]
    rw [← reductionAt_mul Q _ _ _ _ _ a h.backward.entries h.backward.degree,
      h.targetEquation, reductionAt_add, reductionAt_identity,
      reductionAt_positive Q _ _ _ a]
    · exact add_zero _
    · exact positiveMatrix_add Q
        (positiveMatrix_mul_right Q hF h.targetHomotopy)
        (positiveMatrix_mul_left Q h.targetHomotopy hF)
  have hd := (Matrix.toLinearEquivRight'OfInv hfg hgf).finrank_eq
  simpa only [multiplicity, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card] using hd.symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
