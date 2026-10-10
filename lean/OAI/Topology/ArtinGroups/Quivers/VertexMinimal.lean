import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Complexes.CoconePlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

def VertexMinimal [Fintype I] (E : BasedComplex Q (K := K) I) (v : V) : Prop :=
  ∀ i j, (E.differential i j).vertex v = 0

lemma vertexEntries_zero_left {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M)
    (i : I) (j : J) {v : V} (hv : (p i).color ≠ v) : (M i j).vertex v = 0 := by
  have h := congrArg (fun x : Q.Zigzag K => x.vertex v) (hM.1 i j)
  change (vertexId Q (p i).color).vertex v * (M i j).vertex v = (M i j).vertex v at h
  rw [vertexId_eval, ite_eq_right (Ne.symm hv), MulZeroClass.zero_mul] at h
  exact h.symm

lemma vertexEntries_zero_right {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M)
    (i : I) (j : J) {v : V} (hv : (q j).color ≠ v) : (M i j).vertex v = 0 := by
  have h := congrArg (fun x : Q.Zigzag K => x.vertex v) (hM.2 i j)
  change (M i j).vertex v * (vertexId Q (q j).color).vertex v = (M i j).vertex v at h
  rw [vertexId_eval, ite_eq_right (Ne.symm hv), MulZeroClass.mul_zero] at h
  exact h.symm

lemma reductionAt_vertex_boundary [Fintype I]
    (E : BasedComplex Q (K := K) I) (H : Matrix I I (Q.Zigzag K))
    (a : GeneratorPlacement V) (hE : VertexMinimal Q E a.color) :
    reductionAt Q E.placement E.placement (E.differential * H + H * E.differential) a = 0 := by
  apply Matrix.ext
  intro i j
  change (vertexHom Q (K := K) a.color)
    ((E.differential * H + H * E.differential) i.val j.val) = 0
  simp only [Matrix.add_apply, Matrix.mul_apply, map_add, map_sum, map_mul]
  change (∑ k, (E.differential i.val k).vertex a.color * (H k j.val).vertex a.color) +
    (∑ k, (H i.val k).vertex a.color * (E.differential k j.val).vertex a.color) = 0
  have hz (i j : I) : (E.differential i j).vertex a.color = 0 := hE i j
  simp only [hz, MulZeroClass.zero_mul, MulZeroClass.mul_zero, Finset.sum_const_zero, add_zero]

namespace BasedComplex

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem multiplicity_eq_of_vertex_homotopyEquivalence
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (h : HomotopyEquivalence Q E F) (a : GeneratorPlacement V)
    (hE : VertexMinimal Q E a.color) (hF : VertexMinimal Q F a.color) :
    E.multiplicity Q a = F.multiplicity Q a := by
  classical
  let f := reductionAt Q E.placement F.placement h.forward.matrix a
  let g := reductionAt Q F.placement E.placement h.backward.matrix a
  have hfg : f * g = 1 := by
    dsimp only [f, g]
    rw [← reductionAt_mul Q _ _ _ _ _ a h.forward.entries h.forward.degree,
      h.sourceEquation, reductionAt_add, reductionAt_identity,
      reductionAt_vertex_boundary Q E _ a hE, add_zero]
  have hgf : g * f = 1 := by
    dsimp only [f, g]
    rw [← reductionAt_mul Q _ _ _ _ _ a h.backward.entries h.backward.degree,
      h.targetEquation, reductionAt_add, reductionAt_identity,
      reductionAt_vertex_boundary Q F _ a hF, add_zero]
  have hd := (Matrix.toLinearEquivRight'OfInv hfg hgf).finrank_eq
  simpa only [multiplicity, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card] using hd.symm

variable [Fintype V] [DecidableEq A]

omit [Fintype J] [DecidableEq J] [DecidableEq I] in
lemma positiveTwist_vertexMinimal (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (α β : V) (hαβ : α ≠ β) :
    VertexMinimal Q (E.positiveTwist Q α) β := by
  intro i j
  rcases i with i | i
  · exact vertexEntries_zero_left Q (E.positiveTwist Q α).entries (.inl i) j hαβ
  · rcases j with j | j
    · exact vertexEntries_zero_right Q (E.positiveTwist Q α).entries (.inr i) (.inl j) hαβ
    · change (E.differential i j).vertex β = 0
      rw [hE i j]
      rfl

omit [Fintype J] [DecidableEq J] [DecidableEq I] in
lemma negativeTwist_vertexMinimal (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (α β : V) (hαβ : α ≠ β) :
    VertexMinimal Q (E.negativeTwist Q α) β := by
  intro i j
  rcases i with i | i
  · rcases j with j | j
    · change (E.differential i j).vertex β = 0
      rw [hE i j]
      rfl
    · exact vertexEntries_zero_right Q (E.negativeTwist Q α).entries (.inl i) (.inr j) hαβ
  · exact vertexEntries_zero_left Q (E.negativeTwist Q α).entries (.inr i) j hαβ

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
