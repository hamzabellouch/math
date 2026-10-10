import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.GeneratorPlacement

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma corner_scalar {v : V} {x : Q.Zigzag K}
    (hx : vertexId Q v * x = x) (h0 : Homogeneous Q 0 x) :
    x = x.vertex v • vertexId Q v := by
  apply Zigzag.ext
  · ext w
    by_cases hw : w = v
    · subst w
      simp
    · have he := congrArg (fun z : Q.Zigzag K => z.vertex w) hx
      change (vertexId Q v).vertex w * x.vertex w = x.vertex w at he
      rw [vertexId_eval, ite_eq_right hw, MulZeroClass.zero_mul] at he
      simpa [vertexId_eval, hw] using he.symm
  · change x.arrow = x.vertex v • (0 : A → K)
    rw [smul_zero]
    exact h0.2.1 (by decide)
  · change x.token = x.vertex v • (0 : V → K)
    rw [smul_zero]
    exact h0.2.2 (by decide)

variable {I J : Type*}

lemma degree_vertex_support {p : I → GeneratorPlacement V}
    {q : J → GeneratorPlacement V} {M : Matrix I J (Q.Zigzag K)}
    {n v : ℤ} (hc : ProjectiveEntries Q p q M) (hd : MapDegree Q p q n v M)
    (i : I) (j : J) (w : V) (hne : (M i j).vertex w ≠ 0) :
    (p i).color = w ∧ (q j).color = w ∧
    (q j).cochain = (p i).cochain + n ∧
    (q j).internal = (p i).internal + v := by
  have hleft := congrArg (fun x : Q.Zigzag K => x.vertex w) (hc.1 i j)
  have hright := congrArg (fun x : Q.Zigzag K => x.vertex w) (hc.2 i j)
  have hpv : (p i).color = w := by
    by_contra h
    have hh : w ≠ (p i).color := Ne.symm h
    change (vertexId Q (p i).color).vertex w * (M i j).vertex w = (M i j).vertex w at hleft
    rw [vertexId_eval, ite_eq_right hh, MulZeroClass.zero_mul] at hleft
    exact hne hleft.symm
  have hqv : (q j).color = w := by
    by_contra h
    have hh : w ≠ (q j).color := Ne.symm h
    change (M i j).vertex w * (vertexId Q (q j).color).vertex w = (M i j).vertex w at hright
    rw [vertexId_eval, ite_eq_right hh, MulZeroClass.mul_zero] at hright
    exact hne hright.symm
  have hcq : (q j).cochain = (p i).cochain + n := by
    by_contra h
    have hz := (hd i j).1 h
    exact hne (by simp [hz])
  have hiq : (q j).internal = (p i).internal + v := by
    by_contra h
    have hh : v + (p i).internal - (q j).internal ≠ 0 := by omega
    have hz := (hd i j).2.1 hh
    exact hne (by rw [hz]; rfl)
  exact ⟨hpv, hqv, hcq, hiq⟩

namespace BasedComplex

variable [Fintype I]

lemma differential_diagonal_zero (E : BasedComplex Q (K := K) I) (i : I) :
    E.differential i i = 0 :=
  (E.degree i i).1 (by omega)

theorem exists_pivot_of_not_minimal (E : BasedComplex Q (K := K) I)
    (hE : ¬E.IsMinimal Q) :
    ∃ i j : I, ∃ a : K, i ≠ j ∧ a ≠ 0 ∧
      (E.placement j).color = (E.placement i).color ∧
      (E.placement j).cochain = (E.placement i).cochain + 1 ∧
      (E.placement j).internal = (E.placement i).internal ∧
      E.differential i j = a • vertexId Q (E.placement i).color := by
  classical
  change ¬∀ i j, (E.differential i j).vertex = 0 at hE
  push Not at hE
  obtain ⟨i, j, hij⟩ := hE
  have hv : ∃ w, (E.differential i j).vertex w ≠ 0 := by
    by_contra h
    push Not at h
    exact hij (funext h)
  obtain ⟨w, hw⟩ := hv
  obtain ⟨hi, hj, hc, hu⟩ := degree_vertex_support Q E.entries E.degree i j w hw
  have hu' : (E.placement j).internal = (E.placement i).internal := by omega
  refine ⟨i, j, (E.differential i j).vertex w, ?_, hw, hj.trans hi.symm, hc, hu', ?_⟩
  · intro he
    subst j
    omega
  · have hdeg : Homogeneous Q 0 (E.differential i j) := by
      simpa only [zero_add, hu', sub_self] using (E.degree i j).2
    simpa only [hi] using corner_scalar Q (E.entries.1 i j) hdeg

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
