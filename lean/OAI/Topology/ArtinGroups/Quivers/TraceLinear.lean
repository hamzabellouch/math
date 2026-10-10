import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomSpace

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

lemma trace_smul (r : K) (x : Q.Zigzag K) : trace Q (r • x) = r * trace Q x := by
  simp only [trace, token_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

def traceLinear : Q.Zigzag K →ₗ[K] K where
  toFun := trace Q
  map_add' := trace_add Q
  map_smul' := by intro r x; exact trace_smul Q r x

namespace BasedComplex
variable [Fintype I] [Fintype J]

noncomputable def homCycles (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) : Submodule K (Matrix I J (Q.Zigzag K)) :=
  homSpace Q E F n v ⊓ LinearMap.ker (homDifferential Q E F n)

noncomputable def homBoundaries (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) : Submodule K (Matrix I J (Q.Zigzag K)) :=
  (homSpace Q E F (n - 1) v).map (homDifferential Q E F (n - 1))

omit [Fintype V] in
lemma homBoundaries_le_homCycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homBoundaries Q E F n v ≤ homCycles Q E F n v := by
  rintro _ ⟨f, hf, rfl⟩
  constructor
  · change homDifferential Q E F (n - 1) f ∈ homSpace Q E F n v
    have hd := homDifferential_mem Q E F (n - 1) v hf
    rw [sub_add_cancel] at hd
    exact hd
  · change homDifferential Q E F n (homDifferential Q E F (n - 1) f) = 0
    simpa only [sub_add_cancel] using homDifferential_square_zero Q E F (n - 1) f

abbrev homCohomology (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) :=
  homCycles Q E F n v ⧸
    (homBoundaries Q E F n v).comap (homCycles Q E F n v).subtype

noncomputable def supertrace (E : BasedComplex Q (K := K) I) :
    Matrix I I (Q.Zigzag K) →ₗ[K] K where
  toFun f := ∑ i, cochainSign (K := K) (E.placement i).cochain * trace Q (f i i)
  map_add' f g := by
    simp only [Matrix.add_apply, trace_add, _root_.mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, trace_smul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma supertrace_mul (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {n v : ℤ}
    {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q E.placement F.placement n v f)
    (g : Matrix J I (Q.Zigzag K)) :
    supertrace Q F (g * f) = cochainSign (K := K) n * supertrace Q E (f * g) := by
  change (∑ j, cochainSign (K := K) _ * traceLinear Q (∑ i, g j i * f i j)) =
    cochainSign (K := K) n * ∑ i, cochainSign (K := K) _ * traceLinear Q (∑ j, f i j * g j i)
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : (F.placement j).cochain = (E.placement i).cochain + n
  · change cochainSign (K := K) _ * trace Q (g j i * f i j) =
      cochainSign (K := K) n * (cochainSign (K := K) _ * trace Q (f i j * g j i))
    rw [hc, cochainSign_add, trace_mul_comm Q (g j i)]
    ring
  · rw [(hf i j).1 hc, MulZeroClass.mul_zero, MulZeroClass.zero_mul,
      map_zero, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
    exact (MulZeroClass.mul_zero _).symm

lemma supertrace_boundary (E : BasedComplex Q (K := K) I)
    (h : Matrix I I (Q.Zigzag K)) :
    supertrace Q E (homDifferential Q E E (-1) h) = 0 := by
  have hs : cochainSign (K := K) (-1) = -1 := by norm_num [cochainSign]
  have hp : cochainSign (K := K) 1 = -1 := by norm_num [cochainSign]
  change supertrace Q E (E.differential * h - cochainSign (K := K) (-1) • (h * E.differential)) = 0
  have hcyc := supertrace_mul Q E E E.degree h
  rw [hp] at hcyc
  calc
    _ = supertrace Q E (E.differential * h) -
        cochainSign (K := K) (-1) * supertrace Q E (h * E.differential) := by
      exact (supertrace Q E).map_sub _ _ |>.trans
        (congrArg (fun z => supertrace Q E (E.differential * h) - z)
          ((supertrace Q E).map_smul_of_tower (cochainSign (K := K) (-1)) (h * E.differential)))
    _ = 0 := by rw [hs, hcyc]; ring

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
