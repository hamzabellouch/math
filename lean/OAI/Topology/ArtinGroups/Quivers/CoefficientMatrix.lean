import Mathlib
import OAI.Topology.ArtinGroups.Quivers.PathZero

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

def CoefficientMatrix (f : Matrix I J (Q.Zigzag K)) : Prop :=
  ∀ i j, (f i j).arrow = 0 ∧ (f i j).token = 0

omit [Fintype I] [Fintype J] in
lemma matrixZero_eq_self {f : Matrix I J (Q.Zigzag K)} (hf : CoefficientMatrix Q f) :
    matrixZero Q f = f := by
  apply Matrix.ext
  intro i j
  apply ext
  · rfl
  · exact (hf i j).1.symm
  · exact (hf i j).2.symm

omit [Fintype I] [Fintype J] in
lemma matrixZero_linear {f : Matrix I J (Q.Zigzag K)} (hf : LinearMatrix Q f) :
    matrixZero Q f = 0 := matrixZero_eq_zero Q fun i j => (hf i j).1

namespace BasedComplex

lemma matrixZero_homDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) (f : Matrix I J (Q.Zigzag K)) :
    matrixZero Q (homDifferential Q E F n f) = 0 := by
  change matrixZero Q (E.differential * f - cochainSign (K := K) n • (f * F.differential)) = 0
  rw [map_sub, map_smul, matrixZero_mul, matrixZero_mul,
    matrixZero_eq_zero Q hE, matrixZero_eq_zero Q hF,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, sub_zero]

lemma matrixZero_boundary (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n v : ℤ) {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homBoundaries Q E F n v) :
    matrixZero Q f = 0 := by
  obtain ⟨g, _, rfl⟩ := hf
  exact matrixZero_homDifferential Q E F hE hF (n-1) g

lemma coefficient_eq_zero_of_same_differential [Fintype V]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (n v : ℤ)
    (hd : homDimension Q E F n v = 0)
    {f g : Matrix I J (Q.Zigzag K)}
    (hf : f ∈ homSpace Q E F n v) (hg : g ∈ homSpace Q E F n v)
    (h₀ : CoefficientMatrix Q f) (h₁ : LinearMatrix Q g)
    (he : homDifferential Q E F n f = homDifferential Q E F n g) : f = 0 := by
  have hc : f - g ∈ homCycles Q E F n v := by
    refine ⟨Submodule.sub_mem _ hf hg, ?_⟩
    change homDifferential Q E F n (f - g) = 0
    rw [map_sub, he, sub_self]
  have hb := boundary_of_homDimension_zero Q E F n v hd hc
  have hz := matrixZero_boundary Q E F hE hF n v hb
  rw [map_sub, matrixZero_eq_self Q h₀, matrixZero_linear Q h₁, sub_zero] at hz
  exact hz

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
