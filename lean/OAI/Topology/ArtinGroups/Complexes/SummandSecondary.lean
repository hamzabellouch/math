import Mathlib
import OAI.Topology.ArtinGroups.Complexes.RestrictExtendLayerMul
import OAI.Topology.ArtinGroups.Complexes.LeftMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T]

noncomputable def summandSecondary (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (q d n : ℤ)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M) :
    Matrix T {j // (F.placement j).level = d} (Q.Zigzag K) →ₗ[K]
      Matrix T {j // (F.placement j).level = d-1} (Q.Zigzag K) :=
  (leftMatrix Q ι.matrix).comp
    ((secondaryLayer Q E F q d n).comp (leftMatrix Q π.matrix))

lemma summandSecondary_cycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (q d n v : ℤ)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M)
    {f : Matrix T {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q M (F.pureLayer Q hF d) n v) :
    summandSecondary Q E F hE M q d n ι π f ∈
      homCycles Q M (F.pureLayer Q hF (d-1)) (n+1) v := by
  have hp : π.matrix * f ∈ homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n v := by
    simpa only [zero_add] using homCycles_mul Q (map_mem_homCycles Q π) hf
  change (show Matrix T {i // (E.placement i).level = q} (Q.Zigzag K) from ι.matrix) *
    secondaryLayer Q E F q d n (π.matrix * f) ∈ _
  simpa only [zero_add] using homCycles_mul Q (map_mem_homCycles Q ι)
    (secondaryLayer_mem_cycles Q E F hE hF q d n v hp)

lemma summandSecondary_kernel_zero [Fintype V] [DecidableEq T]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (U : Set V) (q d n v : ℤ)
    (hM : ∀ i, (M.placement i).level = q) (hU : ∀ i, (M.placement i).color ∈ U)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M)
    (hret : ι.matrix * π.matrix = projectiveIdentity Q M.placement)
    (hcap : E.CappedOn Q U q) (hd : homDimension Q E F n v = 0)
    (hdeg : n+v = d-q)
    {f : Matrix T {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q M (F.pureLayer Q hF d) n v)
    (hb : summandSecondary Q E F hE M q d n ι π f ∈
      homBoundaries Q M (F.pureLayer Q hF (d-1)) (n+1) v) : f = 0 := by
  have hp : π.matrix * f ∈ homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n v := by
    simpa only [zero_add] using homCycles_mul Q (map_mem_homCycles Q π) hf
  have hs : ∀ i j, (E.placement i.val).color ∉ U → (π.matrix * f) i j = 0 := by
    intro i j hi
    exact pureMap_mul_support Q π q (fun i => i.property) hM U hU f i j hi
  have he : π.matrix * summandSecondary Q E F hE M q d n ι π f =
      secondaryLayer Q E F q d n (π.matrix * f) := by
    change π.matrix * ((show Matrix T {i // (E.placement i).level = q} (Q.Zigzag K) from ι.matrix) *
      secondaryLayer Q E F q d n (π.matrix * f)) = _
    rw [secondaryLayer_eq_target Q E F hE hF U q d n hcap hs]
    have hr : π.matrix * ι.matrix * π.matrix = π.matrix := by
      rw [Matrix.mul_assoc, hret]
      exact mul_projectiveIdentity Q π.entries
    calc
      _ = -(cochainSign (K := K) n • ((π.matrix * ι.matrix * π.matrix) * f *
        restrictLayer Q F F d (d-1) (matrixTwo Q F.differential))) := by
          simp only [Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc]
      _ = _ := by rw [hr]
  have hb' : secondaryLayer Q E F q d n (π.matrix * f) ∈
      homBoundaries Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v := by
    rw [← he]
    simpa only [zero_add] using homCycle_mul_boundary Q (map_mem_homCycles Q π) hb
  have hz : π.matrix * f = 0 := capped_secondary_kernel_zero Q E F hE hF U q d n v hcap hd hp
    (pure_homSpace_coefficient Q _ _ (fun i => i.property) (fun j => j.property) hdeg hp.1) hs hb'
  calc
    f = ι.matrix * (π.matrix * f) := by
      rw [← Matrix.mul_assoc, hret]
      exact (projectiveIdentity_mul Q hf.1.1).symm
    _ = 0 := by rw [hz, Matrix.mul_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
