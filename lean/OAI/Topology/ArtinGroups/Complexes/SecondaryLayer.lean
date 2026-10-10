import Mathlib
import OAI.Topology.ArtinGroups.Complexes.DifferentialMulExtendLayer
import OAI.Topology.ArtinGroups.Complexes.Capped
import OAI.Topology.ArtinGroups.Complexes.MatrixOneMulExtend
import OAI.Topology.ArtinGroups.Quivers.VertexLinear

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def secondaryLayer (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (q d n : ℤ) :
    Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K) →ₗ[K]
    Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d-1} (Q.Zigzag K) :=
  (restrictLayer Q E F q (d-1)).comp
    ((tokenHomDifferential Q E F n).comp (extendLayer Q E F q d))

lemma secondaryLayer_token (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (q d n : ℤ)
    (f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)) :
    TokenMatrix Q (secondaryLayer Q E F q d n f) := by
  intro i j
  exact tokenHomDifferential_tokenMatrix Q E F hE hF n (extendLayer Q E F q d f) i.val j.val

lemma capped_secondaryLayer_extension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (U : Set V) (q d n : ℤ) (hcap : E.CappedOn Q U q)
    {f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hs : ∀ i j, (E.placement i.val).color ∉ U → f i j = 0) :
    extendLayer Q E F q (d-1) (secondaryLayer Q E F q d n f) =
      tokenHomDifferential Q E F n (extendLayer Q E F q d f) := by
  change extendLayer Q E F q (d-1)
    (restrictLayer Q E F q (d-1)
      (tokenHomDifferential Q E F n (extendLayer Q E F q d f))) = _
  apply extend_restrictLayer Q E F q (d-1)
  intro i j hh
  rw [tokenHomDifferential_apply Q E F hE hF,
    capped_matrixTwo_mul_extend Q E F U q d hcap hs, zero_sub]
  change -(cochainSign (K := K) n •
    (extendLayer Q E F q d f * matrixTwo Q F.differential) i j) = 0
  rw [extend_mul_matrixTwo_support Q E F q d f i j hh, smul_zero, neg_zero]

lemma secondaryLayer_mem_cycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (q d n v : ℤ)
    {f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n v) :
    secondaryLayer Q E F q d n f ∈
      homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v := by
  have hlinear : linearHomDifferential Q E F n (extendLayer Q E F q d f) = 0 := by
    rw [linearHomDifferential_extendLayer Q E F hE hF q d n,
      show homDifferential Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n f = 0 from hf.2,
      map_zero]
  have hcomp : tokenHomDifferential Q E F n (extendLayer Q E F q d f) =
      homDifferential Q E F n (extendLayer Q E F q d f) := by
    rw [homDifferential_eq_linear_add_token, hlinear, zero_add]
  constructor
  · change restrictLayer Q E F q (d-1)
      (tokenHomDifferential Q E F n (extendLayer Q E F q d f)) ∈ _
    rw [hcomp]
    exact restrictLayer_homSpace Q E F hE hF q (d-1) (n+1) v
      (homDifferential_mem Q E F n v (extendLayer_homSpace Q E F hE hF q d n v hf.1))
  · change homDifferential Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1)
      (secondaryLayer Q E F q d n f) = 0
    exact homDifferential_tokenMatrix Q _ _
      (fun i j => (E.pureLayer_linear Q hE q i j).1)
      (fun i j => (F.pureLayer_linear Q hF (d-1) i j).1) (n+1)
      (secondaryLayer_token Q E F hE hF q d n f)

lemma capped_secondary_kernel_zero [Fintype V]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q) (U : Set V) (q d n v : ℤ)
    (hcap : E.CappedOn Q U q) (hd : homDimension Q E F n v = 0)
    {f : Matrix {i // (E.placement i).level = q} {j // (F.placement j).level = d} (Q.Zigzag K)}
    (hf : f ∈ homCycles Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n v)
    (h₀ : CoefficientMatrix Q f)
    (hs : ∀ i j, (E.placement i.val).color ∉ U → f i j = 0)
    (hb : secondaryLayer Q E F q d n f ∈
      homBoundaries Q (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1)) (n+1) v) : f = 0 := by
  obtain ⟨g, hg, hlin, he⟩ := token_boundary_primitive Q
    (E.pureLayer Q hE q) (F.pureLayer Q hF (d-1))
    (E.pureLayer_linear Q hE q) (F.pureLayer_linear Q hF (d-1)) (n+1) v
    (secondaryLayer_token Q E F hE hF q d n f) hb
  have hn : n + 1 - 1 = n := by omega
  rw [hn] at hg he
  have hlinear : linearHomDifferential Q E F n (extendLayer Q E F q d f) = 0 := by
    rw [linearHomDifferential_extendLayer Q E F hE hF q d n,
      show homDifferential Q (E.pureLayer Q hE q) (F.pureLayer Q hF d) n f = 0 from hf.2,
      map_zero]
  have hfull : homDifferential Q E F n (extendLayer Q E F q d f) =
      homDifferential Q E F n (extendLayer Q E F q (d-1) g) := by
    rw [homDifferential_eq_linear_add_token Q E F n (extendLayer Q E F q d f),
      hlinear, zero_add, homDifferential_extendLayer Q E F hE hF q (d-1) n hlin, he,
      capped_secondaryLayer_extension Q E F hE hF U q d n hcap hs]
  have hz := coefficient_eq_zero_of_same_differential Q E F hE hF n v hd
    (extendLayer_homSpace Q E F hE hF q d n v hf.1)
    (extendLayer_homSpace Q E F hE hF q (d-1) n v hg)
    (extendLayer_coefficient Q E F q d h₀) (extendLayer_linear Q E F q (d-1) hlin) hfull
  have hh := congrArg (restrictLayer Q E F q d) hz
  rw [restrictLayer_extend, map_zero] at hh
  exact hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
