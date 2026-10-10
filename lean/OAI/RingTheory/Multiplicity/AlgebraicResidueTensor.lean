import Mathlib

namespace OAI

noncomputable section
open IsLocalRing TensorProduct
namespace Lech.ResidueTensor
variable (k R K : Type*) [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
  [Field K] [Algebra k K]
  (hres : Function.Bijective (algebraMap k (ResidueField R)))

 
def fiberEquiv : ((R ⊗[k] K) ⧸ ((maximalIdeal R).map (algebraMap R (R ⊗[k] K)))) ≃ₐ[k] K :=
  (Algebra.TensorProduct.quotientTensorEquiv (R:=k) k K R (maximalIdeal R)).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.ofBijective (Algebra.ofId k (ResidueField R)) hres).symm
      (AlgEquiv.refl : K ≃ₐ[k] K)).trans (Algebra.TensorProduct.lid k K))

@[simp] lemma fiberEquiv_includeRight (b : K) :
    fiberEquiv k R K hres (Ideal.Quotient.mk _
      (Algebra.TensorProduct.includeRight (R:=k) (A:=R) b))=b := by
  change ((AlgEquiv.ofBijective (Algebra.ofId k (ResidueField R)) hres).symm
    (Ideal.Quotient.mk (maximalIdeal R) 1)) • b=b
  simp
  exact (congrArg (· • b)
    (map_one (AlgEquiv.ofBijective (Algebra.ofId k (ResidueField R)) hres).symm)).trans
      (one_smul k b)

include hres
lemma residue_surjective [IsLocalRing (R ⊗[k] K)] (hmap : maximalIdeal (R ⊗[k] K)=
    (maximalIdeal R).map (algebraMap R (R ⊗[k] K)))
    :
    Function.Surjective ((residue (R ⊗[k] K)).comp
      (Algebra.TensorProduct.includeRight (R:=k) (A:=R)).toRingHom) := by
  intro x
  obtain ⟨t,rfl⟩ := IsLocalRing.residue_surjective x
  refine ⟨fiberEquiv k R K hres (Ideal.Quotient.mk _ t),?_⟩
  change Ideal.Quotient.mk (maximalIdeal (R ⊗[k] K)) _=Ideal.Quotient.mk _ t
  rw [hmap]
  apply (fiberEquiv k R K hres).injective
  exact fiberEquiv_includeRight k R K hres _

include hres
lemma maximal_map : ((maximalIdeal R).map (algebraMap R (R ⊗[k] K))).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ ((fiberEquiv k R K hres).toMulEquiv.isField (Field.toIsField K))

variable [Algebra.IsAlgebraic k K]
lemma isLocal : IsLocalRing (R ⊗[k] K) := by
  let T := R ⊗[k] K
  let m := (maximalIdeal R).map (algebraMap R T)
  have hm := maximal_map k R K hres
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨m,hm,?_⟩
  intro Q hQ
  let : Q.IsMaximal := hQ
  let : Algebra.IsIntegral k K := inferInstance
  let : Algebra.IsIntegral R T := inferInstance
  have hcomap := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R:=R) Q
  have hle : m ≤ Q := Ideal.map_le_iff_le_comap.mpr (eq_maximalIdeal hcomap).symm.le
  exact (hm.eq_of_le hQ.ne_top hle).symm

lemma maximalIdeal_eq_map :
    let : IsLocalRing (R ⊗[k] K) := isLocal k R K hres
    maximalIdeal (R ⊗[k] K)=(maximalIdeal R).map (algebraMap R (R ⊗[k] K)) := by
  let : IsLocalRing (R ⊗[k] K) := isLocal k R K hres
  exact (eq_maximalIdeal (maximal_map k R K hres)).symm

end Lech.ResidueTensor

end

end OAI
