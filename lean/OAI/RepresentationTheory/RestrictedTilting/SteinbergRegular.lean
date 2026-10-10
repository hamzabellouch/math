import OAI.RepresentationTheory.RestrictedTilting.Basic

namespace OAI

namespace FiberFunctorProof
open CategoryTheory
open scoped BigOperators
universe u v
variable (k : Type u) [Field k]

 
noncomputable def binaryEval (n : ℕ) (z : k) :
    MvPolynomial.homogeneousSubmodule (Fin 2) k n →ₗ[k] k :=
  (MvPolynomial.aeval ![z,1]).toLinearMap.comp
    (MvPolynomial.homogeneousSubmodule (Fin 2) k n).subtype

lemma binaryEval_basis (n : ℕ) (z : k) (i : Fin (n+1)) :
    binaryEval k n z (binaryBasis k n i) = z^(n-i.val) := by
  simp [binaryEval, binaryBasis_apply]

 

noncomputable def binaryHomogenize (n : ℕ) (P : Polynomial k) :
    MvPolynomial.homogeneousSubmodule (Fin 2) k n :=
  ∑ i : Fin (n+1), P.coeff i.val • binaryBasis k n ⟨n-i.val, by omega⟩

lemma binaryEval_homogenize (n : ℕ) (P : Polynomial k)
    (hP : P.natDegree ≤ n) (z : k) :
    binaryEval k n z (binaryHomogenize k n P) = P.eval z := by
  rw [binaryHomogenize, map_sum]
  simp only [map_smul, binaryEval_basis, smul_eq_mul]
  have hi (i : Fin (n+1)) : n-(n-i.val) = i.val := by omega
  simp only [hi]
  conv_rhs => rw [P.as_sum_range' (n+1) (by omega)]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  exact Fin.sum_univ_eq_sum_range (fun i => P.coeff i * z^i) (n+1)

variable {E : Type v} [Fintype E]

noncomputable def binarySubgroupEval (n : ℕ) (l : E → k) :
    MvPolynomial.homogeneousSubmodule (Fin 2) k n →ₗ[k] (E → k) :=
  LinearMap.pi (fun a => binaryEval k n (l a))

lemma binarySubgroupEval_surjective (l : E → k) (hl : Function.Injective l)
    [Nonempty E] : Function.Surjective (binarySubgroupEval k (Fintype.card E-1) l) := by
  classical
  intro f
  let P := Lagrange.interpolate Finset.univ l f
  have hp := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := l) f hl.injOn
  have hn : P.natDegree ≤ Fintype.card E-1 := by
    by_cases h : P = 0
    · simp [h]
    · have ht : P.natDegree < Fintype.card E :=
        (Polynomial.natDegree_lt_iff_degree_lt h).mpr (by simpa [P] using hp)
      omega
  refine ⟨binaryHomogenize k (Fintype.card E-1) P, ?_⟩
  funext a
  change binaryEval k _ (l a) _ = _
  rw [binaryEval_homogenize k _ P hn]
  exact Lagrange.eval_interpolate_at_node f hl.injOn (Finset.mem_univ a)

noncomputable def binarySubgroupEquiv (l : E → k) (hl : Function.Injective l)
    [Nonempty E] :
    MvPolynomial.homogeneousSubmodule (Fin 2) k (Fintype.card E-1) ≃ₗ[k] (E → k) :=
  LinearEquiv.ofBijective (binarySubgroupEval k _ l) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [binaryBasis_finrank, Module.finrank_pi]
      exact Nat.sub_add_cancel Fintype.card_pos)).mpr (binarySubgroupEval_surjective k l hl),
    binarySubgroupEval_surjective k l hl⟩

lemma binaryEval_unipotent (n : ℕ) (t z : k)
    (v : MvPolynomial.homogeneousSubmodule (Fin 2) k n) :
    binaryEval k n z ((costandard k n).ρ (unipotent k t) v) =
      binaryEval k n (z-t) v := by
  change MvPolynomial.aeval ![z,1]
    (linearChange (dualMatrix k (unipotent k t)) v.val) = MvPolynomial.aeval ![z-t,1] v.val
  have h : (MvPolynomial.aeval ![z,1]).comp (linearChange (dualMatrix k (unipotent k t))) =
      (MvPolynomial.aeval ![z-t,1] : MvPolynomial (Fin 2) k →ₐ[k] k) := by
    ext i
    fin_cases i <;>
      simp [linearChange_X, dualMatrix, unipotent, Matrix.transpose_apply,
        Fin.sum_univ_two, sub_eq_add_neg, add_comm]
  exact DFunLike.congr_fun h v.val

 
noncomputable def groupAlgebraCoefficients (G : Type v) [Fintype G] :
    MonoidAlgebra k G ≃ₗ[k] (G → k) :=
  (MonoidAlgebra.coeffLinearEquiv k).trans (Finsupp.linearEquivFunOnFinite k k G)

@[simp] lemma groupAlgebraCoefficients_apply (G : Type v) [Fintype G]
    (x : MonoidAlgebra k G) (g : G) : groupAlgebraCoefficients k G x g = x.coeff g := rfl

 

theorem steinberg_restriction_regular (p r : ℕ) [Fact p.Prime] [CharP k p]
    (l : (Fin r → ZMod p) →+ k) (hl : Function.Injective l) :
    Nonempty ((restrictElementary k p r l).obj (steinberg k p r) ≅
      FDRep.of (Representation.leftRegular k (Multiplicative (Fin r → ZMod p)))) := by
  classical
  let E := Multiplicative (Fin r → ZMod p)
  let A := (restrictElementary k p r l).obj (steinberg k p r)
  let B := FDRep.of (Representation.leftRegular k E)
  have hc : Fintype.card E = p^r := by
    simp [E, ZMod.card]
  have hi : Function.Injective (fun a : E => l a.toAdd) := by
    intro a b hab
    exact congrArg Multiplicative.ofAdd (hl hab)
  have hb := (binarySubgroupEquiv k (fun a : E => l a.toAdd) hi).bijective
  change Function.Bijective (binarySubgroupEval k (Fintype.card E-1)
    (fun a : E => l a.toAdd)) at hb
  rw [hc] at hb
  let e : A ≃ₗ[k] (E → k) :=
    LinearEquiv.ofBijective (binarySubgroupEval k (p^r-1) (fun a : E => l a.toAdd)) hb
  let L : A ≃ₗ[k] B := e.trans (groupAlgebraCoefficients k E).symm
  have hL (v : A) (b : E) : (L v).coeff b = binaryEval k (p^r-1) (l b.toAdd) v := by
    change groupAlgebraCoefficients k E ((groupAlgebraCoefficients k E).symm (e v)) b = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have heq (a : E) (v : A) : L (A.ρ a v) = B.ρ a (L v) := by
    apply MonoidAlgebra.ext
    ext b
    rw [hL]
    change binaryEval k (p^r-1) (l b.toAdd)
      ((costandard k (p^r-1)).ρ (unipotent k (l a.toAdd)) v) =
      ((Representation.leftRegular k E) a (L v)).coeff b
    erw [binaryEval_unipotent k (p^r-1) (l a.toAdd) (l b.toAdd) v]
    rw [Representation.coeff_ofMulAction, hL]
    have hab : l (a⁻¹ • b).toAdd = l b.toAdd - l a.toAdd := by
      change l (-a.toAdd + b.toAdd) = _
      simp [sub_eq_add_neg, add_comm]
    rw [hab]
  exact ⟨Action.mkIso L.toFGModuleCatIso (fun a => FGModuleCat.hom_ext (LinearMap.ext (heq a)))⟩

 
def RegularSteinbergStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : ℕ), 1 ≤ r → ∀ (l : (Fin r → ZMod p) →+ k), Function.Injective l →
      Nonempty ((restrictElementary k p r l).obj (steinberg k p r) ≅
        FDRep.of (Representation.leftRegular k (Multiplicative (Fin r → ZMod p))))

theorem regular_steinberg : RegularSteinbergStatement.{u} := by
  intro k _ _ p _ _ r _ l hl
  exact steinberg_restriction_regular k p r l hl
end FiberFunctorProof

end OAI
