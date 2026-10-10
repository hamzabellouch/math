import Mathlib
import OAI.RingTheory.Multiplicity.RootRestriction

namespace OAI

noncomputable section
namespace Lech.ProductLaurent
open AddMonoidAlgebra Polynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Equiv.Perm (Fin n))

def permute : Ring R n ≃ₐ[R] Ring R n := domCongr R R (Finsupp.domCongr σ)

lemma permute_ringHom_apply (x : Ring R n) :
    (permute R n σ).toRingHom x=permute R n σ x := rfl

lemma permute_variable (i : Fin n) :
    permute R n σ (variableUnit R n i : Ring R n)=(variableUnit R n (σ i) : Ring R n) := by
  change domCongr R R (Finsupp.domCongr σ) (single (Finsupp.single i 1) 1)=_
  rw [domCongr_single]
  congr 1
  ext j
  simp only [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply,Finsupp.single_apply]
  congr 1
  exact propext (σ.eq_symm_apply)

lemma permute_binaryForm : (binaryForm R n).map (permute R n σ).toRingHom=binaryForm R n := by
  simp only [binaryForm,Polynomial.map_prod,Polynomial.map_add,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_X,Polynomial.map_one,permute_ringHom_apply]
  simp only [permute_variable]
  exact Equiv.prod_comp σ (fun i => C (variableUnit R n i : Ring R n)*X+1)

lemma permute_coefficient (i : Fin (n+1)) :
    permute R n σ ((binaryForm R n).coeff i)=(binaryForm R n).coeff i := by
  simpa only [Polynomial.coeff_map,permute_ringHom_apply] using congrArg (fun p : (Ring R n)[X] => p.coeff i) (permute_binaryForm R n σ)

lemma permute_symm : (permute R n σ).symm=permute R n σ.symm := by
  simp only [permute,domCongr_symm,Finsupp.domCongr_symm]
end Lech.ProductLaurent

namespace Lech.ProductSourceCover
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Equiv.Perm (Fin n))
def permuteWeight (m : Fin n → ℤ) : Fin n → ℤ := fun i => m (σ.symm i)

lemma permute_denominator (s : Finset (Fin (n+1))) :
    ProductLaurent.permute R n σ (denominator R n s)=denominator R n s := by
  simp only [denominator,AwayCover.denominator,map_prod,ProductLaurent.permute_coefficient]

lemma permute_powers :
    (Submonoid.powers (denominator R n Finset.univ)).map (ProductLaurent.permute R n σ)=
      Submonoid.powers (denominator R n Finset.univ) := by
  rw [Submonoid.map_powers,permute_denominator]

def permuteGrid : GridAmbient R n ≃ₐ[R] GridAmbient R n :=
  IsLocalization.algEquivOfAlgEquiv (GridAmbient R n) (GridAmbient R n)
    (ProductLaurent.permute R n σ) (permute_powers R n σ)

lemma permuteGrid_embed (x : Ambient R n) :
    permuteGrid R n σ (embed R n x)=embed R n (ProductLaurent.permute R n σ x) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ _

lemma permuteGrid_symm : (permuteGrid R n σ).symm=permuteGrid R n σ.symm := by
  apply AlgEquiv.coe_ringEquiv_injective
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (denominator R n Finset.univ))
  apply RingHom.ext
  intro x
  change (permuteGrid R n σ).symm (embed R n x)=permuteGrid R n σ.symm (embed R n x)
  apply (permuteGrid R n σ).injective
  rw [AlgEquiv.apply_symm_apply,permuteGrid_embed,permuteGrid_embed,←ProductLaurent.permute_symm,
    AlgEquiv.apply_symm_apply]

lemma permute_ringSections (m : Fin n → ℤ) (x : Ambient R n) (hx : x∈ringSections R n m ∅) :
    ProductLaurent.permute R n σ x∈ringSections R n (permuteWeight n σ m) ∅ := by
  rw [ringSections_mem] at hx ⊢
  intro e he
  rw [ProductLaurent.permute,domCongr_support] at he
  obtain ⟨a,ha,hae⟩ := Finset.mem_map.mp he
  rw [←hae]
  have hh := (allowed_empty n m a).mp (hx a ha)
  apply (allowed_empty n _ _).mpr
  intro i
  change 0 ≤ a (σ.symm i) ∧ a (σ.symm i) ≤ m (σ.symm i)
  exact hh (σ.symm i)

lemma permute_grid (m : Fin n → ℤ) (s : Finset (Fin (n+1)))
    (x : GridAmbient R n) (hx : x∈grid R n m s ∅) :
      permuteGrid R n σ x∈grid R n (permuteWeight n σ m) s ∅ := by
  obtain ⟨N,a,ha,he⟩ := hx
  refine ⟨N,ProductLaurent.permute R n σ a,permute_ringSections R n σ (levelTwist n m s.card N) a ha,?_⟩
  have h := congrArg (permuteGrid R n σ) he
  simpa only [map_mul,map_pow,permuteGrid_embed,permute_denominator] using h
end Lech.ProductSourceCover

namespace Lech.ProjectiveRoot
open ProductSourceCover HomogeneousLocalization
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (σ : Equiv.Perm (Fin n))
attribute [local instance] MvPolynomial.gradedAlgebra

lemma permute_coefficientEvaluation (a : MvPolynomial (Fin (n+1)) R) :
    permuteGrid R n σ (coefficientEvaluation R n a)=coefficientEvaluation R n a := by
  have he : (permuteGrid R n σ).toAlgHom.comp (coefficientEvaluation R n)=coefficientEvaluation R n := by
    ext j
    simp only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,coefficientEvaluation_X,
      targetUnit_val,permuteGrid_embed,ProductLaurent.permute_coefficient]
  exact DFunLike.congr_fun he a

lemma permute_scalarMap (s : Finset (Fin (n+1))) (a : Ring R n s) :
    permuteGrid R n σ (scalarMap R n s a)=scalarMap R n s a := by
  let f := Localization.awayLift (coefficientEvaluation R n).toRingHom
    (product R n s) (coefficientEvaluation_unit R n s)
  have he : ((permuteGrid R n σ : GridAmbient R n →+* GridAmbient R n).comp f)=f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (product R n s))
    apply RingHom.ext
    intro x
    change permuteGrid R n σ (f (algebraMap _ _ x))=f (algebraMap _ _ x)
    dsimp only [f]
    rw [IsLocalization.Away.lift_eq]
    exact permute_coefficientEvaluation R n σ x
  exact DFunLike.congr_fun he a.val

 

def permuteSections (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Sections R n s hs m ≃ₗ[Ring R n s] Sections R n s hs (permuteWeight n σ m) where
  toFun x := ⟨permuteGrid R n σ x.val,permute_grid R n σ m s x.val x.property⟩
  invFun x := ⟨(permuteGrid R n σ).symm x.val,by
    rw [permuteGrid_symm]
    have hh := permute_grid R n σ.symm (permuteWeight n σ m) s x.val x.property
    have hw : permuteWeight n σ.symm (permuteWeight n σ m)=m := by
      funext i
      simp [permuteWeight]
    rw [hw] at hh
    exact hh⟩
  left_inv x := Subtype.ext ((permuteGrid R n σ).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((permuteGrid R n σ).apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (by
    change permuteGrid R n σ (scalarMap R n s a*x.val)=scalarMap R n s a*permuteGrid R n σ x.val
    rw [map_mul,permute_scalarMap])

lemma permuteSections_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (m : Fin n → ℤ) (x : Sections R n s hs m) :
    sectionsRestriction R n hs ht (permuteWeight n σ m) hst (permuteSections R n σ s hs m x)=
      permuteSections R n σ t ht m (sectionsRestriction R n hs ht m hst x) := rfl
end Lech.ProjectiveRoot

end

end OAI
