import Mathlib
import OAI.RingTheory.Multiplicity.DuttaData

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M N : ModuleCat.{u} R} [Module.Free R N] [Module.Finite R N]

lemma exists_unit_pivot (f : M ⟶ N)
    (hf : ¬ f.hom.range ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) :
    ∃ (x : M) (l : N →ₗ[R] R), l (f x) = 1 := by
  classical
  obtain ⟨y,hy,hy'⟩ := SetLike.not_le_iff_exists.mp hf
  obtain ⟨x,rfl⟩ := hy
  let b := Module.finBasis R N
  have hc : ∃ j, b.repr (f x) j ∉ IsLocalRing.maximalIdeal R := by
    by_contra! h
    apply hy'
    rw [← b.sum_repr (f x)]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem_smul (h j) Submodule.mem_top
  obtain ⟨j,hj⟩ := hc
  obtain ⟨u,hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hj
  refine ⟨x,(↑(u⁻¹):R) • b.coord j,?_⟩
  change (↑(u⁻¹):R) * b.repr (f x) j = 1
  rw [← hu]
  exact Units.inv_mul u

lemma exists_nonzero_reverse_projector (f : M ⟶ N)
    (hf : ¬ f.hom.range ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) :
    ∃ t : N ⟶ M, t ≫ f ≫ t = t ∧ f ≫ t ≠ 0 := by
  obtain ⟨x,l,hl⟩ := exists_unit_pivot f hf
  let t : N ⟶ M := ModuleCat.ofHom (l.smulRight x)
  have hx : x ≠ 0 := by
    intro hx
    rw [hx,map_zero,map_zero] at hl
    exact zero_ne_one hl
  refine ⟨t,?_,?_⟩
  · ext y
    change l (f (l y • x)) • x = l y • x
    rw [map_smul,map_smul,hl,smul_eq_mul,mul_one]
  · intro ht
    have hh := congrArg (fun g : M ⟶ M => g x) ht
    change l (f x) • x = 0 at hh
    rw [hl,one_smul] at hh
    exact hx hh
end Lech

end

end OAI
