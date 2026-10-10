import OAI.RepresentationTheory.RestrictedTilting.SteinbergRegular
import OAI.RepresentationTheory.RestrictedTilting.ProjectiveRegular
import OAI.RepresentationTheory.RestrictedTilting.ProjectiveFactor
import OAI.RepresentationTheory.RestrictedTilting.TensorExactness

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe u

 
abbrev Tilting (k : Type u) [Field k] :=
  ObjectProperty.FullSubcategory (IsTilting k)

abbrev tiltingInclusion (k : Type u) [Field k] : Tilting k ⥤ FDRep k (SL2 k) :=
  ObjectProperty.ι (IsTilting k)

 

noncomputable def steinbergIdeal (k : Type u) [Field k] (p n : ℕ) (A B : Tilting k) :
    Submodule k (A ⟶ B) :=
  Submodule.span k {f | ∃ X : Tilting k,
    ∃ a : A.obj ⟶ steinberg k p n ⊗ X.obj,
    ∃ b : steinberg k p n ⊗ X.obj ⟶ B.obj, f.hom = a ≫ b}

variable (k : Type u) [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p]
variable (l : (Fin r → ZMod p) →+ k) (hl : Function.Injective l)
include hl

 
theorem restricted_steinberg_projective :
    Projective ((restrictElementary k p r l).obj (steinberg k p r)) := by
  obtain ⟨e⟩ := steinberg_restriction_regular k p r l hl
  exact Projective.of_iso e.symm (fdrep_leftRegular_projective k _)

 

theorem steinbergIdeal_restricts_projectively (A B : Tilting k) (f : A ⟶ B)
    (hf : f ∈ steinbergIdeal k p r A B) :
    FactorsThroughProjective ((restrictElementary k p r l).map f.hom) := by
  let R := restrictElementary k p r l
  let : R.Additive := by dsimp [R, restrictElementary]; infer_instance
  let : R.Linear k := by dsimp [R, restrictElementary]; infer_instance
  let L : (A ⟶ B) →ₗ[k] (R.obj A.obj ⟶ R.obj B.obj) :=
    (R.mapLinearMap k).comp ((tiltingInclusion k).mapLinearMap k)
  let : HasFiniteBiproducts (FDRep k (Multiplicative (Fin r → ZMod p))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let : RigidCategory (FDRep k (Multiplicative (Fin r → ZMod p))) :=
    BraidedCategory.rigidCategoryOfRightRigidCategory
  let N := (projectiveFactorSubmodule (k := k) (R.obj A.obj) (R.obj B.obj)).comap L
  have hspan : steinbergIdeal k p r A B ≤ N := by
    apply Submodule.span_le.mpr
    rintro g ⟨X,a,b,hg⟩
    change FactorsThroughProjective (R.map g.hom)
    have hS : Projective (R.obj (steinberg k p r)) :=
      restricted_steinberg_projective k p r l hl
    let := hS
    have hT : Projective (R.obj (steinberg k p r ⊗ X.obj)) := by
      change Projective (R.obj (steinberg k p r) ⊗ R.obj X.obj)
      exact projective_tensor _ _
    refine ⟨_,hT,R.map a,R.map b,?_⟩
    rw [← R.map_comp, ← hg]
  exact hspan hf
end FiberFunctorProof

end OAI
