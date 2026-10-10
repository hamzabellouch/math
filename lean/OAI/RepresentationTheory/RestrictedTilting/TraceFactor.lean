import OAI.RepresentationTheory.RestrictedTilting.FiniteFreeTrace

namespace OAI

namespace FiberFunctorProof
open CategoryTheory Representation
universe u
variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]
variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable {I : Type u} [Fintype I]

 
noncomputable def coordinateTraceLift (ρ : Representation k G V)
    (b : Module.Basis I k W) (t : V →ₗ[k] W) :
    V →ₗ[k] (I →₀ MonoidAlgebra k G) :=
  ∑ g : G, ∑ i : I, (Finsupp.lsingle i).comp
    ((MonoidAlgebra.lsingle g).comp ((b.coord i).comp (t.comp (ρ g⁻¹))))

lemma coordinateTraceLift_apply (ρ : Representation k G V)
    (b : Module.Basis I k W) (t : V →ₗ[k] W) (v : V) :
    coordinateTraceLift ρ b t v = ∑ g : G, ∑ i : I,
      Finsupp.single i (MonoidAlgebra.single g (b.repr (t (ρ g⁻¹ v)) i)) := by
  simp [coordinateTraceLift, LinearMap.sum_apply]

noncomputable def coordinateTraceHom (ρ : Representation k G V)
    (b : Module.Basis I k W) (t : V →ₗ[k] W) :
    ρ.IntertwiningMap (Representation.free k G I) where
  toLinearMap := coordinateTraceLift ρ b t
  isIntertwining' h := by
    ext v : 1
    simp only [LinearMap.comp_apply, coordinateTraceLift_apply, map_sum,
      Representation.free_single_single]
    symm
    apply Fintype.sum_equiv (Equiv.mulLeft h)
    intro g
    simp [mul_inv_rev, map_mul]

lemma freeCover_traceLift (ρ : Representation k G V) (σ : Representation k G W)
    (b : Module.Basis I k W) (t : V →ₗ[k] W) :
    (Representation.freeLift σ b).toLinearMap.comp (coordinateTraceLift ρ b t) =
      relativeTrace ρ σ t := by
  ext v
  simp only [LinearMap.comp_apply, coordinateTraceLift_apply, map_sum,
    IntertwiningMap.toLinearMap_apply, Representation.freeLift_single_single, relativeTrace_apply]
  apply Finset.sum_congr rfl
  intro g hg
  simp only [← map_smul]
  rw [← map_sum, b.sum_repr]

 

noncomputable def finiteTraceBasis (V : FDRep k G) :
    Module.Basis (ULift.{u} (Fin (Module.finrank k V))) k V :=
  (Module.finBasis k V).reindex Equiv.ulift.symm

 
theorem relativeTrace_factors (V W : FDRep k G) (f : V ⟶ W) (t : V →ₗ[k] W)
    (ht : relativeTrace V.ρ W.ρ t = f.hom.hom.hom) : FactorsThroughProjective f := by
  let b := finiteTraceBasis W
  let A := FDRep.of (Representation.free k G (ULift.{u} (Fin (Module.finrank k W))))
  refine ⟨A, fdrep_free_projective _, finiteIntertwiner (coordinateTraceHom V.ρ b t),
    finiteIntertwiner (Representation.freeLift W.ρ b), ?_⟩
  apply Action.Hom.ext
  apply InducedCategory.hom_ext
  apply ModuleCat.hom_ext
  exact (freeCover_traceLift V.ρ W.ρ b t).trans ht

 
def underlyingIntertwiner {V W : FDRep k G} (f : V ⟶ W) :
    Representation.IntertwiningMap V.ρ W.ρ where
  toLinearMap := f.hom.hom.hom
  isIntertwining' g := congrArg (fun h : V.V ⟶ W.V => h.hom.hom) (f.comm g)

 
theorem relativeTrace_of_factors (V W : FDRep k G) (f : V ⟶ W)
    (hf : FactorsThroughProjective f) :
    ∃ t : V →ₗ[k] W, relativeTrace V.ρ W.ρ t = f.hom.hom.hom := by
  obtain ⟨P,hP,a,b,rfl⟩ := hf
  let e := finiteFreeCover P
  let : Epi e := finiteFreeCover_epi P
  obtain ⟨s,hs⟩ := hP.factors (𝟙 P) e
  let a' := underlyingIntertwiner (a ≫ s)
  let b' := underlyingIntertwiner (e ≫ b)
  refine ⟨b'.toLinearMap.comp ((freeNormRepresentative _).comp a'.toLinearMap), ?_⟩
  rw [relativeTrace_postcomp, relativeTrace_precomp]
  erw [free_relativeTrace]
  change ((a ≫ s) ≫ (e ≫ b)).hom.hom.hom = (a ≫ b).hom.hom.hom
  rw [Category.assoc, ← Category.assoc s, hs, Category.id_comp]

theorem projective_factor_iff_relativeTrace (V W : FDRep k G) (f : V ⟶ W) :
    FactorsThroughProjective f ↔ ∃ t : V →ₗ[k] W,
      relativeTrace V.ρ W.ρ t = f.hom.hom.hom :=
  ⟨relativeTrace_of_factors V W f, fun ⟨t,ht⟩ => relativeTrace_factors V W f t ht⟩
end FiberFunctorProof

end OAI
