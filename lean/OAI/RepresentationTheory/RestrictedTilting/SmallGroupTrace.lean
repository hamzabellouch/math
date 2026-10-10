import OAI.RepresentationTheory.RestrictedTilting.RelativeTrace
import OAI.RepresentationTheory.RestrictedTilting.ProjectiveFactor
import OAI.RepresentationTheory.RestrictedTilting.ProjectiveRegular

namespace OAI

namespace FiberFunctorProof.SmallGroupTrace
open CategoryTheory Representation
universe u
variable {k : Type u} [Field k] {G : Type} [Group G] [Fintype G]
variable (I : Type u)

 

noncomputable def freeNormRepresentative :
    (I →₀ MonoidAlgebra k G) →ₗ[k] (I →₀ MonoidAlgebra k G) :=
  Finsupp.mapRange.linearMap
    ((MonoidAlgebra.lsingle 1).comp
      ((Finsupp.lapply 1).comp (MonoidAlgebra.coeffLinearEquiv k).toLinearMap))

omit [Fintype G] in
@[simp] lemma freeNormRepresentative_apply (x : I →₀ MonoidAlgebra k G) (i : I) :
    freeNormRepresentative I x i = MonoidAlgebra.single 1 ((x i).coeff 1) := rfl

omit [Fintype G] in
lemma free_action_apply (g : G) (x : I →₀ MonoidAlgebra k G) (i : I) :
    Representation.free k G I g x i = Representation.leftRegular k G g (x i) := by
  classical
  have H : (Finsupp.lapply i).comp (Representation.free k G I g) =
      (Representation.leftRegular k G g).comp (Finsupp.lapply i) := by
    apply Finsupp.lhom_ext
    intro j v
    simp only [LinearMap.comp_apply, Representation.finsupp_single, Finsupp.lapply_apply]
    by_cases h : j = i
    · subst j; simp
    · simp [Ne.symm h]
  exact congr($(H) x)

section
variable {k : Type u} [Field k] {G : Type} [Group G] [Fintype G]

 

lemma free_relativeTrace (I : Type u) :
    relativeTrace (Representation.free k G I) (Representation.free k G I)
      (freeNormRepresentative I) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro i
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  simp only [relativeTrace_apply, Finsupp.finsetSum_apply,
    free_action_apply, freeNormRepresentative_apply]
  simp [Representation.coeff_ofMulAction]

 
noncomputable def finiteIntertwiner {V W : FDRep k G} (f : Representation.IntertwiningMap V.ρ W.ρ) : V ⟶ W :=
  (FDRep.forget₂HomLinearEquiv V W) (Rep.ofHom f)

omit [Fintype G] in
@[simp] lemma finiteIntertwiner_hom {V W : FDRep k G} (f : Representation.IntertwiningMap V.ρ W.ρ) :
    (finiteIntertwiner f).hom.hom.hom = f.toLinearMap := rfl

omit [Fintype G] in
lemma finiteIntertwiner_epi {V W : FDRep k G} (f : Representation.IntertwiningMap V.ρ W.ρ)
    (hf : Function.Surjective f) : Epi (finiteIntertwiner f) := by
  let F := forget₂ (FDRep k G) (Rep k G)
  have : Epi (F.map (finiteIntertwiner f)) := (Rep.epi_iff_surjective _).2 hf
  exact F.epi_of_epi_map this

 

lemma fdrep_free_projective (I : Type u) [Finite I] :
    Projective (FDRep.of (Representation.free k G I)) := by
  apply (forget₂ (FDRep k G) (Rep k G)).projective_of_map_projective
  exact (Rep.toModuleMonoidAlgebra (k := k) (G := G)).projective_of_map_projective
    (P := Rep.of (Representation.free k G I))
    (ModuleCat.projective_of_free (Representation.freeAsModuleBasis k G I))

 
noncomputable def finiteFreeCover (V : FDRep k G) :
    FDRep.of (Representation.free k G (ULift.{u} (Fin (Module.finrank k V)))) ⟶ V :=
  finiteIntertwiner (Representation.freeLift V.ρ
    (fun i : ULift.{u} (Fin (Module.finrank k V)) => Module.finBasis k V i.down))

lemma finiteFreeCover_epi (V : FDRep k G) : Epi (finiteFreeCover V) := by
  classical
  apply finiteIntertwiner_epi
  intro v
  refine ⟨∑ i : Fin (Module.finrank k V),
    Finsupp.single (ULift.up i) (MonoidAlgebra.single 1 ((Module.finBasis k V).repr v i)), ?_⟩
  change (Representation.freeLift V.ρ (fun i : ULift.{u} (Fin (Module.finrank k V)) =>
    Module.finBasis k V i.down)).toLinearMap _ = v
  rw [map_sum]
  simp only [IntertwiningMap.toLinearMap_apply, Representation.freeLift_single_single,
    map_one, Module.End.one_apply]
  exact (Module.finBasis k V).sum_repr v

end

section
variable {k : Type u} [Field k] {G : Type} [Group G] [Fintype G]
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

end

end FiberFunctorProof.SmallGroupTrace

end OAI
