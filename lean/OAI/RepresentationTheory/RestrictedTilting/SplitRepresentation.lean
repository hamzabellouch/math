import Mathlib

namespace OAI

namespace FiberFunctorProof
open CategoryTheory Representation
universe u
variable {k : Type u} [Field k] {G : Type u} [Group G]
variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable {ρ : Representation k G V} {σ : Representation k G W}

 
def kernelInclusion (s : ρ.IntertwiningMap σ) : s.ker.toRepresentation.IntertwiningMap ρ :=
  ⟨s.toLinearMap.ker.subtype, fun _ => rfl⟩

 
def splitKernelProjection (f : σ.IntertwiningMap ρ) (s : ρ.IntertwiningMap σ)
    (h : s.comp f = IntertwiningMap.id σ) :
    ρ.IntertwiningMap s.ker.toRepresentation where
  toLinearMap := (LinearMap.id - f.toLinearMap.comp s.toLinearMap).codRestrict _ (fun v => by
    change s (v - f (s v)) = 0
    have hh : s (f (s v)) = s v := congr($(h) (s v))
    rw [map_sub,hh,sub_self])
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρ g v - f (s (ρ g v)) = ρ g (v - f (s v))
    rw [map_sub, s.isIntertwining, f.isIntertwining]

@[simp] lemma splitKernelProjection_apply (f : σ.IntertwiningMap ρ)
    (s : ρ.IntertwiningMap σ) (h : s.comp f = IntertwiningMap.id σ) (v : V) :
    (splitKernelProjection f s h v : V) = v - f (s v) := rfl

lemma splitKernelProjection_inclusion (f : σ.IntertwiningMap ρ)
    (s : ρ.IntertwiningMap σ) (h : s.comp f = IntertwiningMap.id σ) :
    (splitKernelProjection f s h).comp (kernelInclusion s) =
      IntertwiningMap.id s.ker.toRepresentation := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (v : V) - f (s v) = v
  have hv : s v = 0 := v.property
  simp [hv]

lemma splitKernel_decompose (f : σ.IntertwiningMap ρ)
    (s : ρ.IntertwiningMap σ) (h : s.comp f = IntertwiningMap.id σ) :
    s.toLinearMap.ker.subtype.comp (splitKernelProjection f s h).toLinearMap +
      f.toLinearMap.comp s.toLinearMap = LinearMap.id := by
  ext v
  change (v - f (s v)) + f (s v) = v
  exact sub_add_cancel _ _

lemma projective_of_identity_sum {C : Type*} [Category* C] [Preadditive C]
    {A P Q : C} (hP : Projective P) (hQ : Projective Q)
    (a : A ⟶ P) (b : P ⟶ A) (c : A ⟶ Q) (d : Q ⟶ A)
    (h : a ≫ b + c ≫ d = 𝟙 A) : Projective A := by
  constructor
  intro E X f e he
  obtain ⟨i,hi⟩ := hP.factors (b ≫ f) e
  obtain ⟨j,hj⟩ := hQ.factors (d ≫ f) e
  refine ⟨a ≫ i + c ≫ j, ?_⟩
  simp only [Preadditive.add_comp, Category.assoc, hi, hj]
  rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, h, Category.id_comp]

lemma projective_of_split_kernel (f : σ.IntertwiningMap ρ)
    (s : ρ.IntertwiningMap σ) (h : s.comp f = IntertwiningMap.id σ)
    (hσ : Projective (Rep.of σ)) (hK : Projective (Rep.of s.ker.toRepresentation)) :
    Projective (Rep.of ρ) := by
  apply projective_of_identity_sum hK hσ
    (Rep.ofHom (splitKernelProjection f s h)) (Rep.ofHom (kernelInclusion s))
    (Rep.ofHom s) (Rep.ofHom f)
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  exact splitKernel_decompose f s h
end FiberFunctorProof

end OAI
