import Mathlib

namespace OAI

/-! Kernels, ranges, quotients and factorization of finite-dimensional representations. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
universe u
variable (k : Type u) [Field k]

 
def fdrepHom {G : Type u} [Monoid G] {A B : FDRep k G}
    (f : A →ₗ[k] B) (hf : ∀ g x, f (A.ρ g x) = B.ρ g (f x)) : A ⟶ B where
  hom := FGModuleCat.ofHom f
  comm g := by
    apply FGModuleCat.hom_ext
    exact LinearMap.ext (hf g)

noncomputable def fdrepForget (G : Type u) [Monoid G] : FDRep k G ⥤ ModuleCat k :=
  forget₂ (FDRep k G) (Rep k G) ⋙ forget₂ (Rep k G) (ModuleCat k)

instance (G : Type u) [Monoid G] : (fdrepForget k G).Faithful := by
  dsimp [fdrepForget]
  infer_instance

instance (G : Type u) [Monoid G] : PreservesFiniteLimits (fdrepForget k G) := by
  dsimp [fdrepForget]
  infer_instance

instance (G : Type u) [Monoid G] : PreservesFiniteColimits (fdrepForget k G) := by
  dsimp [fdrepForget]
  infer_instance

instance (G : Type u) [Monoid G] : (fdrepForget k G).Additive where
  map_add := by intros; rfl

lemma fdrep_shortExact {G : Type u} [Monoid G] (S : ShortComplex (FDRep k G))
    (hinj : Function.Injective S.f.hom.hom.hom)
    (hsurj : Function.Surjective S.g.hom.hom.hom)
    (heq : LinearMap.range S.f.hom.hom.hom = LinearMap.ker S.g.hom.hom.hom) :
    S.ShortExact := by
  let F := fdrepForget k G
  have h : (S.map F).ShortExact := {
    exact := ((S.map F).moduleCat_exact_iff_range_eq_ker).mpr heq
    mono_f := (ModuleCat.mono_iff_injective _).mpr hinj
    epi_g := (ModuleCat.epi_iff_surjective _).mpr hsurj }
  exact {
    exact := (S.exact_map_iff_of_faithful F).mp h.exact
    mono_f := F.mono_of_mono_map h.mono_f
    epi_g := F.epi_of_epi_map h.epi_g }

end

universe u
variable (k : Type u) [Field k]
variable {G : Type u} [Monoid G]

abbrev fdrepLinear {A B : FDRep k G} (f : A ⟶ B) : A →ₗ[k] B := f.hom.hom.hom

lemma fdrepLinear_comm {A B : FDRep k G} (f : A ⟶ B) (g : G) (x : A) :
    fdrepLinear k f (A.ρ g x) = B.ρ g (fdrepLinear k f x) := by
  exact LinearMap.congr_fun (congrArg (fun t => t.hom.hom) (f.comm g)) x

lemma fdrep_injective {A B : FDRep k G} (f : A ⟶ B) [Mono f] :
    Function.Injective (fdrepLinear k f) :=
  (ModuleCat.mono_iff_injective ((fdrepForget k G).map f)).mp (by infer_instance)

lemma fdrep_surjective {A B : FDRep k G} (f : A ⟶ B) [Epi f] :
    Function.Surjective (fdrepLinear k f) :=
  (ModuleCat.epi_iff_surjective ((fdrepForget k G).map f)).mp (by infer_instance)

lemma fdrep_exact {S : ShortComplex (FDRep k G)} (h : S.Exact) :
    LinearMap.range (fdrepLinear k S.f) = LinearMap.ker (fdrepLinear k S.g) :=
  ((S.map (fdrepForget k G)).moduleCat_exact_iff_range_eq_ker).mp (h.map (fdrepForget k G))

 
def fdrepKernelSub {A B : FDRep k G} (f : A ⟶ B) : Subrepresentation A.ρ where
  toSubmodule := LinearMap.ker (fdrepLinear k f)
  apply_mem_toSubmodule g x hx := by
    change fdrepLinear k f (A.ρ g x) = 0
    rw [fdrepLinear_comm, show fdrepLinear k f x = 0 from hx, map_zero]

noncomputable def fdrepKernel {A B : FDRep k G} (f : A ⟶ B) : FDRep k G :=
  FDRep.of (fdrepKernelSub k f).toRepresentation

noncomputable def fdrepKernelι {A B : FDRep k G} (f : A ⟶ B) : fdrepKernel k f ⟶ A :=
  fdrepHom k (LinearMap.ker (fdrepLinear k f)).subtype (by intros; rfl)

noncomputable def fdrepKernelLift {A B C : FDRep k G} (f : A ⟶ B) (g : B ⟶ C)
    (w : f ≫ g = 0) : A ⟶ fdrepKernel k g :=
  fdrepHom k ((fdrepLinear k f).codRestrict (LinearMap.ker (fdrepLinear k g)) (by
    intro x
    change fdrepLinear k g (fdrepLinear k f x) = 0
    exact LinearMap.congr_fun (congrArg (fdrepLinear k) w) x)) (by
      intro a x
      apply Subtype.ext
      exact fdrepLinear_comm k f a x)

lemma fdrepKernelLift_ι {A B C : FDRep k G} (f : A ⟶ B) (g : B ⟶ C)
    (w : f ≫ g = 0) : fdrepKernelLift k f g w ≫ fdrepKernelι k g = f := rfl

 
noncomputable def linearFactor {A B C : Type u} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (f : A →ₗ[k] B) (hf : Function.Injective f) (g : C →ₗ[k] B)
    (hg : ∀ x, g x ∈ LinearMap.range f) : C →ₗ[k] A :=
  (LinearEquiv.ofInjective f hf).symm.toLinearMap.comp (g.codRestrict (LinearMap.range f) hg)

lemma linearFactor_comp {A B C : Type u} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C]
    (f : A →ₗ[k] B) (hf : Function.Injective f) (g : C →ₗ[k] B)
    (hg : ∀ x, g x ∈ LinearMap.range f) (x : C) :
    f (linearFactor k f hf g hg x) = g x := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective f hf).apply_symm_apply
    ⟨g x, hg x⟩)

noncomputable def fdrepFactor {A B C : FDRep k G} (f : A ⟶ B)
    (hf : Function.Injective (fdrepLinear k f)) (g : C ⟶ B)
    (hg : ∀ x, fdrepLinear k g x ∈ LinearMap.range (fdrepLinear k f)) : C ⟶ A :=
  fdrepHom k (linearFactor k (fdrepLinear k f) hf (fdrepLinear k g) hg) (by
    intro a x
    apply hf
    rw [linearFactor_comp, fdrepLinear_comm, fdrepLinear_comm, linearFactor_comp])

lemma fdrepFactor_comp {A B C : FDRep k G} (f : A ⟶ B)
    (hf : Function.Injective (fdrepLinear k f)) (g : C ⟶ B)
    (hg : ∀ x, fdrepLinear k g x ∈ LinearMap.range (fdrepLinear k f)) :
    fdrepFactor k f hf g hg ≫ f = g := by
  apply Action.hom_ext
  apply FGModuleCat.hom_ext
  exact LinearMap.ext (linearFactor_comp k (fdrepLinear k f) hf (fdrepLinear k g) hg)


lemma fdrep_splice {A B C D E : FDRep k G}
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact)
    (i : D ⟶ C) (j : C ⟶ E) (v : i ≫ j = 0)
    (hT : (ShortComplex.mk i j v).ShortExact) :
    ∃ (K : FDRep k G) (a : A ⟶ K) (b : K ⟶ D) (r : K ⟶ B)
      (wab : a ≫ b = 0) (wr : r ≫ (g ≫ j) = 0),
      (ShortComplex.mk a b wab).ShortExact ∧
      (ShortComplex.mk r (g ≫ j) wr).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have := hT.mono_f
  have := hT.epi_g
  have hf := fdrep_injective k f
  have hg := fdrep_surjective k g
  have hi := fdrep_injective k i
  have hj := fdrep_surjective k j
  have hexS := fdrep_exact k hS.exact
  have hexT := fdrep_exact k hT.exact
  let K := fdrepKernel k (g ≫ j)
  let r : K ⟶ B := fdrepKernelι k (g ≫ j)
  have w' : f ≫ (g ≫ j) = 0 := by rw [← Category.assoc, w, zero_comp]
  let a : A ⟶ K := fdrepKernelLift k f (g ≫ j) w'
  have hrange (x : K) : fdrepLinear k (r ≫ g) x ∈ LinearMap.range (fdrepLinear k i) := by
    rw [hexT]
    exact x.property
  let b : K ⟶ D := fdrepFactor k i hi (r ≫ g) hrange
  have hb (x : K) : fdrepLinear k i (fdrepLinear k b x) =
      fdrepLinear k g (fdrepLinear k r x) :=
    linearFactor_comp k _ hi _ hrange x
  have ha (x : A) : fdrepLinear k r (fdrepLinear k a x) = fdrepLinear k f x := rfl
  have hab : a ≫ b = 0 := by
    apply Action.hom_ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply hi
    change fdrepLinear k i (fdrepLinear k b (fdrepLinear k a x)) = fdrepLinear k i 0
    rw [hb, ha, map_zero]
    exact LinearMap.congr_fun (congrArg (fdrepLinear k) w) x
  have hr : r ≫ (g ≫ j) = 0 := by
    apply Action.hom_ext
    apply FGModuleCat.hom_ext
    exact LinearMap.ext (fun x => x.property)
  refine ⟨K, a, b, r, hab, hr, fdrep_shortExact k _ ?_ ?_ ?_,
    fdrep_shortExact k _ ?_ ?_ ?_⟩
  · intro x y hxy
    apply hf
    exact congrArg Subtype.val hxy
  · intro d
    obtain ⟨x, hx⟩ := hg (fdrepLinear k i d)
    have hx' : fdrepLinear k (g ≫ j) x = 0 := by
      change fdrepLinear k j (fdrepLinear k g x) = 0
      rw [hx]
      exact LinearMap.congr_fun (congrArg (fdrepLinear k) v) d
    let x' : K := ⟨x, hx'⟩
    refine ⟨x', hi ?_⟩
    rw [hb]
    exact hx
  · apply le_antisymm
    · rw [LinearMap.range_le_ker_iff]
      exact congrArg (fdrepLinear k) hab
    · intro x hx
      have hx' : fdrepLinear k r x ∈ LinearMap.ker (fdrepLinear k g) := by
        change fdrepLinear k g (fdrepLinear k r x) = 0
        rw [← hb, show fdrepLinear k b x = 0 from hx, map_zero]
      rw [← hexS] at hx'
      obtain ⟨y, hy⟩ := hx'
      refine ⟨y, ?_⟩
      apply Subtype.ext
      exact hy
  · exact Subtype.val_injective
  · exact hj.comp hg
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact x.property
    · intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩


lemma fdrepDesc_range {A B C : FDRep k G} (f : A ⟶ B)
    (g : A ⟶ C) (hker : LinearMap.ker (fdrepLinear k f) ≤
      LinearMap.ker (fdrepLinear k g)) (a b : A)
    (h : fdrepLinear k f a = fdrepLinear k f b) :
    fdrepLinear k g a = fdrepLinear k g b := by
  have hz : a-b ∈ LinearMap.ker (fdrepLinear k f) := by
    change fdrepLinear k f (a-b) = 0
    rw [map_sub, h, sub_self]
  have := hker hz
  change fdrepLinear k g (a-b) = 0 at this
  simpa only [map_sub, sub_eq_zero] using this

 
noncomputable def fdrepDesc {A B C : FDRep k G} (f : A ⟶ B)
    (hf : Function.Surjective (fdrepLinear k f)) (g : A ⟶ C)
    (hker : LinearMap.ker (fdrepLinear k f) ≤ LinearMap.ker (fdrepLinear k g)) : B ⟶ C :=
  fdrepHom k (((LinearMap.ker (fdrepLinear k f)).liftQ (fdrepLinear k g) hker).comp
    (LinearMap.quotKerEquivOfSurjective (fdrepLinear k f) hf).symm.toLinearMap) (by
      intro a b
      obtain ⟨x,rfl⟩ := hf b
      have happ (x : A) :
          (LinearMap.quotKerEquivOfSurjective (fdrepLinear k f) hf).symm
            (fdrepLinear k f x) = (LinearMap.ker (fdrepLinear k f)).mkQ x := by
        apply (LinearMap.quotKerEquivOfSurjective (fdrepLinear k f) hf).injective
        simp
      rw [← fdrepLinear_comm k f a x]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, happ]
      exact fdrepLinear_comm k g a x)

lemma fdrepDesc_comp {A B C : FDRep k G} (f : A ⟶ B)
    (hf : Function.Surjective (fdrepLinear k f)) (g : A ⟶ C)
    (hker : LinearMap.ker (fdrepLinear k f) ≤ LinearMap.ker (fdrepLinear k g)) :
    f ≫ fdrepDesc k f hf g hker = g := by
  apply Action.hom_ext
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (LinearMap.ker (fdrepLinear k f)).liftQ (fdrepLinear k g) hker
    ((LinearMap.quotKerEquivOfSurjective (fdrepLinear k f) hf).symm (fdrepLinear k f x)) = _
  have happ : (LinearMap.quotKerEquivOfSurjective (fdrepLinear k f) hf).symm
      (fdrepLinear k f x) = (LinearMap.ker (fdrepLinear k f)).mkQ x := by
    apply (LinearMap.quotKerEquivOfSurjective (fdrepLinear k f) hf).injective
    simp
  rw [happ]
  rfl

def fdrepRangeSub {A B : FDRep k G} (f : A ⟶ B) : Subrepresentation B.ρ where
  toSubmodule := LinearMap.range (fdrepLinear k f)
  apply_mem_toSubmodule g x hx := by
    obtain ⟨a,rfl⟩ := hx
    exact ⟨A.ρ g a, fdrepLinear_comm k f g a⟩

noncomputable def fdrepQuotient {A B : FDRep k G} (f : A ⟶ B) : FDRep k G :=
  FDRep.of (Representation.quotient B.ρ (fdrepRangeSub k f).toSubmodule
    (fdrepRangeSub k f).apply_mem_toSubmodule)

noncomputable def fdrepQuotientπ {A B : FDRep k G} (f : A ⟶ B) : B ⟶ fdrepQuotient k f :=
  fdrepHom k (LinearMap.range (fdrepLinear k f)).mkQ (by
    intros
    rfl)

lemma fdrepQuotientπ_surjective {A B : FDRep k G} (f : A ⟶ B) :
    Function.Surjective (fdrepLinear k (fdrepQuotientπ k f)) :=
  (LinearMap.range (fdrepLinear k f)).mkQ_surjective

lemma fdrepQuotientπ_eq_zero {A B : FDRep k G} (f : A ⟶ B) (x : B) :
    fdrepLinear k (fdrepQuotientπ k f) x = 0 ↔ x ∈ LinearMap.range (fdrepLinear k f) :=
  Submodule.Quotient.mk_eq_zero _

end FiberFunctorProof
end

end OAI
