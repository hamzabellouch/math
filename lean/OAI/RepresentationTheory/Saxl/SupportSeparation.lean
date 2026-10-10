import OAI.RepresentationTheory.Saxl.SpechtClassification

namespace OAI

noncomputable section

open scoped TensorProduct

universe uR uX uY uG uV

namespace Saxl
open scoped MonoidAlgebra

/- In a semisimple module, support containment is equivalent to separation
by homomorphisms (multiplicities are immaterial for the band step). -/
theorem hom_separates_of_simple_support {R : Type uR} {X : Type uX} {Y : Type uY} [Ring R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [IsSemisimpleModule R X]
    (h : ∀ S : Submodule R X, IsSimpleModule R S →
      ∃ f : S →ₗ[R] Y, f ≠ 0) (x : X) (hx : x ≠ 0) :
    ∃ f : X →ₗ[R] Y, f x ≠ 0 := by
  classical
  let K : Submodule R X := ⨅ f : X →ₗ[R] Y, LinearMap.ker f
  have hK : K = ⊥ := by
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le K with hk | ⟨S, hS, hs⟩
    · exact hk
    obtain ⟨f, hf⟩ := h S hs
    obtain ⟨F, hF⟩ := IsSemisimpleModule.extension_property S.subtype S.subtype_injective f
    exfalso
    apply hf
    ext s
    have hm : s.val ∈ K := hS s.property
    have he : F s.val = 0 := ((Submodule.mem_iInf _).mp hm F)
    change f s = 0
    exact (LinearMap.congr_fun hF s).symm.trans he
  by_contra hf
  push Not at hf
  apply hx
  have hm : x ∈ K := (Submodule.mem_iInf _).mpr (fun f => hf f)
  simpa only [hK, Submodule.mem_bot] using hm

end Saxl

namespace Saxl
open scoped MonoidAlgebra

/- The invariant-subspace and group-algebra subtype constructions agree. -/
def subrepModuleEquiv {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    S.toRepresentation.asModule ≃ₗ[ℂ[G]] S.asSubmodule where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (⟨(a • x).val, _⟩ : S.asSubmodule) = a • ⟨x.val, x.property⟩
    apply Subtype.ext
    change (a • x).val = ρ.asModuleEquiv (a • ρ.asModuleEquiv.symm x.val)
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp only [zero_smul, map_zero]; rfl
    | add a b ha hb =>
      simp only [add_smul, map_add]
      change (a • x).val + (b • x).val = _
      rw [ha, hb]
    | single g c =>
      rw [Representation.single_smul, Representation.single_smul]
      rfl

lemma subrep_irreducible_of_simple {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Submodule ℂ[G] ρ.asModule)
    [IsSimpleModule ℂ[G] S] :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' S).toRepresentation := by
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  let e : (Subrepresentation.ofSubmodule' S).toRepresentation.asModule ≃ₗ[ℂ[G]] S :=
    subrepModuleEquiv (Subrepresentation.ofSubmodule' S)
  exact IsSimpleModule.congr e

end Saxl

namespace Saxl
open scoped MonoidAlgebra

theorem intertwining_separates_of_simple_support {G : Type uG} {X : Type uX} {Y : Type uY}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (h : ∀ S : Subrepresentation ρ, Representation.IsIrreducible S.toRepresentation →
      ∃ f : Representation.IntertwiningMap S.toRepresentation σ, f ≠ 0)
    (x : X) (hx : x ≠ 0) :
    ∃ f : Representation.IntertwiningMap ρ σ, f x ≠ 0 := by
  classical
  have hs (S : Submodule ℂ[G] ρ.asModule) (hS : IsSimpleModule ℂ[G] S) :
      ∃ f : S →ₗ[ℂ[G]] σ.asModule, f ≠ 0 := by
    let P := Subrepresentation.ofSubmodule' S
    let := hS
    obtain ⟨f, hf⟩ := h P (subrep_irreducible_of_simple S)
    let F := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
    let E : P.toRepresentation.asModule ≃ₗ[ℂ[G]] S := subrepModuleEquiv P
    refine ⟨F.comp E.symm.toLinearMap, ?_⟩
    intro hz
    apply hf
    apply (Representation.IntertwiningMap.equivLinearMapAsModule _ _).injective
    ext v
    have he := LinearMap.congr_fun hz (E v)
    change F v = 0
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      E.symm_apply_apply, LinearMap.zero_apply] using he
  obtain ⟨f, hf⟩ := hom_separates_of_simple_support hs (ρ.asModuleEquiv.symm x)
    (fun he => hx (ρ.asModuleEquiv.symm.injective (he.trans (map_zero _).symm)))
  exact ⟨(Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm f, hf⟩

end Saxl

namespace Saxl
open scoped MonoidAlgebra

end Saxl

namespace Saxl

def subrepInclusion {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    Representation.IntertwiningMap S.toRepresentation ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

/- All constituents needed from a d-letter permutation module are detected
by a module containing each Specht type of height at most d. -/
theorem word_support_separates {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ d →
      ∃ f : Representation.IntertwiningMap (spechtRep t) σ, f ≠ 0)
    (x : WordSpace n d) (hx : x ≠ 0) :
    ∃ f : Representation.IntertwiningMap (wordRep n d) σ, f x ≠ 0 := by
  apply intertwining_separates_of_simple_support (wordRep n d) σ ?_ x hx
  intro S hS
  let := hS
  obtain ⟨p, ⟨e⟩⟩ := irreducible_equiv_specht S.toRepresentation
  let t := partitionTableau p
  let i : Representation.IntertwiningMap (spechtRep t) (wordRep n d) :=
    (subrepInclusion S).comp e.symm.toIntertwiningMap
  have hi : i ≠ 0 := by
    intro he
    have hz := congrArg (fun F : Representation.IntertwiningMap (spechtRep t) (wordRep n d) =>
      F ⟨polytabloid t, mem_cyclic _ _⟩) he
    have h0 : e.symm ⟨polytabloid t, mem_cyclic _ _⟩ = 0 := Subtype.ext hz
    have h1 := e.symm.injective (h0.trans (map_zero _).symm)
    exact polytabloid_ne_zero t (congrArg Subtype.val h1)
  obtain ⟨f, hf⟩ := h _ t (specht_rows_of_hom t i hi)
  refine ⟨f.comp e.toIntertwiningMap, ?_⟩
  intro he
  apply hf
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  exact congrArg (fun F : Representation.IntertwiningMap S.toRepresentation σ => F z) he

end Saxl

end

end OAI
