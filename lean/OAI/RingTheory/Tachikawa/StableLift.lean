import OAI.RingTheory.Tachikawa.FiniteCoinduction

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts HasDerivedCategory.standard
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma ordinary_inAdd_factorization_pf_zero
    {V : ModuleCat (Enveloping.Alg k (B q) (B q))}
    (hV : InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q)) V)
    (a : Enveloping.regular (k := k) (R := B q) ⟶ V)
    (b : V ⟶ Enveloping.dualRegularObj (k := k) (R := B q)) :
    Enveloping.dualRegularUnderlying ((a ≫ b) (Enveloping.regularUnderlyingEquiv.symm 1)) (pf q) = 0 := by
  classical
  obtain ⟨n,⟨r⟩⟩ := hV
  let W := Enveloping.ordinaryOuterObj (k := k) (R := B q)
  have he : ∑ i : Fin n, (a ≫ r.i ≫ biproduct.π (fun _ : Fin n => W) i) ≫
      (biproduct.ι (fun _ : Fin n => W) i ≫ r.r ≫ b) = a ≫ b := by
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum,← Preadditive.comp_sum]
    conv_lhs => arg 2; arg 2; simp only [← Category.assoc]
    rw [← Preadditive.sum_comp,← Preadditive.sum_comp,biproduct.total]
    dsimp only [W]
    simp only [Category.id_comp,← Category.assoc]
    rw [Category.assoc a,r.retract,Category.comp_id]
  rw [← he]
  change Enveloping.dualRegularUnderlying ((∑ i : Fin n,
    (a ≫ r.i ≫ biproduct.π (fun _ : Fin n => W) i) ≫
      (biproduct.ι (fun _ : Fin n => W) i ≫ r.r ≫ b)).hom
        (Enveloping.regularUnderlyingEquiv.symm 1)) (pf q) = 0
  simp only [ModuleCat.hom_sum,LinearMap.sum_apply,map_sum]
  exact Finset.sum_eq_zero (fun i _ => ordinary_morphism_factorization_pf_zero q _ _)

lemma characterBimoduleMap_not_inAdd_factor
    {V : ModuleCat (Enveloping.Alg k (B q) (B q))}
    (hV : InAdd (Enveloping.ordinaryOuterObj (k := k) (R := B q)) V)
    (a : Enveloping.regular (k := k) (R := B q) ⟶ V)
    (b : V ⟶ Enveloping.dualRegularObj (k := k) (R := B q)) :
    a ≫ b ≠ characterBimoduleMap q := by
  intro h
  have hz := ordinary_inAdd_factorization_pf_zero q hV a b
  rw [h,characterBimoduleMap_apply,characterMapB_one_pf] at hz
  exact one_ne_zero hz

theorem characterBimoduleMap_not_derived_perfect_factor (hq : q ≠ 0)
    (P : CochainComplex (ModuleCat (Enveloping.Alg k (B q) (B q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (B q) (B q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (B q) (B q)) (P.X i))
    (l u : ℤ) (hbound : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (α : DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (Enveloping.regular (k := k) (R := B q))) ⟶ DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (Enveloping.dualRegularObj (k := k) (R := B q)))) :
    α ≫ β ≠ DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map (characterBimoduleMap q)) := by
  intro h
  obtain ⟨V,a,b,hV,hab⟩ := Construction.b_ordinary_factorization q hq P hfin hproj l u hbound
    (characterBimoduleMap q) α β h
  exact characterBimoduleMap_not_inAdd_factor q hV a b hab

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

def inducedSocleMap : Enveloping.inducedRegularCochain (inclusionB q) ⟶
    (CochainComplex.singleFunctor _ 0).obj (U q H hH) :=
  Enveloping.inducedRegularAugmentation (inclusionB q) ≫
    (CochainComplex.singleFunctor _ 0).map
      (HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)) ≫
        socleBimoduleMap q H hH)

omit [CharP k 2] in

lemma inducedSocleMap_square :
    Enveloping.regularUnit (inclusionB q) ≫
    ((bimoduleRestriction q).mapHomologicalComplex (.up ℤ)).map (inducedSocleMap q H hH) ≫
      Enveloping.restrictedSingleMap (inclusionB q) (rhoBimodule q H hH) =
    (Enveloping.regularResolution (k := k) (R := B q)).π' ≫
      (CochainComplex.singleFunctor _ 0).map (characterBimoduleMap q) := by
  have h := Enveloping.regularUnit_square (inclusionB q)
    (HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)) ≫
      socleBimoduleMap q H hH) (rhoBimodule q H hH)
  rw [restricted_socle_character] at h
  exact h

theorem inducedSocleMap_not_derived_perfect_factor (hq : q ≠ 0)
    (P : CochainComplex (ModuleCat.{0} (Enveloping.Alg k (E q) (E q))) ℤ)
    (hfin : ∀ i, Module.Finite (Enveloping.Alg k (E q) (E q)) (P.X i))
    (hproj : ∀ i, Module.Projective (Enveloping.Alg k (E q) (E q)) (P.X i))
    (l u : ℤ) (hb : ∀ i, i < l ∨ u < i → IsZero (P.X i))
    (α : DerivedCategory.Q.obj (Enveloping.inducedRegularCochain (inclusionB q)) ⟶
      DerivedCategory.Q.obj P)
    (β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor _ 0).obj (U q H hH))) :
    α ≫ β ≠ DerivedCategory.Q.map (inducedSocleMap q H hH) := by
  intro h
  obtain ⟨P',f,hf,hp',hfin',hb'⟩ := restricted_perfect_replacement q hq P hfin hproj l u hb
  let := hf
  let F := bimoduleRestriction q
  let Qb := DerivedCategory.Q (C := ModuleCat.{0} (Enveloping.Alg k (B q) (B q)))
  let π := (Enveloping.regularResolution (k := k) (R := B q)).π'
  let η := Enveloping.regularUnit (inclusionB q)
  let ρ := Enveloping.restrictedSingleMap (inclusionB q) (rhoBimodule q H hH)
  let a := inv (Qb.map π) ≫ Qb.map η ≫ exactDerivedHom F α ≫ inv (Qb.map f)
  let b := Qb.map f ≫ exactDerivedHom F β ≫ Qb.map ρ
  apply characterBimoduleMap_not_derived_perfect_factor q hq P' hfin' hp' (l-8) u hb' a b
  calc
    a ≫ b = inv (Qb.map π) ≫ Qb.map η ≫ exactDerivedHom F (α ≫ β) ≫ Qb.map ρ := by
      simp only [a,b,Category.assoc,IsIso.inv_hom_id_assoc,exactDerivedHom_comp]
    _ = inv (Qb.map π) ≫ Qb.map η ≫
        Qb.map ((F.mapHomologicalComplex (.up ℤ)).map (inducedSocleMap q H hH)) ≫ Qb.map ρ := by
      rw [h,exactDerivedHom_map]
    _ = inv (Qb.map π) ≫ Qb.map (π ≫
        (CochainComplex.singleFunctor _ 0).map (characterBimoduleMap q)) := by
      rw [← Functor.map_comp,← Functor.map_comp]
      congr 2
      exact inducedSocleMap_square q H hH
    _ = Qb.map ((CochainComplex.singleFunctor _ 0).map (characterBimoduleMap q)) := by
      simp only [Functor.map_comp,IsIso.inv_hom_id_assoc]

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

def finiteU : FiniteModule k (Enveloping.Alg k (E q) (E q)) where
  obj := U q H hH
  finite := by
    let : IsScalarTower k (Enveloping.Alg k (E q) (E q)) (U q H hH) :=
      IsScalarTower.restrictScalars k (Enveloping.Alg k (E q) (E q)) (U q H hH)
    exact Module.Finite.of_restrictScalars_finite k _ _

lemma inducedSocleMap_high_lift_nonzero (hq : q ≠ 0)
    (f : Enveloping.inducedRegularCochain (inclusionB q) ⟶
        (finiteU q H hH).projectiveResolution.cochainComplex)
    (hf : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU q H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedSocleMap q H hH)) :
    ∀ n : ℕ, 5 ≤ n → CokerAt.map (reflectCochainMap f) n ∉ projectiveFactors (k := k) := by
  let : Module.Injective (Enveloping.Alg k (E q) (E q)) (Enveloping.Alg k (E q) (E q)) :=
    (Enveloping.envelopingForm (formE q) (formE q)).injective
  exact stably_nonzero_high_lift (Enveloping.inducedRegularCochain (inclusionB q))
    (fun _ => by infer_instance) (finiteU q H hH) (inducedSocleMap q H hH) 5 (by omega)
    (fun n hn => inducedRegularCochain_reflect_exact q hq n (by omega))
    (inducedSocleMap_not_derived_perfect_factor q H hH hq) f hf

theorem inducedSocleMap_stably_nonzero_lift (hq : q ≠ 0) :
    ∃ f : Enveloping.inducedRegularCochain (inclusionB q) ⟶
        (finiteU q H hH).projectiveResolution.cochainComplex,
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (finiteU q H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedSocleMap q H hH) ∧
      ∀ n : ℕ, 5 ≤ n → CokerAt.map (reflectCochainMap f) n ∉ projectiveFactors (k := k) := by
  let : Module.Injective (Enveloping.Alg k (E q) (E q)) (Enveloping.Alg k (E q) (E q)) :=
    (Enveloping.envelopingForm (formE q) (formE q)).injective
  apply exists_stably_nonzero_high_lift (Enveloping.inducedRegularCochain (inclusionB q))
    (fun _ => by infer_instance) (finiteU q H hH) (inducedSocleMap q H hH) 5 (by omega)
  · intro n hn
    exact inducedRegularCochain_reflect_exact q hq n (by omega)
  · exact inducedSocleMap_not_derived_perfect_factor q H hH hq

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard

lemma finiteResolutionLift {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
    (P : CochainComplex (ModuleCat.{0} R) ℤ) [P.IsKProjective] (M : FiniteModule k R)
    (v : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M.obj)) :
    ∃ f : P ⟶ M.projectiveResolution.cochainComplex,
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map M.projectiveResolution.π' = v := by
  obtain ⟨f,hf⟩ := kProjective_chain_representative P M.projectiveResolution.cochainComplex
    (v ≫ inv (DerivedCategory.Q.map M.projectiveResolution.π'))
  refine ⟨f,?_⟩
  rw [hf]; simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]

lemma lift_composite_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q T S U : C} (a : P ⟶ Q) (b : Q ⟶ T) (p : Q ⟶ S) (r : T ⟶ U)
    (v : P ⟶ S) (w : S ⟶ U)
    (ha : F.map a ≫ F.map p = F.map v)
    (hb : F.map b ≫ F.map r = F.map p ≫ F.map w) :
    F.map (a ≫ b) ≫ F.map r = F.map (v ≫ w) := by
  rw [Functor.map_comp,Category.assoc,hb,← Category.assoc,ha,← Functor.map_comp]

namespace HomBimodule
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R) (Z : ModuleCat S)
def underlyingLinearEquiv : obj (k := k) X Z ≃ₗ[k] (X →ₗ[k] Z) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c f := by ext x; exact k_smul_apply X Z c f x
instance [FiniteDimensional k X] [FiniteDimensional k Z] : FiniteDimensional k (obj (k := k) X Z) :=
  Module.Finite.equiv (underlyingLinearEquiv X Z).symm
end HomBimodule

namespace Construction
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

def xObj : ModuleCat (E q) := ModuleCat.of (E q) (X q)

def xUnderlyingLinear : xObj q ≃ₗ[k] k where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change characterE q (algebraMap k (E q) c) * (show k from x) = c * (show k from x)
    rw [AlgHom.commutes]; rfl

instance : FiniteDimensional k (xObj q) :=
  Module.Finite.equiv (xUnderlyingLinear q).symm

def finiteS : FiniteModule k (Enveloping.Alg k (E q) (E q)) where
  obj := S q
  finite := by
    let : Module.Finite k (S q) := Module.Finite.equiv
      (HomBimodule.underlyingLinearEquiv (k := k) (xObj q) (xObj q)).symm
    let : IsScalarTower k (Enveloping.Alg k (E q) (E q)) (S q) :=
      IsScalarTower.restrictScalars k (Enveloping.Alg k (E q) (E q)) (S q)
    exact Module.Finite.of_restrictScalars_finite k _ _

def inducedRepresentationMap : Enveloping.inducedRegularCochain (inclusionB q) ⟶
    (CochainComplex.singleFunctor _ 0).obj (S q) :=
  Enveloping.inducedRegularAugmentation (inclusionB q) ≫
    (CochainComplex.singleFunctor _ 0).map
      (HomBimodule.representation (k := k) (ModuleCat.of (E q) (X q)))

omit [CharP k 2] in
lemma inducedRepresentation_socle : inducedRepresentationMap q ≫
    (CochainComplex.singleFunctor _ 0).map (socleBimoduleMap q H hH) = inducedSocleMap q H hH := by
  simp only [inducedRepresentationMap,inducedSocleMap,Functor.map_comp,Category.assoc]

theorem separated_stably_nonzero_lifts (hq : q ≠ 0) :
    ∃ (a : Enveloping.inducedRegularCochain (inclusionB q) ⟶
        (finiteS q).projectiveResolution.cochainComplex)
      (b : (finiteS q).projectiveResolution.cochainComplex ⟶
        (finiteU q H hH).projectiveResolution.cochainComplex),
      DerivedCategory.Q.map a ≫ DerivedCategory.Q.map (finiteS q).projectiveResolution.π' =
        DerivedCategory.Q.map (inducedRepresentationMap q) ∧
      DerivedCategory.Q.map b ≫ DerivedCategory.Q.map (finiteU q H hH).projectiveResolution.π' =
        DerivedCategory.Q.map (finiteS q).projectiveResolution.π' ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map (socleBimoduleMap q H hH)) ∧
      ∀ n : ℕ, 5 ≤ n →
        (CokerAt.map (reflectCochainMap b) n).comp (CokerAt.map (reflectCochainMap a) n)
          ∉ projectiveFactors (k := k) := by
  let : Module.Injective (Enveloping.Alg k (E q) (E q)) (Enveloping.Alg k (E q) (E q)) :=
    (Enveloping.envelopingForm (formE q) (formE q)).injective
  obtain ⟨a,ha⟩ := finiteResolutionLift (Enveloping.inducedRegularCochain (inclusionB q))
    (finiteS q) (DerivedCategory.Q.map (inducedRepresentationMap q))
  obtain ⟨b,hb⟩ := finiteResolutionLift (finiteS q).projectiveResolution.cochainComplex
    (finiteU q H hH) (DerivedCategory.Q.map (finiteS q).projectiveResolution.π' ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map (socleBimoduleMap q H hH)))
  refine ⟨a,b,ha,hb,?_⟩
  have hc : DerivedCategory.Q.map (a ≫ b) ≫
      DerivedCategory.Q.map (finiteU q H hH).projectiveResolution.π' =
      DerivedCategory.Q.map (inducedSocleMap q H hH) := by
    exact (lift_composite_eq DerivedCategory.Q a b _ _ _ _ ha hb).trans
      (congrArg DerivedCategory.Q.map (inducedRepresentation_socle q H hH))
  have hn := inducedSocleMap_high_lift_nonzero q H hH hq (a ≫ b) hc
  intro n h
  have he : reflectCochainMap (a ≫ b) = reflectCochainMap a ≫ reflectCochainMap b := rfl
  simpa only [he,CokerAt.map_comp] using hn n h
end Construction
end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable {M N L : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module R M] [Module R N] [Module R L] [Module k N] [Module k L]
  [IsScalarTower k R N] [IsScalarTower k R L]

namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R))
variable {n : ℕ} (ε : (Fin n → R) →ₗ[R] M)

lemma syzygyPair_natural (b : L →ₗ[R] LinearMap.ker ε) (φ : N →ₗ[R] L)
    (f : M →ₗ[R] N) :
    t.syzygyPair ε (b.comp φ) f = t.syzygyPair ε b (φ.comp f) := by
  simp only [syzygyPair_apply]
  rw [← LinearMap.comp_assoc, t.freeHomDual_natural, LinearMap.comp_assoc]

include t in

theorem exists_nonzero_postcomposition
    (hε : Function.Surjective ε) {m p : ℕ}
    (i : M →ₗ[R] (Fin m → R)) (hi : Function.Injective i)
    (d : (Fin p → R) →ₗ[R] LinearMap.ker ε) (hd : Function.Surjective d)
    (b : L →ₗ[R] LinearMap.ker ε) (φ : N →ₗ[R] L)
    (hb : b.comp φ ∉ projectiveFactors (k := k)) :
    ∃ f : M →ₗ[R] N, φ.comp f ∉ projectiveFactors (k := k) := by
  have hp : t.syzygyPair ε (b.comp φ) ≠ 0 :=
    mt (t.syzygyPair_eq_zero_iff ε hε d hd (b.comp φ)).mp hb
  have hex : ∃ f, t.syzygyPair ε (b.comp φ) f ≠ 0 := by
    by_contra! hn
    exact hp (LinearMap.ext hn)
  obtain ⟨f, hf⟩ := hex
  refine ⟨f, fun hh => hf ?_⟩
  rw [syzygyPair_natural]
  exact t.syzygyPair_vanish_left ε i hi b (φ.comp f) hh

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B]
  [Module R C] [Module R D] [Module k B] [Module k D]
  [IsScalarTower k R B] [IsScalarTower k R D]

lemma projectiveFactors_conjugate_iff (f : A →ₗ[R] B) (e : C ≃ₗ[R] A) (v : B ≃ₗ[R] D) :
    (v.toLinearMap.comp f).comp e.toLinearMap ∈ projectiveFactors (k := k) ↔
      f ∈ projectiveFactors (k := k) := by
  constructor
  · intro h
    have hh := projectiveFactors_postcomp (projectiveFactors_precomp h e.symm.toLinearMap)
      v.symm.toLinearMap
    have he : v.symm.toLinearMap.comp (((v.toLinearMap.comp f).comp e.toLinearMap).comp e.symm.toLinearMap) = f := by
      ext x; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
    rw [he] at hh
    exact hh
  · intro h
    exact projectiveFactors_precomp (projectiveFactors_postcomp h v.toLinearMap) e.toLinearMap

namespace SymmetrizingForm
variable [FiniteDimensional k R] (t : SymmetrizingForm (k := k) (R := R))

include t in

theorem exists_syzygy_postcomposition (U M L : FiniteModule k R) (n : ℕ)
    (b : L.obj →ₗ[R] (U.positive (n+1)).obj) (phi : M.obj →ₗ[R] L.obj)
    (h : b.comp phi ∉ projectiveFactors (k := k)) :
    ∃ beta : (U.positive n).obj →ₗ[R] M.obj, phi.comp beta ∉ projectiveFactors (k := k) := by
  exact t.exists_nonzero_postcomposition (U.positive n).cover.map
    (U.positive n).cover.surjective ((U.positive n).embed t) ((U.positive n).embed_injective t)
    (U.positive (n+1)).cover.map (U.positive (n+1)).cover.surjective b phi h
end SymmetrizingForm
end Tachikawa



namespace Tachikawa.FiniteModule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
variable (t : SymmetrizingForm (k := k) (R := R))

def syzygyInclusion (M : FiniteModule k R) : M.syzygy.obj →ₗ[R] (Fin M.cover.rank → R) :=
  (LinearMap.ker M.cover.map).subtype
lemma syzygyInclusion_injective (M : FiniteModule k R) : Function.Injective M.syzygyInclusion :=
  Subtype.val_injective
lemma syzygyInclusion_exact (M : FiniteModule k R) : Function.Exact M.syzygyInclusion M.cover.map := by
  intro x
  exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩

def cosyzygyProjection (M : FiniteModule k R) :
    (Fin (Module.finrank k M) → R) →ₗ[R] (M.cosyzygy t).obj :=
  (LinearMap.range (M.embed t)).mkQ
lemma cosyzygyProjection_surjective (M : FiniteModule k R) : Function.Surjective (M.cosyzygyProjection t) :=
  Submodule.mkQ_surjective _
lemma cosyzygyProjection_exact (M : FiniteModule k R) :
    Function.Exact (M.embed t) (M.cosyzygyProjection t) := by
  intro x
  exact Submodule.Quotient.mk_eq_zero _

lemma negative_succ_left (M : FiniteModule k R) (n : ℕ) :
    (M.cosyzygy t).negative t n = M.negative t (n+1) := by
  induction n with
  | zero => rfl
  | succ n h => exact congrArg (fun L : FiniteModule k R => L.cosyzygy t) h

theorem descend_nonzero_composition (M U S : FiniteModule k R) (n : ℕ)
    (beta : (U.positive (n+1)).obj →ₗ[R] M.obj)
    (phi : M.obj →ₗ[R] (S.positive (n+2)).obj)
    (hn : phi.comp beta ∉ projectiveFactors (k := k)) :
    ∃ (g : (U.positive n).obj →ₗ[R] (M.cosyzygy t).obj)
      (psi : (M.cosyzygy t).obj →ₗ[R] (S.positive (n+1)).obj),
      psi.comp g ∉ projectiveFactors (k := k) := by
  let : Module.Injective R R := t.injective
  let PU := ModuleCat.of R (Fin (U.positive n).cover.rank → R)
  let PM := ModuleCat.of R (Fin (Module.finrank k M) → R)
  let PS := ModuleCat.of R (Fin (S.positive (n+1)).cover.rank → R)
  obtain ⟨h,g,hu,hl⟩ := exists_exact_square_down (P := PU) (Q := PM)
    (U.positive n).syzygyInclusion (U.positive n).cover.map
    (U.positive n).syzygyInclusion_injective (U.positive n).syzygyInclusion_exact
    (U.positive n).cover.surjective (M.embed t) (M.cosyzygyProjection t)
    (M.cosyzygyProjection_exact t) beta
  obtain ⟨h',psi,hu',hl'⟩ := exists_exact_square_down (P := PM) (Q := PS)
    (M.embed t) (M.cosyzygyProjection t) (M.embed_injective t)
    (M.cosyzygyProjection_exact t) (M.cosyzygyProjection_surjective t)
    (S.positive (n+1)).syzygyInclusion (S.positive (n+1)).cover.map
    (S.positive (n+1)).syzygyInclusion_exact phi
  refine ⟨g,psi,?_⟩
  apply mt (exact_square_factors_iff (P := PU) (Q := PS)
    (U.positive n).syzygyInclusion (U.positive n).cover.map
    (U.positive n).syzygyInclusion_injective (U.positive n).syzygyInclusion_exact
    (U.positive n).cover.surjective
    (S.positive (n+1)).syzygyInclusion (S.positive (n+1)).cover.map
    (S.positive (n+1)).syzygyInclusion_injective (S.positive (n+1)).syzygyInclusion_exact
    (S.positive (n+1)).cover.surjective
    (phi.comp beta) (h'.comp h) (psi.comp g) ?_ ?_).mpr hn
  · erw [LinearMap.comp_assoc,hu,← LinearMap.comp_assoc,hu',LinearMap.comp_assoc]
  · rw [← LinearMap.comp_assoc,hl',LinearMap.comp_assoc,hl,← LinearMap.comp_assoc]

theorem descend_nonzero_composition_iterated (U S : FiniteModule k R) (n : ℕ)
    (M : FiniteModule k R) (beta : (U.positive n).obj →ₗ[R] M.obj)
    (phi : M.obj →ₗ[R] (S.positive (n+1)).obj)
    (hn : phi.comp beta ∉ projectiveFactors (k := k)) :
    ∃ (g : U.obj →ₗ[R] (M.negative t n).obj)
      (psi : (M.negative t n).obj →ₗ[R] (S.positive 1).obj),
      psi.comp g ∉ projectiveFactors (k := k) := by
  induction n generalizing M with
  | zero => exact ⟨beta,phi,hn⟩
  | succ n ih =>
    obtain ⟨g,psi,hg⟩ := descend_nonzero_composition t M U S n beta phi hn
    rw [← negative_succ_left t M n]
    exact ih (M.cosyzygy t) g psi hg
end Tachikawa.FiniteModule



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct
namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
def inducedFiveCokerEquiv (f : R →ₐ[k] S) :
    CokerAt (reflectCochain (inducedRegularCochain f)) 5 ≃ₗ[Alg k S S] (inducedCokerFive f).obj :=
  resolutionReflectCokerEquiv (regularResolution (k := k) (R := R))
    (AlgebraInduction.functor (envelopingMap f)) 5
end Enveloping

namespace Construction
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

theorem exists_Y_lift_with_nonzero_composition (hq : q ≠ 0) :
    ∃ (g : (finiteU q H hH).obj ⟶ (Y q).obj)
      (psi : (Y q).obj ⟶ ((finiteS q).positive 1).obj),
      (g ≫ psi).hom ∉ projectiveFactors (k := k) := by
  let N := Enveloping.inducedCokerFive (inclusionB q)
  let Us := finiteU q H hH
  let Ss := finiteS q
  let t := Enveloping.envelopingForm (formE q) (formE q)
  obtain ⟨a,b,_ha,_hb,hn⟩ := separated_stably_nonzero_lifts q H hH hq
  let aa := CokerAt.map (reflectCochainMap a) 5
  let bb := CokerAt.map (reflectCochainMap b) 5
  let eN := Enveloping.inducedFiveCokerEquiv (inclusionB q)
  let eS := Ss.reflectCokerPositiveEquiv 5
  let eU := Us.reflectCokerPositiveEquiv 5
  let phi :=
    (eS.toLinearMap.comp aa).comp eN.symm.toLinearMap
  let b' :=
    (eU.toLinearMap.comp bb).comp eS.symm.toLinearMap
  have hbphi : b'.comp phi ∉ projectiveFactors (k := k) := by
    have he : b'.comp phi = (eU.toLinearMap.comp (bb.comp aa)).comp eN.symm.toLinearMap := by
      ext x
      change eU (bb (eS.symm (eS (aa (eN.symm x))))) = eU (bb (aa (eN.symm x)))
      rw [eS.symm_apply_apply]
    rw [he, projectiveFactors_conjugate_iff]
    exact hn 5 (by omega)
  obtain ⟨beta,hbeta⟩ := t.exists_syzygy_postcomposition Us N (Ss.positive 5) 4 b' phi hbphi
  obtain ⟨g,psi,hg⟩ := FiniteModule.descend_nonzero_composition_iterated t Us Ss 4 N beta phi hbeta
  exact ⟨ModuleCat.ofHom (X := (finiteU q H hH).obj) (Y := (Y q).obj) g,
    ModuleCat.ofHom (X := (Y q).obj) (Y := ((finiteS q).positive 1).obj) psi,hg⟩
end Construction
end Tachikawa



namespace Tachikawa.BalancedTensor
variable {k R S M M' N : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k S M'] [IsScalarTower k Rᵐᵒᵖ M'] [SMulCommClass S Rᵐᵒᵖ M']
  [AddCommGroup N] [Module k N] [Module R N]

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M'] in
lemma restrictEquiv_mapLeft (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (x : T (k := k) (R := R) (S := S) (M := M) (N := N)) :
    restrictEquiv (mapLeft (k := k) (N := N) f hf x) =
      mapLeft (k := k) (S := k) (N := N) (f.restrictScalars k) hf (restrictEquiv x) := by
  induction x using induction_on with
  | h0 => simp
  | ht m n => rfl
  | ha x y hx hy => simp only [map_add, hx, hy]

lemma mapLeft_injective_of_right_split (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (r : M' →ₗ[Rᵐᵒᵖ] M) (hr : ∀ m, r (f m) = m) :
    Function.Injective (mapLeft (k := k) (N := N) f hf) := by
  let g := mapLeft (k := k) (S := k) (N := N) (r.restrictScalars k) r.map_smul
  have hg : ∀ x : T (k := k) (R := R) (S := k) (M := M) (N := N),
      g (mapLeft (k := k) (S := k) (N := N) (f.restrictScalars k) hf x) = x := by
    intro x
    induction x using induction_on with
    | h0 => simp only [map_zero]
    | ht m n => exact congrArg (fun m => mk (k := k) (R := R) (S := k) m n) (hr m)
    | ha x y hx hy => simp only [map_add, hx, hy]
  intro x y h
  apply (restrictEquiv (k := k) (R := R) (S := S)).injective
  have h' := congrArg (restrictEquiv (k := k) (R := R) (S := S)) h
  rw [restrictEquiv_mapLeft, restrictEquiv_mapLeft] at h'
  exact (hg _).symm.trans ((congrArg g h').trans (hg _))

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R S M P Q N : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup P] [Module k P] [Module S P] [Module Rᵐᵒᵖ P]
  [IsScalarTower k S P] [IsScalarTower k Rᵐᵒᵖ P] [SMulCommClass S Rᵐᵒᵖ P]
  [AddCommGroup Q] [Module k Q] [Module S Q] [Module Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [AddCommGroup N] [Module k N] [Module R N]

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ P]
  [SMulCommClass S Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ P] in
lemma mapLeft_surjective (f : M →ₗ[S] P)
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) (hs : Function.Surjective f) :
    Function.Surjective (mapLeft (k := k) (N := N) f hf) := by
  intro x
  induction x using induction_on with
  | h0 => exact ⟨0,map_zero _⟩
  | ht m n =>
    obtain ⟨m',rfl⟩ := hs m
    exact ⟨mk m' n,rfl⟩
  | ha x y hx hy =>
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact ⟨a+b,map_add _ _ _⟩

lemma mapLeft_exact_of_right_splitting (f : M →ₗ[S] P) (g : P →ₗ[S] Q)
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (hg : ∀ (r : Rᵐᵒᵖ) m, g (r • m) = r • g m)
    (r : P →ₗ[Rᵐᵒᵖ] M) (s : Q →ₗ[Rᵐᵒᵖ] P)
    (hid : ∀ p, f (r p) + s (g p) = p) (hz : ∀ m, g (f m) = 0) :
    Function.Exact (mapLeft (k := k) (N := N) f hf) (mapLeft (k := k) (N := N) g hg) := by
  let F := mapLeft (k := k) (S := k) (N := N) (f.restrictScalars k) hf
  let G := mapLeft (k := k) (S := k) (N := N) (g.restrictScalars k) hg
  let Rr := mapLeft (k := k) (S := k) (N := N) (r.restrictScalars k) r.map_smul
  let Ss := mapLeft (k := k) (S := k) (N := N) (s.restrictScalars k) s.map_smul
  have hid' (x : T (k := k) (R := R) (S := k) (M := P) (N := N)) :
      F (Rr x) + Ss (G x) = x := by
    induction x using induction_on with
    | h0 => simp only [map_zero,add_zero]
    | ht p n =>
      change mk (f (r p)) n + mk (s (g p)) n = mk p n
      rw [← LinearMap.add_apply,← map_add,hid]
    | ha x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm,hx,hy]
  have hz' (x : T (k := k) (R := R) (S := S) (M := M) (N := N)) :
      mapLeft (k := k) (N := N) g hg (mapLeft (k := k) (N := N) f hf x) = 0 := by
    induction x using induction_on with
    | h0 => simp only [map_zero]
    | ht m n => change mk (g (f m)) n = 0; rw [hz,map_zero,LinearMap.zero_apply]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  intro x
  constructor
  · intro hx
    let x' := restrictEquiv (k := k) (R := R) (S := S) x
    have hG : G x' = 0 := by
      simpa only [restrictEquiv_mapLeft,map_zero] using
        congrArg (restrictEquiv (k := k) (R := R) (S := S)) hx
    refine ⟨(restrictEquiv (k := k) (R := R) (S := S)).symm (Rr x'),?_⟩
    apply (restrictEquiv (k := k) (R := R) (S := S)).injective
    rw [restrictEquiv_mapLeft,LinearEquiv.apply_symm_apply]
    have h := hid' x'
    rw [hG,map_zero,add_zero] at h
    exact h
  · rintro ⟨y,rfl⟩
    exact hz' y
end Tachikawa.BalancedTensor



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R) {M N : ModuleCat.{0} (Alg k S R)}

instance eval_finite [FiniteDimensional k M] [FiniteDimensional k X] :
    Module.Finite S (evalObj X M) :=
  Module.Finite.of_restrictScalars_finite k S (evalType X M)

lemma evalMap_injective [FiniteDimensional k R] [FiniteDimensional k M]
    [Module.Projective Rᵐᵒᵖ (Obj M)] (t : SymmetrizingForm (k := k) (R := R))
    (f : M ⟶ N) (hf : Function.Injective f) : Function.Injective (evalMap X f) := by
  let : Module.Injective Rᵐᵒᵖ Rᵐᵒᵖ := t.op.injective
  let : Module.Finite Rᵐᵒᵖ (Obj M) := Module.Finite.of_restrictScalars_finite k Rᵐᵒᵖ (Obj M)
  let : Module.Injective Rᵐᵒᵖ (Obj M) := injective_of_finite_projective
  obtain ⟨r,hr⟩ := Module.Injective.extension_property Rᵐᵒᵖ (Obj M) (Obj M) (Obj N)
    (rightMap f) hf LinearMap.id
  exact BalancedTensor.mapLeft_injective_of_right_split (leftMap f) (rightMap f).map_smul r
    (fun m => LinearMap.congr_fun hr m)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R) {M P Q : ModuleCat.{0} (Alg k S R)}

lemma evalMap_surjective (g : P ⟶ Q) (hg : Function.Surjective g) :
    Function.Surjective (evalMap X g) :=
  BalancedTensor.mapLeft_surjective (leftMap g) (rightMap g).map_smul hg

lemma evalMap_exact [FiniteDimensional k R] [FiniteDimensional k M]
    [Module.Projective Rᵐᵒᵖ (Obj M)] (t : SymmetrizingForm (k := k) (R := R))
    (f : M ⟶ P) (g : P ⟶ Q) (hi : Function.Injective f)
    (he : Function.Exact f g) (hs : Function.Surjective g) :
    Function.Exact (evalMap X f) (evalMap X g) := by
  let : Module.Injective Rᵐᵒᵖ Rᵐᵒᵖ := t.op.injective
  let : Module.Finite Rᵐᵒᵖ (Obj M) := Module.Finite.of_restrictScalars_finite k Rᵐᵒᵖ (Obj M)
  let : Module.Injective Rᵐᵒᵖ (Obj M) := injective_of_finite_projective
  let H := linearShortExact (rightMap f) (rightMap g) he hi hs
  let : CategoryTheory.Injective (linearShortComplex (rightMap f) (rightMap g) he).X₁ :=
    Module.injective_object_of_injective_module Rᵐᵒᵖ (Obj M)
  let sp := H.splittingOfInjective
  apply BalancedTensor.mapLeft_exact_of_right_splitting (leftMap f) (leftMap g)
    (rightMap f).map_smul (rightMap g).map_smul sp.r.hom sp.s.hom
  · intro p
    exact congrArg (fun z : ModuleCat.of Rᵐᵒᵖ (Obj P) ⟶ ModuleCat.of Rᵐᵒᵖ (Obj P) => z p) sp.id
  · intro m
    exact (he _).mpr ⟨m,rfl⟩
end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))
  (X : ModuleCat.{0} R) [FiniteDimensional k X]
  {M N P Q M' N' : ModuleCat.{0} (Alg k S R)}
  [FiniteDimensional k M] [FiniteDimensional k N]
  [Module.Projective Rᵐᵒᵖ (Obj M)] [Module.Projective Rᵐᵒᵖ (Obj N)]
  [Module.Finite (Alg k S R) P] [Module.Projective (Alg k S R) P]
  [Module.Finite (Alg k S R) Q] [Module.Projective (Alg k S R) Q]

include t u in

lemma eval_square_factors_iff
    (i : M ⟶ P) (pi : P ⟶ M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N ⟶ Q) (delta : Q ⟶ N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (f : M ⟶ N) (h : P ⟶ Q) (g : M' ⟶ N')
    (hu : i ≫ h = f ≫ j) (hl : h ≫ delta = pi ≫ g) :
    (evalMap X f).hom ∈ projectiveFactors (k := k) ↔
      (evalMap X g).hom ∈ projectiveFactors (k := k) := by
  let : Module.Injective S S := u.injective
  let : FiniteDimensional k P := Module.Finite.trans (Alg k S R) P
  let : FiniteDimensional k Q := Module.Finite.trans (Alg k S R) Q
  apply exact_square_factors_iff (P := evalObj X P) (Q := evalObj X Q)
    (evalMap X i).hom (evalMap X pi).hom
    (evalMap_injective X t i hi) (evalMap_exact X t i pi hi hex hpi)
    (evalMap_surjective X pi hpi)
    (evalMap X j).hom (evalMap X delta).hom
    (evalMap_injective X t j hj) (evalMap_exact X t j delta hj hex' hdelta)
    (evalMap_surjective X delta hdelta)
    (evalMap X f).hom (evalMap X h).hom (evalMap X g).hom
  · have hmap := congrArg (evaluation X).map hu
    rw [Functor.map_comp,Functor.map_comp] at hmap
    ext x
    exact congrArg (fun a : (evaluation X).obj M ⟶ (evaluation X).obj Q => a x) hmap
  · have hmap := congrArg (evaluation X).map hl
    rw [Functor.map_comp,Functor.map_comp] at hmap
    ext x
    exact congrArg (fun a : (evaluation X).obj P ⟶ (evaluation X).obj N' => a x) hmap
end Tachikawa.Enveloping



namespace Tachikawa.BimoduleTensorHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (tR : SymmetrizingForm (k := k) (R := R))
  (tS : SymmetrizingForm (k := k) (R := S))
  {M : ModuleCat.{0} (Enveloping.Alg k S R)} {X : ModuleCat.{0} R} {Z : ModuleCat.{0} S}
  [FiniteDimensional k M] [FiniteDimensional k X]

omit tR tS [FiniteDimensional k M] in
lemma uncurry_factors {f : M ⟶ HomBimodule.obj (k := k) X Z}
    (hf : f.hom ∈ projectiveFactors (k := k)) :
    (uncurry f).hom ∈ projectiveFactors (k := k) := by
  obtain ⟨P, hPf, hPp, a, b, hab⟩ := hf
  let := hPf
  let := hPp
  let : FiniteDimensional k P := Module.Finite.trans (Enveloping.Alg k S R) P
  let a₀ : M ⟶ P := ModuleCat.ofHom a
  let b₀ : P ⟶ HomBimodule.obj (k := k) X Z := ModuleCat.ofHom (X := P) (Y := HomBimodule.obj (k := k) X Z) b
  have he : a₀ ≫ b₀ = f := ModuleCat.hom_ext hab
  refine ⟨Enveloping.evalObj X P, inferInstance, inferInstance,
    (Enveloping.evalMap X a₀).hom, (uncurry b₀).hom, ?_⟩
  exact ModuleCat.hom_ext_iff.mp ((uncurry_precompose a₀ b₀).symm.trans (congrArg uncurry he))

omit [FiniteDimensional k X] in
include tR tS in

lemma factors_of_uncurry [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M)]
    {f : M ⟶ HomBimodule.obj (k := k) X Z}
    (hf : (uncurry f).hom ∈ projectiveFactors (k := k)) :
    f.hom ∈ projectiveFactors (k := k) := by
  obtain ⟨P,hPf,hPp,a,b,hab⟩ := hf
  let := hPf
  let := hPp
  let : Module.Injective S S := tS.injective
  let : Module.Injective S P := injective_of_finite_projective
  let J := ModuleCat.of (Enveloping.Alg k S R)
    (Fin (Module.finrank k M) → Enveloping.Alg k S R)
  let i : M ⟶ J := ModuleCat.ofHom ((tS.tensor tR.op).freeEmbedding (M := M))
  have hi : Function.Injective i := (tS.tensor tR.op).freeEmbedding_injective
  have hei := Enveloping.evalMap_injective X tR i hi
  obtain ⟨a',ha'⟩ := Module.Injective.extension_property S P (Enveloping.evalObj X M)
    (Enveloping.evalObj X J) (Enveloping.evalMap X i).hom hei a
  let ag : Enveloping.evalObj X J ⟶ Z := ModuleCat.ofHom (b.comp a')
  let g : J ⟶ HomBimodule.obj (k := k) X Z := curry ag
  have hcomp : i ≫ g = f := by
    apply (equiv (k := k)).injective
    change uncurry (i ≫ g) = uncurry f
    rw [uncurry_precompose]
    change Enveloping.evalMap X i ≫ uncurry (curry ag) = _
    rw [uncurry_curry]
    apply ModuleCat.hom_ext
    change (b.comp a').comp (Enveloping.evalMap X i).hom = (uncurry f).hom
    rw [LinearMap.comp_assoc, ha', hab]
  exact ⟨J, inferInstance, inferInstance, i.hom, g.hom, ModuleCat.hom_ext_iff.mp hcomp⟩

include tR tS in

lemma factors_iff_uncurry [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M)]
    (f : M ⟶ HomBimodule.obj (k := k) X Z) :
    f.hom ∈ projectiveFactors (k := k) ↔ (uncurry f).hom ∈ projectiveFactors (k := k) :=
  ⟨uncurry_factors, factors_of_uncurry tR tS⟩

def linearEquiv : (M →ₗ[Enveloping.Alg k S R] HomBimodule.obj (k := k) X Z) ≃ₗ[k]
    (Enveloping.evalObj X M →ₗ[S] Z) :=
  (ModuleCat.homLinearEquiv (S := k)).symm.trans
    ((equiv (k := k)).trans (ModuleCat.homLinearEquiv (S := k)))

def stableEquiv [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M)] :
    StableHom (k := k) (R := Enveloping.Alg k S R) (M := M)
      (N := HomBimodule.obj (k := k) X Z) ≃ₗ[k]
    StableHom (k := k) (R := S) (M := Enveloping.evalObj X M) (N := Z) :=
  Submodule.Quotient.equiv _ _ (linearEquiv (k := k)) (by
    ext g
    constructor
    · rintro ⟨f,hf,rfl⟩
      exact (factors_iff_uncurry tR tS (ModuleCat.ofHom (X := M) (Y := HomBimodule.obj (k := k) X Z) f)).mp hf
    · intro hg
      obtain ⟨f,rfl⟩ := (linearEquiv (k := k) (M := M) (X := X) (Z := Z)).surjective g
      exact ⟨f,(factors_iff_uncurry tR tS (ModuleCat.ofHom (X := M) (Y := HomBimodule.obj (k := k) X Z) f)).mpr hg,rfl⟩)

end Tachikawa.BimoduleTensorHom



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))
  (X : ModuleCat.{0} R) (Z : ModuleCat.{0} S) [FiniteDimensional k X]

include t u in

theorem evaluation_nonzero_of_syzygy_composition
    (U M T : FiniteModule k (Enveloping.Alg k S R))
    [Module.Projective Rᵐᵒᵖ (Enveloping.Obj U.obj)]
    [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M.obj)]
    (e : T.obj ≃ₗ[Enveloping.Alg k S R] HomBimodule.obj (k := k) X Z)
    (g : U.obj →ₗ[Enveloping.Alg k S R] M.obj)
    (phi : M.obj →ₗ[Enveloping.Alg k S R] T.syzygy.obj)
    (hn : phi.comp g ∉ projectiveFactors (k := k)) :
    (Enveloping.evalMap X (ModuleCat.ofHom (X := U.obj) (Y := M.obj) g)).hom
      ∉ projectiveFactors (k := k) := by
  let tau := Enveloping.envelopingForm u t
  let : Module.Injective (Enveloping.Alg k S R) (Enveloping.Alg k S R) := tau.injective
  let PU := ModuleCat.of (Enveloping.Alg k S R)
    (Fin (Module.finrank k U) → Enveloping.Alg k S R)
  let PM := ModuleCat.of (Enveloping.Alg k S R)
    (Fin (Module.finrank k M) → Enveloping.Alg k S R)
  let PT := ModuleCat.of (Enveloping.Alg k S R) (Fin T.cover.rank → Enveloping.Alg k S R)
  obtain ⟨h,g',hu,hl⟩ := exists_exact_square_down (P := PU) (Q := PM)
    (U.embed tau) (U.cosyzygyProjection tau) (U.embed_injective tau)
    (U.cosyzygyProjection_exact tau) (U.cosyzygyProjection_surjective tau)
    (M.embed tau) (M.cosyzygyProjection tau) (M.cosyzygyProjection_exact tau) g
  obtain ⟨h',psi,hu',hl'⟩ := exists_exact_square_down (P := PM) (Q := PT)
    (M.embed tau) (M.cosyzygyProjection tau) (M.embed_injective tau)
    (M.cosyzygyProjection_exact tau) (M.cosyzygyProjection_surjective tau)
    T.syzygyInclusion T.cover.map T.syzygyInclusion_exact phi
  have hnon : psi.comp g' ∉ projectiveFactors (k := k) := by
    apply mt (exact_square_factors_iff (P := PU) (Q := PT)
      (U.embed tau) (U.cosyzygyProjection tau) (U.embed_injective tau)
      (U.cosyzygyProjection_exact tau) (U.cosyzygyProjection_surjective tau)
      T.syzygyInclusion T.cover.map T.syzygyInclusion_injective
      T.syzygyInclusion_exact T.cover.surjective
      (phi.comp g) (h'.comp h) (psi.comp g') ?_ ?_).mpr hn
    · rw [LinearMap.comp_assoc,hu,← LinearMap.comp_assoc,hu',LinearMap.comp_assoc]
    · rw [← LinearMap.comp_assoc,hl',LinearMap.comp_assoc,hl,← LinearMap.comp_assoc]
  intro hgeval
  have hshift : (Enveloping.evalMap X (ModuleCat.ofHom
      (X := (U.cosyzygy tau).obj) (Y := (M.cosyzygy tau).obj) g')).hom
        ∈ projectiveFactors (k := k) := by
    apply (Enveloping.eval_square_factors_iff t u X
      (ModuleCat.ofHom (X := U.obj) (Y := PU) (U.embed tau))
      (ModuleCat.ofHom (X := PU) (Y := (U.cosyzygy tau).obj) (U.cosyzygyProjection tau))
      (U.embed_injective tau) (U.cosyzygyProjection_exact tau) (U.cosyzygyProjection_surjective tau)
      (ModuleCat.ofHom (X := M.obj) (Y := PM) (M.embed tau))
      (ModuleCat.ofHom (X := PM) (Y := (M.cosyzygy tau).obj) (M.cosyzygyProjection tau))
      (M.embed_injective tau) (M.cosyzygyProjection_exact tau) (M.cosyzygyProjection_surjective tau)
      (ModuleCat.ofHom g) (ModuleCat.ofHom h) (ModuleCat.ofHom g')
      (ModuleCat.hom_ext hu) (ModuleCat.hom_ext hl)).mp hgeval
  let gt : (U.cosyzygy tau).obj ⟶ (M.cosyzygy tau).obj := ModuleCat.ofHom g'
  let psit : (M.cosyzygy tau).obj ⟶ HomBimodule.obj (k := k) X Z :=
    ModuleCat.ofHom (X := (M.cosyzygy tau).obj)
      (Y := HomBimodule.obj (k := k) X Z) (e.toLinearMap.comp psi)
  have hc : (BimoduleTensorHom.uncurry (gt ≫ psit)).hom ∈ projectiveFactors (k := k) := by
    rw [BimoduleTensorHom.uncurry_precompose]
    exact projectiveFactors_postcomp hshift (BimoduleTensorHom.uncurry psit).hom
  let : Module.Projective Rᵐᵒᵖ (Enveloping.Obj (U.cosyzygy tau).obj) :=
    Enveloping.cosyzygy_right_projective u t U
  have hh := BimoduleTensorHom.factors_of_uncurry t u hc
  have hh' := projectiveFactors_postcomp hh e.symm.toLinearMap
  apply hnon
  convert hh' using 1
  ext x
  change psi (g' x) = e.symm (e (psi (g' x)))
  exact (e.symm_apply_apply _).symm
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

theorem exists_evaluated_Y_lift (hq : q ≠ 0) :
    ∃ g : (finiteU q H hH).obj ⟶ (Y q).obj,
      (Enveloping.evalMap (xObj q) g).hom ∉ projectiveFactors (k := k) := by
  obtain ⟨g,psi,hn⟩ := exists_Y_lift_with_nonzero_composition q H hH hq
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (Y q).obj) := (Y_side_projective q hq).2
  let : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (finiteU q H hH).obj) := by
    change Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj (U q H hH))
    infer_instance
  refine ⟨g,?_⟩
  exact evaluation_nonzero_of_syzygy_composition (formE q) (formE q)
    (xObj q) (xObj q) (finiteU q H hH) (Y q) (finiteS q)
    (LinearEquiv.refl _ _) g.hom psi.hom hn




omit [CharP k 2] in
lemma sigma_fixed_x (r : E q) (x : xObj q) :
    sigma q H hH r • x = r • x := by
  change characterE q (sigma q H hH r) * (show k from x) =
    characterE q r * (show k from x)
  rw [characterE_sigma]

def uXIso : Enveloping.evalObj (xObj q) (finiteU q H hH).obj ≅ xObj q :=
  Enveloping.twistedEvalIso (sigma q H hH) (xObj q) (sigma_fixed_x q H hH)

theorem exists_nonzero_X_YX (hq : q ≠ 0) :
    ∃ g : (finiteU q H hH).obj ⟶ (Y q).obj,
      ((uXIso q H hH).inv ≫ Enveloping.evalMap (xObj q) g).hom ∉
        projectiveFactors (k := k) := by
  obtain ⟨g,hg⟩ := exists_evaluated_Y_lift q H hH hq
  refine ⟨g,?_⟩
  intro hh
  have hp := projectiveFactors_precomp hh (uXIso q H hH).hom.hom
  apply hg
  convert hp using 1
  apply ModuleCat.hom_ext_iff.mp
  change Enveloping.evalMap (xObj q) g =
    (uXIso q H hH).hom ≫ ((uXIso q H hH).inv ≫ Enveloping.evalMap (xObj q) g)
  simp

end Tachikawa.Construction

end

end OAI
