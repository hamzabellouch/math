import OAI.RingTheory.Tachikawa.TwistHom

namespace OAI


noncomputable section
namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k A B : Type u} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma map_add_left {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f f' : M ⟶ M') (g : N ⟶ N') : map (k := k) (f+f') g = map f g + map f' g := by
  apply LinearMap.restrictScalars_injective k
  change TensorProduct.map ((f.hom.restrictScalars k)+(f'.hom.restrictScalars k))
    (g.hom.restrictScalars k) = _
  exact TensorProduct.map_add_left _ _ _

lemma map_add_right {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g g' : N ⟶ N') : map (k := k) f (g+g') = map f g + map f g' := by
  apply LinearMap.restrictScalars_injective k
  change TensorProduct.map (f.hom.restrictScalars k)
    ((g.hom.restrictScalars k)+(g'.hom.restrictScalars k)) = _
  exact TensorProduct.map_add_right _ _ _

instance (M : ModuleCat.{u} A) : ((bifunctor k A B).obj M).Additive where
  map_add {_X _Y} g g' := ModuleCat.hom_ext (map_add_right (k := k) (𝟙 M) g g')

instance : (bifunctor k A B).Additive where
  map_add {_X _Y} f f' := by
    apply NatTrans.ext
    funext N
    exact ModuleCat.hom_ext (map_add_left f f' (𝟙 N))

end Tachikawa.OuterTensor



namespace Tachikawa.TotalMap
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
universe u
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable {I₁ I₂ J : Type u} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
variable (F : C ⥤ D) [F.Additive] (K : HomologicalComplex₂ C c₁ c₂)
variable (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]

abbrev map₂ : HomologicalComplex₂ D c₁ c₂ :=
  ((F.mapHomologicalComplex c₂).mapHomologicalComplex c₁).obj K

variable [K.HasTotal c] [(map₂ F K).HasTotal c]

instance sourceHasCoproduct (j : J) : HasCoproduct
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) :=
  (inferInstance : K.HasTotal c) j

instance targetHasCoproduct (j : J) : HasCoproduct
    (fun t => F.obj (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j t)) :=
  (inferInstance : (map₂ F K).HasTotal c) j

abbrev compareX (j : J) : ((map₂ F K).total c).X j ⟶ F.obj ((K.total c).X j) :=
  sigmaComparison F (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)

@[reassoc (attr := simp)]
lemma ι_compareX (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    (map₂ F K).ιTotal c i₁ i₂ j h ≫ compareX F K c j =
      F.map (K.ιTotal c i₁ i₂ j h) := by
  exact ι_comp_sigmaComparison F
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j) ⟨(i₁,i₂), h⟩

@[reassoc]
lemma ιOrZero_compareX (i₁ : I₁) (i₂ : I₂) (j : J) :
    (map₂ F K).ιTotalOrZero c i₁ i₂ j ≫ compareX F K c j =
      F.map (K.ιTotalOrZero c i₁ i₂ j) := by
  by_cases h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j
  · simp only [ιTotalOrZero_eq _ _ _ _ _ h, ι_compareX]
  · simp only [ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp, F.map_zero]

lemma d₁_compareX (i₁ : I₁) (i₂ : I₂) (j : J) :
    (map₂ F K).d₁ c i₁ i₂ j ≫ compareX F K c j = F.map (K.d₁ c i₁ i₂ j) := by
  change (ComplexShape.ε₁ c₁ c₂ c (i₁,i₂) •
    (F.map ((K.d i₁ (c₁.next i₁)).f i₂) ≫ (map₂ F K).ιTotalOrZero c _ _ j)) ≫
      compareX F K c j = F.map (ComplexShape.ε₁ c₁ c₂ c (i₁,i₂) •
        ((K.d i₁ (c₁.next i₁)).f i₂ ≫ K.ιTotalOrZero c _ _ j))
  rw [Linear.units_smul_comp, Category.assoc, ιOrZero_compareX,
    F.map_units_smul, F.map_comp]

lemma d₂_compareX (i₁ : I₁) (i₂ : I₂) (j : J) :
    (map₂ F K).d₂ c i₁ i₂ j ≫ compareX F K c j = F.map (K.d₂ c i₁ i₂ j) := by
  change (ComplexShape.ε₂ c₁ c₂ c (i₁,i₂) •
    (F.map ((K.X i₁).d i₂ (c₂.next i₂)) ≫ (map₂ F K).ιTotalOrZero c _ _ j)) ≫
      compareX F K c j = F.map (ComplexShape.ε₂ c₁ c₂ c (i₁,i₂) •
        ((K.X i₁).d i₂ (c₂.next i₂) ≫ K.ιTotalOrZero c _ _ j))
  rw [Linear.units_smul_comp, Category.assoc, ιOrZero_compareX,
    F.map_units_smul, F.map_comp]

def comparison : (map₂ F K).total c ⟶ (F.mapHomologicalComplex c).obj (K.total c) where
  f := compareX F K c
  comm' j j' _ := by
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ h
    simp only [ι_compareX_assoc, Functor.mapHomologicalComplex_obj_d,
      ← F.map_comp, total_d, Preadditive.comp_add, ι_D₁, ι_D₂, F.map_add,
      Preadditive.add_comp, ι_D₁_assoc, ι_D₂_assoc, d₁_compareX, d₂_compareX]

variable [∀ j, PreservesColimit
  (Discrete.functor (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)) F]

instance (j : J) : IsIso (compareX F K c j) := by
  have : PreservesColimit (Discrete.functor
    (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j)) F := inferInstance
  change IsIso (sigmaComparison F (K.toGradedObject.mapObjFun (ComplexShape.π c₁ c₂ c) j))
  rw [← PreservesCoproduct.inv_hom]
  infer_instance

instance : IsIso (comparison F K c) := by
  have (j : J) : IsIso ((comparison F K c).f j) :=
    inferInstanceAs (IsIso (compareX F K c j))
  exact HomologicalComplex.Hom.isIso_of_components _

def iso : (map₂ F K).total c ≅ (F.mapHomologicalComplex c).obj (K.total c) :=
  asIso (comparison F K c)

end Tachikawa.TotalMap



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B : Type u) [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

abbrev forgetA := ModuleCat.restrictScalars (algebraMap k A)
abbrev forgetB := ModuleCat.restrictScalars (algebraMap k B)
abbrev forgetE := ModuleCat.restrictScalars (algebraMap k (A ⊗[k] B))
abbrev tensorF := CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} k)

def forgetObjIso (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    (forgetE k A B).obj ((bifunctor k A B).obj M |>.obj N) ≅
      ((tensorF k).obj ((forgetA k A).obj M)).obj ((forgetB k B).obj N) :=
  LinearEquiv.toModuleIso
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (algebraMap k (A ⊗[k] B) r) • (show Obj k A B M N from x) = r • (show M ⊗[k] N from x)
        change action k A B M N (algebraMap k (A ⊗[k] B) r) x = r • (show M ⊗[k] N from x)
        rw [AlgHom.commutes]
        rfl }

@[reassoc]
lemma forgetObjIso_natural {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (forgetE k A B).map (ModuleCat.ofHom (map (k := k) f g)) ≫ (forgetObjIso k A B M' N').hom =
      (forgetObjIso k A B M N).hom ≫
        ((tensorF k).map ((forgetA k A).map f)).app ((forgetB k B).obj N) ≫
          ((tensorF k).obj ((forgetA k A).obj M')).map ((forgetB k B).map g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

@[reassoc]
lemma forgetBifunctor_natural {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (forgetE k A B).map ((bifunctor k A B).map f |>.app N) ≫
      (forgetE k A B).map (((bifunctor k A B).obj M').map g) ≫
      (forgetObjIso k A B M' N').hom =
    (forgetObjIso k A B M N).hom ≫
      ((tensorF k).map ((forgetA k A).map f)).app ((forgetB k B).obj N) ≫
        ((tensorF k).obj ((forgetA k A).obj M')).map ((forgetB k B).map g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end Tachikawa.OuterTensor

namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B : Type u) [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable {I₁ I₂ : Type u} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K : HomologicalComplex (ModuleCat.{u} A) c₁) (L : HomologicalComplex (ModuleCat.{u} B) c₂)

abbrev outerBicomplex := ((bifunctor k A B).mapBifunctorHomologicalComplex c₁ c₂).obj K |>.obj L
abbrev vectorBicomplex := ((tensorF k).mapBifunctorHomologicalComplex c₁ c₂).obj
  (((forgetA k A).mapHomologicalComplex c₁).obj K) |>.obj
    (((forgetB k B).mapHomologicalComplex c₂).obj L)

def forgetBicomplexIso :
    TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K L) ≅ vectorBicomplex k A B K L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => forgetObjIso k A B (K.X i) (L.X j)) (by
        intro j j' _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul x y => rfl
        | add x y hx hy =>
          exact (map_add _ x y).trans
            ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))) (by
      intro i i' _
      apply HomologicalComplex.Hom.ext
      funext j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x y => rfl
      | add x y hx hy =>
        exact (map_add _ x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))

variable {J : Type u} (c : ComplexShape J) [DecidableEq J]
  [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K L (bifunctor k A B) c]
  [HasMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K)
    (((forgetB k B).mapHomologicalComplex c₂).obj L) (tensorF k) c]
  [(TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K L)).HasTotal c]

def forgetTotalIso :
    ((forgetE k A B).mapHomologicalComplex c).obj
      (mapBifunctor K L (bifunctor k A B) c) ≅
    mapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K)
      (((forgetB k B).mapHomologicalComplex c₂).obj L) (tensorF k) c :=
  (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).symm ≪≫
    HomologicalComplex₂.total.mapIso (forgetBicomplexIso k A B K L) c

@[reassoc]
lemma ι_forgetTotalIso (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁,i₂) = j) :
    (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) ≫
      (forgetTotalIso k A B K L c).hom.f j =
    (forgetObjIso k A B (K.X i₁) (L.X i₂)).hom ≫
      ιMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K)
        (((forgetB k B).mapHomologicalComplex c₂).obj L) (tensorF k) c i₁ i₂ j h := by
  erw [← TotalMap.ι_compareX (forgetE k A B) (outerBicomplex k A B K L) c i₁ i₂ j h]
  change (_ ≫ (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j) ≫
    ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).inv ≫
      (HomologicalComplex₂.total.mapIso (forgetBicomplexIso k A B K L) c).hom).f j = _
  erw [HomologicalComplex.comp_f, Category.assoc, ← Category.assoc
    ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j)
      ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).inv.f j)]
  have hh := HomologicalComplex.congr_hom
    (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom_inv_id j
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hh
  erw [hh, Category.id_comp]
  exact HomologicalComplex₂.ιTotal_map _ _ (forgetBicomplexIso k A B K L).hom c i₁ i₂ j h

variable (K' : HomologicalComplex (ModuleCat.{u} A) c₁)
  (L' : HomologicalComplex (ModuleCat.{u} B) c₂)
  [HasMapBifunctor K' L' (bifunctor k A B) c]
  [HasMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K')
    (((forgetB k B).mapHomologicalComplex c₂).obj L') (tensorF k) c]
  [(TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K' L')).HasTotal c]

@[reassoc]
lemma forgetTotalIso_natural (f : K ⟶ K') (g : L ⟶ L') :
    ((forgetE k A B).mapHomologicalComplex c).map
      (mapBifunctorMap f g (bifunctor k A B) c) ≫ (forgetTotalIso k A B K' L' c).hom =
    (forgetTotalIso k A B K L c).hom ≫
      mapBifunctorMap (((forgetA k A).mapHomologicalComplex c₁).map f)
        (((forgetB k B).mapHomologicalComplex c₂).map g) (tensorF k) c := by
  apply HomologicalComplex.Hom.ext
  funext j
  rw [← cancel_epi ((TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j)]
  apply HomologicalComplex₂.total.hom_ext
  intro i₁ i₂ h
  have hh : (TotalMap.map₂ (forgetE k A B) (outerBicomplex k A B K L)).ιTotal c i₁ i₂ j h ≫
      (TotalMap.iso (forgetE k A B) (outerBicomplex k A B K L) c).hom.f j =
      (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) :=
    TotalMap.ι_compareX (forgetE k A B) (outerBicomplex k A B K L) c i₁ i₂ j h
  rw [← Category.assoc, ← Category.assoc, hh]
  change (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) ≫
    ((forgetE k A B).map ((mapBifunctorMap f g (bifunctor k A B) c).f j) ≫ _) =
      (forgetE k A B).map (ιMapBifunctor K L (bifunctor k A B) c i₁ i₂ j h) ≫
        ((forgetTotalIso k A B K L c).hom.f j ≫ _)
  rw [← Category.assoc, ← Functor.map_comp, ι_mapBifunctorMap,
    Functor.map_comp, Functor.map_comp]
  rw [Category.assoc, Category.assoc, ι_forgetTotalIso,
    ι_forgetTotalIso_assoc, ι_mapBifunctorMap]
  exact forgetBifunctor_natural_assoc k A B (f.f i₁) (g.f i₂)
    (ιMapBifunctor (((forgetA k A).mapHomologicalComplex c₁).obj K')
      (((forgetB k B).mapHomologicalComplex c₂).obj L') (tensorF k) c i₁ i₂ j h)

end Tachikawa.OuterTensor



namespace Tachikawa.AlgebraInduction
open CategoryTheory CategoryTheory.Limits
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)

lemma res_map_exact (T : ShortComplex (ModuleCat.{0} S)) (h : T.Exact) :
    (T.map (res φ)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

instance : PreservesFiniteLimits (res φ) := by
  have h := ((Functor.exact_tfae (res φ)).out 2 4).mp (res_map_exact φ)
  exact h.1
instance : PreservesFiniteColimits (res φ) := by
  have h := ((Functor.exact_tfae (res φ)).out 2 4).mp (res_map_exact φ)
  exact h.2

end Tachikawa.AlgebraInduction



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def freeObj (m : ℕ) : ModuleCat A := ModuleCat.of A (Fin m → A)

def underlyingFree (m : ℕ) : (freeObj A m) ≃ₗ[k] (Fin m → A) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    ext i
    change (algebraMap k A r) * x i = r • x i
    exact (Algebra.smul_def r (x i)).symm

def freeEquivLinear (m n : ℕ) :
    ((freeObj A m) ⊗[k] (freeObj B n)) ≃ₗ[k]
      (Fin m → Fin n → A ⊗[k] B) :=
  (TensorProduct.congr (underlyingFree k A m) (underlyingFree k B n)).trans
    ((TensorProduct.piLeft k (Fin n → B) (fun _ : Fin m => A)).trans
      (LinearEquiv.piCongrRight fun _ => TensorProduct.piRight k k A (fun _ : Fin n => B)))

lemma freeEquivLinear_tmul (m n : ℕ) (x : freeObj A m)
    (y : freeObj B n) :
    freeEquivLinear k A B m n (x ⊗ₜ[k] y) = fun i j => x i ⊗ₜ[k] y j := rfl

lemma freeEquivLinear_action (m n : ℕ) (r : A ⊗[k] B) :
    (freeEquivLinear k A B m n).toLinearMap.comp
      (action k A B (freeObj A m) (freeObj B n) r) =
      (Algebra.lsmul k k (Fin m → Fin n → A ⊗[k] B) r).comp
      (freeEquivLinear k A B m n).toLinearMap := by
  induction r using TensorProduct.inductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    ext i j
    change (a * x i) ⊗ₜ[k] (b * y j) = (a ⊗ₜ[k] b) * (x i ⊗ₜ[k] y j)
    exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm
  | add r s hr hs =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hr, hs]

def freeEquiv (m n : ℕ) :
    Obj k A B (freeObj A m) (freeObj B n) ≃ₗ[A ⊗[k] B]
      (Fin m → Fin n → A ⊗[k] B) where
  __ := (freeEquivLinear k A B m n).toAddEquiv
  map_smul' r z := LinearMap.congr_fun (freeEquivLinear_action k A B m n r) z

instance freeProjective (m n : ℕ) :
    Module.Projective (A ⊗[k] B)
      (Obj k A B (freeObj A m) (freeObj B n)) :=
  Module.Projective.of_equiv' (freeEquiv k A B m n).symm

lemma projective (M : ModuleCat A) (N : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N] :
    Module.Projective (A ⊗[k] B) (Obj k A B M N) := by
  let c := finiteFreeCover (R := A) (M := M)
  let d := finiteFreeCover (R := B) (M := N)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  obtain ⟨j,hj⟩ := Module.projective_lifting_property d.map LinearMap.id d.surjective
  have : Module.Projective (A ⊗[k] B)
      (Obj k A B (ModuleCat.of A (Fin c.rank → A))
        (ModuleCat.of B (Fin d.rank → B))) := freeProjective k A B c.rank d.rank
  apply Module.Projective.of_split
    (map (k := k) (ModuleCat.ofHom i) (ModuleCat.ofHom j))
    (map (k := k) (ModuleCat.ofHom c.map) (ModuleCat.ofHom d.map))
  rw [map_comp]
  have hi' : ModuleCat.ofHom i ≫ ModuleCat.ofHom c.map = 𝟙 M := ModuleCat.hom_ext hi
  have hj' : ModuleCat.ofHom j ≫ ModuleCat.ofHom d.map = 𝟙 N := ModuleCat.hom_ext hj
  rw [hi',hj',map_id]

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {M U : ModuleCat A} {N V : ModuleCat B}

def morphism (f : M ⟶ U) (g : N ⟶ V) :
    (((bifunctor k A B).obj M).obj N ⟶ ((bifunctor k A B).obj U).obj V) :=
  ModuleCat.ofHom (map (k := k) f g)

lemma map_smul_left (r : k) (f : M ⟶ U) (g : N ⟶ V) :
    morphism (k := k) (r • f) g = r • morphism (k := k) f g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change map (k := k) _ _ z = (algebraMap k (A ⊗[k] B) r) • (map (k := k) f g z)
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    change (r • f x) ⊗ₜ[k] g y = (algebraMap k (A ⊗[k] B) r) • (show Obj k A B U V from f x ⊗ₜ[k] g y)
    change (r • f x) ⊗ₜ[k] g y = action k A B U V (algebraMap k (A ⊗[k] B) r) _
    rw [AlgHom.commutes]
    exact TensorProduct.smul_tmul' _ _ _
  | add z z' hz hz' =>
    exact ((map (k := k) _ _).map_add z z').trans
      ((congrArg₂ (· + ·) hz hz').trans ((smul_add _ _ _).symm.trans
      (congrArg (fun w : Obj k A B U V => (algebraMap k (A ⊗[k] B) r) • w)
        ((map (k := k) f g).map_add z z').symm)))

lemma map_smul_right (r : k) (f : M ⟶ U) (g : N ⟶ V) :
    morphism (k := k) f (r • g) = r • morphism (k := k) f g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change map (k := k) _ _ z = (algebraMap k (A ⊗[k] B) r) • (map (k := k) f g z)
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    change f x ⊗ₜ[k] (r • g y) = (algebraMap k (A ⊗[k] B) r) • (show Obj k A B U V from f x ⊗ₜ[k] g y)
    change f x ⊗ₜ[k] (r • g y) = action k A B U V (algebraMap k (A ⊗[k] B) r) _
    rw [AlgHom.commutes]
    exact TensorProduct.tmul_smul _ _ _
  | add z z' hz hz' =>
    exact ((map (k := k) _ _).map_add z z').trans
      ((congrArg₂ (· + ·) hz hz').trans ((smul_add _ _ _).symm.trans
      (congrArg (fun w : Obj k A B U V => (algebraMap k (A ⊗[k] B) r) • w)
        ((map (k := k) f g).map_add z z').symm)))

def homMap : (M ⟶ U) ⊗[k] (N ⟶ V) →ₗ[k]
    (((bifunctor k A B).obj M).obj N ⟶ ((bifunctor k A B).obj U).obj V) :=
  TensorProduct.lift
    { toFun := fun f =>
        { toFun := fun g => morphism (k := k) f g
          map_add' := fun g g' => ModuleCat.hom_ext (map_add_right f g g')
          map_smul' := fun r g => map_smul_right r f g }
      map_add' := fun f f' => LinearMap.ext fun g => ModuleCat.hom_ext (map_add_left f f' g)
      map_smul' := fun r f => LinearMap.ext fun g => map_smul_left r f g }

@[simp] lemma homMap_tmul (f : M ⟶ U) (g : N ⟶ V) :
    homMap (f ⊗ₜ[k] g) = morphism (k := k) f g := rfl

def restrictHom : (M ⟶ U) →ₗ[k] (M →ₗ[k] U) where
  toFun f := f.hom.restrictScalars k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma restrictHom_injective : Function.Injective (restrictHom (k := k) (M := M) (U := U)) := by
  intro f g h
  exact ModuleCat.hom_ext (LinearMap.restrictScalars_injective k h)

def underlyingHom (f : ((bifunctor k A B).obj M |>.obj N) ⟶
    ((bifunctor k A B).obj U |>.obj V)) : M ⊗[k] N →ₗ[k] U ⊗[k] V where
  toFun := f.hom
  map_add' := f.hom.map_add
  map_smul' r z := by
    have h := f.hom.map_smul (algebraMap k (A ⊗[k] B) r) z
    change f.hom (action k A B M N (algebraMap k (A ⊗[k] B) r) z) =
      action k A B U V (algebraMap k (A ⊗[k] B) r) (f.hom z) at h
    rw [AlgHom.commutes, AlgHom.commutes] at h
    exact h

lemma homMap_underlying (z : (M ⟶ U) ⊗[k] (N ⟶ V)) :
    underlyingHom (homMap z) =
      TensorProduct.homTensorHomMap (RingHom.id k) M N U V
        (TensorProduct.map (restrictHom (k := k)) (restrictHom (k := k)) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul f g => rfl
  | add z z' hz hz' =>
    rw [map_add]
    change underlyingHom (homMap z) + underlyingHom (homMap z') = _
    simp only [map_add, hz, hz']

lemma homMap_injective [FiniteDimensional k M] [FiniteDimensional k N] :
    Function.Injective (homMap (k := k) (M := M) (N := N) (U := U) (V := V)) := by
  intro x y h
  have h' := congrArg underlyingHom h
  rw [homMap_underlying, homMap_underlying,
    ← homTensorHomEquiv_apply, ← homTensorHomEquiv_apply] at h'
  have h'' := (homTensorHomEquiv k M N U V).injective h'
  exact TensorProduct.map_injective_of_flat_flat _ _ (restrictHom_injective (k := k))
    (restrictHom_injective (k := k)) h''

end Tachikawa.OuterTensor



namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def unitLinear (φ : R →ₐ[k] S) (M : ModuleCat R) : M →ₗ[k] (functor φ).obj M where
  toFun := unit φ M
  map_add' := (unit φ M).hom.map_add
  map_smul' c x := by
    have h := (unit φ M).hom.map_smul (algebraMap k R c) x
    change (show (functor φ).obj M from unit φ M ((algebraMap k R c) • x)) =
      φ (algebraMap k R c) • (show (functor φ).obj M from unit φ M x) at h
    rw [IsScalarTower.algebraMap_smul, φ.commutes, IsScalarTower.algebraMap_smul] at h
    exact h

lemma unitLinear_smul (φ : R →ₐ[k] S) (M : ModuleCat R) (r : R) (m : M) :
    unitLinear φ M (r • m) = φ r • unitLinear φ M m := (unit φ M).hom.map_smul r m

end Tachikawa.AlgebraInduction

namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T) (M : ModuleCat A) (N : ModuleCat B)

abbrev inductionTarget := (bifunctor k S T).obj ((AlgebraInduction.functor φ).obj M) |>.obj
  ((AlgebraInduction.functor ψ).obj N)

def inductionUnit : ((bifunctor k A B).obj M).obj N ⟶
    (AlgebraInduction.res (Algebra.TensorProduct.map φ ψ)).obj (inductionTarget φ ψ M N) :=
  ModuleCat.ofHom
    (X := ((bifunctor k A B).obj M).obj N)
    (Y := (AlgebraInduction.res (Algebra.TensorProduct.map φ ψ)).obj (inductionTarget φ ψ M N))
    { toFun := TensorProduct.map (AlgebraInduction.unitLinear φ M) (AlgebraInduction.unitLinear ψ N)
      map_add' := map_add _
      map_smul' := by
        intro r z
        induction r using TensorProduct.inductionOn with
        | add a b ha hb =>
          erw [add_smul, map_add, ha, hb, RingHom.id_apply, add_smul]
          rfl
        | tmul a b =>
          induction z using TensorProduct.inductionOn with
          | add x y hx hy =>
            erw [smul_add, map_add, hx, hy, map_add, smul_add]
            rfl
          | tmul x y =>
            change AlgebraInduction.unitLinear φ M (a • x) ⊗ₜ[k]
                AlgebraInduction.unitLinear ψ N (b • y) =
              (φ a • AlgebraInduction.unitLinear φ M x) ⊗ₜ[k]
                (ψ b • AlgebraInduction.unitLinear ψ N y)
            rw [AlgebraInduction.unitLinear_smul, AlgebraInduction.unitLinear_smul] }

def inductionComparison :
    (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).obj
      (((bifunctor k A B).obj M).obj N) ⟶ inductionTarget φ ψ M N :=
  AlgebraInduction.extend (Algebra.TensorProduct.map φ ψ) (inductionUnit φ ψ M N)

@[simp] lemma inductionComparison_pure (s : S) (t : T) (x : M) (y : N) :
    inductionComparison φ ψ M N
      (BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
        (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from s ⊗ₜ[k] t)
        (show Obj k A B M N from x ⊗ₜ[k] y)) =
      (s • AlgebraInduction.unitLinear φ M x) ⊗ₜ[k]
        (t • AlgebraInduction.unitLinear ψ N y) := rfl

lemma inductionComparison_surjective : Function.Surjective (inductionComparison φ ψ M N) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    obtain ⟨a,ha⟩ := hz
    obtain ⟨b,hb⟩ := hw
    exact ⟨a+b, by erw [map_add,ha,hb]; rfl⟩
  | tmul u v =>
    refine BalancedTensor.induction_on (k := k) (R := A) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := M) u ?_ ?_ ?_
    · exact ⟨0, by erw [map_zero, TensorProduct.zero_tmul]; rfl⟩
    · intro s x
      refine BalancedTensor.induction_on (k := k) (R := B) (S := T)
        (M := AlgebraInduction.Bimod ψ) (N := N) v ?_ ?_ ?_
      · exact ⟨0, by erw [map_zero, TensorProduct.tmul_zero]; rfl⟩
      · intro t y
        refine ⟨BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
          (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from
            (show S from s) ⊗ₜ[k] (show T from t))
          (show Obj k A B M N from x ⊗ₜ[k] y), ?_⟩
        rw [inductionComparison_pure]
        congr 1
        · exact (AlgebraInduction.mk_one_smul φ M (show S from s) x).symm
        · exact (AlgebraInduction.mk_one_smul ψ N (show T from t) y).symm
      · intro v w hv hw
        obtain ⟨a,ha⟩ := hv
        obtain ⟨b,hb⟩ := hw
        exact ⟨a+b, by erw [map_add,ha,hb,TensorProduct.tmul_add]; rfl⟩
    · intro u w hu hw
      obtain ⟨a,ha⟩ := hu
      obtain ⟨b,hb⟩ := hw
      exact ⟨a+b, by erw [map_add,ha,hb,TensorProduct.add_tmul]; rfl⟩

@[reassoc] lemma inductionComparison_natural {M' : ModuleCat A} {N' : ModuleCat B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).map (ModuleCat.ofHom (map f g)) ≫
        inductionComparison φ ψ M' N' =
      inductionComparison φ ψ M N ≫ ModuleCat.ofHom
        (map ((AlgebraInduction.functor φ).map f) ((AlgebraInduction.functor ψ).map g)) := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
    (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
    (N := ((bifunctor k A B).obj M).obj N)
  intro s z
  change (show S ⊗[k] T from s) •
      (show inductionTarget φ ψ M' N' from inductionUnit φ ψ M' N' (map f g z)) =
    (map ((AlgebraInduction.functor φ).map f) ((AlgebraInduction.functor ψ).map g))
      ((show S ⊗[k] T from s) • (show inductionTarget φ ψ M N from inductionUnit φ ψ M N z))
  erw [map_smul]
  congr 1
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact ((congrArg (inductionUnit φ ψ M' N') (map_add (map f g) x y)).trans
      (map_add (inductionUnit φ ψ M' N').hom _ _)).trans
        ((congrArg₂ (· + ·) hx hy).trans
          ((map_add (map ((AlgebraInduction.functor φ).map f)
            ((AlgebraInduction.functor ψ).map g)) _ _).symm.trans
              (congrArg (map ((AlgebraInduction.functor φ).map f)
                ((AlgebraInduction.functor ψ).map g))
                  (map_add (inductionUnit φ ψ M N).hom x y).symm)))
  | tmul x y => rfl

end Tachikawa.OuterTensor



namespace Tachikawa.BalancedTensor
variable {k R S M N P : Type*} [Field k] [Ring R] [Ring S] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module R N]
  [AddCommGroup P] [Module k P]

def liftGround (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n)) :
    T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[k] P :=
  (lift (S := k) f hf).comp restrictEquiv.toLinearMap

@[simp] lemma liftGround_mk (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n))
    (m : M) (n : N) :
    liftGround (S := S) f hf (mk (k := k) (R := R) (S := S) m n) = f m n := rfl

omit [SMulCommClass S Rᵐᵒᵖ M] in
@[ext] theorem hom_ext_ground
    {f g : T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[k] P}
    (h : ∀ m n, f (mk m n) = g (mk m n)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | h0 => simp only [map_zero]
  | ht m n => exact h m n
  | ha x y hx hy => simp only [map_add, hx, hy]

lemma liftGround_add (f g : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n))
    (hg : ∀ (r : R) (m : M) (n : N), g (MulOpposite.op r • m) n = g m (r • n))
    (hfg : ∀ (r : R) (m : M) (n : N), (f+g) (MulOpposite.op r • m) n = (f+g) m (r • n)) :
    liftGround (S := S) (f+g) hfg = liftGround f hf + liftGround g hg := by
  apply hom_ext_ground
  intro m n
  rfl

lemma liftGround_smul (c : k) (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n))
    (hcf : ∀ (r : R) (m : M) (n : N), (c • f) (MulOpposite.op r • m) n = (c • f) m (r • n)) :
    liftGround (S := S) (c • f) hcf = c • liftGround f hf := by
  apply hom_ext_ground
  intro m n
  rfl

end Tachikawa.BalancedTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T) (M : ModuleCat A) (N : ModuleCat B)

abbrev inductionSource := (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).obj
  (((bifunctor k A B).obj M).obj N)

def underlyingEquiv (M : ModuleCat A) (N : ModuleCat B) :
    (((bifunctor k A B).obj M).obj N) ≃ₗ[k] (M ⊗[k] N) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := IsScalarTower.algebraMap_smul (A ⊗[k] B) c
    (show Obj k A B M N from x)

def inductionSourceMk : (S ⊗[k] T) →ₗ[k] (M ⊗[k] N) →ₗ[k] inductionSource φ ψ M N :=
  (((BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
      (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
      (N := ((bifunctor k A B).obj M).obj N)).restrictScalars k).compl₂
        (underlyingEquiv M N).symm.toLinearMap).compr₂
          (AlgebraInduction.underlyingEquiv (Algebra.TensorProduct.map φ ψ)
            (((bifunctor k A B).obj M).obj N)).symm.toLinearMap

def inductionPure : AlgebraInduction.Bimod φ →ₗ[k] M →ₗ[k]
    AlgebraInduction.Bimod ψ →ₗ[k] N →ₗ[k] inductionSource φ ψ M N where
  toFun s :=
    { toFun := fun x =>
        { toFun := fun t =>
            { toFun := fun y => inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
              map_add' := by
                intro y z
                simp only [TensorProduct.tmul_add, map_add]
              map_smul' := by
                intro c y
                simp only [TensorProduct.tmul_smul, map_smul]
                rfl }
          map_add' := by
            intro t u
            ext y
            change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] ((show T from t)+(show T from u))) (x ⊗ₜ[k] y) = _
            erw [TensorProduct.tmul_add, map_add, LinearMap.add_apply]
          map_smul' := by
            intro c t
            ext y
            change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (c • (show T from t))) (x ⊗ₜ[k] y) = _
            erw [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply] }
      map_add' := by
        intro x z
        ext t y
        change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) ((x+z) ⊗ₜ[k] y) = _
        simp only [TensorProduct.add_tmul, map_add]
        rfl
      map_smul' := by
        intro c x
        ext t y
        change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) ((c • x) ⊗ₜ[k] y) = _
        simp only [← TensorProduct.smul_tmul', map_smul]
        rfl }
  map_add' s u := by
    refine LinearMap.ext fun x => LinearMap.ext fun t => LinearMap.ext fun y => ?_
    change inductionSourceMk φ ψ M N (((show S from s)+(show S from u)) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y) =
      inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y) +
        inductionSourceMk φ ψ M N ((show S from u) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
    rw [TensorProduct.add_tmul, map_add, LinearMap.add_apply]
  map_smul' c s := by
    refine LinearMap.ext fun x => LinearMap.ext fun t => LinearMap.ext fun y => ?_
    change inductionSourceMk φ ψ M N ((c • (show S from s)) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y) =
      c • inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
    rw [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply]

lemma inductionPure_balance_left (a : A) (s : AlgebraInduction.Bimod φ) (x : M) :
    inductionPure φ ψ M N (MulOpposite.op a • s) x = inductionPure φ ψ M N s (a • x) := by
  ext t y
  have h := BalancedTensor.balance (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
    (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
    (N := ((bifunctor k A B).obj M).obj N)
    (a ⊗ₜ[k] (1 : B)) ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
  have h₁ : MulOpposite.op (a ⊗ₜ[k] (1 : B)) •
      (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from
        ((show S from s) ⊗ₜ[k] (show T from t))) = ((show S from s) * φ a) ⊗ₜ[k] (show T from t) := by
    change ((show S from s) ⊗ₜ[k] (show T from t)) * (φ a ⊗ₜ[k] ψ 1) = _
    erw [map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h₂ : (a ⊗ₜ[k] (1 : B)) •
      (show ((bifunctor k A B).obj M).obj N from x ⊗ₜ[k] y) = (a • x) ⊗ₜ[k] y := by
    change (a • x) ⊗ₜ[k] ((1 : B) • y) = _
    rw [one_smul]
  rw [h₁, h₂] at h
  exact h

lemma inductionPure_balance_right (b : B) (s : AlgebraInduction.Bimod φ) (x : M)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionPure φ ψ M N s x (MulOpposite.op b • t) y =
      inductionPure φ ψ M N s x t (b • y) := by
  have h := BalancedTensor.balance (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
    (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
    (N := ((bifunctor k A B).obj M).obj N)
    ((1 : A) ⊗ₜ[k] b) ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
  have h₁ : MulOpposite.op ((1 : A) ⊗ₜ[k] b) •
      (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from
        ((show S from s) ⊗ₜ[k] (show T from t))) = (show S from s) ⊗ₜ[k] ((show T from t) * ψ b) := by
    change ((show S from s) ⊗ₜ[k] (show T from t)) * (φ 1 ⊗ₜ[k] ψ b) = _
    erw [map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h₂ : ((1 : A) ⊗ₜ[k] b) •
      (show ((bifunctor k A B).obj M).obj N from x ⊗ₜ[k] y) = x ⊗ₜ[k] (b • y) := by
    change ((1 : A) • x) ⊗ₜ[k] (b • y) = _
    rw [one_smul]
  rw [h₁, h₂] at h
  exact h

def inductionLeftLift : BalancedTensor.T (k := k) (R := A) (S := S) (M := AlgebraInduction.Bimod φ) (N := M) →ₗ[k]
    AlgebraInduction.Bimod ψ →ₗ[k] N →ₗ[k] inductionSource φ ψ M N :=
  (BalancedTensor.liftGround (S := S) (inductionPure φ ψ M N)
    (inductionPure_balance_left φ ψ M N))

@[simp] lemma inductionLeftLift_mk (s : AlgebraInduction.Bimod φ) (x : M)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionLeftLift φ ψ M N (BalancedTensor.mk (k := k) (R := A) (S := S) s x) t y =
      inductionPure φ ψ M N s x t y := rfl

lemma inductionLeftLift_balance (z : BalancedTensor.T (k := k) (R := A) (S := S) (M := AlgebraInduction.Bimod φ) (N := M)) (b : B)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionLeftLift φ ψ M N z (MulOpposite.op b • t) y =
      inductionLeftLift φ ψ M N z t (b • y) := by
  induction z using BalancedTensor.induction_on with
  | h0 => simp
  | ha z w hz hw => simp only [map_add, LinearMap.add_apply, hz, hw]
  | ht s x => exact inductionPure_balance_right φ ψ M N b s x t y

def inductionRightLift
    (z : BalancedTensor.T (k := k) (R := A) (S := S) (M := AlgebraInduction.Bimod φ) (N := M)) :
    BalancedTensor.T (k := k) (R := B) (S := T) (M := AlgebraInduction.Bimod ψ) (N := N) →ₗ[k]
      inductionSource φ ψ M N :=
  BalancedTensor.liftGround (S := T) (inductionLeftLift φ ψ M N z)
    (inductionLeftLift_balance φ ψ M N z)

lemma inductionRightLift_add (z w : BalancedTensor.T (k := k) (R := A) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := M)) :
    inductionRightLift φ ψ M N (z+w) =
      inductionRightLift φ ψ M N z + inductionRightLift φ ψ M N w := by
  unfold inductionRightLift
  simp only [map_add]
  apply BalancedTensor.liftGround_add

lemma inductionRightLift_smul (c : k) (z : BalancedTensor.T (k := k) (R := A) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := M)) :
    inductionRightLift φ ψ M N (c • z) = c • inductionRightLift φ ψ M N z := by
  unfold inductionRightLift
  simp only [map_smul]
  apply BalancedTensor.liftGround_smul

def inductionInverseBilinear : BalancedTensor.T (k := k) (R := A) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := M) →ₗ[k]
    BalancedTensor.T (k := k) (R := B) (S := T) (M := AlgebraInduction.Bimod ψ) (N := N) →ₗ[k]
      inductionSource φ ψ M N where
  toFun := inductionRightLift φ ψ M N
  map_add' := inductionRightLift_add φ ψ M N
  map_smul' := inductionRightLift_smul φ ψ M N

def inductionInverseLinear : inductionTarget φ ψ M N →ₗ[k] inductionSource φ ψ M N :=
  (TensorProduct.lift (inductionInverseBilinear φ ψ M N)).comp
    ((TensorProduct.map (AlgebraInduction.underlyingEquiv φ M).toLinearMap
      (AlgebraInduction.underlyingEquiv ψ N).toLinearMap).comp
        (underlyingEquiv ((AlgebraInduction.functor φ).obj M)
          ((AlgebraInduction.functor ψ).obj N)).toLinearMap)

@[simp] lemma inductionInverseLinear_pure (s : AlgebraInduction.Bimod φ) (x : M)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionInverseLinear φ ψ M N
      (BalancedTensor.mk (k := k) (R := A) (S := S) s x ⊗ₜ[k]
        BalancedTensor.mk (k := k) (R := B) (S := T) t y) =
      inductionSourceMk φ ψ M N (s ⊗ₜ[k] t) (x ⊗ₜ[k] y) := rfl

lemma inductionInverse_comparison_pure (s : S) (t : T) (x : M) (y : N) :
    inductionInverseLinear φ ψ M N
      (inductionComparison φ ψ M N (inductionSourceMk φ ψ M N (s ⊗ₜ[k] t) (x ⊗ₜ[k] y))) =
      inductionSourceMk φ ψ M N (s ⊗ₜ[k] t) (x ⊗ₜ[k] y) := by
  change inductionInverseLinear φ ψ M N
    ((s • AlgebraInduction.unitLinear φ M x) ⊗ₜ[k]
      (t • AlgebraInduction.unitLinear ψ N y)) = _
  have hs : (s • AlgebraInduction.unitLinear φ M x : (AlgebraInduction.functor φ).obj M) =
      BalancedTensor.mk (k := k) (R := A) (S := S) (show AlgebraInduction.Bimod φ from s) x :=
    (AlgebraInduction.mk_one_smul φ M s x).symm
  have ht : (t • AlgebraInduction.unitLinear ψ N y : (AlgebraInduction.functor ψ).obj N) =
      BalancedTensor.mk (k := k) (R := B) (S := T) (show AlgebraInduction.Bimod ψ from t) y :=
    (AlgebraInduction.mk_one_smul ψ N t y).symm
  exact (congrArg (inductionInverseLinear φ ψ M N)
    (congrArg₂ (fun (u : (AlgebraInduction.functor φ).obj M)
      (v : (AlgebraInduction.functor ψ).obj N) =>
        (show inductionTarget φ ψ M N from u ⊗ₜ[k] v)) hs ht)).trans
      (inductionInverseLinear_pure φ ψ M N s x t y)

lemma inductionInverse_comparison :
    (inductionInverseLinear φ ψ M N).comp
      ((inductionComparison φ ψ M N).hom.restrictScalars k) = LinearMap.id := by
  let e := AlgebraInduction.underlyingEquiv (Algebra.TensorProduct.map φ ψ)
    (((bifunctor k A B).obj M).obj N)
  let f := ((inductionInverseLinear φ ψ M N).comp
      ((inductionComparison φ ψ M N).hom.restrictScalars k)).comp e.symm.toLinearMap
  have hfg : f = e.symm.toLinearMap := by
    apply BalancedTensor.hom_ext_ground
    intro s z
    change (f.comp ((BalancedTensor.mk (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
      (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
      (N := ((bifunctor k A B).obj M).obj N)) s)) z = _
    let F : (S ⊗[k] T) →ₗ[k] (M ⊗[k] N) →ₗ[k] inductionSource φ ψ M N :=
      (inductionSourceMk φ ψ M N).compr₂
        ((inductionInverseLinear φ ψ M N).comp
          ((inductionComparison φ ψ M N).hom.restrictScalars k))
    have hF : F = inductionSourceMk φ ψ M N := by
      apply LinearMap.ext
      intro st
      induction st using TensorProduct.inductionOn with
      | add st uv hst huv => simp only [map_add, hst, huv]
      | tmul s t =>
        apply TensorProduct.ext'
        intro x y
        exact inductionInverse_comparison_pure φ ψ M N s t x y
    exact LinearMap.congr_fun (LinearMap.congr_fun hF (show S ⊗[k] T from s))
      (show M ⊗[k] N from z)
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun hfg (e z)

lemma inductionComparison_injective : Function.Injective (inductionComparison φ ψ M N) := by
  apply Function.LeftInverse.injective (f := inductionComparison φ ψ M N)
    (g := inductionInverseLinear φ ψ M N)
  intro z
  exact LinearMap.congr_fun (inductionInverse_comparison φ ψ M N) z

def inductionIso : inductionSource φ ψ M N ≅ inductionTarget φ ψ M N :=
  (LinearEquiv.ofBijective (inductionComparison φ ψ M N).hom
    ⟨inductionComparison_injective φ ψ M N, inductionComparison_surjective φ ψ M N⟩).toModuleIso

@[simp] lemma inductionIso_hom : (inductionIso φ ψ M N).hom = inductionComparison φ ψ M N := rfl

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)

abbrev algebraTwist {R : Type} [Ring R] [Algebra k R] (ρ : R ≃ₐ[k] R) :=
  AlgebraInduction.res ρ.symm.toAlgHom

def restrictionGround {R : Type} [Ring R] [Algebra k R] (ρ : R ≃ₐ[k] R)
    (M : ModuleCat R) : (algebraTwist ρ).obj M ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change ρ.symm (algebraMap k R c) • (show M from x) = c • (show M from x)
    rw [ρ.symm.commutes]
    rfl

def twistObjIso (M : ModuleCat A) (N : ModuleCat B) :
    ((bifunctor k A B).obj ((algebraTwist σ).obj M)).obj ((algebraTwist τ).obj N) ≅
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) := by
  let eq := TensorProduct.congr (restrictionGround σ M) (restrictionGround τ N)
  let e : Obj k A B ((algebraTwist σ).obj M) ((algebraTwist τ).obj N) ≃ₗ[k]
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) :=
    eq.trans ((underlyingEquiv M N).symm.trans
      (restrictionGround (Algebra.TensorProduct.congr σ τ) (((bifunctor k A B).obj M).obj N)).symm)
  let f : ((bifunctor k A B).obj ((algebraTwist σ).obj M)).obj ((algebraTwist τ).obj N) ⟶
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) :=
    ModuleCat.ofHom (X := ((bifunctor k A B).obj ((algebraTwist σ).obj M)).obj ((algebraTwist τ).obj N))
      (Y := (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N))
    { toFun := e
      map_add' := e.map_add
      map_smul' a z := by
        induction a using TensorProduct.inductionOn with
        | tmul a b =>
          induction z using TensorProduct.inductionOn with
          | tmul x y => rfl
          | add x y hx hy =>
            erw [smul_add, map_add, hx, hy, map_add, smul_add]
            rfl
        | add a b ha hb =>
          erw [add_smul, map_add, ha, hb, RingHom.id_apply, add_smul]
          rfl }
  exact (LinearEquiv.ofBijective f.hom e.bijective).toModuleIso

@[reassoc]
lemma twistObjIso_natural {M M' : ModuleCat A} {N N' : ModuleCat B}
    (f : M ⟶ M') (g : N ⟶ N') :
    morphism ((algebraTwist σ).map f) ((algebraTwist τ).map g) ≫ (twistObjIso σ τ M' N').hom =
      (twistObjIso σ τ M N).hom ≫ (algebraTwist (Algebra.TensorProduct.congr σ τ)).map (morphism f g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)
variable {I₁ I₂ : Type} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (P : HomologicalComplex (ModuleCat A) c₁) (Q : HomologicalComplex (ModuleCat B) c₂)

abbrev twistComplex {R : Type} [Ring R] [Algebra k R] {I : Type} {c : ComplexShape I}
    (ρ : R ≃ₐ[k] R) (K : HomologicalComplex (ModuleCat R) c) :=
  ((algebraTwist ρ).mapHomologicalComplex c).obj K

def twistBicomplexIso :
    outerBicomplex k A B (twistComplex σ P) (twistComplex τ Q) ≅
      TotalMap.map₂ (algebraTwist (Algebra.TensorProduct.congr σ τ)) (outerBicomplex k A B P Q) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j => twistObjIso σ τ (P.X i) (Q.X j)) (by
        intro j j' _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul x y => rfl
        | add x y hx hy =>
          exact (map_add _ x y).trans
            ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))) (by
      intro i i' _
      apply HomologicalComplex.Hom.ext
      funext j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x y => rfl
      | add x y hx hy =>
        exact (map_add _ x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm))

variable {J : Type} (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor P Q (bifunctor k A B) c]
  [HasMapBifunctor (twistComplex σ P) (twistComplex τ Q) (bifunctor k A B) c]
  [(TotalMap.map₂ (algebraTwist (Algebra.TensorProduct.congr σ τ))
    (outerBicomplex k A B P Q)).HasTotal c]

def twistTotalIso :
    mapBifunctor (twistComplex σ P) (twistComplex τ Q) (bifunctor k A B) c ≅
      twistComplex (Algebra.TensorProduct.congr σ τ) (mapBifunctor P Q (bifunctor k A B) c) :=
  HomologicalComplex₂.total.mapIso (twistBicomplexIso σ τ P Q) c ≪≫
    TotalMap.iso (algebraTwist (Algebra.TensorProduct.congr σ τ)) (outerBicomplex k A B P Q) c

@[reassoc]
lemma ι_twistTotalIso (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁,i₂) = j) :
    ιMapBifunctor (twistComplex σ P) (twistComplex τ Q) (bifunctor k A B) c i₁ i₂ j h ≫
      (twistTotalIso σ τ P Q c).hom.f j =
    (twistObjIso σ τ (P.X i₁) (Q.X i₂)).hom ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map
        (ιMapBifunctor P Q (bifunctor k A B) c i₁ i₂ j h) := by
  change _ ≫ ((HomologicalComplex₂.total.mapIso (twistBicomplexIso σ τ P Q) c).hom.f j ≫ _) = _
  change HomologicalComplex₂.ιTotal _ c i₁ i₂ j h ≫
    ((HomologicalComplex₂.total.map (twistBicomplexIso σ τ P Q).hom c).f j ≫ _) = _
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map,Category.assoc]
  change (twistObjIso σ τ (P.X i₁) (Q.X i₂)).hom ≫ _ ≫
    TotalMap.compareX (algebraTwist (Algebra.TensorProduct.congr σ τ))
      (outerBicomplex k A B P Q) c j = _
  erw [TotalMap.ι_compareX]
  rfl

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def freeBasis {m : ℕ} (A : Type) [Ring A] (i : Fin m) : freeObj A m := Pi.single i 1

def freeTensorBasis {m n : ℕ} (i : Fin m) (j : Fin n) :
    (((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n)) := freeBasis A i ⊗ₜ[k] freeBasis B j

def freeAt {m : ℕ} (i : Fin m) (U : ModuleCat A) : U →ₗ[k] (freeObj A m ⟶ U) where
  toFun u := ModuleCat.ofHom
    { toFun := fun x => x i • u
      map_add' := fun x y => add_smul (x i) (y i) u
      map_smul' := fun r x => mul_smul r (x i) u }
  map_add' u v := ModuleCat.hom_ext (LinearMap.ext fun x => smul_add (x i) u v)
  map_smul' r u := ModuleCat.hom_ext (LinearMap.ext fun x => smul_comm (x i) r u)

@[simp] lemma freeAt_single {m : ℕ} (i j : Fin m) (U : ModuleCat A) (u : U) :
    freeAt (k := k) i U u (freeBasis A j) = if i = j then u else 0 := by
  change ((Pi.single j 1 : Fin m → A) i) • u = _
  by_cases h : i = j
  · subst j; simp
  · simp [h]

variable {U : ModuleCat A} {V : ModuleCat B}

def freeValue {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) (i : Fin m) (j : Fin n) : U ⊗[k] V :=
  f.hom (freeTensorBasis (k := k) i j)

def freeLift {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) :
    (freeObj A m ⟶ U) ⊗[k] (freeObj B n ⟶ V) :=
  ∑ i, ∑ j, TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V)
    (freeValue f i j)

lemma freeLift_single_component {m n : ℕ} (i i' : Fin m) (j j' : Fin n) (z : U ⊗[k] V) :
    (homMap (TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V) z)).hom
      (freeTensorBasis (k := k) (A := A) (B := B) i' j') =
      if i = i' ∧ j = j' then z else 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
    change (freeAt (k := k) i U u (freeBasis A i')) ⊗ₜ[k]
      (freeAt (k := k) j V v (freeBasis B j')) = _
    simp only [freeAt_single]
    split_ifs <;> simp_all
  | add z w hz hw =>
    simp only [map_add, ModuleCat.hom_add]
    change (homMap (TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V) z)).hom
        (freeTensorBasis (k := k) i' j') +
      (homMap (TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V) w)).hom
        (freeTensorBasis (k := k) i' j') = _
    rw [hz, hw]
    split_ifs
    · rfl
    · exact zero_add _

lemma homMap_freeLift_single {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) (i : Fin m) (j : Fin n) :
    (homMap (freeLift f)).hom (freeTensorBasis (k := k) (A := A) (B := B) i j) =
      f.hom (freeTensorBasis (k := k) (A := A) (B := B) i j) := by
  classical
  let ev : (((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) →+ (U ⊗[k] V) :=
    { toFun := fun g => g.hom (freeTensorBasis (k := k) i j)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (homMap (freeLift f)) = _
  simp only [freeLift, map_sum]
  change (∑ a, ∑ b, (homMap (TensorProduct.map (freeAt (k := k) a U)
    (freeAt (k := k) b V) (freeValue f a b))).hom
    (freeTensorBasis (k := k) i j)) = _
  simp only [freeLift_single_component]
  change (∑ a : Fin m, ∑ b : Fin n,
    (if a = i ∧ b = j then freeValue f a b else 0) : U ⊗[k] V) = freeValue f i j
  have hs (v : Fin m → Fin n → U ⊗[k] V) :
      (∑ a, ∑ b, if a = i ∧ b = j then v a b else 0) = v i j := by
    simp [ite_and, Finset.sum_ite_irrel]
  exact hs (freeValue f)

lemma freeEquiv_single {m n : ℕ} (i : Fin m) (j : Fin n) :
    freeEquiv k A B m n (freeTensorBasis (k := k) (A := A) (B := B) i j) =
      Pi.single i (Pi.single j 1) := by
  ext a b
  change ((Pi.single i 1 : Fin m → A) a) ⊗ₜ[k] ((Pi.single j 1 : Fin n → B) b) = _
  by_cases ha : a = i <;> by_cases hb : b = j <;> subst_vars <;>
    simp_all [Algebra.TensorProduct.one_def]

lemma freeHom_ext {m n : ℕ}
    (f g : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V)
    (h : ∀ i j, f.hom (freeTensorBasis (k := k) (A := A) (B := B) i j) =
      g.hom (freeTensorBasis (k := k) (A := A) (B := B) i j)) : f = g := by
  let e := freeEquiv k A B m n
  have hs (i : Fin m) (j : Fin n) : e.symm (Pi.single i (Pi.single j 1)) =
      freeTensorBasis (k := k) (A := A) (B := B) i j :=
    e.symm_apply_eq.mpr (freeEquiv_single (k := k) i j).symm
  have he : f.hom.comp e.symm.toLinearMap = g.hom.comp e.symm.toLinearMap := by
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.pi_ext'
    intro j
    apply LinearMap.ext_ring
    change f.hom (e.symm (Pi.single i (Pi.single j 1))) =
      g.hom (e.symm (Pi.single i (Pi.single j 1)))
    rw [hs]
    exact h i j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun he (e z)
  change f.hom (e.symm (e z)) = g.hom (e.symm (e z)) at hz
  exact (congrArg f.hom (e.symm_apply_apply z)).symm.trans
    (hz.trans (congrArg g.hom (e.symm_apply_apply z)))

lemma homMap_freeLift {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) : homMap (freeLift f) = f :=
  freeHom_ext _ _ (homMap_freeLift_single f)

lemma homMap_free_surjective (m n : ℕ) :
    Function.Surjective (homMap (k := k) (M := freeObj A m) (N := freeObj B n)
      (U := U) (V := V)) := fun f => ⟨freeLift f, homMap_freeLift f⟩

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma morphism_comp {M M' M'' : ModuleCat A} {N N' N'' : ModuleCat B}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    morphism (k := k) f g ≫ morphism f' g' = morphism (f ≫ f') (g ≫ g') :=
  ModuleCat.hom_ext (map_comp f f' g g')

@[simp] lemma morphism_id (M : ModuleCat A) (N : ModuleCat B) :
    morphism (k := k) (𝟙 M) (𝟙 N) = 𝟙 (((bifunctor k A B).obj M).obj N) :=
  ModuleCat.hom_ext (map_id M N)

def precompose {M M' U : ModuleCat A} (p : M' ⟶ M) : (M ⟶ U) →ₗ[k] (M' ⟶ U) where
  toFun f := p ≫ f
  map_add' _ _ := by simp only [Preadditive.comp_add]
  map_smul' _ _ := by simp only [CategoryTheory.Linear.comp_smul, RingHom.id_apply]

lemma homMap_precompose {M M' U : ModuleCat A} {N N' V : ModuleCat B}
    (p : M' ⟶ M) (q : N' ⟶ N) (z : (M ⟶ U) ⊗[k] (N ⟶ V)) :
    homMap (TensorProduct.map (precompose (k := k) p) (precompose (k := k) q) z) =
      morphism p q ≫ homMap z := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    change morphism (p ≫ f) (q ≫ g) = morphism p q ≫ morphism f g
    exact (morphism_comp p f q g).symm
  | add z w hz hw => simp only [map_add, Preadditive.comp_add, hz, hw]

lemma homMap_surjective (M U : ModuleCat A) (N V : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N] :
    Function.Surjective (homMap (k := k) (M := M) (N := N) (U := U) (V := V)) := by
  let c := finiteFreeCover (R := A) (M := M)
  let d := finiteFreeCover (R := B) (M := N)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  obtain ⟨j,hj⟩ := Module.projective_lifting_property d.map LinearMap.id d.surjective
  intro f
  let p : freeObj A c.rank ⟶ M := ModuleCat.ofHom c.map
  let q : freeObj B d.rank ⟶ N := ModuleCat.ofHom d.map
  let u : M ⟶ freeObj A c.rank := ModuleCat.ofHom i
  let v : N ⟶ freeObj B d.rank := ModuleCat.ofHom j
  obtain ⟨z,hz⟩ := homMap_free_surjective (k := k) c.rank d.rank (morphism p q ≫ f)
  refine ⟨TensorProduct.map (precompose (k := k) u) (precompose (k := k) v) z, ?_⟩
  rw [homMap_precompose, hz, ← Category.assoc, morphism_comp]
  have hu : u ≫ p = 𝟙 M := ModuleCat.hom_ext hi
  have hv : v ≫ q = 𝟙 N := ModuleCat.hom_ext hj
  rw [hu,hv,morphism_id,Category.id_comp]

def homEquiv (M U : ModuleCat A) (N V : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N]
    [FiniteDimensional k M] [FiniteDimensional k N] :
    (M ⟶ U) ⊗[k] (N ⟶ V) ≃ₗ[k]
      (((bifunctor k A B).obj M).obj N ⟶ ((bifunctor k A B).obj U).obj V) :=
  LinearEquiv.ofBijective homMap ⟨homMap_injective,homMap_surjective M U N V⟩

end Tachikawa.OuterTensor

end

end OAI
