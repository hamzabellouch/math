import OAI.RingTheory.Tachikawa.OuterTensor

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k]
  {K L M N : ChainComplex (ModuleCat k) ℕ}

lemma vectorTensor_quasiIso (f : K ⟶ L) (g : M ⟶ N) [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)) (.down ℕ)) := by
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  obtain ⟨e', he'⟩ := (ChainComplex.quasiIso_iff_of_projective g).mp inferInstance
  rw [← he, ← he']
  exact (bifunctorHomotopyEquiv _ (.down ℕ) e e').quasiIso_hom

end Tachikawa



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {K K' : ChainComplex (ModuleCat A) ℕ} {L L' : ChainComplex (ModuleCat B) ℕ}

instance restrictionPreservesHomology {R S : Type} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.restrictScalars f).PreservesHomology where
  preservesKernels _ := inferInstance
  preservesCokernels _ := inferInstance

lemma quasiIso (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g (bifunctor k A B) (.down ℕ)) := by
  apply (quasiIso_map_iff_of_preservesHomology _ (forgetE k A B)).mp
  rw [← quasiIso_iff_comp_right _ (forgetTotalIso k A B K' L' (.down ℕ)).hom,
    forgetTotalIso_natural]
  have := vectorTensor_quasiIso (((forgetA k A).mapHomologicalComplex (.down ℕ)).map f)
    (((forgetB k B).mapHomologicalComplex (.down ℕ)).map g)
  infer_instance

end Tachikawa.OuterTensor



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]

def bifunctorZeroIso (K : ChainComplex C₁ ℕ) (L : ChainComplex C₂ ℕ)
    [HasMapBifunctor K L F (.down ℕ)] :
    (mapBifunctor K L F (.down ℕ)).X 0 ≅ (F.obj (K.X 0)).obj (L.X 0) where
  hom := mapBifunctorDesc (fun i j h => eqToHom (by
    have hh : i + j = 0 := h
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hh
    rfl))
  inv := ιMapBifunctor K L F (.down ℕ) 0 0 0 rfl
  hom_inv_id := by
    apply mapBifunctor.hom_ext
    intro i j h
    have hh : i + j = 0 := h
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hh
    rw [ι_mapBifunctorDesc_assoc]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  inv_hom_id := by rw [ι_mapBifunctorDesc]; rfl

variable (M : C₁) (N : C₂)
variable [HasMapBifunctor ((ChainComplex.single₀ C₁).obj M)
  ((ChainComplex.single₀ C₂).obj N) F (.down ℕ)]
abbrev singleBifunctor := mapBifunctor ((ChainComplex.single₀ C₁).obj M)
  ((ChainComplex.single₀ C₂).obj N) F (.down ℕ)

omit [HasZeroObject D] in
lemma singleBifunctor_isZero (n : ℕ) (hn : n ≠ 0) : IsZero ((singleBifunctor F M N).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro i j h
  rw [Category.comp_id, comp_zero]
  have hij : i + j = n := h
  by_cases hi : i = 0
  · have hj : j ≠ 0 := by omega
    exact ((F.obj _).map_isZero
      (isZero_single_obj_X (.down ℕ) 0 N j hj)).eq_of_src _ _
  · exact ((F.flip.obj _).map_isZero
      (isZero_single_obj_X (.down ℕ) 0 M i hi)).eq_of_src _ _

def bifunctorSingleIso : singleBifunctor F M N ≅
    (ChainComplex.single₀ D).obj ((F.obj M).obj N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => if hn : n = 0 then by
      subst n
      exact bifunctorZeroIso F _ _
    else (singleBifunctor_isZero F M N n hn).iso
      (isZero_single_obj_X (.down ℕ) 0 ((F.obj M).obj N) n hn)) (by
      intro i j hij
      cases i with
      | zero => simp only [ComplexShape.down_Rel] at hij; omega
      | succ i => exact (singleBifunctor_isZero F M N (i+1) (by omega)).eq_of_src _ _)

end Tachikawa



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {M : ModuleCat A} {N : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (hP : ∀ n, Module.Finite A (P.complex.X n))
  (hQ : ∀ n, Module.Finite B (Q.complex.X n))

include hP hQ in
lemma total_projective (n : ℕ) :
    Projective ((mapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ)).X n) := by
  let (i : ℕ) : Module.Finite A (P.complex.X i) := hP i
  let (i : ℕ) : Module.Finite B (Q.complex.X i) := hQ i
  have (i j : ℕ) : Module.Projective (A ⊗[k] B)
      (Obj k A B (P.complex.X i) (Q.complex.X j)) := projective k A B _ _
  have (i j : ℕ) : Projective
      (((bifunctor k A B).obj (P.complex.X i)).obj (Q.complex.X j)) := by
    change Projective (ModuleCat.of (A ⊗[k] B) (Obj k A B (P.complex.X i) (Q.complex.X j)))
    infer_instance
  change Projective (∐ fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
    ((bifunctor k A B).obj (P.complex.X ij.val.1)).obj (Q.complex.X ij.val.2))
  infer_instance

def resolution : ProjectiveResolution ((bifunctor k A B).obj M |>.obj N) where
  complex := mapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ)
  projective := total_projective k A B P Q hP hQ
  π := mapBifunctorMap P.π Q.π (bifunctor k A B) (.down ℕ) ≫
    (bifunctorSingleIso (bifunctor k A B) M N).hom
  quasiIso := by
    have := quasiIso k A B P.π Q.π
    infer_instance

end Tachikawa.OuterTensor



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {I : Type} (F : I → ModuleCat R) (N : ModuleCat R)

def coproductHomEquiv : (∐ F ⟶ N) ≃ₗ[k] (∀ i, F i ⟶ N) where
  toFun f i := Sigma.ι F i ≫ f
  invFun f := Sigma.desc f
  left_inv f := Sigma.hom_ext _ _ (fun i => by simp)
  right_inv f := funext fun i => by simp
  map_add' f g := funext fun i => by simp only [Pi.add_apply, Preadditive.comp_add]
  map_smul' r f := funext fun i => by simp only [Pi.smul_apply, RingHom.id_apply, CategoryTheory.Linear.comp_smul]

variable {J : Type} [Finite J] (G : J → ModuleCat k)

def coproductPiEquiv : (∐ G : ModuleCat k) ≃ₗ[k] (∀ i, G i) :=
  ((biproduct.isoCoproduct G).symm ≪≫ ModuleCat.biproductIsoPi G).toLinearEquiv

lemma coproductPiEquiv_ι (i j : J) (x : G i) :
    coproductPiEquiv G (Sigma.ι G i x) j =
      (biproduct.ι G i ≫ biproduct.π G j) x := by
  have h : Sigma.ι G i ≫ (biproduct.isoCoproduct G).inv = biproduct.ι G i := by simp
  have h' : (ModuleCat.biproductIsoPi G).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π G j := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  change ((Sigma.ι G i ≫ (biproduct.isoCoproduct G).inv ≫
    (ModuleCat.biproductIsoPi G).hom ≫ ModuleCat.ofHom (LinearMap.proj j)) x) = _
  rw [h', ← Category.assoc, h]

lemma coproductPiEquiv_ι_self (i : J) (x : G i) :
    coproductPiEquiv G (Sigma.ι G i x) i = x := by
  rw [coproductPiEquiv_ι, biproduct.ι_π_self]
  rfl

lemma coproductPiEquiv_ι_ne {i j : J} (h : i ≠ j) (x : G i) :
    coproductPiEquiv G (Sigma.ι G i x) j = 0 := by
  rw [coproductPiEquiv_ι, biproduct.ι_π_ne _ h]
  rfl

end Tachikawa



namespace Tachikawa.TotalDualPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

instance : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (i : Multiplicative ℕ) => (-1 : ℤˣ)^i.toAdd)
    (fun i j => pow_add (-1 : ℤˣ) i.toAdd j.toAdd)
  rel_add p q r (h : p+1=q) := by change p+r+1=q+r; omega
  add_rel p q r (h : p+1=q) := by change r+p+1=r+q; omega
  ε'_succ := by
    intro p q h
    change p+1=q at h
    change (-1 : ℤˣ)^q = -(-1 : ℤˣ)^p
    subst q
    rw [pow_succ, mul_neg, mul_one]

abbrev Diag (n : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 = n}
variable (K : HomologicalComplex₂ (ModuleCat R) (.down ℕ) (.down ℕ))
  (G : HomologicalComplex₂ (ModuleCat k) (.up ℕ) (.up ℕ)) (N : ModuleCat R)
  (p : ∀ i j, (G.X i).X j ≃ₗ[k] ((K.X i).X j ⟶ N))

abbrev chainFamily (n : ℕ) (t : Diag n) : ModuleCat R := (K.X t.val.1).X t.val.2
abbrev cochainFamily (n : ℕ) (t : Diag n) : ModuleCat k := (G.X t.val.1).X t.val.2

instance (n : ℕ) : Finite (Diag n) := by
  let f : Diag n → Fin (n+1) × Fin (n+1) := fun t =>
    (⟨t.val.1, by have := t.property; omega⟩, ⟨t.val.2, by have := t.property; omega⟩)
  apply Finite.of_injective f
  intro t u h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : Fin (n+1) × Fin (n+1) => z.1.val) h)
    (congrArg (fun z : Fin (n+1) × Fin (n+1) => z.2.val) h)

def equiv (n : ℕ) : (G.total (.up ℕ)).X n ≃ₗ[k] ((K.total (.down ℕ)).X n ⟶ N) :=
  (coproductPiEquiv (cochainFamily G n)).trans
    ((LinearEquiv.piCongrRight (fun t : Diag n => p t.val.1 t.val.2)).trans
      (coproductHomEquiv (k := k) (chainFamily K n) N).symm)

lemma evaluate (n i j : ℕ) (h : i+j=n) (z : (G.total (.up ℕ)).X n) :
    K.ιTotal (.down ℕ) i j n h ≫ equiv K G N p n z =
      p i j (coproductPiEquiv (cochainFamily G n) z ⟨(i,j),h⟩) := by
  exact congrFun ((coproductHomEquiv (k := k) (chainFamily K n) N).apply_symm_apply
    (fun t : Diag n => p t.val.1 t.val.2 (coproductPiEquiv (cochainFamily G n) z t))) ⟨(i,j),h⟩

lemma evaluate_ι_self (n i j : ℕ) (h : i+j=n) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) i j n h ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) = p i j x := by
  rw [evaluate]
  change p i j (coproductPiEquiv (cochainFamily G n)
    (Sigma.ι (cochainFamily G n) ⟨(i,j),h⟩ x) ⟨(i,j),h⟩) = _
  rw [coproductPiEquiv_ι_self]

lemma evaluate_ι_ne (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n)
    (hne : (a,b) ≠ (i,j)) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) a b n h' ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) = 0 := by
  rw [evaluate]
  change p a b (coproductPiEquiv (cochainFamily G n)
    (Sigma.ι (cochainFamily G n) ⟨(i,j),h⟩ x) ⟨(a,b),h'⟩) = _
  rw [coproductPiEquiv_ι_ne _ (show (⟨(i,j),h⟩ : Diag n) ≠ ⟨(a,b),h'⟩ by
    intro he; exact hne (congrArg Subtype.val he).symm), map_zero]

end Tachikawa.TotalDualPairing



namespace Tachikawa.TotalDualPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [hk : CharP k 2]

lemma units_smul_eq {M : Type*} [AddCommGroup M] [Module k M] (u : ℤˣ) (x : M) : u • x = x := by
  rcases Int.units_eq_one_or u with h | h
  · rw [h, one_smul]
  · rw [h]
    change (-1 : ℤ) • x = x
    rw [neg_one_zsmul, ← neg_one_smul k, CharTwo.neg_eq (1 : k), one_smul]

variable (K : HomologicalComplex₂ (ModuleCat R) (.down ℕ) (.down ℕ))
  (G : HomologicalComplex₂ (ModuleCat k) (.up ℕ) (.up ℕ)) (N : ModuleCat R)
  (p : ∀ i j, (G.X i).X j ≃ₗ[k] ((K.X i).X j ⟶ N))

omit hk in
lemma up_d₁ (i j n : ℕ) (h : i+1+j=n) :
    G.d₁ (.up ℕ) i j n =
      (G.d i (i+1)).f j ≫ G.ιTotal (.up ℕ) (i+1) j n h := by
  rw [G.d₁_eq (.up ℕ) (show (ComplexShape.up ℕ).Rel i (i+1) from rfl) j n h]
  change (1 : ℤˣ) • _ = _
  exact one_smul _ _

lemma up_d₂ (i j n : ℕ) (h : i+(j+1)=n) :
    G.d₂ (.up ℕ) i j n =
      (G.X i).d j (j+1) ≫ G.ιTotal (.up ℕ) i (j+1) n h := by
  rw [G.d₂_eq (.up ℕ) i (show (ComplexShape.up ℕ).Rel j (j+1) from rfl) n h,
    units_smul_eq (k := k)]

lemma down_d₁ (i j n : ℕ) (h : i+j=n) :
    K.d₁ (.down ℕ) (i+1) j n =
      (K.d (i+1) i).f j ≫ K.ιTotal (.down ℕ) i j n h := by
  rw [K.d₁_eq (.down ℕ) (show (ComplexShape.down ℕ).Rel (i+1) i from rfl) j n h]
  change (1 : ℤˣ) • _ = _
  exact one_smul _ _

include hk in
lemma down_d₂ (i j n : ℕ) (h : i+j=n) :
    K.d₂ (.down ℕ) i (j+1) n =
      (K.X i).d (j+1) j ≫ K.ιTotal (.down ℕ) i j n h := by
  rw [K.d₂_eq (.down ℕ) i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl) n h,
    units_smul_eq (k := k)]

lemma down_d₁_zero (j n : ℕ) : K.d₁ (.down ℕ) 0 j n = 0 :=
  K.d₁_eq_zero (.down ℕ) 0 j n (by change ¬ _+1=0; omega)

lemma down_d₂_zero (i n : ℕ) : K.d₂ (.down ℕ) i 0 n = 0 :=
  K.d₂_eq_zero (.down ℕ) i 0 n (by change ¬ _+1=0; omega)

variable (hp₁ : ∀ i j (x : (G.X i).X j),
  p (i+1) j ((G.d i (i+1)).f j x) = (K.d (i+1) i).f j ≫ p i j x)
variable (hp₂ : ∀ i j (x : (G.X i).X j),
  p i (j+1) ((G.X i).d j (j+1) x) = (K.X i).d (j+1) j ≫ p i j x)

omit hk in
include hp₁ in
lemma horizontal (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n+1) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.d₁ (.up ℕ) i j (n+1) x) =
    K.d₁ (.down ℕ) a b n ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) := by
  rw [up_d₁ G i j (n+1) (by omega)]
  change K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.ιTotal (.up ℕ) (i+1) j (n+1) _ ((G.d i (i+1)).f j x)) = _
  cases a with
  | zero =>
    rw [down_d₁_zero, zero_comp]
    exact evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
      intro he
      have hc := congrArg (fun t : ℕ × ℕ => t.1) he
      dsimp at hc
      omega) _
  | succ a =>
    rw [down_d₁ K a b n (by omega), Category.assoc]
    by_cases hab : (a,b) = (i,j)
    · have ha := congrArg Prod.fst hab
      have hb := congrArg Prod.snd hab
      dsimp at ha hb
      subst a b
      rw [evaluate_ι_self, evaluate_ι_self]
      exact hp₁ i j x
    · rw [evaluate_ι_ne K G N p _ _ _ _ _ _ _ hab, comp_zero]
      exact evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
        intro he
        apply hab
        have h1 := congrArg (fun t : ℕ × ℕ => t.1) he
        have h2 := congrArg (fun t : ℕ × ℕ => t.2) he
        apply Prod.ext <;> dsimp at * <;> omega) _

include hp₂ in
lemma vertical (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n+1) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.d₂ (.up ℕ) i j (n+1) x) =
    K.d₂ (.down ℕ) a b n ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) := by
  rw [up_d₂ G i j (n+1) (by omega)]
  change K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.ιTotal (.up ℕ) i (j+1) (n+1) _ ((G.X i).d j (j+1) x)) = _
  cases b with
  | zero =>
    rw [down_d₂_zero, zero_comp]
    exact evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
      intro he
      have hc := congrArg (fun t : ℕ × ℕ => t.2) he
      dsimp at hc
      omega) _
  | succ b =>
    rw [down_d₂ (k := k) K a b n (by omega), Category.assoc]
    by_cases hab : (a,b) = (i,j)
    · have ha := congrArg Prod.fst hab
      have hb := congrArg Prod.snd hab
      dsimp at ha hb
      subst a b
      rw [evaluate_ι_self, evaluate_ι_self]
      exact hp₂ i j x
    · rw [evaluate_ι_ne K G N p _ _ _ _ _ _ _ hab, comp_zero]
      exact evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
        intro he
        apply hab
        have h1 := congrArg (fun t : ℕ × ℕ => t.1) he
        have h2 := congrArg (fun t : ℕ × ℕ => t.2) he
        apply Prod.ext <;> dsimp at * <;> omega) _

end Tachikawa.TotalDualPairing



namespace Tachikawa.TotalDualPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable (K : HomologicalComplex₂ (ModuleCat R) (.down ℕ) (.down ℕ))
  (G : HomologicalComplex₂ (ModuleCat k) (.up ℕ) (.up ℕ)) (N : ModuleCat R)
  (p : ∀ i j, (G.X i).X j ≃ₗ[k] ((K.X i).X j ⟶ N))
  (hp₁ : ∀ i j (x : (G.X i).X j),
    p (i+1) j ((G.d i (i+1)).f j x) = (K.d (i+1) i).f j ≫ p i j x)
  (hp₂ : ∀ i j (x : (G.X i).X j),
    p i (j+1) ((G.X i).d j (j+1) x) = (K.X i).d (j+1) j ≫ p i j x)

include hp₁ hp₂ in
lemma comm (n : ℕ) :
    (G.total (.up ℕ)).d n (n+1) ≫ ModuleCat.ofHom (equiv K G N p (n+1)).toLinearMap =
    ModuleCat.ofHom (equiv K G N p n).toLinearMap ≫
      (resolutionHom k R (K.total (.down ℕ)) N).d n (n+1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  erw [← Category.assoc, total_d, Preadditive.comp_add, ι_D₁, ι_D₂,
    Preadditive.add_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (equiv K G N p (n+1) (G.d₁ (.up ℕ) i j (n+1) x)) +
    (equiv K G N p (n+1) (G.d₂ (.up ℕ) i j (n+1) x)) =
    (K.total (.down ℕ)).d (n+1) n ≫
      (equiv K G N p n (G.ιTotal (.up ℕ) i j n h x))
  apply HomologicalComplex₂.total.hom_ext
  intro a b h'
  erw [Preadditive.comp_add, horizontal K G N p hp₁ n i j a b h h' x,
    vertical K G N p hp₂ n i j a b h h' x, ← Category.assoc,
    total_d, Preadditive.comp_add, ι_D₁, ι_D₂, Preadditive.add_comp]

def comparison : G.total (.up ℕ) ⟶ resolutionHom k R (K.total (.down ℕ)) N where
  f n := ModuleCat.ofHom (equiv K G N p n).toLinearMap
  comm' n n' h := by
    change n+1=n' at h
    subst n'
    exact (comm K G N p hp₁ hp₂ n).symm

instance : IsIso (comparison K G N p hp₁ hp₂) := by
  have (n : ℕ) : IsIso ((comparison K G N p hp₁ hp₂).f n) :=
    (equiv K G N p n).toModuleIso.isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

def iso : G.total (.up ℕ) ≅ resolutionHom k R (K.total (.down ℕ)) N :=
  asIso (comparison K G N p hp₁ hp₂)

end Tachikawa.TotalDualPairing



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (P : ChainComplex (ModuleCat A) ℕ) (Q : ChainComplex (ModuleCat B) ℕ)
  (U : ModuleCat A) (V : ModuleCat B)

abbrev homBicomplex := ((tensorF k).mapBifunctorHomologicalComplex (.up ℕ) (.up ℕ)).obj
  (resolutionHom k A P U) |>.obj (resolutionHom k B Q V)

variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Finite B (Q.X n)]
  [∀ n, Module.Projective A (P.X n)] [∀ n, Module.Projective B (Q.X n)]
  [∀ n, FiniteDimensional k (P.X n)] [∀ n, FiniteDimensional k (Q.X n)]

def homBicomplexEquiv (i j : ℕ) : ((homBicomplex (k := k) P Q U V).X i).X j ≃ₗ[k]
    (((outerBicomplex k A B P Q).X i).X j ⟶ ((bifunctor k A B).obj U).obj V) :=
  homEquiv (k := k) (P.X i) U (Q.X j) V

lemma precompose_id {M U : ModuleCat A} :
    precompose (k := k) (U := U) (𝟙 M) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  exact Category.id_comp f

lemma homBicomplexEquiv_horizontal (i j : ℕ) (x : ((homBicomplex (k := k) P Q U V).X i).X j) :
    homBicomplexEquiv P Q U V (i+1) j ((homBicomplex (k := k) P Q U V).d i (i+1) |>.f j <| x) =
      ((outerBicomplex k A B P Q).d (i+1) i).f j ≫ homBicomplexEquiv P Q U V i j x := by
  change (P.X i ⟶ U) ⊗[k] (Q.X j ⟶ V) at x
  change homMap (TensorProduct.map (precompose (k := k) (P.d (i+1) i)) LinearMap.id x) =
    morphism (P.d (i+1) i) (𝟙 (Q.X j)) ≫ homMap x
  have h := homMap_precompose (P.d (i+1) i) (𝟙 (Q.X j)) x
  rw [precompose_id] at h
  exact h

lemma homBicomplexEquiv_vertical (i j : ℕ) (x : ((homBicomplex (k := k) P Q U V).X i).X j) :
    homBicomplexEquiv P Q U V i (j+1) (((homBicomplex (k := k) P Q U V).X i).d j (j+1) x) =
      ((outerBicomplex k A B P Q).X i).d (j+1) j ≫ homBicomplexEquiv P Q U V i j x := by
  change (P.X i ⟶ U) ⊗[k] (Q.X j ⟶ V) at x
  change homMap (TensorProduct.map LinearMap.id (precompose (k := k) (Q.d (j+1) j)) x) =
    morphism (𝟙 (P.X i)) (Q.d (j+1) j) ≫ homMap x
  have h := homMap_precompose (𝟙 (P.X i)) (Q.d (j+1) j) x
  rw [precompose_id] at h
  exact h

variable [CharP k 2]

def homTotalIso :
    mapBifunctor (resolutionHom k A P U) (resolutionHom k B Q V) (tensorF k) (.up ℕ) ≅
    resolutionHom k (A ⊗[k] B) (mapBifunctor P Q (bifunctor k A B) (.down ℕ))
      (((bifunctor k A B).obj U).obj V) :=
  TotalDualPairing.iso (outerBicomplex k A B P Q) (homBicomplex (k := k) P Q U V) _
    (homBicomplexEquiv P Q U V) (homBicomplexEquiv_horizontal P Q U V)
    (homBicomplexEquiv_vertical P Q U V)

end Tachikawa.OuterTensor



namespace Tachikawa.VectorSplit
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}

def homologyIsoH (K : HomologicalComplex (ModuleCat k) c) (i : I) :
    K.homology i ≅ ModuleCat.of k (H K i) :=
  (homologyHomotopyEquiv K).toHomologyIso i ≪≫
    zeroDifferentialHomologyIso (homologyComplex K) (fun _ _ => rfl) i

end Tachikawa.VectorSplit



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B] [CharP k 2]
  {M U : ModuleCat A} {N V : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
  [∀ n, FiniteDimensional k (P.complex.X n)] [∀ n, FiniteDimensional k (Q.complex.X n)]

abbrev tensorResolution := resolution k A B P Q (fun _ => inferInstance) (fun _ => inferInstance)
abbrev homologyTensor := mapBifunctor
  (VectorSplit.homologyComplex (resolutionHom k A P.complex U))
  (VectorSplit.homologyComplex (resolutionHom k B Q.complex V)) (tensorF k) (.up ℕ)

def extKunneth (n : ℕ) :
    Ext (((bifunctor k A B).obj M).obj N) (((bifunctor k A B).obj U).obj V) n ≃ₗ[k]
      (∀ t : TotalDualPairing.Diag n, Ext M U t.val.1 ⊗[k] Ext N V t.val.2) := by
  let S := tensorResolution (k := k) P Q
  let H := resolutionHom k (A ⊗[k] B) S.complex (((bifunctor k A B).obj U).obj V)
  let e₁ := (resolutionHomologyExtAll (N := ((bifunctor k A B).obj U).obj V) S n (k := k)).symm
  let e₂ := (VectorSplit.homologyIsoH H n).symm.toLinearEquiv
  let e₃ := ((homologyFunctor (ModuleCat k) (.up ℕ) n).mapIso
    (homTotalIso P.complex Q.complex U V).symm).toLinearEquiv
  let e₄ := (VectorSplit.tensorHomologyIso (resolutionHom k A P.complex U)
    (resolutionHom k B Q.complex V) (.up ℕ) n).toLinearEquiv
  let e₅ := coproductPiEquiv (fun t : TotalDualPairing.Diag n =>
    ModuleCat.of k (VectorSplit.H (resolutionHom k A P.complex U) t.val.1 ⊗[k]
      VectorSplit.H (resolutionHom k B Q.complex V) t.val.2))
  let e₆ := LinearEquiv.piCongrRight (fun t : TotalDualPairing.Diag n =>
    TensorProduct.congr (resolutionHomologyExtAll (N := U) P t.val.1 (k := k))
      (resolutionHomologyExtAll (N := V) Q t.val.2 (k := k)))
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆))))

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)

@[reassoc]
lemma bifunctor_maps {M M' : ModuleCat A} {N N' : ModuleCat B}
    (u : M ⟶ M') (v : N ⟶ N') :
    ((bifunctor k A B).map u).app N ≫ ((bifunctor k A B).obj M').map v = morphism u v := by
  change morphism u (𝟙 N) ≫ morphism (𝟙 M') v = _
  rw [morphism_comp,Category.comp_id,Category.id_comp]

instance algebraTwist_preserves_projective {R : Type} [Ring R] [Algebra k R]
    (ρ : R ≃ₐ[k] R) : (algebraTwist ρ).PreservesProjectiveObjects := by
  have : (algebraTwist ρ).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv ρ.symm.toRingEquiv
  infer_instance

variable {M : ModuleCat A} {N : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (e : (algebraTwist σ).obj M ≅ M) (f : (algebraTwist τ).obj N ≅ N)
  (lP : ProjectiveResolution.Hom P (mappedResolution (algebraTwist σ) P) e.inv)
  (lQ : ProjectiveResolution.Hom Q (mappedResolution (algebraTwist τ) Q) f.inv)

def tensorTwistObjIso :
    (algebraTwist (Algebra.TensorProduct.congr σ τ)).obj (((bifunctor k A B).obj M).obj N) ≅
      (((bifunctor k A B).obj M).obj N) :=
  (twistObjIso σ τ M N).symm ≪≫
    { hom := morphism e.hom f.hom
      inv := morphism e.inv f.inv
      hom_inv_id := by rw [morphism_comp,e.hom_inv_id,f.hom_inv_id,morphism_id]
      inv_hom_id := by rw [morphism_comp,e.inv_hom_id,f.inv_hom_id,morphism_id] }

abbrev tensorTwistLiftHom :=
  mapBifunctorMap lP.hom lQ.hom (bifunctor k A B) (.down ℕ) ≫
    (twistTotalIso σ τ P.complex Q.complex (.down ℕ)).hom

@[reassoc]
lemma ι_tensorTwistLiftHom (i j n : ℕ) (h : i+j=n) :
    ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) i j n h ≫
      (tensorTwistLiftHom σ τ P Q e f lP lQ).f n =
    morphism (lP.hom.f i) (lQ.hom.f j) ≫
      (twistObjIso σ τ (P.complex.X i) (Q.complex.X j)).hom ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map
        (ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) i j n h) := by
  dsimp only [mappedResolution] at lP lQ ⊢
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc,ι_mapBifunctorMap]
  simp only [Category.assoc]
  rw [bifunctor_maps_assoc]
  change morphism (lP.hom.f i) (lQ.hom.f j) ≫
    ιMapBifunctor (twistComplex σ P.complex) (twistComplex τ Q.complex)
      (bifunctor k A B) (.down ℕ) i j n h ≫
      (twistTotalIso σ τ P.complex Q.complex (.down ℕ)).hom.f n = _
  exact congrArg (fun morph => morphism (lP.hom.f i) (lQ.hom.f j) ≫ morph)
    (ι_twistTotalIso σ τ P.complex Q.complex (.down ℕ) i j n h)

variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]

lemma ι_resolution_π_zero :
    ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) 0 0 0 rfl ≫
      (tensorResolution (k := k) P Q).π.f 0 = morphism (P.π.f 0) (Q.π.f 0) := by
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc,ι_mapBifunctorMap]
  simp only [Category.assoc]
  erw [bifunctor_maps_assoc]
  change _ ≫ (bifunctorZeroIso (bifunctor k A B) _ _).inv ≫
    (bifunctorZeroIso (bifunctor k A B) _ _).hom = _
  rw [Iso.inv_hom_id,Category.comp_id]

def tensorTwistLift : ProjectiveResolution.Hom (tensorResolution (k := k) P Q)
    (mappedResolution (algebraTwist (Algebra.TensorProduct.congr σ τ))
      (tensorResolution (k := k) P Q)) (tensorTwistObjIso σ τ e f).inv where
  hom := tensorTwistLiftHom σ τ P Q e f lP lQ
  hom_f_zero_comp_π_f_zero := by
    dsimp only [mappedResolution] at lP lQ ⊢
    apply (cancel_epi (bifunctorZeroIso (bifunctor k A B) P.complex Q.complex).inv).mp
    change ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) 0 0 0 rfl ≫
      ((tensorTwistLiftHom σ τ P Q e f lP lQ).f 0 ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map ((tensorResolution (k := k) P Q).π.f 0)) =
      ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) 0 0 0 rfl ≫
      ((tensorResolution (k := k) P Q).π.f 0 ≫ (tensorTwistObjIso σ τ e f).inv)
    rw [← Category.assoc,ι_tensorTwistLiftHom]
    simp only [Category.assoc]
    erw [Category.assoc (twistObjIso σ τ (P.complex.X 0) (Q.complex.X 0)).hom,
      ← (algebraTwist (Algebra.TensorProduct.congr σ τ)).map_comp
        (ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) 0 0 0 rfl)
        ((tensorResolution (k := k) P Q).π.f 0),
      ι_resolution_π_zero,
      ← twistObjIso_natural σ τ (P.π.f 0) (Q.π.f 0),
      ← Category.assoc,← Category.assoc,
      morphism_comp (lP.hom.f 0) ((algebraTwist σ).map (P.π.f 0))
        (lQ.hom.f 0) ((algebraTwist τ).map (Q.π.f 0))]
    have hp : lP.hom.f 0 ≫ (algebraTwist σ).map (P.π.f 0) = P.π.f 0 ≫ e.inv :=
      lP.hom_f_zero_comp_π_f_zero
    have hq : lQ.hom.f 0 ≫ (algebraTwist τ).map (Q.π.f 0) = Q.π.f 0 ≫ f.inv :=
      lQ.hom_f_zero_comp_π_f_zero
    erw [hp,hq,← morphism_comp (P.π.f 0) e.inv (Q.π.f 0) f.inv,
      Category.assoc,ι_resolution_π_zero]
    rfl

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
@[reassoc]
lemma tensorF_maps {k : Type} [Field k] {U U' V V' : ModuleCat k}
    (u : U ⟶ U') (v : V ⟶ V') :
    ((tensorF k).map u).app V ≫ ((tensorF k).obj U').map v =
      ModuleCat.ofHom (TensorProduct.map u.hom v.hom) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add,hx,hy]

variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  [CharP k 2]
  {M : ModuleCat A} {N : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
  [∀ n, FiniteDimensional k (P.complex.X n)] [∀ n, FiniteDimensional k (Q.complex.X n)]

lemma homTotal_evaluate (n i j : ℕ) (h : i+j=n)
    (z : (P.complex.X i ⟶ M) ⊗[k] (Q.complex.X j ⟶ N)) :
    ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) i j n h ≫
      (homTotalIso P.complex Q.complex M N).hom.f n
        (ιMapBifunctor (resolutionHom k A P.complex M) (resolutionHom k B Q.complex N)
          (tensorF k) (.up ℕ) i j n h z) = homMap z :=
  TotalDualPairing.evaluate_ι_self _ _ _ (homBicomplexEquiv P.complex Q.complex M N) n i j h z

lemma homTotal_evaluate_ne (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n)
    (hne : (a,b) ≠ (i,j)) (z : (P.complex.X i ⟶ M) ⊗[k] (Q.complex.X j ⟶ N)) :
    ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) a b n h' ≫
      (homTotalIso P.complex Q.complex M N).hom.f n
        (ιMapBifunctor (resolutionHom k A P.complex M) (resolutionHom k B Q.complex N)
          (tensorF k) (.up ℕ) i j n h z) = 0 :=
  TotalDualPairing.evaluate_ι_ne _ _ _ (homBicomplexEquiv P.complex Q.complex M N) n i j a b h h' hne z

variable (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)
  (e : (algebraTwist σ).obj M ≅ M) (f : (algebraTwist τ).obj N ≅ N)
  (lP : ProjectiveResolution.Hom P (mappedResolution (algebraTwist σ) P) e.inv)
  (lQ : ProjectiveResolution.Hom Q (mappedResolution (algebraTwist τ) Q) f.inv)

abbrev tensorResolutionTwist := resolutionTwistHom (k := k)
  (algebraTwist (Algebra.TensorProduct.congr σ τ)) (tensorResolution (k := k) P Q)
  (tensorTwistObjIso σ τ e f) (tensorTwistLift σ τ P Q e f lP lQ).hom

omit [CharP k 2] [∀ n, Module.Finite A (P.complex.X n)]
  [∀ n, Module.Finite B (Q.complex.X n)]
  [∀ n, FiniteDimensional k (P.complex.X n)]
  [∀ n, FiniteDimensional k (Q.complex.X n)] in
lemma homMap_twist (i j : ℕ) (z : (P.complex.X i ⟶ M) ⊗[k] (Q.complex.X j ⟶ N)) :
    homMap (TensorProduct.map
      ((resolutionTwistHom (k := k) (algebraTwist σ) P e lP.hom).f i).hom
      ((resolutionTwistHom (k := k) (algebraTwist τ) Q f lQ.hom).f j).hom z) =
    morphism (lP.hom.f i) (lQ.hom.f j) ≫
      (twistObjIso σ τ (P.complex.X i) (Q.complex.X j)).hom ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map (homMap z) ≫
      (tensorTwistObjIso σ τ e f).hom := by
  dsimp only [mappedResolution] at lP lQ ⊢
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
    change morphism (lP.hom.f i ≫ (algebraTwist σ).map u ≫ e.hom)
      (lQ.hom.f j ≫ (algebraTwist τ).map v ≫ f.hom) =
      morphism (lP.hom.f i) (lQ.hom.f j) ≫
        (twistObjIso σ τ (P.complex.X i) (Q.complex.X j)).hom ≫
        (algebraTwist (Algebra.TensorProduct.congr σ τ)).map (morphism u v) ≫
        (twistObjIso σ τ M N).inv ≫ morphism e.hom f.hom
    refine (morphism_comp (lP.hom.f i) ((algebraTwist σ).map u ≫ e.hom)
      (lQ.hom.f j) ((algebraTwist τ).map v ≫ f.hom)).symm.trans ?_
    apply congrArg (fun morph => morphism (lP.hom.f i) (lQ.hom.f j) ≫ morph)
    refine (morphism_comp ((algebraTwist σ).map u) e.hom
      ((algebraTwist τ).map v) f.hom).symm.trans ?_
    exact (congrArg (fun morph => morph ≫ morphism e.hom f.hom)
      ((Iso.eq_comp_inv (twistObjIso σ τ M N)).mpr
        (twistObjIso_natural σ τ u v))).trans (by simp only [Category.assoc]; rfl)
  | add z w hz hw =>
    exact (congrArg homMap (map_add _ z w)).trans ((map_add homMap _ _).trans
      ((congrArg₂ (· + ·) hz hw).trans (by
        erw [map_add, Functor.map_add, Preadditive.add_comp,
          Preadditive.comp_add, Preadditive.comp_add]
        rfl)))

lemma homTotal_twist :
    mapBifunctorMap (resolutionTwistHom (k := k) (algebraTwist σ) P e lP.hom)
      (resolutionTwistHom (k := k) (algebraTwist τ) Q f lQ.hom) (tensorF k) (.up ℕ) ≫
      (homTotalIso P.complex Q.complex M N).hom =
    (homTotalIso P.complex Q.complex M N).hom ≫ tensorResolutionTwist P Q σ τ e f lP lQ := by
  dsimp only [mappedResolution] at lP lQ ⊢
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro i j h
  change _ ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  rw [← Category.assoc,ι_mapBifunctorMap]
  simp only [Category.assoc]
  rw [tensorF_maps_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (P.complex.X i ⟶ M) ⊗[k] (Q.complex.X j ⟶ N) at z
  change (homTotalIso P.complex Q.complex M N).hom.f n
    (ιMapBifunctor (resolutionHom k A P.complex M) (resolutionHom k B Q.complex N)
      (tensorF k) (.up ℕ) i j n h
      (TensorProduct.map
        ((resolutionTwistHom (k := k) (algebraTwist σ) P e lP.hom).f i).hom
        ((resolutionTwistHom (k := k) (algebraTwist τ) Q f lQ.hom).f j).hom z)) =
    (tensorTwistLiftHom σ τ P Q e f lP lQ).f n ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map
        ((homTotalIso P.complex Q.complex M N).hom.f n
          (ιMapBifunctor (resolutionHom k A P.complex M) (resolutionHom k B Q.complex N)
      (tensorF k) (.up ℕ) i j n h z)) ≫ (tensorTwistObjIso σ τ e f).hom
  apply mapBifunctor.hom_ext
  intro a b h'
  rw [← Category.assoc,ι_tensorTwistLiftHom]
  simp only [Category.assoc]
  erw [Category.assoc,← Functor.map_comp_assoc]
  by_cases hab : (a,b) = (i,j)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hab
    erw [homTotal_evaluate,homTotal_evaluate]
    exact homMap_twist P Q σ τ e f lP lQ a b z
  · erw [homTotal_evaluate_ne P Q n i j a b h h' hab,
      homTotal_evaluate_ne P Q n i j a b h h' hab]
    erw [Functor.map_zero,zero_comp,comp_zero]

end Tachikawa.OuterTensor

end

end OAI
