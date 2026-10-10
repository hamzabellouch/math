import OAI.RingTheory.Tachikawa.DerivedInduction

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R S : Type} [Ring R] [Ring S]

def cokerLinearEquiv {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B] [Module R C] [Module R D]
    (f : A →ₗ[R] B) (g : C →ₗ[R] D) (e : A ≃ₗ[R] C) (v : B ≃ₗ[R] D)
    (h : v.toLinearMap.comp f = g.comp e.toLinearMap) :
    (B ⧸ LinearMap.range f) ≃ₗ[R] (D ⧸ LinearMap.range g) :=
  Submodule.Quotient.equiv _ _ v (by
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,rfl⟩
      exact ⟨e z,(LinearMap.congr_fun h z).symm⟩
    · rintro ⟨y,rfl⟩
      obtain ⟨z,rfl⟩ := e.surjective y
      exact ⟨f z,⟨z,rfl⟩,LinearMap.congr_fun h z⟩)

def resolutionReflectCokerEquiv {M : ModuleCat.{0} R} (P : ProjectiveResolution M)
    (F : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] (n : ℕ) :
    CokerAt (reflectCochain ((F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)) n ≃ₗ[S]
      (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).X n ⧸
        LinearMap.range (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).d (n+1) n).hom) := by
  let e₁ := F.mapIso (P.cochainComplexXIso (-((n:ℤ)+1)) (n+1) (by omega))
  let e₂ := F.mapIso (P.cochainComplexXIso (-(n:ℤ)) n)
  apply cokerLinearEquiv _ _ e₁.toLinearEquiv e₂.toLinearEquiv
  apply ModuleCat.hom_ext_iff.mp
  change F.map (P.cochainComplex.d _ _) ≫ F.map _ = F.map _ ≫ F.map (P.complex.d _ _)
  rw [P.cochainComplex_d (-((n:ℤ)+1)) (-(n:ℤ)) (n+1) n (by omega) rfl]
  simp only [← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

namespace FiniteModule
variable {k : Type} [Field k] [Algebra k R] [FiniteDimensional k R] (M : FiniteModule k R)
lemma pos_cover_exact (n : ℕ) :
    Function.Exact (M.posDifferential n) (M.positive n).cover.map := by
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (M.positive (n+1)).cover.surjective ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩
  · rintro ⟨y,rfl⟩
    exact ((M.positive (n+1)).cover.map y).property

def naturalCokerPositiveEquiv (n : ℕ) :
    (M.projectiveResolution.complex.X n ⧸ LinearMap.range (M.projectiveResolution.complex.d (n+1) n).hom)
      ≃ₗ[R] (M.positive n).obj := by
  have hd : (M.projectiveResolution.complex.d (n+1) n).hom = M.posDifferential n := by
    dsimp only [projectiveResolution, resolutionOfExact]
    exact congrArg ModuleCat.Hom.hom (ChainComplex.of_d _ _ n)
  change (M.posTerm n ⧸ LinearMap.range (M.projectiveResolution.complex.d (n+1) n).hom) ≃ₗ[R] _
  exact (Submodule.quotEquivOfEq _ _ (hd ▸ (M.pos_cover_exact n).linearMap_ker_eq.symm)).trans
    ((M.positive n).cover.map.quotKerEquivOfSurjective (M.positive n).cover.surjective)

def reflectCokerPositiveEquiv (n : ℕ) :
    CokerAt (reflectCochain M.projectiveResolution.cochainComplex) n ≃ₗ[R] (M.positive n).obj :=
  (resolutionReflectCokerEquiv M.projectiveResolution (𝟭 (ModuleCat R)) n).trans
    (M.naturalCokerPositiveEquiv n)
end FiniteModule
end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev natJJ := mapBifunctor (C.inducedComplex q hp) (C.inducedComplex q hp)
  (OuterTensor.bifunctor k (T q) (T q)) (.down ℕ)
abbrev natJJDouble := ((OuterTensor.bifunctor k (T q) (T q)).mapBifunctorHomologicalComplex
  (.down ℕ) (.down ℕ)).obj (C.inducedComplex q hp) |>.obj (C.inducedComplex q hp)
abbrev intJJDouble := ((OuterTensor.bifunctor k (T q) (T q)).mapBifunctorHomologicalComplex
  (.down ℤ) (.down ℤ)).obj (forwardJ q hp) |>.obj (forwardJ q hp)

def jjNatIntX (n : ℕ) : (natJJ q hp).X n ⟶ (forwardJJ q hp).X (n:ℤ) :=
  (natJJDouble q hp).totalDesc (c₁₂ := .down ℕ) (fun i j h =>
    (intJJDouble q hp).ιTotal (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) (by
      change (i:ℤ)+(j:ℤ)=(n:ℤ); change i+j=n at h; omega))

@[reassoc (attr := simp)] lemma ι_jjNatIntX (i j n : ℕ) (h : i+j=n) :
    (natJJDouble q hp).ιTotal (.down ℕ) i j n h ≫ jjNatIntX q hp n =
      (intJJDouble q hp).ιTotal (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) (by
        change (i:ℤ)+(j:ℤ)=(n:ℤ); omega) := by
  apply ι_totalDesc

def jjIntNatComponent (n : ℕ) (i j : ℤ) (h : i+j=(n:ℤ)) :
    ((intJJDouble q hp).X i).X j ⟶ (natJJ q hp).X n := by
  cases i with
  | ofNat i =>
    cases j with
    | ofNat j => exact (natJJDouble q hp).ιTotal (.down ℕ) i j n (by change i+j=n; dsimp at h; omega)
    | negSucc j => exact 0
  | negSucc i => exact 0

def jjIntNatX (n : ℕ) : (forwardJJ q hp).X (n:ℤ) ⟶ (natJJ q hp).X n :=
  (intJJDouble q hp).totalDesc (c₁₂ := .down ℤ) (jjIntNatComponent q hp n)

@[reassoc (attr := simp)] lemma ι_jjIntNatX (i j : ℤ) (n : ℕ) (h : i+j=(n:ℤ)) :
    (intJJDouble q hp).ιTotal (.down ℤ) i j (n:ℤ) h ≫ jjIntNatX q hp n =
      jjIntNatComponent q hp n i j h := by
  apply ι_totalDesc

def jjNatIntIso (n : ℕ) : (natJJ q hp).X n ≅ (forwardJJ q hp).X (n:ℤ) where
  hom := jjNatIntX q hp n
  inv := jjIntNatX q hp n
  hom_inv_id := by
    apply total.hom_ext
    intro i j h
    simp only [ι_jjNatIntX_assoc, Category.comp_id]
    erw [ι_jjIntNatX q hp (i:ℤ) (j:ℤ) n]
    rfl
  inv_hom_id := by
    apply total.hom_ext
    intro i j h
    rw [ι_jjIntNatX_assoc, Category.comp_id]
    cases i with
    | ofNat i =>
      cases j with
      | ofNat j => exact ι_jjNatIntX q hp i j n (by dsimp at h; omega)
      | negSucc j =>
        apply (OuterTensor.isZero_obj_right _ _ (forwardJ_below q hp _ (by omega))).eq_of_src
    | negSucc i =>
      apply (OuterTensor.isZero_obj_left _ _ (forwardJ_below q hp _ (by omega))).eq_of_src




lemma forwardJ_d_nat (n : ℕ) : (forwardJ q hp).d ((n:ℤ)+1) (n:ℤ) = C.inducedD q n := by
  change (TrivialInduction.functor (k := k)).map ((C.forwardComplex q hp).d ((n:ℤ)+1) n) = _
  rw [show (C.forwardComplex q hp).d ((n:ℤ)+1) n = C.forwardD q n from ChainComplex.of_d _ _ _]
  rfl

lemma forwardJ_d_bottom : (forwardJ q hp).d 0 (-1) = 0 := by
  change (TrivialInduction.functor (k := k)).map ((C.forwardComplex q hp).d 0 (-1)) = _
  have h : (C.forwardComplex q hp).d 0 (-1) = 0 := by
    change ChainComplex.of.d (C.forwardObj q) (C.forwardD q) 0 (-1) = 0
    simp only [ChainComplex.of.d, dite_eq_left (show (0:ℤ) = -1 + 1 from rfl)]
    rfl
  rw [h, Functor.map_zero]

lemma jjNatInt_d₁ (i j n : ℕ) (h : i+j=n+1) :
    (natJJDouble q hp).d₁ (.down ℕ) i j n ≫ jjNatIntX q hp n =
      (intJJDouble q hp).d₁ (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) := by
  cases i with
  | zero =>
    erw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by change ¬ _+1=0; omega), zero_comp,
      HomologicalComplex₂.d₁_eq' _ _ (show (ComplexShape.down ℤ).Rel 0 (-1) from rfl)]
    change 0 = (1:ℤˣ) • (((OuterTensor.bifunctor k (T q) (T q)).map
      ((forwardJ q hp).d 0 (-1) )).app ((forwardJ q hp).X (j:ℤ))) ≫ _
    erw [forwardJ_d_bottom, Functor.map_zero, NatTrans.app_zero, zero_comp, smul_zero]
  | succ i =>
    rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℕ).Rel (i+1) i from rfl)
        j n (by change i+j=n; omega),
      HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.down ℤ).Rel ((i+1:ℕ):ℤ) (i:ℤ) from rfl)
        (j:ℤ) (n:ℤ) (by change (i:ℤ)+(j:ℤ)=(n:ℤ); omega)]
    change ((1:ℤˣ) • (((OuterTensor.bifunctor k (T q) (T q)).map
      ((C.inducedComplex q hp).d (i+1) i)).app ((C.inducedComplex q hp).X j)) ≫ _) ≫ _ =
      (1:ℤˣ) • (((OuterTensor.bifunctor k (T q) (T q)).map
      ((forwardJ q hp).d ((i:ℤ)+1) (i:ℤ) )).app ((forwardJ q hp).X (j:ℤ))) ≫ _
    erw [one_smul, one_smul, Category.assoc, ι_jjNatIntX,
      C.inducedComplex_d, forwardJ_d_nat]
    rfl

lemma natIntSign (i : ℕ) : (i:ℤ).negOnePow = (-1:ℤˣ)^i := by
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using Int.coe_negOnePow_natCast i

lemma jjNatInt_d₂ (i j n : ℕ) (h : i+j=n+1) :
    (natJJDouble q hp).d₂ (.down ℕ) i j n ≫ jjNatIntX q hp n =
      (intJJDouble q hp).d₂ (.down ℤ) (i:ℤ) (j:ℤ) (n:ℤ) := by
  cases j with
  | zero =>
    erw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by change ¬ _+1=0; omega), zero_comp,
      HomologicalComplex₂.d₂_eq' _ _ (i:ℤ) (show (ComplexShape.down ℤ).Rel 0 (-1) from rfl)]
    change 0 = (i:ℤ).negOnePow • (((OuterTensor.bifunctor k (T q) (T q)).obj
      ((forwardJ q hp).X (i:ℤ) )).map ((forwardJ q hp).d 0 (-1))) ≫ _
    erw [forwardJ_d_bottom, Functor.map_zero, zero_comp, smul_zero]
  | succ j =>
    rw [HomologicalComplex₂.d₂_eq _ _ i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl)
        n (by change i+j=n; omega),
      HomologicalComplex₂.d₂_eq _ _ (i:ℤ) (show (ComplexShape.down ℤ).Rel ((j+1:ℕ):ℤ) (j:ℤ) from rfl)
        (n:ℤ) (by change (i:ℤ)+(j:ℤ)=(n:ℤ); omega)]
    change (((-1:ℤˣ)^i) • (((OuterTensor.bifunctor k (T q) (T q)).obj
      ((C.inducedComplex q hp).X i)).map ((C.inducedComplex q hp).d (j+1) j)) ≫ _) ≫ _ =
      (i:ℤ).negOnePow • (((OuterTensor.bifunctor k (T q) (T q)).obj
      ((forwardJ q hp).X (i:ℤ) )).map ((forwardJ q hp).d ((j:ℤ)+1) (j:ℤ))) ≫ _
    erw [Linear.units_smul_comp, Category.assoc, ι_jjNatIntX,
      C.inducedComplex_d, forwardJ_d_nat, natIntSign]
    rfl

lemma jjNatInt_d (n : ℕ) :
    jjNatIntX q hp (n+1) ≫ (forwardJJ q hp).d ((n+1:ℕ):ℤ) (n:ℤ) =
      (natJJ q hp).d (n+1) n ≫ jjNatIntX q hp n := by
  apply total.hom_ext
  intro i j h
  rw [ι_jjNatIntX_assoc]
  simp only [total_d, Preadditive.comp_add, Preadditive.add_comp,
    ι_D₁_assoc, ι_D₂_assoc]
  rw [jjNatInt_d₁ q hp i j n h, jjNatInt_d₂ q hp i j n h]
  erw [Preadditive.comp_add, ι_D₁, ι_D₂]

def jjNatIntCokerEquiv (n : ℕ) :
    ((natJJ q hp).X (n+1) ⧸ LinearMap.range ((natJJ q hp).d (n+2) (n+1)).hom) ≃ₗ[E q]
      CokerAt (forwardJJ q hp) ((n+1:ℕ):ℤ) :=
  cokerLinearEquiv _ _ (jjNatIntIso q hp (n+2)).toLinearEquiv
    (jjNatIntIso q hp (n+1)).toLinearEquiv
    (ModuleCat.hom_ext_iff.mp (jjNatInt_d q hp (n+1)).symm)

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

abbrev StableMap (M N : ModuleCat.{0} R) :=
  StableHom (k := k) (R := R) (M := M) (N := N)

structure StableEquiv (M N : ModuleCat.{0} R) where
  hom : M →ₗ[R] N
  inv : N →ₗ[R] M
  inv_hom : inv.comp hom - LinearMap.id ∈ projectiveFactors (k := k)
  hom_inv : hom.comp inv - LinearMap.id ∈ projectiveFactors (k := k)

variable {M N L : ModuleCat.{0} R}

lemma stableClass_eq_iff (f g : M →ₗ[R] N) :
    stableClass (k := k) f = stableClass (k := k) g ↔
      f-g ∈ projectiveFactors (k := k) := by
  rw [← sub_eq_zero, ← map_sub, stableClass_eq_zero_iff]

def stablePrecompose (g : L →ₗ[R] M) : StableMap (k := k) M N →ₗ[k] StableMap (k := k) L N :=
  (projectiveFactors (k := k)).mapQ (projectiveFactors (k := k))
    (homPrecompose g) (fun _ hf => projectiveFactors_precomp hf g)

@[simp] lemma stablePrecompose_class (g : L →ₗ[R] M) (f : M →ₗ[R] N) :
    stablePrecompose (k := k) g (stableClass (k := k) f) =
      stableClass (k := k) (f.comp g) := rfl

namespace StableEquiv

def refl (M : ModuleCat.{0} R) : StableEquiv (k := k) M M where
  hom := LinearMap.id
  inv := LinearMap.id
  inv_hom := by simp only [LinearMap.id_comp, sub_self]; exact Submodule.zero_mem _
  hom_inv := by simp only [LinearMap.id_comp, sub_self]; exact Submodule.zero_mem _

def symm (e : StableEquiv (k := k) M N) : StableEquiv (k := k) N M where
  hom := e.inv
  inv := e.hom
  inv_hom := e.hom_inv
  hom_inv := e.inv_hom

def ofLinearEquiv (e : M ≃ₗ[R] N) : StableEquiv (k := k) M N where
  hom := e.toLinearMap
  inv := e.symm.toLinearMap
  inv_hom := by
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; exact e.symm_apply_apply x
    rw [h, sub_self]; exact Submodule.zero_mem _
  hom_inv := by
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext x; exact e.apply_symm_apply x
    rw [h, sub_self]; exact Submodule.zero_mem _

lemma post_inverse (e : StableEquiv (k := k) M N) (f : L →ₗ[R] M) :
    stableClass (k := k) (e.inv.comp (e.hom.comp f)) = stableClass (k := k) f := by
  apply (stableClass_eq_iff _ _).mpr
  have h := projectiveFactors_precomp e.inv_hom f
  simpa only [LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc] using h

lemma pre_inverse (e : StableEquiv (k := k) M N) (f : M →ₗ[R] L) :
    stableClass (k := k) ((f.comp e.inv).comp e.hom) = stableClass (k := k) f := by
  apply (stableClass_eq_iff _ _).mpr
  have h := projectiveFactors_postcomp e.inv_hom f
  simpa only [LinearMap.comp_sub, LinearMap.comp_id, LinearMap.comp_assoc] using h

def post (e : StableEquiv (k := k) M N) (L : ModuleCat.{0} R) :
    StableMap (k := k) L M ≃ₗ[k] StableMap (k := k) L N :=
  { stablePostcompose e.hom with
    invFun := stablePostcompose e.inv
    left_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.post_inverse f
    right_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.symm.post_inverse f }

def pre (e : StableEquiv (k := k) M N) (L : ModuleCat.{0} R) :
    StableMap (k := k) M L ≃ₗ[k] StableMap (k := k) N L :=
  { stablePrecompose e.inv with
    invFun := stablePrecompose e.hom
    left_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.pre_inverse f
    right_inv := by
      intro x
      obtain ⟨f,rfl⟩ := stableClass_surjective x
      exact e.symm.pre_inverse f }

def trans (e : StableEquiv (k := k) M N) (d : StableEquiv (k := k) N L) :
    StableEquiv (k := k) M L where
  hom := d.hom.comp e.hom
  inv := e.inv.comp d.inv
  inv_hom := by
    have h := projectiveFactors_postcomp (projectiveFactors_precomp d.inv_hom e.hom) e.inv
    have heq : (e.inv.comp d.inv).comp (d.hom.comp e.hom) - LinearMap.id =
        (e.inv.comp ((d.inv.comp d.hom - LinearMap.id).comp e.hom)) +
        (e.inv.comp e.hom - LinearMap.id) := by
      simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
        LinearMap.comp_assoc]
      abel
    rw [heq]
    exact Submodule.add_mem _ h e.inv_hom
  hom_inv := by
    have h := projectiveFactors_postcomp (projectiveFactors_precomp e.hom_inv d.inv) d.hom
    have heq : (d.hom.comp e.hom).comp (e.inv.comp d.inv) - LinearMap.id =
        (d.hom.comp ((e.hom.comp e.inv - LinearMap.id).comp d.inv)) +
        (d.hom.comp d.inv - LinearMap.id) := by
      simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
        LinearMap.comp_assoc]
      abel
    rw [heq]
    exact Submodule.add_mem _ h d.hom_inv

end StableEquiv
end Tachikawa



namespace Tachikawa.NatCoker
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q S : ChainComplex (ModuleCat.{0} R) ℕ}

abbrev obj (P : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) := ModuleCat.of R (C P n)

def map (f : P ⟶ Q) (n : ℕ) : C P n →ₗ[R] C Q n :=
  (LinearMap.range (P.d (n+2) (n+1)).hom).liftQ ((π Q n).comp (f.f (n+1)).hom) (by
    rintro _ ⟨x,rfl⟩
    change π Q n (f.f (n+1) (P.d (n+2) (n+1) x)) = 0
    have h := congrArg (fun g : P.X (n+2) ⟶ Q.X (n+1) => g x) (f.comm (n+2) (n+1)).symm
    change f.f (n+1) (P.d (n+2) (n+1) x) = Q.d (n+2) (n+1) (f.f (n+2) x) at h
    rw [h]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_,rfl⟩)

@[simp] lemma map_π (f : P ⟶ Q) (n : ℕ) (x : P.X (n+1)) :
    map f n (π P n x) = π Q n (f.f (n+1) x) := rfl

@[simp] lemma map_id (n : ℕ) : map (𝟙 P) n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

@[simp] lemma map_comp (f : P ⟶ Q) (g : Q ⟶ S) (n : ℕ) :
    map (f ≫ g) n = (map g n).comp (map f n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

lemma homotopy_factors (f g : P ⟶ Q) (h : Homotopy f g) (n : ℕ)
    [Module.Finite R (P.X n)] [Module.Projective R (P.X n)] :
    map f n - map g n ∈ projectiveFactors (k := k)
      (M := obj P n) (N := obj Q n) := by
  have he : map f n - map g n =
      ((π Q n).comp (h.hom n (n+1)).hom).comp (ι P n) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := Submodule.mkQ_surjective _ x
    have hc := h.comm (n+1)
    rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n+1) n from rfl),
      prevD_eq _ (show (ComplexShape.down ℕ).Rel (n+2) (n+1) from rfl)] at hc
    have hx := congrArg (fun u : P.X (n+1) ⟶ Q.X (n+1) => π Q n (u y)) hc
    change π Q n (f.f (n+1) y) = π Q n
      ((h.hom n (n+1)) (P.d (n+1) n y) +
        Q.d (n+2) (n+1) (h.hom (n+1) (n+2) y) + g.f (n+1) y) at hx
    have hz : π Q n (Q.d (n+2) (n+1) (h.hom (n+1) (n+2) y)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨_,rfl⟩
    simp only [map_add, hz, add_zero] at hx
    change π Q n (f.f (n+1) y) - π Q n (g.f (n+1) y) = _
    rw [hx, add_sub_cancel_right]
    rfl
  rw [he]
  exact ⟨P.X n,inferInstance,inferInstance,ι P n,
    (π Q n).comp (h.hom n (n+1)).hom,rfl⟩

def stableEquiv (e : HomotopyEquiv P Q) (n : ℕ)
    [Module.Finite R (P.X n)] [Module.Projective R (P.X n)]
    [Module.Finite R (Q.X n)] [Module.Projective R (Q.X n)] :
    StableEquiv (k := k) (obj P n) (obj Q n) where
  hom := map e.hom n
  inv := map e.inv n
  inv_hom := by
    simpa only [map_comp, map_id] using homotopy_factors _ _ e.homotopyHomInvId n
  hom_inv := by
    simpa only [map_comp, map_id] using homotopy_factors _ _ e.homotopyInvHomId n

end Tachikawa.NatCoker



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

lemma reverseJJ_above (j : ℤ) (hj : 4 < j) : IsZero ((reverseJJ q hq).X j) :=
  OuterTensor.total_isZero_above_int _ _ 2 2 (reverseJ_above q hq) (reverseJ_above q hq) j hj

def jjFiberHighEquiv (j : ℤ) (hj : 4 ≤ j) :
    (jjFiber q hq hp).X j ≃ₗ[E q] (forwardJJ q hp).X j := by
  let : Subsingleton ((reverseJJ q hq).X (j+1)) :=
    ModuleCat.subsingleton_of_isZero (reverseJJ_above q hq (j+1) (by omega))
  exact LinearEquiv.ofBijective (LinearMap.snd (E q) ((reverseJJ q hq).X (j+1)) _) ⟨
    fun x y h => Prod.ext (Subsingleton.elim _ _) h, fun y => ⟨(0,y),rfl⟩⟩

@[simp] lemma jjFiberHighEquiv_apply (j : ℤ) (hj : 4 ≤ j) (x : (jjFiber q hq hp).X j) :
    jjFiberHighEquiv q hq hp j hj x = x.2 := rfl

def jjFiberHighCokerEquiv (j : ℤ) (hj : 4 ≤ j) :
    CokerAt (jjFiber q hq hp) j ≃ₗ[E q] CokerAt (forwardJJ q hp) j := by
  apply cokerLinearEquiv _ _
    ((jjFiberHighEquiv q hq hp (j+1) (by omega)).trans (LinearEquiv.neg (E q)))
    (jjFiberHighEquiv q hq hp j hj)
  apply LinearMap.ext
  intro x
  change ((jjFiber q hq hp).d (j+1) j x).2 = (forwardJJ q hp).d (j+1) j (-x.2)
  rw [show (jjFiber q hq hp).d (j+1) j = ModuleFiber.differential (jjReverseComparison q hq hp) j from
    ModuleFiber.complex_d _ j]
  change -(forwardJJ q hp).d (j+1) j x.2 = (forwardJJ q hp).d (j+1) j (-x.2)
  rw [map_neg]

def natJJFiveFiberEquiv : NatCoker.C (natJJ q hp) 4 ≃ₗ[E q] CokerAt (jjFiber q hq hp) 5 :=
  (jjNatIntCokerEquiv q hp 4).trans (jjFiberHighCokerEquiv q hq hp 5 (by omega)).symm

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R)

def evalCokerIso {M N : ModuleCat.{0} (Alg k S R)} (f : M ⟶ N) :
    evalObj (k := k) X (ModuleCat.of _ (N ⧸ LinearMap.range f.hom)) ≅
      ModuleCat.of S (evalObj (k := k) X N ⧸ LinearMap.range (evalMap (k := k) X f).hom) := by
  let : PreservesColimits (evaluation (k := k) (S := S) X) :=
    (evaluationAdjunction (k := k) X).leftAdjoint_preservesColimits
  exact (evaluation (k := k) X).mapIso (ModuleCat.cokernelIsoRangeQuotient f).symm ≪≫
    PreservesCokernel.iso (evaluation (k := k) X) f ≪≫ ModuleCat.cokernelIsoRangeQuotient (evalMap (k := k) X f)

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)

lemma goodComponent_up_at
    (i j l : ℤ) (hij : i+1=j) (hjl : j+1=l)
    (hq : Function.Exact (Q.d l j) (Q.d j i))
    [Module.Projective R (P.X j)]
    (a : P.X i →ₗ[R] Q.X j) (ha : GoodComponent f i j a) :
    ∃ b : P.X j →ₗ[R] Q.X l,
      (f.f j).hom = a.comp (P.d j i).hom + (Q.d l j).hom.comp b ∧
      GoodComponent f j l b := by
  let r := (f.f j).hom - a.comp (P.d j i).hom
  have hr (x : P.X j) : r x ∈ LinearMap.range (Q.d l j).hom := by
    have he := hq
    have hi : i = j-1 := by omega
    have hl : l = j+1 := by omega
    subst i
    subst l
    apply (he _).mp
    have hc := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm j (j-1))) x
    change Q.d j (j-1) (f.f j x) = f.f (j-1) (P.d j (j-1) x) at hc
    have hh := LinearMap.congr_fun ha x
    change f.f (j-1) (P.d j (j-1) x) - Q.d j (j-1) (a (P.d j (j-1) x)) = 0 at hh
    change Q.d j (j-1) (f.f j x - a (P.d j (j-1) x)) = 0
    rw [map_sub, hc]
    exact hh
  obtain ⟨b, hb⟩ := Module.projective_lifting_property
    (Q.d l j).hom.rangeRestrict (r.codRestrict _ hr) (by rintro ⟨x, y, rfl⟩; exact ⟨y, rfl⟩)
  have hb' : (Q.d l j).hom.comp b = r := by
    ext x
    exact congrArg Subtype.val (LinearMap.congr_fun hb x)
  refine ⟨b, ?_, ?_⟩
  · rw [hb']
    dsimp only [r]
    abel
  · unfold GoodComponent
    rw [hb']
    dsimp only [r]
    rw [sub_sub_cancel, LinearMap.comp_assoc]
    have hd : (P.d j i).hom.comp (P.d l j).hom = 0 :=
      ModuleCat.hom_ext_iff.mp (P.d_comp_d _ _ _)
    rw [hd, LinearMap.comp_zero]

section Initial
variable {k : Type} [Field k] [Algebra k R] [Module.Injective R R]

lemma tail_initial_component (n : ℤ)
    (hp : Function.Exact (P.d (n+1) n) (P.d n (n-1)))
    (hf : CokerAt.map f n ∈ projectiveFactors (k := k)) :
    ∃ a : P.X (n-1) →ₗ[R] Q.X n, GoodComponent f (n-1) n a := by
  obtain ⟨J, hJf, hJp, u, v, hvu⟩ := hf
  let := hJf
  let := hJp
  let : Module.Injective R J := injective_of_finite_projective
  obtain ⟨u', hu⟩ := Module.Injective.extension_property R J
    (CokerAt P n) (P.X (n-1)) (CokerAt.ι P n) (CokerAt.ι_injective P n hp) u
  obtain ⟨v', hv⟩ := Module.projective_lifting_property (CokerAt.π Q n) v
    (CokerAt.π_surjective Q n)
  refine ⟨v'.comp u', ?_⟩
  unfold GoodComponent
  apply LinearMap.ext
  intro x
  have h : CokerAt.π Q n (f.f n x - v' (u' (P.d n (n-1) x))) = 0 := by
    have hu' := LinearMap.congr_fun hu (CokerAt.π P n x)
    change u' (P.d n (n-1) x) = u (CokerAt.π P n x) at hu'
    rw [map_sub, hu']
    have hv' := LinearMap.congr_fun hv (u (CokerAt.π P n x))
    dsimp only [LinearMap.comp_apply] at hv'
    have hvu' := LinearMap.congr_fun hvu (CokerAt.π P n x)
    change v (u (CokerAt.π P n x)) = CokerAt.π Q n (f.f n x) at hvu'
    rw [hv', hvu', sub_self]
  have hz := congrArg (CokerAt.ι Q n) h
  rw [map_zero, CokerAt.ι_π] at hz
  change Q.d n (n-1) (f.f n x - v' (u' (P.d n (n-1) x))) = 0 at hz
  have hc := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm n (n-1))) x
  change Q.d n (n-1) (f.f n x) = f.f (n-1) (P.d n (n-1) x) at hc
  change f.f (n-1) (P.d n (n-1) x) - Q.d n (n-1) (v' (u' (P.d n (n-1) x))) = 0
  rw [map_sub, hc] at hz
  exact hz
end Initial

lemma exact_tail_at (n : ℤ)
    (hq : ∀ j, n ≤ j → Function.Exact (Q.d (j+1) j) (Q.d j (j-1)))
    (i j l : ℤ) (hij : i+1=j) (hjl : j+1=l) (hj : n ≤ j) :
    Function.Exact (Q.d l j) (Q.d j i) := by
  have hi : i=j-1 := by omega
  have hl : l=j+1 := by omega
  subst i
  subst l
  exact hq j hj

namespace TailNull
variable (n : ℤ)

def State (j : ℤ) :=
  {a : P.X j →ₗ[R] Q.X (j+1) // n-1 ≤ j → GoodComponent f j (j+1) a}

variable (hq : ∀ j, n ≤ j → Function.Exact (Q.d (j+1) j) (Q.d j (j-1)))
variable (pproj : ∀ j, Module.Projective R (P.X j))

def up (j : ℤ) (hj : n-1 ≤ j) (a : State f n j) : State f n (j+1) := by
  let := pproj (j+1)
  have he : Function.Exact (Q.d (j+1+1) (j+1)) (Q.d (j+1) j) := by
    exact exact_tail_at n hq j (j+1) (j+1+1) rfl rfl (by omega)
  let hh := goodComponent_up_at f j (j+1) (j+1+1) rfl rfl he a.val (a.property hj)
  exact ⟨hh.choose, fun _ => hh.choose_spec.2⟩

def stateMap {i : ℤ} (a : State f n i) (j : ℤ) (h : i+1=j) : P.X i →ₗ[R] Q.X j := by
  subst j
  exact a.val

def Step (i j : ℤ) (h : i+1=j) (a : State f n i) (b : State f n j) : Prop :=
  (f.f j).hom = (stateMap f n a j h).comp (P.d j i).hom + (Q.d (j+1) j).hom.comp b.val

lemma up_step (j : ℤ) (hj : n-1 ≤ j) (a : State f n j) :
    Step f n j (j+1) rfl a (up f n hq pproj j hj a) := by
  let := pproj (j+1)
  have he : Function.Exact (Q.d (j+1+1) (j+1)) (Q.d (j+1) j) := by
    exact exact_tail_at n hq j (j+1) (j+1+1) rfl rfl (by omega)
  exact (goodComponent_up_at f j (j+1) (j+1+1) rfl rfl he a.val (a.property hj)).choose_spec.1

variable (a₀ : State f n (n-1))

def component (j : ℤ) : State f n j :=
  j.inductionOn' (n-1) a₀ (fun j hj => up f n hq pproj j hj)
    (fun j hj _ => ⟨0, fun h => by omega⟩)

lemma component_up (j : ℤ) (hj : n-1 ≤ j) :
    component f n hq pproj a₀ (j+1) = up f n hq pproj j hj (component f n hq pproj a₀ j) :=
  Int.inductionOn'_add_one hj

lemma hasStep (i j : ℤ) (h : i+1=j) (hj : n ≤ j) :
    Step f n i j h (component f n hq pproj a₀ i) (component f n hq pproj a₀ j) := by
  subst j
  have hi : n-1 ≤ i := by omega
  rw [component_up f n hq pproj a₀ i hi]
  exact up_step f n hq pproj i hi _

def hom (i j : ℤ) : P.X i ⟶ Q.X j :=
  if h : i+1=j then ModuleCat.ofHom (stateMap f n (component f n hq pproj a₀ i) j h) else 0

lemma hom_zero (i j : ℤ) (h : ¬ (ComplexShape.down ℤ).Rel j i) :
    hom f n hq pproj a₀ i j = 0 := dite_eq_right h

lemma nullHomotopicMap_f (j : ℤ) (hj : n ≤ j) :
    (Homotopy.nullHomotopicMap (hom f n hq pproj a₀)).f j = f.f j := by
  rw [Homotopy.nullHomotopicMap_f
    (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)
    (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega)]
  simp only [hom, dite_eq_left (show j-1+1=j by omega)]
  apply ModuleCat.hom_ext
  exact (hasStep f n hq pproj a₀ (j-1) j (by omega) hj).symm

end TailNull

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace Cutoff
variable (Q : ChainComplex (ModuleCat.{0} R) ℤ) (n : ℤ)

def term (j : ℤ) : Submodule R (Q.X j) := if j ≤ n then ⊤ else ⊥

lemma d_mem (i j : ℤ) (x : term Q n i) : Q.d i j x.val ∈ term Q n j := by
  classical
  by_cases hj : j ≤ n
  · simp only [term, ite_eq_left hj, Submodule.mem_top]
  · by_cases hi : i ≤ n
    · have hrel : ¬ (ComplexShape.down ℤ).Rel i j := by
        change ¬ j+1=i
        omega
      rw [Q.shape i j hrel]
      exact (term Q n j).zero_mem
    · have hx : x.val = 0 := by simpa only [term, ite_eq_right hi, Submodule.mem_bot] using x.property
      rw [hx, map_zero]
      exact (term Q n j).zero_mem

def differential (i j : ℤ) : term Q n i →ₗ[R] term Q n j :=
  ((Q.d i j).hom.comp (term Q n i).subtype).codRestrict _ (d_mem Q n i j)

@[simp] lemma differential_val (i j : ℤ) (x : term Q n i) :
    (differential Q n i j x).val = Q.d i j x.val := rfl

def complex : ChainComplex (ModuleCat.{0} R) ℤ where
  X j := ModuleCat.of R (term Q n j)
  d i j := ModuleCat.ofHom (differential Q n i j)
  shape i j h := by
    apply ModuleCat.hom_ext
    ext x
    change Q.d i j x.val = 0
    rw [Q.shape i j h]
    rfl
  d_comp_d' i j l _ _ := by
    apply ModuleCat.hom_ext
    ext x
    change Q.d j l (Q.d i j x.val) = 0
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (Q.d_comp_d i j l)) x.val

def inclusion : complex Q n ⟶ Q where
  f j := ModuleCat.ofHom (term Q n j).subtype
  comm' _ _ _ := rfl

variable {Q} {P : ChainComplex (ModuleCat.{0} R) ℤ}

def lift (f : P ⟶ Q) (h : ∀ j, n < j → f.f j = 0) : P ⟶ complex Q n where
  f j := ModuleCat.ofHom <| (f.f j).hom.codRestrict (term Q n j) (by
    intro x
    by_cases hj : j ≤ n
    · simp only [term, ite_eq_left hj, Submodule.mem_top]
    · change f.f j x ∈ term Q n j
      rw [h j (by omega)]
      exact (term Q n j).zero_mem)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    change Q.d i j (f.f i x) = f.f j (P.d i j x)
    exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm i j)) x

lemma lift_inclusion (f : P ⟶ Q) (h : ∀ j, n < j → f.f j = 0) :
    lift n f h ≫ inclusion Q n = f := by
  ext j x
  rfl

lemma term_subsingleton (j : ℤ) (h : n < j) : Subsingleton (term Q n j) := by
  simpa only [term, ite_eq_right (show ¬ j ≤ n by omega)] using
    (inferInstance : Subsingleton (⊥ : Submodule R (Q.X j)))

lemma term_projective (j : ℤ) [Module.Projective R (Q.X j)] :
    Module.Projective R (term Q n j) := by
  classical
  by_cases h : j ≤ n
  · have he : term Q n j = ⊤ := ite_eq_left h
    exact Module.Projective.of_equiv ((LinearEquiv.ofEq _ _ he).trans
      (Submodule.topEquiv : (⊤ : Submodule R (Q.X j)) ≃ₗ[R] Q.X j)).symm
  · have := term_subsingleton (Q := Q) n j (by omega)
    infer_instance

lemma term_finite (j : ℤ) [Module.Finite R (Q.X j)] : Module.Finite R (term Q n j) := by
  classical
  by_cases h : j ≤ n
  · have he : term Q n j = ⊤ := ite_eq_left h
    exact Module.Finite.equiv ((LinearEquiv.ofEq _ _ he).trans
      (Submodule.topEquiv : (⊤ : Submodule R (Q.X j)) ≃ₗ[R] Q.X j)).symm
  · have := term_subsingleton (Q := Q) n j (by omega)
    infer_instance

lemma term_subsingleton_below (l : ℤ) (hQ : ∀ j, j < l → Subsingleton (Q.X j))
    (j : ℤ) (hj : j < l) : Subsingleton (term Q n j) := by
  let := hQ j hj
  infer_instance

end Cutoff
end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable [Module.Injective R R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}

theorem perfect_factorization (f : P ⟶ Q) (n l : ℤ)
    (hp : Function.Exact (P.d (n+1) n) (P.d n (n-1)))
    (hq : ∀ j, n ≤ j → Function.Exact (Q.d (j+1) j) (Q.d j (j-1)))
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qproj : ∀ j, Module.Projective R (Q.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j))
    (qbound : ∀ j, j < l → Subsingleton (Q.X j))
    (hf : CokerAt.map f n ∈ projectiveFactors (k := k)) :
    ∃ (K : ChainComplex (ModuleCat.{0} R) ℤ) (a : P ⟶ K) (b : K ⟶ Q),
      Nonempty (Homotopy f (a ≫ b)) ∧
      (∀ j, Module.Projective R (K.X j)) ∧
      (∀ j, Module.Finite R (K.X j)) ∧
      (∀ j, j < l ∨ n ≤ j → Subsingleton (K.X j)) := by
  obtain ⟨a₀, ha₀⟩ := tail_initial_component f n hp hf
  let astart : TailNull.State f n (n-1) := by
    unfold TailNull.State
    have hi : n-1+1=n := by omega
    rw [hi]
    exact ⟨a₀, fun _ => ha₀⟩
  let h := TailNull.hom f n hq pproj astart
  let z := Homotopy.nullHomotopicMap h
  let f' := f-z
  have hf' (j : ℤ) (hj : n-1 < j) : f'.f j = 0 := by
    change f.f j - z.f j = 0
    rw [TailNull.nullHomotopicMap_f f n hq pproj astart j (by omega)]
    exact sub_self _
  let a := Cutoff.lift (n-1) f' hf'
  refine ⟨Cutoff.complex Q (n-1), a, Cutoff.inclusion Q (n-1), ?_, ?_, ?_, ?_⟩
  · have he : a ≫ Cutoff.inclusion Q (n-1) = f' := Cutoff.lift_inclusion (n-1) f' hf'
    rw [he]
    apply Nonempty.intro
    refine Homotopy.equivSubZero.symm ?_
    have hz : f-f'=z := by dsimp only [f']; abel
    rw [hz]
    exact Homotopy.nullHomotopy h (TailNull.hom_zero f n hq pproj astart)
  · intro j
    let := qproj j
    exact Cutoff.term_projective (Q := Q) (n-1) j
  · intro j
    let := qfin j
    exact Cutoff.term_finite (Q := Q) (n-1) j
  · intro j hj
    rcases hj with hj | hj
    · exact Cutoff.term_subsingleton_below (n-1) l qbound j hj
    · exact Cutoff.term_subsingleton (n-1) j (by omega)

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [Module.Injective R R]
variable {P Q : CochainComplex (ModuleCat.{0} R) ℤ}

theorem cochain_perfect_factorization (f : P ⟶ Q) (n l : ℤ)
    (hp : Function.Exact ((reflectCochain P).d (n+1) n) ((reflectCochain P).d n (n-1)))
    (hq : ∀ j, n ≤ j → Function.Exact ((reflectCochain Q).d (j+1) j)
      ((reflectCochain Q).d j (j-1)))
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qproj : ∀ j, Module.Projective R (Q.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j))
    (qbound : ∀ j, -l < j → Subsingleton (Q.X j))
    (hf : CokerAt.map (reflectCochainMap f) n ∈ projectiveFactors (k := k)) :
    ∃ (L : CochainComplex (ModuleCat.{0} R) ℤ)
      (a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)
      (b : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj Q),
      a ≫ b = DerivedCategory.Q.map f ∧
      (∀ j, Module.Projective R (L.X j)) ∧
      (∀ j, Module.Finite R (L.X j)) ∧
      (∀ j, j < -n+1 ∨ -l < j → IsZero (L.X j)) := by
  obtain ⟨L,a,b,⟨H⟩,hproj,hfin,hbound⟩ := perfect_factorization
    (reflectCochainMap f) n l hp hq (fun j => pproj (-j))
      (fun j => qproj (-j)) (fun j => qfin (-j))
      (fun j hj => qbound (-j) (by omega)) hf
  let a' := (reflectCochainIso P).inv ≫ reflectChainMap a
  let b' := reflectChainMap b ≫ (reflectCochainIso Q).hom
  refine ⟨reflectChain L, DerivedCategory.Q.map a', DerivedCategory.Q.map b', ?_,
    (fun j => hproj (-j)), (fun j => hfin (-j)), ?_⟩
  · have he : (reflectCochainIso P).inv ≫ reflectChainMap (reflectCochainMap f) ≫
      (reflectCochainIso Q).hom = f := by
      rw [reflectCochainIso_natural, Iso.inv_hom_id_assoc]
    have H' := ((reflectChainHomotopy H).compLeft (reflectCochainIso P).inv).compRight
      (reflectCochainIso Q).hom
    have hH := DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{0} R) H'
    rw [Category.assoc,he] at hH
    rw [← Functor.map_comp]
    exact hH.symm.trans (congrArg DerivedCategory.Q.map (by rfl))
  · intro j hj
    exact ModuleCat.isZero_iff_subsingleton.mpr (hbound (-j) (by omega))

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

lemma projectiveResolution_reflect_exact {M : ModuleCat.{0} R} (P : ProjectiveResolution M)
    (n : ℕ) (hn : 0 < n) :
    Function.Exact ((reflectCochain P.cochainComplex).d ((n:ℤ)+1) n)
      ((reflectCochain P.cochainComplex).d n ((n:ℤ)-1)) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ m)
  exact resolution_reflect_exact P (𝟭 (ModuleCat.{0} R)) (m+1) (by omega)
    (by
      change Function.Exact (P.complex.d (m+1+1) (m+1)) (P.complex.d (m+1) (m+1-1))
      rw [show m+1-1=m by omega]
      exact h)

theorem stably_nonzero_high_lift [Module.Injective R R]
    (P : CochainComplex (ModuleCat.{0} R) ℤ)
    (pproj : ∀ j, Module.Projective R (P.X j)) (M : FiniteModule k R)
    (v : P ⟶ (CochainComplex.singleFunctor _ 0).obj M.obj)
    (n₀ : ℕ) (hn₀ : 0 < n₀)
    (hex : ∀ n : ℕ, n₀ ≤ n → Function.Exact ((reflectCochain P).d ((n:ℤ)+1) n)
      ((reflectCochain P).d n ((n:ℤ)-1)))
    (hnot : ∀ (L : CochainComplex (ModuleCat.{0} R) ℤ)
      ( _hfin : ∀ j, Module.Finite R (L.X j)) ( _hproj : ∀ j, Module.Projective R (L.X j))
      (l u : ℤ) ( _hb : ∀ j, j < l ∨ u < j → IsZero (L.X j))
      (a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)
      (b : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M.obj)),
      a ≫ b ≠ DerivedCategory.Q.map v)
    (f : P ⟶ M.projectiveResolution.cochainComplex)
    (hfv : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map M.projectiveResolution.π' =
      DerivedCategory.Q.map v) :
    ∀ n : ℕ, n₀ ≤ n → CokerAt.map (reflectCochainMap f) n ∉ projectiveFactors (k := k) := by
  let Q := M.projectiveResolution
  intro n hn hz
  have hq (j : ℤ) (hj : (n:ℤ) ≤ j) :
      Function.Exact ((reflectCochain Q.cochainComplex).d (j+1) j)
        ((reflectCochain Q.cochainComplex).d j (j-1)) := by
    lift j to ℕ using (show 0 ≤ j by omega) with m hm
    subst hm
    exact projectiveResolution_reflect_exact Q m (by omega)
  have qproj (j : ℤ) : Module.Projective R (Q.cochainComplex.X j) := by infer_instance
  have qfin (j : ℤ) : Module.Finite R (Q.cochainComplex.X j) :=
    finite_resolution_cochain Q (fun _ => inferInstance) j
  have qb (j : ℤ) (hj : -(0:ℤ) < j) : Subsingleton (Q.cochainComplex.X j) :=
    ModuleCat.isZero_iff_subsingleton.mp (Q.cochainComplex.isZero_of_isStrictlyLE 0 j (by omega))
  obtain ⟨L,a,b,he,hlp,hlf,hlb⟩ := cochain_perfect_factorization f n 0 (hex n hn)
    hq pproj qproj qfin qb hz
  apply hnot L hlf hlp (-(n:ℤ)+1) 0 (by simpa only [neg_zero] using hlb) a
    (b ≫ DerivedCategory.Q.map Q.π')
  rw [← Category.assoc,he,hfv]

theorem exists_stably_nonzero_high_lift [Module.Injective R R]
    (P : CochainComplex (ModuleCat.{0} R) ℤ) [P.IsKProjective]
    (pproj : ∀ j, Module.Projective R (P.X j)) (M : FiniteModule k R)
    (v : P ⟶ (CochainComplex.singleFunctor _ 0).obj M.obj)
    (n₀ : ℕ) (hn₀ : 0 < n₀)
    (hex : ∀ n : ℕ, n₀ ≤ n → Function.Exact ((reflectCochain P).d ((n:ℤ)+1) n)
      ((reflectCochain P).d n ((n:ℤ)-1)))
    (hnot : ∀ (L : CochainComplex (ModuleCat.{0} R) ℤ)
      ( _hfin : ∀ j, Module.Finite R (L.X j)) ( _hproj : ∀ j, Module.Projective R (L.X j))
      (l u : ℤ) ( _hb : ∀ j, j < l ∨ u < j → IsZero (L.X j))
      (a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)
      (b : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj M.obj)),
      a ≫ b ≠ DerivedCategory.Q.map v) :
    ∃ f : P ⟶ M.projectiveResolution.cochainComplex,
      DerivedCategory.Q.map f ≫ DerivedCategory.Q.map M.projectiveResolution.π' =
        DerivedCategory.Q.map v ∧
      ∀ n : ℕ, n₀ ≤ n → CokerAt.map (reflectCochainMap f) n ∉ projectiveFactors (k := k) := by
  let Q := M.projectiveResolution
  obtain ⟨f,hf⟩ := kProjective_chain_representative P Q.cochainComplex
    (DerivedCategory.Q.map v ≫ inv (DerivedCategory.Q.map Q.π'))
  have hfv : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map Q.π' = DerivedCategory.Q.map v := by
    rw [hf]; simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]
  exact ⟨f,hfv,stably_nonzero_high_lift P pproj M v n₀ hn₀ hex hnot f hfv⟩

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def resRegularUnderlying (φ : R →ₐ[k] S) :
    (AlgebraInduction.res φ).obj (ModuleCat.of S S) ≃ₗ[k] S where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change φ (algebraMap k R c) * (show S from x) = c • (show S from x)
    rw [AlgHom.commutes,Algebra.smul_def]

abbrev restrictedOuterRegular (φ : R →ₐ[k] S) :=
  ((OuterTensor.bifunctor k R Rᵐᵒᵖ).obj
    ((AlgebraInduction.res φ).obj (ModuleCat.of S S))).obj
      ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ))

def restrictedOuterRegularUnderlying (φ : R →ₐ[k] S) :
    OuterTensor.Obj k R Rᵐᵒᵖ
      ((AlgebraInduction.res φ).obj (ModuleCat.of S S))
      ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)) ≃ₗ[k] Alg k S S :=
  TensorProduct.congr (resRegularUnderlying φ) (resRegularUnderlying φ.op)

lemma restrictedOuterRegularUnderlying_tmul (φ : R →ₐ[k] S)
    (x : (AlgebraInduction.res φ).obj (ModuleCat.of S S))
    (y : (AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)) :
    restrictedOuterRegularUnderlying φ (x ⊗ₜ[k] y) =
      (show S from x) ⊗ₜ[k] (show Sᵐᵒᵖ from y) := rfl

lemma restrictedOuterRegular_action (φ : R →ₐ[k] S) (a : Alg k R R)
    (z : ((AlgebraInduction.res φ).obj (ModuleCat.of S S)) ⊗[k]
      ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ))) :
    TensorProduct.congr (resRegularUnderlying φ) (resRegularUnderlying φ.op)
      ((OuterTensor.action k R Rᵐᵒᵖ _ _ a) z) =
    envelopingMap φ a *
      TensorProduct.congr (resRegularUnderlying φ) (resRegularUnderlying φ.op) z := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add,LinearMap.add_apply,map_add,ha,hb,map_add,add_mul]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add,map_add,hx,hy,map_add,mul_add]
    | tmul x y =>
      change (φ a * (show S from x)) ⊗ₜ[k] (φ.op b * (show Sᵐᵒᵖ from y)) =
        (φ a ⊗ₜ[k] φ.op b) * ((show S from x) ⊗ₜ[k] (show Sᵐᵒᵖ from y))
      exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

def restrictedOuterRegularEquiv (φ : R →ₐ[k] S) :
    restrictedOuterRegular φ ≃ₗ[Alg k R R]
      (AlgebraInduction.res (envelopingMap φ)).obj (ModuleCat.of (Alg k S S) (Alg k S S)) where
  __ := (restrictedOuterRegularUnderlying φ).toAddEquiv
  map_smul' a z := restrictedOuterRegular_action φ a z

def restrictedOuterRegularIso (φ : R →ₐ[k] S) :
    restrictedOuterRegular φ ≅
      (AlgebraInduction.res (envelopingMap φ)).obj (ModuleCat.of (Alg k S S) (Alg k S S)) :=
  (restrictedOuterRegularEquiv φ).toModuleIso

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

lemma ext_subsingleton_retract_left {X X' Y : C} (r : Retract X X') (n : ℕ)
    [Subsingleton (Ext X' Y n)] : Subsingleton (Ext X Y n) := by
  have hz (x : Ext X Y n) : x = 0 := by
    have h : (Ext.mk₀ r.r).comp x (zero_add n) = 0 := Subsingleton.elim _ _
    have h' := congrArg (fun z => (Ext.mk₀ r.i).comp z (zero_add n)) h
    simpa only [Ext.mk₀_comp_mk₀_assoc, r.retract, Ext.mk₀_id_comp, Ext.comp_zero] using h'
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

lemma ext_subsingleton_retract_right {X Y Y' : C} (r : Retract Y Y') (n : ℕ)
    [Subsingleton (Ext X Y' n)] : Subsingleton (Ext X Y n) := by
  have hz (x : Ext X Y n) : x = 0 := by
    have h : x.comp (Ext.mk₀ r.i) (add_zero n) = 0 := Subsingleton.elim _ _
    have h' := congrArg (fun z => z.comp (Ext.mk₀ r.r) (add_zero n)) h
    simpa only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      r.retract, Ext.comp_mk₀_id, Ext.zero_comp] using h'
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

def InAdd (W V : C) : Prop := ∃ n : ℕ, Nonempty (Retract V (⨁ fun _ : Fin n => W))

lemma ext_subsingleton_inAdd_left {W V Y : C} (h : InAdd W V) (n : ℕ)
    [Subsingleton (Ext W Y n)] : Subsingleton (Ext V Y n) := by
  obtain ⟨d,⟨r⟩⟩ := h
  let : Subsingleton (Ext (⨁ fun _ : Fin d => W) Y n) :=
    (Ext.biproductAddEquiv (biproduct.isBilimit _) Y n).injective.subsingleton
  exact ext_subsingleton_retract_left r n

lemma ext_subsingleton_inAdd_right {W V X : C} (h : InAdd W V) (n : ℕ)
    [Subsingleton (Ext X W n)] : Subsingleton (Ext X V n) := by
  obtain ⟨d,⟨r⟩⟩ := h
  let : Subsingleton (Ext X (⨁ fun _ : Fin d => W) n) :=
    (Ext.addEquivBiproduct X (biproduct.isBilimit _) n).injective.subsingleton
  exact ext_subsingleton_retract_right r n

end Tachikawa

end

end OAI
