import OAI.RingTheory.Tachikawa.OuterExt

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}

lemma homologyMap_eq_of_component {C : Type*} [Category C] [Abelian C]
    {K L : HomologicalComplex C c} (f g : K ⟶ L) (i : I) (h : f.f i = g.f i) :
    homologyMap f i = homologyMap g i := by
  apply (cancel_epi (K.homologyπ i)).1
  rw [homologyπ_naturality,homologyπ_naturality]
  congr 1
  apply (cancel_mono (L.iCycles i)).1
  rw [cyclesMap_i,cyclesMap_i,h]

lemma homologyMap_eq_scalar {K : HomologicalComplex (ModuleCat k) c}
    (f : K ⟶ K) (i : I) (r : k) (hf : f.f i = r • 𝟙 (K.X i)) :
    homologyMap f i = r • 𝟙 (K.homology i) := by
  have h := homologyMap_eq_of_component f (r • 𝟙 K) i hf
  rw [h]
  change ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat k) c i).map
    (r • 𝟙 K)) = _
  have hsc : (shortComplexFunctor (ModuleCat k) c i).map (r • 𝟙 K) =
      r • 𝟙 (K.sc i) := by ext <;> rfl
  rw [hsc,ShortComplex.homologyMap_smul,ShortComplex.homologyMap_id]
  rfl

lemma homologyMap_scalar_of_conjugate {K L : HomologicalComplex (ModuleCat k) c}
    (e : HomotopyEquiv K L) (f : K ⟶ K) (i : I) (r : k)
    (hf : (e.inv ≫ f ≫ e.hom).f i = r • 𝟙 (L.X i)) :
    homologyMap f i = r • 𝟙 (K.homology i) := by
  have h := homologyMap_eq_scalar (e.inv ≫ f ≫ e.hom) i r hf
  have hh := e.homotopyInvHomId.homologyMap_eq i
  rw [homologyMap_comp,homologyMap_id] at hh
  apply (cancel_epi (homologyMap e.inv i)).1
  apply (cancel_mono (homologyMap e.hom i)).1
  rw [Category.assoc,← homologyMap_comp,← homologyMap_comp,h]
  rw [Linear.comp_smul,Category.comp_id,Linear.smul_comp]
  exact (congrArg (fun z => r • z) hh).symm

namespace VectorSplit

instance tensorFunctor_linear : (tensorFunctor (k := k)).Linear k where
  map_smul := by
    intro X Y f r
    apply NatTrans.ext
    funext Z
    exact MonoidalLinear.smul_whiskerRight r f Z

variable {K L : CochainComplex (ModuleCat k) ℕ}

lemma tensor_conjugate_component (f : K ⟶ K) (g : L ⟶ L)
    (n : ℕ) (a b : ℕ → k) (r : k)
    (hf : ∀ i, (inclusion K ≫ f ≫ projection K).f i = a i • 𝟙 _)
    (hg : ∀ j, (inclusion L ≫ g ≫ projection L).f j = b j • 𝟙 _)
    (hab : ∀ i j, i+j=n → a i * b j = r ∨
      IsZero (((tensorFunctor (k := k)).obj ((homologyComplex K).X i)).obj
        ((homologyComplex L).X j))) :
    ((tensorHomologyHomotopyEquiv K L (.up ℕ)).inv ≫
      mapBifunctorMap f g (tensorFunctor (k := k)) (.up ℕ) ≫
        (tensorHomologyHomotopyEquiv K L (.up ℕ)).hom).f n = r • 𝟙 _ := by
  change (mapBifunctorMap (inclusion K) (inclusion L) (tensorFunctor (k := k)) (.up ℕ) ≫
    mapBifunctorMap f g (tensorFunctor (k := k)) (.up ℕ) ≫
    mapBifunctorMap (projection K) (projection L) (tensorFunctor (k := k)) (.up ℕ)).f n = _
  rw [← Category.assoc,bifunctorMap_comp,bifunctorMap_comp]
  simp only [Category.assoc]
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  erw [ι_mapBifunctorMap]
  rcases hab i j hij with hab | hz
  · rw [hf,hg]
    simp only [Functor.map_smul,NatTrans.app_smul,CategoryTheory.Functor.map_id,NatTrans.id_app,
      Linear.smul_comp,Linear.comp_smul,Category.id_comp,Category.comp_id,smul_smul,
      ]
    rw [mul_comm (b j),hab]
    rfl
  · exact hz.eq_of_src _ _

lemma tensor_homology_scalar (f : K ⟶ K) (g : L ⟶ L)
    (n : ℕ) (a b : ℕ → k) (r : k)
    (hf : ∀ i, (inclusion K ≫ f ≫ projection K).f i = a i • 𝟙 _)
    (hg : ∀ j, (inclusion L ≫ g ≫ projection L).f j = b j • 𝟙 _)
    (hab : ∀ i j, i+j=n → a i * b j = r ∨
      IsZero (((tensorFunctor (k := k)).obj ((homologyComplex K).X i)).obj
        ((homologyComplex L).X j))) :
    homologyMap (mapBifunctorMap f g (tensorFunctor (k := k)) (.up ℕ)) n = r • 𝟙 _ :=
  homologyMap_scalar_of_conjugate (tensorHomologyHomotopyEquiv K L (.up ℕ)) _ n r
    (tensor_conjugate_component f g n a b r hf hg hab)
end VectorSplit
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {X Y : ModuleCat R} (P : ProjectiveResolution X)

lemma resolutionHomologyExtAll_quotient (n : ℕ)
    (z : VectorSplit.Z (resolutionHom k R P.complex Y) n) :
    resolutionHomologyExtAll (N := Y) P n (VectorSplit.quotient _ n z) =
      resolutionCyclesToExt Y P n z := by
  have aux {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
      (f : V →ₗ[k] W) (hf : Function.Surjective f) (T : Submodule k V)
      (h : f.ker = T) (z : V) :
      (by rw [← h]; exact f.quotKerEquivOfSurjective hf : (V ⧸ T) ≃ₗ[k] W) (T.mkQ z) = f z := by
    subst T
    exact LinearMap.quotKerEquivOfSurjective_apply_mk f hf z
  exact aux (resolutionCyclesToExt Y P n) (resolutionCyclesToExt_surjective Y P n)
    _ (resolutionCyclesToExt_ker_all P n) z

variable (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesProjectiveObjects] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (e : F.obj X ≅ X)

lemma resolutionTwistHom_scalar
    (l : ProjectiveResolution.Hom P (mappedResolution F P) e.inv) (n : ℕ) (r : k)
    (h : ∀ x : Ext X X n, extIso (k := k) e e n (x.mapExactFunctor F) = r • x) :
    (VectorSplit.inclusion (resolutionHom k R P.complex X) ≫
      resolutionTwistHom (k := k) F P e l.hom ≫
      VectorSplit.projection (resolutionHom k R P.complex X)).f n = r • 𝟙 _ := by
  let K := resolutionHom k R P.complex X
  let S := resolutionTwistHom (k := k) F P e l.hom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change VectorSplit.H K n at x
  let z := VectorSplit.representatives K n x
  have hz : S.f n z.val ∈ VectorSplit.Z K n := by
    change K.d n ((ComplexShape.up ℕ).next n) (S.f n z.val) = 0
    have he := congrArg (fun f => f z.val) (S.comm n ((ComplexShape.up ℕ).next n))
    change K.d n ((ComplexShape.up ℕ).next n) (S.f n z.val) =
      S.f ((ComplexShape.up ℕ).next n) (K.d n ((ComplexShape.up ℕ).next n) z.val) at he
    rw [he,z.property]
    exact map_zero _
  change VectorSplit.quotient K n (VectorSplit.retract K n (S.f n z.val)) = r • x
  rw [show (S.f n z.val) = (⟨S.f n z.val,hz⟩ : VectorSplit.Z K n).val from rfl,
    VectorSplit.retract_cycle]
  apply (resolutionHomologyExtAll (N := X) P n (k := k)).injective
  rw [(resolutionHomologyExtAll (N := X) P n (k := k)).map_smul r x,
    resolutionHomologyExtAll_quotient]
  have hs := resolutionTwistHom_extMk (k := k) F P e l z.val
    ((resolutionHom_memZ k R P.complex X n z.val).mp z.property)
  change extIso (k := k) e e n ((resolutionCyclesToExt X P n z).mapExactFunctor F) =
    resolutionCyclesToExt X P n ⟨S.f n z.val,hz⟩ at hs
  rw [← hs,h]
  congr 1
  rw [← resolutionHomologyExtAll_quotient,VectorSplit.quotient_representatives_apply]

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}

lemma component_scalar_of_homologyMap {K : HomologicalComplex (ModuleCat k) c}
    (hd : ∀ i j, K.d i j = 0) (f : K ⟶ K) (i : I) (r : k)
    (h : homologyMap f i = r • 𝟙 _) : f.f i = r • 𝟙 _ := by
  have : IsIso (K.iCycles i) := (K.sc i).isIso_iCycles (hd _ _)
  have : IsIso (K.homologyπ i) := (K.sc i).isIso_homologyπ (hd _ _)
  have hc : cyclesMap f i = r • 𝟙 _ := by
    apply (cancel_mono (K.homologyπ i)).1
    rw [← homologyπ_naturality,h,Linear.comp_smul,Linear.smul_comp,
      Category.comp_id,Category.id_comp]
  apply (cancel_epi (K.iCycles i)).1
  rw [← cyclesMap_i,hc,Linear.smul_comp,Linear.comp_smul,
    Category.comp_id,Category.id_comp]

lemma conjugate_scalar_of_homologyMap {K L : HomologicalComplex (ModuleCat k) c}
    (e : HomotopyEquiv K L) (hd : ∀ i j, L.d i j = 0) (f : K ⟶ K)
    (i : I) (r : k) (h : homologyMap f i = r • 𝟙 _) :
    (e.inv ≫ f ≫ e.hom).f i = r • 𝟙 _ := by
  apply component_scalar_of_homologyMap hd
  rw [homologyMap_comp,homologyMap_comp,h]
  simp only [Linear.comp_smul,Linear.smul_comp,Category.id_comp]
  rw [← homologyMap_comp,e.homotopyInvHomId.homologyMap_eq,homologyMap_id]

lemma homologyMap_scalar_of_intertwine {K L : HomologicalComplex (ModuleCat k) c}
    (e : K ≅ L) (f : K ⟶ K) (g : L ⟶ L) (h : f ≫ e.hom = e.hom ≫ g)
    (i : I) (r : k) (hf : homologyMap f i = r • 𝟙 _) :
    homologyMap g i = r • 𝟙 _ := by
  have hs := congrArg (fun u => homologyMap u i) h
  rw [homologyMap_comp,homologyMap_comp,hf] at hs
  apply (cancel_epi (homologyMap e.hom i)).1
  rw [Linear.comp_smul,Category.comp_id]
  exact hs.symm.trans (by rw [Linear.smul_comp,Category.id_comp])

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesProjectiveObjects] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : ModuleCat R} (P : ProjectiveResolution X) (e : F.obj X ≅ X)

lemma extTwist_scalar_of_homologyMap
    (l : ProjectiveResolution.Hom P (mappedResolution F P) e.inv) (n : ℕ) (r : k)
    (h : homologyMap (resolutionTwistHom (k := k) F P e l.hom) n = r • 𝟙 _)
    (x : Ext X X n) : extIso (k := k) e e n (x.mapExactFunctor F) = r • x := by
  let K := resolutionHom k R P.complex X
  let S := resolutionTwistHom (k := k) F P e l.hom
  have hf := conjugate_scalar_of_homologyMap (VectorSplit.homologyHomotopyEquiv K)
    (fun _ _ => rfl) S n r h
  obtain ⟨y,rfl⟩ := (resolutionHomologyExtAll (N := X) P n (k := k)).surjective x
  let z := VectorSplit.representatives K n y
  have hz : S.f n z.val ∈ VectorSplit.Z K n := by
    change K.d n ((ComplexShape.up ℕ).next n) (S.f n z.val) = 0
    have he := congrArg (fun f => f z.val) (S.comm n ((ComplexShape.up ℕ).next n))
    change K.d n ((ComplexShape.up ℕ).next n) (S.f n z.val) =
      S.f ((ComplexShape.up ℕ).next n) (K.d n ((ComplexShape.up ℕ).next n) z.val) at he
    rw [he,z.property]
    exact map_zero _
  have hy := congrArg (fun u => u y) hf
  change VectorSplit.quotient K n (VectorSplit.retract K n (S.f n z.val)) = r • y at hy
  rw [show S.f n z.val = (⟨S.f n z.val,hz⟩ : VectorSplit.Z K n).val from rfl,
    VectorSplit.retract_cycle] at hy
  have hs := resolutionTwistHom_extMk (k := k) F P e l z.val
    ((resolutionHom_memZ k R P.complex X n z.val).mp z.property)
  change extIso (k := k) e e n ((resolutionCyclesToExt X P n z).mapExactFunctor F) =
    resolutionCyclesToExt X P n ⟨S.f n z.val,hz⟩ at hs
  rw [← resolutionHomologyExtAll_quotient,VectorSplit.quotient_representatives_apply] at hs
  rw [hs,← resolutionHomologyExtAll_quotient,hy]
  exact (resolutionHomologyExtAll (N := X) P n (k := k)).map_smul r y

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

def rightMultiply (r : R) : R →ₗ[R] R where
  toFun x := x*r
  map_add' x y := add_mul x y r
  map_smul' a x := mul_assoc a x r

@[simp] lemma rightMultiply_apply (r x : R) : rightMultiply r x = x*r := rfl

def Nakayama (k R M : Type) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] := Module.Dual k (M →ₗ[R] R)

namespace Nakayama
instance : AddCommGroup (Nakayama k R M) := inferInstanceAs (AddCommGroup (Module.Dual k (M →ₗ[R] R)))
instance : Module k (Nakayama k R M) := inferInstanceAs (Module k (Module.Dual k (M →ₗ[R] R)))
instance : FunLike (Nakayama k R M) (M →ₗ[R] R) k := inferInstanceAs (FunLike (Module.Dual k (M →ₗ[R] R)) _ _)
instance : LinearMapClass (Nakayama k R M) k (M →ₗ[R] R) k := inferInstanceAs (LinearMapClass (Module.Dual k (M →ₗ[R] R)) _ _ _)
@[ext] lemma ext {x y : Nakayama k R M} (h : ∀ f, x f = y f) : x=y := LinearMap.ext h

def homRight (r : R) : (M →ₗ[R] R) →ₗ[k] (M →ₗ[R] R) where
  toFun f := (rightMultiply r).comp f
  map_add' f g := by ext; simp [add_mul]
  map_smul' c f := by ext; simp

@[simp] lemma homRight_apply (r : R) (f : M →ₗ[R] R) (x : M) : homRight (k := k) r f x = f x*r := rfl

instance : Module R (Nakayama k R M) where
  smul r ψ := ψ.comp (homRight r)
  one_smul ψ := by ext f; change ψ (homRight 1 f) = ψ f; congr 1; ext; simp
  mul_smul r s ψ := by
    ext f
    change ψ (homRight (r*s) f) = ψ (homRight s (homRight r f))
    congr 1
    ext
    simp [mul_assoc]
  smul_zero r := by ext; rfl
  smul_add r ψ φ := by ext; rfl
  zero_smul ψ := by
    ext f
    change ψ (homRight 0 f) = 0
    have he : homRight (k := k) 0 f = 0 := by ext; simp
    rw [he]
    exact ψ.map_zero
  add_smul r s ψ := by
    ext f
    change ψ (homRight (r+s) f) = ψ (homRight r f) + ψ (homRight s f)
    rw [← map_add]
    congr 1
    ext
    simp [mul_add]

@[simp] lemma action_apply (r : R) (ψ : Nakayama k R M) (f : M →ₗ[R] R) :
    (r • ψ) f = ψ (homRight (k := k) r f) := rfl
@[simp] lemma add_apply (ψ φ : Nakayama k R M) (f : M →ₗ[R] R) : (ψ+φ) f = ψ f+φ f := rfl
@[simp] lemma zero_apply (f : M →ₗ[R] R) : (0 : Nakayama k R M) f = 0 := rfl
@[simp] lemma smul_apply (c : k) (ψ : Nakayama k R M) (f : M →ₗ[R] R) : (c • ψ) f = c*ψ f := rfl

instance : IsScalarTower k R (Nakayama k R M) where
  smul_assoc c r ψ := by
    ext f
    change ψ (homRight (c • r) f) = c • ψ (homRight r f)
    calc
      ψ (homRight (c • r) f) = ψ (c • homRight r f) := by
        congr 1
        ext
        simp
      _ = _ := (ψ : Module.Dual k (M →ₗ[R] R)).map_smul c _

variable [Module k M] [IsScalarTower k R M]

def evaluationBilinear : DualBimodule k R →ₗ[R] M →ₗ[k] Nakayama k R M where
  toFun φ :=
    { toFun := fun m =>
        { toFun := fun f => φ (f m)
          map_add' := by intro f g; simp
          map_smul' := by intro c f; simp }
      map_add' := by
        intro m n
        ext f
        change φ (f (m+n)) = φ (f m) + φ (f n)
        simp
      map_smul' := by
        intro c m
        ext f
        change (φ : R →ₗ[k] k) ((f.restrictScalars k) (c • m)) = c * φ (f m)
        exact ((φ : R →ₗ[k] k).comp (f.restrictScalars k)).map_smul c m }
  map_add' := by intro x y; ext m f; rfl
  map_smul' := by intro r φ; ext m f; rfl

@[simp] lemma evaluationBilinear_apply (φ : DualBimodule k R) (m : M) (f : M →ₗ[R] R) :
    evaluationBilinear (k := k) (R := R) φ m f = φ (f m) := rfl

lemma evaluation_balanced (r : R) (φ : DualBimodule k R) (m : M) :
    evaluationBilinear (MulOpposite.op r • φ) m = evaluationBilinear (k := k) (R := R) φ (r • m) := by
  ext f
  simp

def evaluation : BalancedTensor.T (k := k) (R := R) (S := R)
    (M := DualBimodule k R) (N := M) →ₗ[R] Nakayama k R M :=
  BalancedTensor.lift evaluationBilinear evaluation_balanced

@[simp] lemma evaluation_mk (φ : DualBimodule k R) (m : M) (f : M →ₗ[R] R) :
    evaluation (BalancedTensor.mk φ m) f = φ (f m) := rfl

omit [Module k M] [IsScalarTower k R M] in

def map (f : M →ₗ[R] N) : Nakayama k R M →ₗ[R] Nakayama k R N where
  toFun ψ :=
    { toFun := fun g => ψ (g.comp f)
      map_add' := by
        intro g h
        change ψ (g.comp f + h.comp f) = ψ (g.comp f) + ψ (h.comp f)
        exact ψ.map_add _ _
      map_smul' := by
        intro c g
        change ψ (c • g.comp f) = c • ψ (g.comp f)
        exact ψ.map_smul c _ }
  map_add' := by intro ψ φ; ext g; rfl
  map_smul' := by intro r ψ; ext g; rfl

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma map_apply (f : M →ₗ[R] N) (ψ : Nakayama k R M) (g : N →ₗ[R] R) : map f ψ g = ψ (g.comp f) := rfl

variable [Module k N] [IsScalarTower k R N]

lemma evaluation_natural (f : M →ₗ[R] N) :
    (map (k := k) f).comp evaluation = evaluation.comp (BalancedTensor.mapRight f) := by
  apply BalancedTensor.hom_ext
  intro φ m
  ext g
  rfl

variable [FiniteDimensional k R]
local notation "V" => BalancedTensor.T (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M)

def paired (l : Module.Dual k V) (m : M) : Module.Dual k (Module.Dual k R) where
  toFun φ := l (BalancedTensor.mk (R := R) (S := R) (M := DualBimodule k R) φ m)
  map_add' φ ψ := by
    let φ' : DualBimodule k R := φ
    let ψ' : DualBimodule k R := ψ
    change l (BalancedTensor.mk (M := DualBimodule k R) (φ' + ψ') m) =
      l (BalancedTensor.mk φ' m) + l (BalancedTensor.mk ψ' m)
    rw [map_add, LinearMap.add_apply, map_add]
  map_smul' c φ := by
    change l (BalancedTensor.mk (M := DualBimodule k R) (c • φ) m) = c • l (BalancedTensor.mk (M := DualBimodule k R) φ m)
    have h : BalancedTensor.mk (k := k) (R := R) (S := R) (M := DualBimodule k R) (c • φ) m =
        c • BalancedTensor.mk (M := DualBimodule k R) φ m := by
      exact congrArg (fun a : M →ₗ[k] V => a m)
        ((BalancedTensor.mk (k := k) (R := R) (S := R) (M := DualBimodule k R)).restrictScalars k |>.map_smul c φ)
    rw [h]
    exact l.map_smul c _

def transposeFun (l : Module.Dual k V) (m : M) : R := (Module.evalEquiv k R).symm (paired l m)

omit [IsScalarTower k R M] in
@[simp] lemma transposeFun_eval (l : Module.Dual k V) (m : M) (φ : DualBimodule k R) :
    φ (transposeFun l m) = l (BalancedTensor.mk φ m) :=
  Module.apply_evalEquiv_symm_apply k R φ (paired l m)

def transpose (l : Module.Dual k V) : M →ₗ[R] R where
  toFun := transposeFun l
  map_add' x y := by
    apply (Module.evalEquiv k R).injective
    ext φ
    change φ (transposeFun l (x+y)) = φ (transposeFun l x + transposeFun l y)
    rw [map_add]
    exact (transposeFun_eval l (x+y) φ).trans (by
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) (transposeFun_eval l x φ).symm (transposeFun_eval l y φ).symm)
  map_smul' r m := by
    apply (Module.evalEquiv k R).injective
    ext φ
    change φ (transposeFun l (r • m)) = φ (r * transposeFun l m)
    let φ' : DualBimodule k R := φ
    change φ' (transposeFun l (r • m)) = (MulOpposite.op r • φ') (transposeFun l m)
    rw [transposeFun_eval, transposeFun_eval, BalancedTensor.balance]

lemma transpose_evaluation (l : Module.Dual k V) (z : V) :
    l z = evaluation z (transpose l) := by
  induction z using BalancedTensor.induction_on with
  | h0 => simp
  | ht φ m => exact (transposeFun_eval l m φ).symm
  | ha x y hx hy => simp only [map_add, add_apply, hx, hy]

lemma evaluation_injective : Function.Injective (evaluation (k := k) (R := R) (M := M)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  apply (Module.forall_dual_apply_eq_zero_iff k z).mp
  intro l
  rw [transpose_evaluation, hz, zero_apply]

variable [FiniteDimensional k M]

lemma evaluation_surjective : Function.Surjective (evaluation (k := k) (R := R) (M := M)) := by
  let : Module.Finite k (M →ₗ[R] R) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k R M R k)
      (LinearMap.restrictScalars_injective k)
  apply (LinearMap.dualMap_injective_iff (f := (evaluation (k := k) (R := R) (M := M)).restrictScalars k)).mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro l hl
  let f := (Module.evalEquiv k (M →ₗ[R] R)).symm l
  have he : ∀ ψ : Nakayama k R M, l ψ = ψ f := by
    intro ψ
    exact (Module.apply_evalEquiv_symm_apply k (M →ₗ[R] R) ψ l).symm
  have hf : f = 0 := by
    ext m
    apply (Module.forall_dual_apply_eq_zero_iff k (f m)).mp
    intro φ
    have hz := LinearMap.congr_fun hl (BalancedTensor.mk (M := DualBimodule k R) φ m)
    change l (evaluation (BalancedTensor.mk (M := DualBimodule k R) φ m)) = 0 at hz
    rw [he] at hz
    exact hz
  apply LinearMap.ext
  intro ψ
  rw [he, hf]
  exact ψ.map_zero

def evaluationEquiv : V ≃ₗ[R] Nakayama k R M :=
  LinearEquiv.ofBijective evaluation ⟨evaluation_injective, evaluation_surjective⟩

end Nakayama
end Tachikawa



namespace Tachikawa.Nakayama
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Z] [Module R Z] [Module k Z] [IsScalarTower k R Z]

def rankOne (a : P →ₗ[R] R) (z : Z) : P →ₗ[R] Z where
  toFun p := a p • z
  map_add' p q := by simp [add_smul]
  map_smul' r p := by simp [mul_smul]

@[simp] lemma rankOne_apply (a : P →ₗ[R] R) (z : Z) (p : P) : rankOne a z p = a p • z := rfl

def coevaluation : Module.Dual k (P →ₗ[R] Z) →ₗ[k] (Z →ₗ[R] Nakayama k R P) where
  toFun ψ :=
    { toFun := fun z =>
        { toFun := fun a => ψ (rankOne a z)
          map_add' := by
            intro a b
            rw [← ψ.map_add]
            congr 1
            ext p
            simp [add_smul]
          map_smul' := by
            intro c a
            rw [← ψ.map_smul]
            congr 1
            ext p
            simp [smul_assoc] }
      map_add' := by
        intro x y
        ext a
        change ψ (rankOne a (x+y)) = ψ (rankOne a x) + ψ (rankOne a y)
        rw [← ψ.map_add]
        congr 1
        ext p
        simp [smul_add]
      map_smul' := by
        intro r z
        ext a
        change ψ (rankOne a (r • z)) = ψ (rankOne (homRight r a) z)
        congr 1
        ext p
        simp [mul_smul] }
  map_add' := by intro x y; ext z a; rfl
  map_smul' := by intro c ψ; ext z a; rfl

@[simp] lemma coevaluation_apply (ψ : Module.Dual k (P →ₗ[R] Z)) (z : Z) (a : P →ₗ[R] R) :
    coevaluation ψ z a = ψ (rankOne a z) := rfl

variable (n : ℕ) (p : P →ₗ[R] (Fin n → R)) (s : (Fin n → R) →ₗ[R] P)
  (hs : s.comp p = LinearMap.id)

include hs in
lemma decomposed (x : P) : ∑ i, p x i • s (Pi.single i 1) = x := by
  have hh := congrArg (fun a : (Fin n → R) →ₗ[R] P => a (p x))
    ((LinearEquiv.piRing R P (Fin n) ℤ).symm_apply_apply s)
  have hh' : (∑ i, p x i • s (Pi.single i 1)) = s (p x) := by
    simpa only [LinearEquiv.piRing_symm_apply, LinearEquiv.piRing_apply] using hh
  exact hh'.trans (LinearMap.congr_fun hs x)

include hs in
lemma rankOne_sum (f : P →ₗ[R] Z) :
    ∑ i, rankOne ((LinearMap.proj i).comp p) (f (s (Pi.single i 1))) = f := by
  ext x
  simp only [LinearMap.sum_apply, rankOne_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  simpa only [map_sum, map_smul] using congrArg f (decomposed n p s hs x)

def homPair (g : Z →ₗ[R] Nakayama k R P) : Module.Dual k (P →ₗ[R] Z) where
  toFun f := ∑ i, g (f (s (Pi.single i 1))) ((LinearMap.proj i).comp p)
  map_add' := by intro a b; simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    simp only [LinearMap.smul_apply]
    simp only [← IsScalarTower.algebraMap_smul R c, map_smul, action_apply]
    have hh (a : P →ₗ[R] R) : homRight (k := k) (algebraMap k R c) a = c • a := by
      ext x
      simp [Algebra.mul_smul_comm, Algebra.algebraMap_eq_smul_one]
    simp only [hh, map_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

include hs in
lemma homPair_coevaluation (ψ : Module.Dual k (P →ₗ[R] Z)) :
    homPair n p s (coevaluation ψ) = ψ := by
  ext f
  change (∑ i, ψ (rankOne ((LinearMap.proj i).comp p) (f (s (Pi.single i 1))))) = ψ f
  rw [← map_sum, rankOne_sum n p s hs]

include hs in
lemma coevaluation_homPair (g : Z →ₗ[R] Nakayama k R P) :
    coevaluation (homPair n p s g) = g := by
  ext z a
  change (∑ i, g (a (s (Pi.single i 1)) • z) ((LinearMap.proj i).comp p)) = g z a
  simp only [map_smul, action_apply]
  rw [← map_sum]
  congr 1
  ext x
  simp only [LinearMap.sum_apply, homRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  have hx := congrArg a (decomposed n p s hs x)
  simpa only [map_sum, map_smul, smul_eq_mul] using hx

lemma coevaluation_bijective [Module.Finite R P] [Module.Projective R P] :
    Function.Bijective (coevaluation (k := k) (R := R) (P := P) (Z := Z)) := by
  let c := finiteFreeCover (R := R) (M := P)
  obtain ⟨i, hi⟩ := Module.projective_lifting_property c.map (LinearMap.id (R := R) (M := P)) c.surjective
  exact ⟨Function.LeftInverse.injective (homPair_coevaluation c.rank i c.map hi),
    Function.RightInverse.surjective (coevaluation_homPair c.rank i c.map hi)⟩

def homDualEquiv [Module.Finite R P] [Module.Projective R P] :
    (Z →ₗ[R] Nakayama k R P) ≃ₗ[k] Module.Dual k (P →ₗ[R] Z) :=
  (LinearEquiv.ofBijective coevaluation coevaluation_bijective).symm

end Tachikawa.Nakayama



namespace Tachikawa
variable {k U V W : Type*} [Field k]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

lemma exact_dual (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, (LinearMap.exact_iff.mp h)]

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z] [Module R Z]
  [Module k Z] [IsScalarTower k R Z]

def homPrecomp (f : P →ₗ[R] Q) : (Q →ₗ[R] Z) →ₗ[k] (P →ₗ[R] Z) where
  toFun g := g.comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma homPrecomp_apply (f : P →ₗ[R] Q) (g : Q →ₗ[R] Z) :
    homPrecomp (k := k) f g = g.comp f := rfl

namespace Nakayama
lemma coevaluation_natural_left (f : P →ₗ[R] Q) (ψ : Module.Dual k (P →ₗ[R] Z)) :
    (map f).comp (coevaluation ψ) = coevaluation (ψ.comp (homPrecomp f)) := by
  ext z a
  rfl

lemma coevaluation_natural_right {Z' : Type} [AddCommGroup Z'] [Module R Z']
    [Module k Z'] [IsScalarTower k R Z'] (f : Z' →ₗ[R] Z) (ψ : Module.Dual k (P →ₗ[R] Z)) :
    (coevaluation ψ).comp f = coevaluation (ψ.comp (LinearMap.compRight k f)) := by
  ext z a
  change ψ (rankOne a (f z)) = ψ (f.comp (rankOne a z))
  congr 1
  ext p
  exact (f.map_smul _ _).symm

@[simp] lemma coevaluation_homDualEquiv [Module.Finite R P] [Module.Projective R P]
    (g : Z →ₗ[R] Nakayama k R P) : coevaluation (homDualEquiv g) = g :=
  (LinearEquiv.ofBijective coevaluation coevaluation_bijective).apply_symm_apply g

@[simp] lemma homDualEquiv_coevaluation [Module.Finite R P] [Module.Projective R P]
    (ψ : Module.Dual k (P →ₗ[R] Z)) : homDualEquiv (coevaluation ψ) = ψ :=
  (LinearEquiv.ofBijective coevaluation coevaluation_bijective).symm_apply_apply ψ

lemma homDualEquiv_natural_left [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R Q] [Module.Projective R Q]
    (f : P →ₗ[R] Q) (g : Z →ₗ[R] Nakayama k R P) :
    homDualEquiv ((map f).comp g) = (homDualEquiv g).comp (homPrecomp f) := by
  apply coevaluation_bijective.injective
  rw [coevaluation_homDualEquiv, ← coevaluation_natural_left, coevaluation_homDualEquiv]

instance injective [Module.Finite R P] [Module.Projective R P] :
    Module.Injective R (Nakayama k R P) where
  out {X Y} _ _ _ _ f hf g := by
    let : Module k X := Module.compHom X (algebraMap k R)
    let : Module k Y := Module.compHom Y (algebraMap k R)
    let : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let : IsScalarTower k R Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let fp : (P →ₗ[R] X) →ₗ[k] (P →ₗ[R] Y) := LinearMap.compRight k f
    have hinj : Function.Injective fp := by
      intro a b h
      ext p
      exact hf (LinearMap.congr_fun h p)
    obtain ⟨l, hl⟩ := fp.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
    let ψ := homDualEquiv (k := k) g
    refine ⟨coevaluation (ψ.comp l), ?_⟩
    intro x
    have hnat := coevaluation_natural_right f (ψ.comp l)
    have hh : (ψ.comp l).comp fp = ψ := by
      rw [LinearMap.comp_assoc, hl, LinearMap.comp_id]
    have hcomp : (coevaluation (ψ.comp l)).comp f = g := by
      rw [hnat]
      change coevaluation ((ψ.comp l).comp fp) = g
      rw [hh]
      exact coevaluation_homDualEquiv g
    exact LinearMap.congr_fun hcomp x

@[simp] lemma map_id : map (k := k) (LinearMap.id : P →ₗ[R] P) = LinearMap.id := by
  ext ψ a
  rfl

@[simp] lemma map_zero : map (k := k) (0 : P →ₗ[R] Q) = 0 := by
  ext ψ a
  change ψ (a.comp 0) = 0
  simp

lemma map_comp {T : Type} [AddCommGroup T] [Module R T]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) : map (k := k) (g.comp f) = (map g).comp (map f) := by
  ext ψ a
  rfl

end Nakayama
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace Nakayama

def functor : ModuleCat R ⥤ ModuleCat R where
  obj M := ModuleCat.of R (Nakayama k R M)
  map f := ModuleCat.ofHom (map f.hom)
  map_id _ := ModuleCat.hom_ext map_id
  map_comp f g := ModuleCat.hom_ext (map_comp f.hom g.hom)

instance : (functor (k := k) (R := R)).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    change map (k := k) (f.hom+g.hom) = map f.hom + map g.hom
    ext ψ a
    change ψ (a.comp (f.hom+g.hom)) = ψ (a.comp f.hom) + ψ (a.comp g.hom)
    rw [LinearMap.comp_add, map_add]

def complex (P : ChainComplex (ModuleCat R) ℤ) : ChainComplex (ModuleCat R) ℤ :=
  ((functor (k := k)).mapHomologicalComplex (ComplexShape.down ℤ)).obj P

lemma complex_exact {P : ChainComplex (ModuleCat R) ℤ} (hP : TotallyAcyclic P) :
    ComplexExact (complex (k := k) P) := by
  intro j
  let f := homPrecomp (k := k) (Z := R) (P.d j (j-1)).hom
  let g := homPrecomp (k := k) (Z := R) (P.d (j+1) j).hom
  have hex : Function.Exact f g := by
    intro a
    change a.comp (P.d (j+1) j).hom = 0 ↔ ∃ b : P.X (j-1) →ₗ[R] R, b.comp (P.d j (j-1)).hom = a
    constructor
    · exact hP.2 j a
    · rintro ⟨b, rfl⟩
      rw [LinearMap.comp_assoc]
      have hh := ModuleCat.hom_ext_iff.mp (P.d_comp_d (j+1) j (j-1))
      change (P.d j (j-1)).hom.comp (P.d (j+1) j).hom = 0 at hh
      rw [hh, LinearMap.comp_zero]
  change Function.Exact g.dualMap f.dualMap
  exact exact_dual f g hex

variable {P Q Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z] [Module R Z]

lemma homPrecomp_exact (f : P →ₗ[R] Q) (g : Q →ₗ[R] Z)
    (h : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (homPrecomp (k := k) (Z := R) g) (homPrecomp (k := k) f) := by
  intro a
  change a.comp f = 0 ↔ ∃ b : Z →ₗ[R] R, b.comp g = a
  constructor
  · intro ha
    have hk : LinearMap.ker g ≤ LinearMap.ker a := by
      intro q hq
      obtain ⟨p, rfl⟩ := (h q).mp hq
      exact LinearMap.congr_fun ha p
    let b := (g.ker.liftQ a hk).comp (g.quotKerEquivOfSurjective hg).symm.toLinearMap
    refine ⟨b, ?_⟩
    ext q
    change g.ker.liftQ a hk ((g.quotKerEquivOfSurjective hg).symm (g q)) = a q
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  · rintro ⟨b, rfl⟩
    rw [LinearMap.comp_assoc, h.linearMap_comp_eq_zero, LinearMap.comp_zero]

lemma map_exact (f : P →ₗ[R] Q) (g : Q →ₗ[R] Z)
    (h : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (map (k := k) f) (map g) := by
  exact exact_dual _ _ (homPrecomp_exact (k := k) f g h hg)

lemma map_surjective (g : Q →ₗ[R] Z) (hg : Function.Surjective g) :
    Function.Surjective (map (k := k) g) := by
  change Function.Surjective (homPrecomp (k := k) (Z := R) g).dualMap
  apply LinearMap.dualMap_surjective_of_injective
  intro a b hab
  ext z
  obtain ⟨q, rfl⟩ := hg z
  exact LinearMap.congr_fun hab q

end Nakayama
end Tachikawa



namespace Tachikawa
namespace TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

def Obj (k R M : Type) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] := M × Nakayama k R M

instance : AddCommGroup (Obj k R M) := inferInstanceAs (AddCommGroup (M × Nakayama k R M))
instance : Module R (Obj k R M) := inferInstanceAs (Module R (M × Nakayama k R M))
instance : Module k (Obj k R M) := inferInstanceAs (Module k (M × Nakayama k R M))
instance : IsScalarTower k R (Obj k R M) := inferInstanceAs (IsScalarTower k R (M × Nakayama k R M))

def act (a : TrivialExtension k R) (x : Obj k R M) : Obj k R M :=
  (a.fst • x.1, Nakayama.evaluationBilinear a.snd x.1 + a.fst • x.2)

instance : Module (TrivialExtension k R) (Obj k R M) where
  smul := act
  one_smul x := by
    apply Prod.ext
    · exact one_smul _ _
    · change Nakayama.evaluationBilinear (0 : DualBimodule k R) x.1 + (1:R) • x.2 = _
      simp
  mul_smul a b x := by
    apply Prod.ext
    · exact mul_smul _ _ _
    · change Nakayama.evaluationBilinear (a.fst • b.snd + MulOpposite.op b.fst • a.snd) x.1 +
        (a.fst*b.fst) • x.2 = Nakayama.evaluationBilinear a.snd (b.fst • x.1) +
          a.fst • (Nakayama.evaluationBilinear b.snd x.1 + b.fst • x.2)
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        Nakayama.evaluation_balanced, smul_add, mul_smul]
      abel
  smul_zero a := by
    apply Prod.ext
    · exact smul_zero _
    · change Nakayama.evaluationBilinear a.snd 0 + a.fst • (0 : Nakayama k R M) = 0
      simp
  smul_add a x y := by
    apply Prod.ext
    · exact smul_add _ _ _
    · change Nakayama.evaluationBilinear a.snd (x.1+y.1) + a.fst • (x.2+y.2) = _
      simp only [map_add, smul_add]
      change _ = (Nakayama.evaluationBilinear a.snd x.1 + a.fst • x.2) +
        (Nakayama.evaluationBilinear a.snd y.1 + a.fst • y.2)
      abel
  zero_smul x := by
    apply Prod.ext
    · exact zero_smul _ _
    · change Nakayama.evaluationBilinear (0 : DualBimodule k R) x.1 + (0:R) • x.2 = 0
      simp
  add_smul a b x := by
    apply Prod.ext
    · exact add_smul _ _ _
    · change Nakayama.evaluationBilinear (a.snd+b.snd) x.1 + (a.fst+b.fst) • x.2 = _
      simp only [map_add, LinearMap.add_apply, add_smul]
      change _ = (Nakayama.evaluationBilinear a.snd x.1 + a.fst • x.2) +
        (Nakayama.evaluationBilinear b.snd x.1 + b.fst • x.2)
      abel

@[simp] lemma inl_smul (r : R) (x : Obj k R M) :
    (TrivSqZeroExt.inl r : TrivialExtension k R) • x = r • x := by
  apply Prod.ext
  · rfl
  · change Nakayama.evaluationBilinear (0 : DualBimodule k R) x.1 + r • x.2 = _
    simp only [map_zero, LinearMap.zero_apply, zero_add]
    rfl

instance : IsScalarTower k (TrivialExtension k R) (Obj k R M) :=
  IsScalarTower.of_algebraMap_smul (fun c x => by
    change (TrivSqZeroExt.inl (algebraMap k R c) : TrivialExtension k R) • x = c • x
    rw [inl_smul, IsScalarTower.algebraMap_smul])

def unit : M →ₗ[R] Obj k R M := LinearMap.inl R M (Nakayama k R M)
def first : Obj k R M →ₗ[R] M := LinearMap.fst R M (Nakayama k R M)
def second : Obj k R M →ₗ[R] Nakayama k R M := LinearMap.snd R M (Nakayama k R M)

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma unit_apply (x : M) : unit (k := k) (R := R) x = (x,0) := rfl
omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma first_apply (x : Obj k R M) : first x = x.1 := rfl
omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma second_apply (x : Obj k R M) : second x = x.2 := rfl

def map (f : M →ₗ[R] N) : Obj k R M →ₗ[TrivialExtension k R] Obj k R N where
  toFun x := (f x.1, Nakayama.map f x.2)
  map_add' x y := by
    exact Prod.ext (f.map_add x.1 y.1) ((Nakayama.map f).map_add x.2 y.2)
  map_smul' a x := by
    apply Prod.ext
    · exact f.map_smul _ _
    · change Nakayama.map f (Nakayama.evaluationBilinear a.snd x.1 + a.fst • x.2) =
        Nakayama.evaluationBilinear a.snd (f x.1) + a.fst • Nakayama.map f x.2
      rw [map_add, map_smul]
      rfl

@[simp] lemma map_apply (f : M →ₗ[R] N) (x : Obj k R M) :
    map (k := k) f x = (f x.1, Nakayama.map f x.2) := rfl

lemma map_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (map (k := k) f) := by
  intro x
  obtain ⟨m,hm⟩ := hf x.1
  obtain ⟨ψ,hψ⟩ := Nakayama.map_surjective (k := k) f hf x.2
  exact ⟨(m,ψ), Prod.ext hm hψ⟩

lemma map_exact {O : Type} [AddCommGroup O] [Module R O]
    [Module k O] [IsScalarTower k R O] (f : M →ₗ[R] N) (g : N →ₗ[R] O)
    (h : Function.Exact f g) (hν : Function.Exact (Nakayama.map (k := k) f) (Nakayama.map g)) :
    Function.Exact (map (k := k) f) (map g) := by
  intro x
  constructor
  · intro hx
    obtain ⟨m,hm⟩ := (h x.1).mp (congrArg Prod.fst hx)
    obtain ⟨ψ,hψ⟩ := (hν x.2).mp (congrArg Prod.snd hx)
    exact ⟨(m,ψ), Prod.ext hm hψ⟩
  · rintro ⟨y,rfl⟩
    exact Prod.ext (h.apply_apply_eq_zero y.1) (hν.apply_apply_eq_zero y.2)

end TrivialInduction
end Tachikawa



namespace Tachikawa.TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (n : ℕ)

def coordinateHom (i : Fin n) : R →ₗ[k] ((Fin n → R) →ₗ[R] R) where
  toFun r := (rightMultiply r).comp (LinearMap.proj i)
  map_add' r s := by ext x; simp [mul_add]
  map_smul' c r := by ext x; simp [Algebra.mul_smul_comm]

@[simp] lemma coordinateHom_apply (i : Fin n) (r : R) (x : Fin n → R) :
    coordinateHom (k := k) n i r x = x i*r := rfl

lemma sum_coordinateHom (f : (Fin n → R) →ₗ[R] R) :
    ∑ i, coordinateHom (k := k) n i (f (Pi.single i 1)) = f := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.sum_apply]
  change (∑ i, x i * f (Pi.single i 1)) = f x
  have hx := congrArg f (Nakayama.decomposed n (LinearMap.id : (Fin n → R) →ₗ[R] (Fin n → R))
    LinearMap.id rfl x)
  simpa only [LinearMap.id_apply, map_sum, map_smul, smul_eq_mul] using hx

def freeMap : (Fin n → TrivialExtension k R) →ₗ[TrivialExtension k R] Obj k R (Fin n → R) where
  toFun a := ∑ i, a i • unit (Pi.single i 1)
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

lemma freeMap_first (a : Fin n → TrivialExtension k R) :
    first (freeMap (k := k) n a) = fun i => (a i).fst := by
  change first (∑ i, a i • unit (Pi.single i 1)) = _
  rw [map_sum]
  ext j
  change (∑ i, (a i).fst • Pi.single i (1:R)) j = _
  simp [Finset.sum_apply, Pi.single_apply]

lemma freeMap_second (a : Fin n → TrivialExtension k R) :
    second (freeMap (k := k) n a) = ∑ i, Nakayama.evaluationBilinear (a i).snd (Pi.single i 1) := by
  change second (∑ i, a i • unit (Pi.single i 1)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change Nakayama.evaluationBilinear (a i).snd (Pi.single i 1) + (a i).fst • (0 : Nakayama k R (Fin n → R)) = _
  simp

lemma freeMap_second_apply (a : Fin n → TrivialExtension k R) (f : (Fin n → R) →ₗ[R] R) :
    second (freeMap (k := k) n a) f = ∑ i, (a i).snd (f (Pi.single i 1)) := by
  rw [freeMap_second]
  change (∑ i, (Nakayama.evaluationBilinear (a i).snd (Pi.single i 1) : Module.Dual k ((Fin n → R) →ₗ[R] R))) f = _
  exact LinearMap.sum_apply Finset.univ (fun i => (Nakayama.evaluationBilinear (a i).snd (Pi.single i 1) : Module.Dual k ((Fin n → R) →ₗ[R] R))) f

def freeInv (x : Obj k R (Fin n → R)) : Fin n → TrivialExtension k R :=
  fun i => ⟨x.1 i, (x.2 : Module.Dual k ((Fin n → R) →ₗ[R] R)).comp (coordinateHom n i)⟩

lemma freeMap_freeInv (x : Obj k R (Fin n → R)) : freeMap (k := k) n (freeInv n x) = x := by
  apply Prod.ext
  · exact freeMap_first n (freeInv n x)
  · apply Nakayama.ext
    intro f
    rw [← second_apply, freeMap_second_apply]
    change (∑ i, x.2 (coordinateHom n i (f (Pi.single i 1)))) = x.2 f
    rw [← map_sum, sum_coordinateHom]

lemma freeInv_freeMap (a : Fin n → TrivialExtension k R) : freeInv n (freeMap (k := k) n a) = a := by
  funext i
  apply TrivSqZeroExt.ext
  · exact congrFun (freeMap_first n a) i
  · apply DualBimodule.ext
    intro r
    change second (freeMap (k := k) n a) (coordinateHom n i r) = (a i).snd r
    rw [freeMap_second_apply]
    simp only [coordinateHom_apply, Pi.single_apply]
    simp [ite_mul, apply_ite, map_zero]

def freeEquiv : (Fin n → TrivialExtension k R) ≃ₗ[TrivialExtension k R] Obj k R (Fin n → R) :=
  LinearEquiv.ofBijective (freeMap n) ⟨Function.LeftInverse.injective (freeInv_freeMap n),
    Function.RightInverse.surjective (freeMap_freeInv n)⟩

instance : Module.Projective (TrivialExtension k R) (Obj k R (Fin n → R)) :=
  Module.Projective.of_equiv (freeEquiv (k := k) (R := R) n)

variable {M : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

lemma map_id : map (k := k) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext x
  apply Prod.ext
  · rfl
  · exact LinearMap.congr_fun Nakayama.map_id x.2

lemma map_comp {N O : Type} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
    [AddCommGroup O] [Module R O] [Module k O] [IsScalarTower k R O]
    (f : M →ₗ[R] N) (g : N →ₗ[R] O) :
    map (k := k) (g.comp f) = (map g).comp (map f) := rfl

instance inducedProjective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective (TrivialExtension k R) (Obj k R M) := by
  let c := finiteFreeCover (R := R) (M := M)
  obtain ⟨s,hs⟩ := Module.projective_lifting_property c.map (LinearMap.id (R := R) (M := M)) c.surjective
  apply Module.Projective.of_split (map (k := k) s) (map c.map)
  rw [← map_comp, hs, map_id]

end Tachikawa.TrivialInduction



namespace Tachikawa.TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N P : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup P] [Module R P] [Module k P] [IsScalarTower k R P]

def restrict (f : Obj k R M →ₗ[TrivialExtension k R] Obj k R N) : M →ₗ[R] Obj k R N where
  toFun m := f (unit m)
  map_add' m n := by rw [map_add, map_add]
  map_smul' r m := by
    rw [map_smul, ← inl_smul, map_smul, inl_smul]
    rfl

@[simp] lemma restrict_apply (f : Obj k R M →ₗ[TrivialExtension k R] Obj k R N) (m : M) :
    restrict f m = f (unit m) := rfl

def lift (u : M →ₗ[R] Obj k R N) : Obj k R M →ₗ[TrivialExtension k R] Obj k R N where
  toFun x := ((u x.1).1, (u x.1).2 + Nakayama.map (first.comp u) x.2)
  map_add' x y := by
    apply Prod.ext
    · change (u (x.1+y.1)).1 = (u x.1).1+(u y.1).1
      rw [map_add]
      rfl
    · change (u (x.1+y.1)).2 + Nakayama.map (first.comp u) (x.2+y.2) = _
      rw [map_add, map_add]
      change ((u x.1).2+(u y.1).2) + (Nakayama.map (first.comp u) x.2+Nakayama.map (first.comp u) y.2) = _
      change ((u x.1).2+(u y.1).2) + (Nakayama.map (first.comp u) x.2+Nakayama.map (first.comp u) y.2) =
        ((u x.1).2 + Nakayama.map (first.comp u) x.2) + ((u y.1).2 + Nakayama.map (first.comp u) y.2)
      abel
  map_smul' a x := by
    apply Prod.ext
    · change (u (a.fst • x.1)).1 = a.fst • (u x.1).1
      rw [map_smul]
      rfl
    · change (u (a.fst • x.1)).2 + Nakayama.map (first.comp u)
        (Nakayama.evaluationBilinear a.snd x.1 + a.fst • x.2) =
        Nakayama.evaluationBilinear a.snd (u x.1).1 + a.fst • ((u x.1).2 + Nakayama.map (first.comp u) x.2)
      rw [map_smul, map_add, map_smul, smul_add]
      have he : Nakayama.map (first.comp u) (Nakayama.evaluationBilinear a.snd x.1) =
          Nakayama.evaluationBilinear a.snd (u x.1).1 := rfl
      rw [he]
      change a.fst • (u x.1).2 + (_ + _) = _
      abel

@[simp] lemma lift_unit (u : M →ₗ[R] Obj k R N) (m : M) : lift u (unit m) = u m := by
  apply Prod.ext
  · rfl
  · change (u m).2 + Nakayama.map (first.comp u) 0 = (u m).2
    rw [map_zero, add_zero]

@[simp] lemma restrict_lift (u : M →ₗ[R] Obj k R N) : restrict (lift u) = u := by
  ext m
  exact lift_unit u m

variable [FiniteDimensional k R] [FiniteDimensional k M]

lemma hom_ext {f g : Obj k R M →ₗ[TrivialExtension k R] Obj k R N}
    (h : ∀ m, f (unit m) = g (unit m)) : f = g := by
  let lower : Nakayama k R M →ₗ[R] Obj k R M := LinearMap.inr R M (Nakayama k R M)
  have ht : ∀ ψ : Nakayama k R M, f (lower ψ) = g (lower ψ) := by
    intro ψ
    obtain ⟨z, rfl⟩ := Nakayama.evaluation_surjective (k := k) (R := R) (M := M) ψ
    induction z using BalancedTensor.induction_on with
    | h0 => rw [map_zero, map_zero, map_zero, map_zero]
    | ht φ m =>
      have he : lower (Nakayama.evaluation (BalancedTensor.mk φ m)) =
          (TrivSqZeroExt.inr φ : TrivialExtension k R) • unit m := by
        apply Prod.ext
        · change (0:M) = (0:R) • m
          exact (zero_smul R m).symm
        · change Nakayama.evaluationBilinear φ m = Nakayama.evaluationBilinear φ m + (0:R) • (0 : Nakayama k R M)
          rw [zero_smul, add_zero]
      rw [he, map_smul, map_smul, h]
    | ha z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
  apply LinearMap.ext
  intro x
  have hx : x = unit (k := k) (R := R) x.1 + lower x.2 := by
    apply Prod.ext
    · change x.1 = x.1+0
      rw [add_zero]
    · change x.2 = 0+x.2
      rw [zero_add]
  rw [hx, map_add, map_add, h, ht]

@[simp] lemma lift_restrict (f : Obj k R M →ₗ[TrivialExtension k R] Obj k R N) :
    lift (restrict f) = f := hom_ext (fun m => lift_unit (restrict f) m)

lemma restrict_injective : Function.Injective (restrict (k := k) (R := R) (M := M) (N := N)) := by
  intro f g h
  apply hom_ext
  intro m
  exact LinearMap.congr_fun h m

omit [FiniteDimensional k R] [FiniteDimensional k M] in
lemma map_unit (a : M →ₗ[R] N) (m : M) : map (k := k) a (unit m) = unit (a m) := by
  apply Prod.ext
  · rfl
  · exact (Nakayama.map a).map_zero

omit [FiniteDimensional k R] [FiniteDimensional k M] in
lemma restrict_comp (f : Obj k R N →ₗ[TrivialExtension k R] Obj k R P) (a : M →ₗ[R] N) :
    restrict (f.comp (map a)) = (restrict f).comp a := by
  apply LinearMap.ext
  intro m
  change f (map a (unit m)) = f (unit (a m))
  rw [map_unit]

end Tachikawa.TrivialInduction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace Nakayama
variable {P Q T Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup T] [Module R T]
  [AddCommGroup Z] [Module R Z] [Module k Z] [IsScalarTower k R Z]
  [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]
  [Module.Finite R T] [Module.Projective R T]

lemma hom_map_exact (f : P →ₗ[R] Q) (g : Q →ₗ[R] T)
    (h : Function.Exact (homPrecomp (k := k) (Z := Z) g) (homPrecomp (k := k) f)) :
    Function.Exact (LinearMap.compRight k (map (k := k) f) :
        (Z →ₗ[R] Nakayama k R P) →ₗ[k] (Z →ₗ[R] Nakayama k R Q))
      (LinearMap.compRight k (map (k := k) g)) := by
  have he := exact_dual _ _ h
  apply (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := homDualEquiv (k := k) (P := P) (Z := Z))
    (e₂ := homDualEquiv (k := k) (P := Q) (Z := Z))
    (e₃ := homDualEquiv (k := k) (P := T) (Z := Z))
    (g₁₂ := (homPrecomp (k := k) f).dualMap) (g₂₃ := (homPrecomp (k := k) g).dualMap) ?_ ?_).mp he
  · apply LinearMap.ext
    intro a
    exact (homDualEquiv_natural_left f a).symm
  · apply LinearMap.ext
    intro a
    exact (homDualEquiv_natural_left g a).symm

variable (C : ChainComplex (ModuleCat R) ℤ)

def cokerEquiv : CokerAt (complex (k := k) C) 0 ≃ₗ[R] Nakayama k R (CokerAt C 0) := by
  change (Nakayama k R (C.X 0) ⧸ LinearMap.range (map (k := k) (C.d 1 0).hom)) ≃ₗ[R] Nakayama k R (CokerAt C 0)
  let g := map (k := k) (CokerAt.π C 0)
  have he : Function.Exact (map (k := k) (C.d 1 0).hom) g :=
    map_exact _ _ (fun x => Submodule.Quotient.mk_eq_zero _) (CokerAt.π_surjective C 0)
  have hh : LinearMap.range (map (k := k) (C.d 1 0).hom) = LinearMap.ker g := by
    ext x
    exact (he x).symm
  exact (Submodule.quotEquivOfEq _ _ hh).trans (g.quotKerEquivOfSurjective (map_surjective _ (CokerAt.π_surjective C 0)))

def injectiveTail (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j))
    (proj : ∀ j, Module.Projective R (C.X j)) :
    InjectiveResolution (ModuleCat.of R (CokerAt (complex (k := k) C) 0)) := by
  let I := complex (k := k) C
  let X (n : ℕ) := I.X (-(n : ℤ)-1)
  let d (n : ℕ) : X n ⟶ X (n+1) := I.d (-(n : ℤ)-1) (-((n+1 : ℕ) : ℤ)-1)
  let ε : ModuleCat.of R (CokerAt I 0) ⟶ X 0 := ModuleCat.ofHom (CokerAt.ι I 0)
  have hI : ComplexExact I := complex_exact hC
  apply coresolutionOfExact _ X d ε
  · intro n
    exact hI.adjacent I _ _ _ (by omega) (by omega)
  · intro x
    constructor
    · intro hx
      change I.d (-1) (-2) x = 0 at hx
      obtain ⟨y, hy⟩ := (hI.adjacent I 0 (-1) (-2) (by omega) (by omega) x).mp hx
      exact ⟨CokerAt.π I 0 y, hy⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := CokerAt.π_surjective I 0 y
      exact (hI.adjacent I 0 (-1) (-2) (by omega) (by omega)).apply_apply_eq_zero z
  · exact CokerAt.ι_injective I 0 (hI 0)
  · intro n
    let := fin (-(n : ℤ)-1)
    let := proj (-(n : ℤ)-1)
    change Injective (ModuleCat.of R (Nakayama k R (C.X (-(n : ℤ)-1))))
    let : Module.Injective R (Nakayama k R (C.X (-(n : ℤ)-1))) := Nakayama.injective
    exact Module.injective_object_of_injective_module R _

lemma injectiveTail_d (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j))
    (proj : ∀ j, Module.Projective R (C.X j)) (n : ℕ) :
    (injectiveTail (k := k) C hC fin proj).cocomplex.d n (n+1) =
      (complex (k := k) C).d (-(n : ℤ)-1) (-((n+1 : ℕ) : ℤ)-1) := by
  dsimp only [injectiveTail, coresolutionOfExact]
  exact CochainComplex.of_d _ _ n

lemma ext_negative (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j))
    (proj : ∀ j, Module.Projective R (C.X j))
    (Z : ModuleCat R) (n : ℕ)
    (h : Function.Exact
      (homPrecomp (k := k) (Z := Z) (C.d (-((n+1 : ℕ) : ℤ)-1) (-((n+2 : ℕ) : ℤ)-1)).hom)
      (homPrecomp (k := k) (C.d (-(n : ℤ)-1) (-((n+1 : ℕ) : ℤ)-1)).hom)) :
    Subsingleton (Abelian.Ext Z (ModuleCat.of R (CokerAt (complex (k := k) C) 0)) (n+1)) := by
  let I := injectiveTail (k := k) C hC fin proj
  apply ext_subsingleton_of_coboundaries I n
  intro f hf
  rw [injectiveTail_d] at hf
  let := fin (-(n : ℤ)-1)
  let := fin (-((n+1 : ℕ) : ℤ)-1)
  let := fin (-((n+2 : ℕ) : ℤ)-1)
  let := proj (-(n : ℤ)-1)
  let := proj (-((n+1 : ℕ) : ℤ)-1)
  let := proj (-((n+2 : ℕ) : ℤ)-1)
  have he := hom_map_exact (Z := Z) _ _ h
  obtain ⟨g, hg⟩ := (he f.hom).mp (ModuleCat.hom_ext_iff.mp hf)
  refine ⟨ModuleCat.ofHom g, ?_⟩
  rw [injectiveTail_d]
  exact ModuleCat.hom_ext hg

end Nakayama
end Tachikawa



namespace Tachikawa
open CategoryTheory

lemma boundaries_of_ext_subsingleton {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (P : ProjectiveResolution X) (n : ℕ)
    [Subsingleton (Abelian.Ext X Y (n+1))]
    (f : P.complex.X (n+1) ⟶ Y) (hf : P.complex.d (n+2) (n+1) ≫ f = 0) :
    ∃ g : P.complex.X n ⟶ Y, P.complex.d (n+1) n ≫ g = f := by
  exact (P.extMk_eq_zero_iff f (n+2) rfl hf n rfl).mp (Subsingleton.elim _ _)

lemma ext_subsingleton_target_iso {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} (e : Y ≅ Z) (n : ℕ) [Subsingleton (Abelian.Ext X Y n)] :
    Subsingleton (Abelian.Ext X Z n) := by
  let h := (Abelian.extFunctorObj X n).mapIso e
  let e' : Abelian.Ext X Y n ≃+ Abelian.Ext X Z n := h.addCommGroupIsoToAddEquiv
  exact e'.symm.injective.subsingleton

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace TrivialInduction
variable {M : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

instance nakayamaFinite [FiniteDimensional k R] [FiniteDimensional k M] :
    FiniteDimensional k (Nakayama k R M) := by
  let : Module.Finite k (M →ₗ[R] R) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k R M R k)
      (LinearMap.restrictScalars_injective k)
  exact inferInstanceAs (FiniteDimensional k (Module.Dual k (M →ₗ[R] R)))

instance inducedFinite [FiniteDimensional k R] [FiniteDimensional k M] :
    FiniteDimensional k (Obj k R M) := inferInstanceAs (FiniteDimensional k (M × Nakayama k R M))

lemma projective_of_inducedProjective [Module.Finite R M]
    [Module.Projective (TrivialExtension k R) (Obj k R M)] : Module.Projective R M := by
  let c := finiteFreeCover (R := R) (M := M)
  obtain ⟨s,hs⟩ := Module.projective_lifting_property (map (k := k) c.map)
    (LinearMap.id (R := TrivialExtension k R) (M := Obj k R M)) (map_surjective c.map c.surjective)
  apply Module.Projective.of_split (first.comp (restrict s)) c.map
  apply LinearMap.ext
  intro m
  exact congrArg Prod.fst (LinearMap.congr_fun hs (unit m))

variable (C : ChainComplex (ModuleCat R) ℤ)

def inducedResolution (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j)) :
    ProjectiveResolution (ModuleCat.of (TrivialExtension k R) (Obj k R (CokerAt C 0))) := by
  let X (n : ℕ) := ModuleCat.of (TrivialExtension k R) (Obj k R (C.X (n : ℤ)))
  let d (n : ℕ) : X (n+1) ⟶ X n := ModuleCat.ofHom (map (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom)
  let ε : X 0 ⟶ ModuleCat.of (TrivialExtension k R) (Obj k R (CokerAt C 0)) :=
    ModuleCat.ofHom (map (CokerAt.π C 0))
  apply resolutionOfExact _ X d ε
  · intro n
    apply map_exact
    · exact hC.1.adjacent C _ _ _ (by omega) (by omega)
    · exact (Nakayama.complex_exact (k := k) hC).adjacent _ _ _ _ (by omega) (by omega)
  · apply map_exact
    · exact fun x => Submodule.Quotient.mk_eq_zero _
    · exact Nakayama.map_exact _ _ (fun x => Submodule.Quotient.mk_eq_zero _) (CokerAt.π_surjective C 0)
  · exact map_surjective _ (CokerAt.π_surjective C 0)
  · intro n
    let := fin (n : ℤ)
    let := proj (n : ℤ)
    infer_instance

lemma inducedResolution_d (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j)) (n : ℕ) :
    (inducedResolution (k := k) C hC fin proj).complex.d (n+1) n =
      ModuleCat.ofHom (map (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom) := by
  dsimp only [inducedResolution, resolutionOfExact]
  exact ChainComplex.of_d _ _ n

theorem transfer [FiniteDimensional k R] (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j))
    (pos : ∀ n : ℕ, Function.Exact
      (homPrecomp (k := k) (Z := CokerAt C 0) (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom)
      (homPrecomp (k := k) (C.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom))
    (neg : ∀ n : ℕ, Function.Exact
      (homPrecomp (k := k) (Z := CokerAt C 0) (C.d (-((n+1 : ℕ) : ℤ)-1) (-((n+2 : ℕ) : ℤ)-1)).hom)
      (homPrecomp (k := k) (C.d (-(n : ℤ)-1) (-((n+1 : ℕ) : ℤ)-1)).hom))
    (n : ℕ) :
    Subsingleton (Abelian.Ext
      (ModuleCat.of (TrivialExtension k R) (Obj k R (CokerAt C 0)))
      (ModuleCat.of (TrivialExtension k R) (Obj k R (CokerAt C 0))) (n+1)) := by
  let Q := completeResolutionTail C hC.1 proj
  let Z := CokerAt C 0
  let := Nakayama.ext_negative (k := k) C hC fin proj (ModuleCat.of R Z) n (neg n)
  let : Subsingleton (Abelian.Ext (ModuleCat.of R Z) (ModuleCat.of R (Nakayama k R Z)) (n+1)) :=
    ext_subsingleton_target_iso (Nakayama.cokerEquiv (k := k) C).toModuleIso (n+1)
  apply ext_subsingleton_of_boundaries (inducedResolution (k := k) C hC fin proj) n
  intro f hf
  rw [inducedResolution_d] at hf
  let f₀ : Obj k R (C.X ((n+1 : ℕ) : ℤ)) →ₗ[TrivialExtension k R] Obj k R Z := f.hom
  have hf₀ : f₀.comp (map (C.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom) = 0 :=
    congrArg ModuleCat.Hom.hom hf
  have hf' := congrArg (restrict (k := k) (R := R)) hf₀
  rw [restrict_comp] at hf'
  have hzero : restrict (0 : Obj k R (C.X ((n+2 : ℕ) : ℤ)) →ₗ[TrivialExtension k R] Obj k R Z) = 0 := by
    apply LinearMap.ext
    intro x
    rfl
  rw [hzero] at hf'
  have hf₁ : (first.comp (restrict f₀)).comp (C.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom = 0 := by
    rw [LinearMap.comp_assoc, hf', LinearMap.comp_zero]
  obtain ⟨g₁,hg₁⟩ := (pos n (first.comp (restrict f₀))).mp hf₁
  have hf₂ : (Q.complex.d (n+2) (n+1)) ≫ ModuleCat.ofHom (second.comp (restrict f₀)) = 0 := by
    rw [completeResolutionTail_d]
    apply ModuleCat.hom_ext
    change (second.comp (restrict f₀)).comp (C.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom = 0
    rw [LinearMap.comp_assoc, hf', LinearMap.comp_zero]
  obtain ⟨g₂,hg₂⟩ := boundaries_of_ext_subsingleton Q n (ModuleCat.ofHom (second.comp (restrict f₀))) hf₂
  rw [completeResolutionTail_d] at hg₂
  let g : C.X (n : ℤ) →ₗ[R] Obj k R Z := g₁.prod g₂.hom
  refine ⟨ModuleCat.ofHom (lift g), ?_⟩
  rw [inducedResolution_d]
  apply ModuleCat.hom_ext
  change (lift g).comp (map (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom) = f₀
  let := fin ((n+1 : ℕ) : ℤ)
  let : FiniteDimensional k (C.X ((n+1 : ℕ) : ℤ)) := Module.Finite.trans R _
  apply restrict_injective
  rw [restrict_comp, restrict_lift]
  apply LinearMap.ext
  intro x
  exact Prod.ext (LinearMap.congr_fun hg₁ x) (congrArg (fun h => h x) hg₂)

end TrivialInduction



def TrivialInflation (k R M : Type) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] := M

namespace TrivialInflation
variable {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
instance : AddCommGroup (TrivialInflation k R M) := inferInstanceAs (AddCommGroup M)
instance : Module k (TrivialInflation k R M) := inferInstanceAs (Module k M)
instance : Module R (TrivialInflation k R M) := inferInstanceAs (Module R M)
instance : IsScalarTower k R (TrivialInflation k R M) := inferInstanceAs (IsScalarTower k R M)
instance : Module (TrivialExtension k R) (TrivialInflation k R M) :=
  Module.compHom M (TrivSqZeroExt.fstHom k R (DualBimodule k R)).toRingHom
instance : IsScalarTower k (TrivialExtension k R) (TrivialInflation k R M) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change (algebraMap k R c) • (show M from x) = c • x
    exact IsScalarTower.algebraMap_smul R c x
instance [FiniteDimensional k M] : FiniteDimensional k (TrivialInflation k R M) :=
  inferInstanceAs (FiniteDimensional k M)

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma smul_def (a : TrivialExtension k R) (x : TrivialInflation k R M) :
    a • x = (a.fst • (show M from x) : M) := rfl

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma inl_smul (r : R) (x : TrivialInflation k R M) :
    (TrivSqZeroExt.inl r : TrivialExtension k R) • x = r • x := rfl

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma inr_smul (φ : DualBimodule k R) (x : TrivialInflation k R M) :
    (TrivSqZeroExt.inr φ : TrivialExtension k R) • x = 0 := zero_smul R x

def map (f : M →ₗ[R] N) : TrivialInflation k R M →ₗ[TrivialExtension k R] TrivialInflation k R N where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := f.map_smul a.fst x

def restrict (f : TrivialInduction.Obj k R M →ₗ[TrivialExtension k R] TrivialInflation k R N) : M →ₗ[R] N where
  toFun m := f (TrivialInduction.unit m)
  map_add' m n := by rw [map_add, map_add]; rfl
  map_smul' r m := by
    rw [map_smul, ← TrivialInduction.inl_smul, map_smul]
    rfl

def lift (f : M →ₗ[R] N) : TrivialInduction.Obj k R M →ₗ[TrivialExtension k R] TrivialInflation k R N where
  toFun x := f x.1
  map_add' x y := f.map_add x.1 y.1
  map_smul' a x := f.map_smul a.fst x.1

omit [Module k N] [IsScalarTower k R N] in
@[simp] lemma restrict_lift (f : M →ₗ[R] N) : restrict (lift (k := k) f) = f := rfl

omit [Module k N] [IsScalarTower k R N] in
lemma lift_restrict [FiniteDimensional k R] [FiniteDimensional k M]
    (f : TrivialInduction.Obj k R M →ₗ[TrivialExtension k R] TrivialInflation k R N) :
    lift (restrict f) = f := by
  let lower : Nakayama k R M →ₗ[R] TrivialInduction.Obj k R M := LinearMap.inr R M _
  have hz : ∀ ψ : Nakayama k R M, f (lower ψ) = 0 := by
    intro ψ
    obtain ⟨z, rfl⟩ := Nakayama.evaluation_surjective (k := k) (R := R) (M := M) ψ
    induction z using BalancedTensor.induction_on with
    | h0 => rw [map_zero, map_zero, map_zero]
    | ht φ m =>
      have he : lower (Nakayama.evaluation (BalancedTensor.mk φ m)) =
          (TrivSqZeroExt.inr φ : TrivialExtension k R) • TrivialInduction.unit m := by
        apply Prod.ext
        · exact (zero_smul R m).symm
        · change Nakayama.evaluationBilinear φ m = Nakayama.evaluationBilinear φ m + (0:R) • (0 : Nakayama k R M)
          rw [zero_smul, add_zero]
      rw [he, map_smul, inr_smul]
    | ha z w hz hw => rw [map_add, map_add, map_add, hz, hw, add_zero]
  apply LinearMap.ext
  intro x
  have hx : x = TrivialInduction.unit (k := k) (R := R) x.1 + lower x.2 := by
    apply Prod.ext
    · exact (add_zero _).symm
    · exact (zero_add _).symm
  change f (TrivialInduction.unit x.1) = f x
  conv_rhs => rw [hx, map_add, hz, add_zero]

def homEquiv [FiniteDimensional k R] [FiniteDimensional k M] :
    (TrivialInduction.Obj k R M →ₗ[TrivialExtension k R] TrivialInflation k R N) ≃ₗ[k] (M →ₗ[R] N) where
  toFun := restrict
  invFun := lift
  left_inv := lift_restrict
  right_inv := restrict_lift
  map_add' f g := by apply LinearMap.ext; intro m; rfl
  map_smul' c f := by apply LinearMap.ext; intro m; rfl

omit [Module k N] [IsScalarTower k R N] in
lemma restrict_comp {P : Type} [AddCommGroup P] [Module R P] [Module k P] [IsScalarTower k R P]
    (f : TrivialInduction.Obj k R M →ₗ[TrivialExtension k R] TrivialInflation k R N)
    (a : P →ₗ[R] M) :
    restrict (f.comp (TrivialInduction.map a)) = (restrict f).comp a := by
  apply LinearMap.ext
  intro p
  change f (TrivialInduction.map a (TrivialInduction.unit p)) = f (TrivialInduction.unit (a p))
  rw [TrivialInduction.map_unit]

end TrivialInflation
end Tachikawa

end

end OAI
