import OAI.RingTheory.Tachikawa.Tensor

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

structure FiniteModule (k R : Type) [Field k] [Ring R] [Algebra k R] where
  obj : ModuleCat.{0} R
  finite : Module.Finite R obj

namespace FiniteModule
instance : CoeSort (FiniteModule k R) Type := ⟨fun M => M.obj⟩
instance (M : FiniteModule k R) : AddCommGroup M := inferInstanceAs (AddCommGroup M.obj)
instance (M : FiniteModule k R) : Module R M := inferInstanceAs (Module R M.obj)
instance (M : FiniteModule k R) : Module k M := inferInstanceAs (Module k M.obj)
instance (M : FiniteModule k R) : IsScalarTower k R M := inferInstanceAs (IsScalarTower k R M.obj)
instance (M : FiniteModule k R) : Module.Finite R M := M.finite
instance (M : FiniteModule k R) : Module.Finite k M := Module.Finite.trans R M

variable (M : FiniteModule k R)

def cover : FiniteFreeCover R M := finiteFreeCover

def syzygy : FiniteModule k R where
  obj := ModuleCat.of R (LinearMap.ker M.cover.map)
  finite := by
    let : IsNoetherianRing R := IsNoetherianRing.of_finite k R
    exact inferInstanceAs (Module.Finite R (LinearMap.ker M.cover.map))

variable (t : SymmetrizingForm (k := k) (R := R))

def embed : M →ₗ[R] (Fin (Module.finrank k M) → R) := t.freeEmbedding
lemma embed_injective : Function.Injective (M.embed t) := t.freeEmbedding_injective

def cosyzygy : FiniteModule k R where
  obj := ModuleCat.of R ((Fin (Module.finrank k M) → R) ⧸ LinearMap.range (M.embed t))
  finite := inferInstanceAs (Module.Finite R ((Fin (Module.finrank k M) → R) ⧸ LinearMap.range (M.embed t)))

def positive : ℕ → FiniteModule k R
  | 0 => M
  | n+1 => (positive n).syzygy

def negative : ℕ → FiniteModule k R
  | 0 => M
  | n+1 => (negative n).cosyzygy t

abbrev posTerm (n : ℕ) := Fin (M.positive n).cover.rank → R
abbrev negTerm (n : ℕ) := Fin (Module.finrank k (M.negative t n)) → R

def posDifferential (n : ℕ) : M.posTerm (n+1) →ₗ[R] M.posTerm n :=
  (LinearMap.ker (M.positive n).cover.map).subtype.comp (M.positive (n+1)).cover.map

def negDifferential (n : ℕ) : M.negTerm t n →ₗ[R] M.negTerm t (n+1) :=
  ((M.negative t (n+1)).embed t).comp (LinearMap.range ((M.negative t n).embed t)).mkQ

def middle : M.posTerm 0 →ₗ[R] M.negTerm t 0 := (M.embed t).comp M.cover.map

lemma pos_exact (n : ℕ) : Function.Exact (M.posDifferential (n+1)) (M.posDifferential n) := by
  intro x
  change ((M.positive (n+1)).cover.map x).val = 0 ↔ _
  constructor
  · intro hx
    have hx' : (M.positive (n+1)).cover.map x = 0 := Subtype.ext hx
    obtain ⟨y, hy⟩ := (M.positive (n+2)).cover.surjective ⟨x, hx'⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, rfl⟩
    exact congrArg Subtype.val ((M.positive (n+2)).cover.map y).property

lemma neg_exact (n : ℕ) : Function.Exact (M.negDifferential t n) (M.negDifferential t (n+1)) := by
  intro x
  constructor
  · intro hx
    have hz : (LinearMap.range ((M.negative t (n+1)).embed t)).mkQ x = 0 :=
      (M.negative t (n+2)).embed_injective t (hx.trans ((M.negative t (n+2)).embed t).map_zero.symm)
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨z, hz⟩ := (Submodule.mkQ_surjective (LinearMap.range ((M.negative t n).embed t))) y
    refine ⟨z, ?_⟩
    change (M.negative t (n+1)).embed t ((LinearMap.range ((M.negative t n).embed t)).mkQ z) = x
    exact (congrArg ((M.negative t (n+1)).embed t) hz).trans hy
  · rintro ⟨y, rfl⟩
    apply ((M.negative t (n+2)).embed t).map_eq_zero_iff ((M.negative t (n+2)).embed_injective t) |>.mpr
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩

lemma middle_exact_left : Function.Exact (M.posDifferential 0) (M.middle t) := by
  intro x
  change M.embed t (M.cover.map x) = 0 ↔ _
  rw [map_eq_zero_iff _ (M.embed_injective t)]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (M.positive 1).cover.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, rfl⟩
    exact ((M.positive 1).cover.map y).property

lemma middle_exact_right : Function.Exact (M.middle t) (M.negDifferential t 0) := by
  intro x
  constructor
  · intro hx
    have hz : (LinearMap.range (M.embed t)).mkQ x = 0 :=
      (M.negative t 1).embed_injective t (hx.trans ((M.negative t 1).embed t).map_zero.symm)
    obtain ⟨y, rfl⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨z, rfl⟩ := M.cover.surjective y
    exact ⟨z, rfl⟩
  · rintro ⟨y, rfl⟩
    apply ((M.negative t 1).embed t).map_eq_zero_iff ((M.negative t 1).embed_injective t) |>.mpr
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨M.cover.map y, rfl⟩

def term : ℤ → ModuleCat R
  | .ofNat n => ModuleCat.of R (M.posTerm n)
  | .negSucc n => ModuleCat.of R (M.negTerm t n)

def differential (j : ℤ) : M.term t (j+1) ⟶ M.term t j := by
  cases j with
  | ofNat n => exact ModuleCat.ofHom (M.posDifferential n)
  | negSucc n =>
    cases n with
    | zero => exact ModuleCat.ofHom (M.middle t)
    | succ n =>
      exact ModuleCat.ofHom (M.negDifferential t n)

lemma differential_exact (j : ℤ) :
    Function.Exact (M.differential t (j+1)) (M.differential t j) := by
  cases j with
  | ofNat n => exact M.pos_exact n
  | negSucc n =>
    cases n with
    | zero => exact M.middle_exact_left t
    | succ n =>
      cases n with
      | zero => exact M.middle_exact_right t
      | succ n =>
        exact M.neg_exact t n

def complete : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (M.term t) (M.differential t) (fun j =>
    ModuleCat.hom_ext <| LinearMap.ext <| (M.differential_exact t j).apply_apply_eq_zero)

lemma complete_exact : ComplexExact (M.complete t) := by
  suffices ∀ (j i : ℤ), i=j-1 →
      Function.Exact ((M.complete t).d (j+1) j) ((M.complete t).d j i) by
    exact fun j => this j (j-1) rfl
  intro j i hi
  have hj : j=i+1 := by omega
  subst j
  change Function.Exact (ChainComplex.of.d (M.term t) (M.differential t) (i+1+1) (i+1))
    (ChainComplex.of.d (M.term t) (M.differential t) (i+1) i)
  simp only [ChainComplex.of_d]
  exact M.differential_exact t i

lemma complete_projective (j : ℤ) : Module.Projective R ((M.complete t).X j) := by
  cases j <;> exact inferInstanceAs (Module.Projective R (Fin _ → R))

lemma complete_finite (j : ℤ) : Module.Finite R ((M.complete t).X j) := by
  cases j <;> exact inferInstanceAs (Module.Finite R (Fin _ → R))

@[simp] lemma complete_d (j : ℤ) : (M.complete t).d (j+1) j = M.differential t j :=
  ChainComplex.of_d _ _ j

def augmentation : CokerAt (M.complete t) 0 →ₗ[R] M :=
  CokerAt.descend _ _ M.cover.map (by
    rw [complete_d]
    apply LinearMap.ext
    intro x
    exact ((M.positive 1).cover.map x).property)

lemma augmentation_surjective : Function.Surjective (M.augmentation t) := by
  intro x
  obtain ⟨y, rfl⟩ := M.cover.surjective x
  exact ⟨CokerAt.π (M.complete t) 0 y, rfl⟩

lemma augmentation_injective : Function.Injective (M.augmentation t) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨y, rfl⟩ := CokerAt.π_surjective (M.complete t) 0 x
  change M.cover.map y = 0 at hx
  obtain ⟨z, hz⟩ := (M.positive 1).cover.surjective ⟨y, hx⟩
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  use z
  rw [complete_d]
  exact congrArg Subtype.val hz

def cokerEquiv : CokerAt (M.complete t) 0 ≃ₗ[R] M :=
  LinearEquiv.ofBijective (M.augmentation t)
    ⟨M.augmentation_injective t, M.augmentation_surjective t⟩

lemma complete_totallyAcyclic : TotallyAcyclic (M.complete t) := by
  refine ⟨M.complete_exact t, ?_⟩
  intro j f hf
  let : Module.Injective R R := t.injective
  obtain ⟨g, hg⟩ := Module.Injective.extension_property R R
    (CokerAt (M.complete t) j) ((M.complete t).X (j-1))
    (CokerAt.ι (M.complete t) j) (CokerAt.ι_injective _ _ (M.complete_exact t j))
    (CokerAt.descend _ _ f hf)
  refine ⟨g, ?_⟩
  have hh := congrArg (fun a => a.comp (CokerAt.π (M.complete t) j)) hg
  simpa only [LinearMap.comp_assoc, CokerAt.ι_comp_π, CokerAt.descend_comp_π] using hh

end FiniteModule
end Tachikawa



namespace Tachikawa.FiniteModule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R)

lemma pos_augmentation_exact : Function.Exact (M.posDifferential 0) M.cover.map := by
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (M.positive 1).cover.surjective ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩
  · rintro ⟨y,rfl⟩
    exact ((M.positive 1).cover.map y).property

def projectiveResolution : ProjectiveResolution M.obj :=
  resolutionOfExact M.obj (fun n => ModuleCat.of R (M.posTerm n))
    (fun n => ModuleCat.ofHom (M.posDifferential n)) (ModuleCat.ofHom M.cover.map)
    M.pos_exact M.pos_augmentation_exact M.cover.surjective (fun _ => by infer_instance)

instance (n : ℕ) : Module.Finite R (M.projectiveResolution.complex.X n) := by
  change Module.Finite R (M.posTerm n)
  infer_instance

instance (n : ℕ) : FiniteDimensional k (M.projectiveResolution.complex.X n) :=
  Module.Finite.trans R _

end Tachikawa.FiniteModule



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (M : ModuleCat.{0} (Alg k S R))

abbrev tensorFunctor : ModuleCat.{0} R ⥤ ModuleCat.{0} S :=
  BalancedTensor.functor (k := k) (R := R) (S := S) (M := Obj M)

abbrev tensorComplex (P : ChainComplex (ModuleCat.{0} R) ℤ) :=
  ((tensorFunctor M).mapHomologicalComplex (.down ℤ)).obj P

lemma tensorComplex_exact [FiniteDimensional k (Obj M)] [Module.Projective Rᵐᵒᵖ (Obj M)]
    (P : ChainComplex (ModuleCat.{0} R) ℤ) (hP : ComplexExact P) :
    ComplexExact (tensorComplex M P) := by
  let : Module.Finite Rᵐᵒᵖ (Obj M) := Module.Finite.of_restrictScalars_finite k _ _
  intro j
  exact BalancedTensor.mapRight_exact (P.d (j+1) j).hom (P.d j (j-1)).hom (hP j)

lemma tensorComplex_finite [FiniteDimensional k R] [FiniteDimensional k (Obj M)]
    (P : ChainComplex (ModuleCat.{0} R) ℤ) (fin : ∀ j, Module.Finite R (P.X j)) (j : ℤ) :
    Module.Finite S ((tensorComplex M P).X j) := by
  let := fin j
  let : FiniteDimensional k (P.X j) := Module.Finite.trans R _
  let : FiniteDimensional k ((tensorComplex M P).X j) := inferInstanceAs
    (FiniteDimensional k (BalancedTensor.T (k := k) (R := R) (S := S) (M := Obj M) (N := P.X j)))
  exact Module.Finite.of_restrictScalars_finite k _ _

lemma tensorComplex_projective [Module.Projective S (Obj M)]
    (P : ChainComplex (ModuleCat.{0} R) ℤ)
    (fin : ∀ j, Module.Finite R (P.X j)) (proj : ∀ j, Module.Projective R (P.X j)) (j : ℤ) :
    Module.Projective S ((tensorComplex M P).X j) := by
  let := fin j
  let := proj j
  exact BalancedTensor.map_projective (k := k) (R := R) (S := S) (M := Obj M) (N := P.X j)

variable [FiniteDimensional k R] [FiniteDimensional k (Obj M)]
  [Module.Projective Rᵐᵒᵖ (Obj M)]
  (N : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))

lemma tensor_augmentation_exact : Function.Exact
    ((tensorComplex M (N.complete t)).d 1 0)
    ((tensorFunctor M).map (ModuleCat.ofHom N.cover.map)) := by
  let : Module.Finite Rᵐᵒᵖ (Obj M) := Module.Finite.of_restrictScalars_finite k _ _
  apply BalancedTensor.mapRight_exact
  change Function.Exact ((N.complete t).d (0+1) 0) N.cover.map
  rw [N.complete_d]
  exact N.pos_augmentation_exact

omit [FiniteDimensional k R] [FiniteDimensional k (Obj M)] [Module.Projective Rᵐᵒᵖ (Obj M)] in
lemma tensor_map_surjective {X Y : ModuleCat R} (f : X ⟶ Y)
    (hf : Function.Surjective f) : Function.Surjective ((tensorFunctor M).map f) :=
  BalancedTensor.mapRight_surjective f.hom hf

def tensorAugmentationEquiv : CokerAt (tensorComplex M (N.complete t)) 0 ≃ₗ[S]
    (tensorFunctor M).obj N.obj :=
  CokerAt.augmentationEquiv _ _ 0
    ((tensorFunctor M).map (ModuleCat.ofHom N.cover.map)).hom
    (tensor_augmentation_exact M N t)
    (tensor_map_surjective M (X := (N.complete t).X 0) (Y := N.obj)
      (ModuleCat.ofHom N.cover.map) N.cover.surjective)

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (M : Type) [AddCommGroup M] [Module k M] [Module R M] [Module Sᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]

def action : Alg k R S →ₐ[k] Module.End k M :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k M) (Algebra.lsmul k k M)
    (fun r s => by
      ext x
      exact smul_comm r s x)

def ofBimodule : ModuleCat (Alg k R S) :=
  letI := Module.compHom M (action (k := k) (R := R) (S := S) M).toRingHom
  ModuleCat.of (Alg k R S) M

end Enveloping

namespace BalancedTensor
variable {k R S U M N : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N] [Module Uᵐᵒᵖ N]
  [IsScalarTower k R N] [IsScalarTower k Uᵐᵒᵖ N] [SMulCommClass R Uᵐᵒᵖ N]

local instance : SMulCommClass Uᵐᵒᵖ R N := SMulCommClass.symm R Uᵐᵒᵖ N

def rightAction : Uᵐᵒᵖ →+* Module.End S (T (k := k) (R := R) (S := S) (M := M) (N := N)) where
  toFun u := mapRight ((Algebra.lsmul k R N) u)
  map_one' := by
    change mapRight (k := k) (S := S) (M := M) ((Algebra.lsmul k R N) 1) = LinearMap.id
    rw [map_one]
    exact mapRight_id
  map_mul' u v := by
    change mapRight (k := k) (S := S) (M := M) ((Algebra.lsmul k R N) (u*v)) = _
    rw [map_mul]
    exact mapRight_comp _ _
  map_zero' := by rw [map_zero]; exact mapRight_zero
  map_add' u v := by rw [map_add]; exact mapRight_add _ _

instance rightModule : Module Uᵐᵒᵖ (T (k := k) (R := R) (S := S) (M := M) (N := N)) :=
  Module.compHom _ (rightAction (k := k) (R := R) (S := S) (M := M) (N := N))

@[simp] lemma right_smul_mk (u : Uᵐᵒᵖ) (m : M) (n : N) :
    u • (mk (k := k) (R := R) (S := S) m n) = mk m (u • n) := rfl

instance rightTower : IsScalarTower k Uᵐᵒᵖ (T (k := k) (R := R) (S := S) (M := M) (N := N)) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    induction x using induction_on with
    | h0 => simp
    | ht m n =>
      rw [right_smul_mk, IsScalarTower.algebraMap_smul]
      exact (mk m).map_smul c n
    | ha x y hx hy => simp only [smul_add, hx, hy]

instance rightComm : SMulCommClass S Uᵐᵒᵖ (T (k := k) (R := R) (S := S) (M := M) (N := N)) where
  smul_comm s u x := by
    change s • (rightAction (k := k) (R := R) (S := S) (M := M) (N := N) u) x =
      (rightAction (k := k) (R := R) (S := S) (M := M) (N := N) u) (s • x)
    exact ((rightAction (k := k) (R := R) (S := S) (M := M) (N := N) u).map_smul s x).symm

end BalancedTensor
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable {M N : Type} [AddCommGroup M] [Module k M] [Module R M] [Module Sᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module R N] [Module Sᵐᵒᵖ N]
  [IsScalarTower k R N] [IsScalarTower k Sᵐᵒᵖ N] [SMulCommClass R Sᵐᵒᵖ N]

lemma ofBimodule_tmul_smul (r : R) (s : Sᵐᵒᵖ) (m : M) :
    (r ⊗ₜ[k] s) • (show ofBimodule (k := k) (R := R) (S := S) M from m) =
      (show ofBimodule (k := k) (R := R) (S := S) M from r • s • m) := rfl

def ofBimoduleHom (f : M →ₗ[R] N) (hf : ∀ (s : Sᵐᵒᵖ) m, f (s • m) = s • f m) :
    ofBimodule (k := k) (R := R) (S := S) M ⟶ ofBimodule (k := k) (R := R) (S := S) N :=
  ModuleCat.ofHom (X := ofBimodule (k := k) (R := R) (S := S) M)
    (Y := ofBimodule (k := k) (R := R) (S := S) N)
  { toFun := fun x => f x
    map_add' := f.map_add
    map_smul' a x := by
      change f ((action (k := k) (R := R) (S := S) M a) (show M from x)) =
        (action (k := k) (R := R) (S := S) N a) (f x)
      induction a using TensorProduct.inductionOn with
      | tmul r s =>
        change f (r • s • (show M from x)) = r • s • (show N from f x)
        exact (f.map_smul r _).trans (congrArg (fun z => r • z) (hf s x))
      | add a b ha hb =>
        rw [map_add, map_add]
        change f ((action (k := k) (R := R) (S := S) M a) x +
          (action (k := k) (R := R) (S := S) M b) x) = _
        exact (f.map_add _ _).trans (congrArg₂ (fun x y : N => x+y) ha hb) }

def reassembleIso (M : ModuleCat (Alg k R S)) :
    ofBimodule (k := k) (R := R) (S := S) (Obj M) ≅ M :=
  LinearEquiv.toModuleIso (show (ofBimodule (k := k) (R := R) (S := S) (Obj M)) ≃ₗ[Alg k R S] M from
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' a x := by
      change (show M from (action (k := k) (R := R) (S := S) (Obj M) a) x) = a • (show M from x)
      induction a using TensorProduct.inductionOn with
      | tmul r s => exact (tmul_smul M r s x).symm
      | add a b ha hb =>
        rw [map_add, add_smul]
        exact congrArg₂ (fun x y : M => x+y) ha hb })

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R)

abbrev evalType (M : ModuleCat (Alg k S R)) :=
  BalancedTensor.T (k := k) (R := R) (S := S) (M := Obj M) (N := X)

def evalObj (M : ModuleCat (Alg k S R)) : ModuleCat S := ModuleCat.of S (evalType X M)

def evalMap {M N : ModuleCat (Alg k S R)} (f : M ⟶ N) : evalObj X M ⟶ evalObj X N :=
  ModuleCat.ofHom (BalancedTensor.mapLeft (k := k) (R := R) (S := S) (N := X)
    (leftMap f) (fun r m => (rightMap f).map_smul r m))

@[simp] lemma evalMap_mk {M N : ModuleCat (Alg k S R)} (f : M ⟶ N) (m : Obj M) (x : X) :
    evalMap X f (BalancedTensor.mk m x) = BalancedTensor.mk (k := k) (R := R) (S := S) (N := X) (leftMap f m) x := rfl

def evaluation : ModuleCat (Alg k S R) ⥤ ModuleCat S where
  obj := evalObj X
  map := evalMap X
  map_id M := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl

instance : (evaluation (S := S) (k := k) X).Additive where
  map_add {M N f g} := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (k := k) (R := R) (S := S) (N := X) (leftMap (f+g) m) x =
      BalancedTensor.mk (k := k) (R := R) (S := S) (N := X) (leftMap f m) x + BalancedTensor.mk (k := k) (R := R) (S := S) (N := X) (leftMap g m) x
    exact congrArg (fun h : X →ₗ[k] evalType X N => h x)
      ((BalancedTensor.mk (k := k) (R := R) (S := S) (M := Obj N) (N := X)).map_add
        (leftMap f m) (leftMap g m))

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def tensorNatTrans {M M' : ModuleCat (Alg k R R)} (f : M ⟶ M') :
    tensorFunctor M ⟶ tensorFunctor M' where
  app X := evalMap X f
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl

variable [FiniteDimensional k R] (M : ModuleCat (Alg k R R))
  [FiniteDimensional k (Obj M)] [Module.Projective R (Obj M)]
  [Module.Projective Rᵐᵒᵖ (Obj M)]
  (N : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))
  (v : N.obj ⟶ (tensorFunctor M).obj N.obj)

lemma exists_tensorCompleteLift : ∃ l : N.complete t ⟶ tensorComplex M (N.complete t),
    l.f 0 ≫ (tensorFunctor M).map (ModuleCat.ofHom N.cover.map) =
      ModuleCat.ofHom N.cover.map ≫ v := by
  let u := (tensorAugmentationEquiv M N t).symm.toLinearMap.comp
    (v.hom.comp (N.cokerEquiv t).toLinearMap)
  obtain ⟨l,hl⟩ := exists_complete_lift (N.complete t) (tensorComplex M (N.complete t))
    (N.complete_totallyAcyclic t) (tensorComplex_exact M _ (N.complete_exact t))
    (N.complete_projective t) (tensorComplex_finite M _ (N.complete_finite t))
    (tensorComplex_projective M _ (N.complete_finite t) (N.complete_projective t)) u
  refine ⟨l,?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx := congrArg (tensorAugmentationEquiv M N t)
    (LinearMap.congr_fun hl (CokerAt.π (N.complete t) 0 x))
  change (tensorAugmentationEquiv M N t) (CokerAt.π _ 0 (l.f 0 x)) =
    (tensorAugmentationEquiv M N t) ((tensorAugmentationEquiv M N t).symm
      (v ((N.cokerEquiv t) (CokerAt.π _ 0 x)))) at hx
  rw [LinearEquiv.apply_symm_apply] at hx
  exact hx

def tensorCompleteLift : N.complete t ⟶ tensorComplex M (N.complete t) :=
  (exists_tensorCompleteLift M N t v).choose
lemma tensorCompleteLift_aug : (tensorCompleteLift M N t v).f 0 ≫
    (tensorFunctor M).map (ModuleCat.ofHom N.cover.map) = ModuleCat.ofHom N.cover.map ≫ v :=
  (exists_tensorCompleteLift M N t v).choose_spec

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)

def GoodComponent (i j : ℤ) (h : P.X i →ₗ[R] Q.X j) : Prop :=
  ((f.f i).hom - (Q.d j i).hom.comp h).comp (P.d j i).hom = 0

lemma goodComponent_up (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (i j l : ℤ) (hij : i+1=j) (hjl : j+1=l)
    (a : P.X i →ₗ[R] Q.X j) (ha : GoodComponent f i j a) :
    ∃ b : P.X j →ₗ[R] Q.X l,
      (f.f j).hom = a.comp (P.d j i).hom + (Q.d l j).hom.comp b ∧
      GoodComponent f j l b := by
  let := pproj j
  let r := (f.f j).hom - a.comp (P.d j i).hom
  have hr (x : P.X j) : r x ∈ LinearMap.range (Q.d l j).hom := by
    have he := hq j
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

lemma goodComponent_down (hp : TotallyAcyclic P)
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
    (i j l : ℤ) (hij : i+1=j) (hjl : j+1=l)
    (b : P.X j →ₗ[R] Q.X l) (hb : GoodComponent f j l b) :
    ∃ a : P.X i →ₗ[R] Q.X j,
      (f.f j).hom = a.comp (P.d j i).hom + (Q.d l j).hom.comp b ∧
      GoodComponent f i j a := by
  subst l
  let := qfin j
  let := qproj j
  have hi : i = j-1 := by omega
  subst i
  obtain ⟨a, ha⟩ := hp.projective_boundaries j
    ((f.f j).hom - (Q.d (j+1) j).hom.comp b) hb
  refine ⟨a, ?_, ?_⟩
  · rw [ha]
    abel
  · unfold GoodComponent
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply]
    have hc := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.comm j (j-1))) x
    change Q.d j (j-1) (f.f j x) = f.f (j-1) (P.d j (j-1) x) at hc
    have hx := LinearMap.congr_fun ha x
    change a (P.d j (j-1) x) = f.f j x - Q.d (j+1) j (b x) at hx
    rw [hx, map_sub, ← hc]
    have hd := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (Q.d_comp_d (j+1) j (j-1))) (b x)
    change Q.d j (j-1) (Q.d (j+1) j (b x)) = 0 at hd
    rw [hd, sub_zero, sub_self]

namespace CompleteNull

def State (j : ℤ) := {h : P.X j →ₗ[R] Q.X (j+1) // GoodComponent f j (j+1) h}

def stateMap {i : ℤ} (a : State f i) (j : ℤ) (h : i+1=j) : P.X i →ₗ[R] Q.X j := by
  subst j
  exact a.val

@[simp] lemma stateMap_self {i : ℤ} (a : State f i) : stateMap f a (i+1) rfl = a.val := rfl

def Step (i j : ℤ) (h : i+1=j) (a : State f i) (b : State f j) : Prop :=
  (f.f j).hom = (stateMap f a j h).comp (P.d j i).hom + (Q.d (j+1) j).hom.comp b.val

variable (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))

def up (j : ℤ) (a : State f j) : State f (j+1) :=
  let h := goodComponent_up f hq pproj j (j+1) (j+1+1) rfl rfl a.val a.property
  ⟨h.choose, h.choose_spec.2⟩

lemma up_step (j : ℤ) (a : State f j) : Step f j (j+1) rfl a (up f hq pproj j a) :=
  (goodComponent_up f hq pproj j (j+1) (j+1+1) rfl rfl a.val a.property).choose_spec.1

def down (i j : ℤ) (h : i+1=j) (b : State f j) : State f i := by
  subst j
  let h := goodComponent_down f hp qfin qproj i (i+1) (i+1+1) rfl rfl b.val b.property
  exact ⟨h.choose, h.choose_spec.2⟩

lemma down_step (i j : ℤ) (h : i+1=j) (b : State f j) :
    Step f i j h (down f hp qfin qproj i j h b) b := by
  subst j
  exact (goodComponent_down f hp qfin qproj i (i+1) (i+1+1) rfl rfl b.val b.property).choose_spec.1

variable (b₀ : State f 0)

def component (j : ℤ) : State f j :=
  j.inductionOn' 0 b₀ (fun j _ => up f hq pproj j)
    (fun j _ => down f hp qfin qproj (j-1) j (by omega))

lemma component_up (j : ℤ) (hj : 0 ≤ j) :
    component f hp hq pproj qfin qproj b₀ (j+1) =
      up f hq pproj j (component f hp hq pproj qfin qproj b₀ j) :=
  Int.inductionOn'_add_one hj

lemma component_down (j : ℤ) (hj : j ≤ 0) :
    component f hp hq pproj qfin qproj b₀ (j-1) =
      down f hp qfin qproj (j-1) j (by omega) (component f hp hq pproj qfin qproj b₀ j) :=
  Int.inductionOn'_sub_one hj

lemma hasStep_down (i j : ℤ) (h : i+1=j) (hj : j ≤ 0) :
    Step f i j h (component f hp hq pproj qfin qproj b₀ i)
      (component f hp hq pproj qfin qproj b₀ j) := by
  have hi : i=j-1 := by omega
  subst i
  rw [component_down f hp hq pproj qfin qproj b₀ j hj]
  exact down_step f hp qfin qproj (j-1) j h _

lemma hasStep (i j : ℤ) (h : i+1=j) :
    Step f i j h (component f hp hq pproj qfin qproj b₀ i)
      (component f hp hq pproj qfin qproj b₀ j) := by
  by_cases hi : 0 ≤ i
  · subst j
    rw [component_up f hp hq pproj qfin qproj b₀ i hi]
    exact up_step f hq pproj i _
  · exact hasStep_down f hp hq pproj qfin qproj b₀ i j h (by omega)

def homotopy : Homotopy f 0 where
  hom i j := if h : i+1=j then
    ModuleCat.ofHom (stateMap f (component f hp hq pproj qfin qproj b₀ i) j h) else 0
  zero i j h := by
    exact dite_eq_right h
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i-1) by change i-1+1=i; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (i+1) i from rfl)]
    simp only [dite_eq_left (show i-1+1=i by omega), zero_f, add_zero]
    apply ModuleCat.hom_ext
    exact hasStep f hp hq pproj qfin qproj b₀ (i-1) i (by omega)

end CompleteNull

variable {k : Type} [Field k] [Algebra k R]

lemma exists_good_component_zero (hp : TotallyAcyclic P)
    (pproj : Module.Projective R (P.X 0))
    (hf : CokerAt.map f 0 ∈ projectiveFactors (k := k)) :
    Nonempty (CompleteNull.State f 0) := by
  obtain ⟨J, hJf, hJp, a, b, hab⟩ := hf
  let := hJf
  let := hJp
  let := pproj
  obtain ⟨a', ha⟩ := hp.extend_at 0 (-1) rfl a
  obtain ⟨b', hb⟩ := Module.projective_lifting_property (CokerAt.π Q 0) b
    (CokerAt.π_surjective Q 0)
  let r := (f.f 0).hom - (b'.comp a').comp (P.d 0 (-1)).hom
  have hr (x : P.X 0) : r x ∈ LinearMap.range (Q.d 1 0).hom := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change CokerAt.π Q 0 (r x) = 0
    have ha' := LinearMap.congr_fun ha (CokerAt.π P 0 x)
    change a' (P.d 0 (-1) x) = a (CokerAt.π P 0 x) at ha'
    have hb' := LinearMap.congr_fun hb (a (CokerAt.π P 0 x))
    change CokerAt.π Q 0 (b' (a (CokerAt.π P 0 x))) = b (a (CokerAt.π P 0 x)) at hb'
    have hab' := LinearMap.congr_fun hab (CokerAt.π P 0 x)
    change b (a (CokerAt.π P 0 x)) = CokerAt.π Q 0 (f.f 0 x) at hab'
    change CokerAt.π Q 0 (f.f 0 x - b' (a' (P.d 0 (-1) x))) = 0
    rw [map_sub, ha', hb', hab', sub_self]
  obtain ⟨c, hc⟩ := Module.projective_lifting_property
    (Q.d 1 0).hom.rangeRestrict (r.codRestrict _ hr)
    (by rintro ⟨x, y, rfl⟩; exact ⟨y, rfl⟩)
  have hc' : (Q.d 1 0).hom.comp c = r := by
    ext x
    exact congrArg Subtype.val (LinearMap.congr_fun hc x)
  refine ⟨⟨c, ?_⟩⟩
  unfold GoodComponent
  change ((f.f 0).hom - (Q.d 1 0).hom.comp c).comp (P.d 1 0).hom = 0
  rw [hc']
  dsimp only [r]
  rw [sub_sub_cancel, LinearMap.comp_assoc]
  have hd : (P.d 0 (-1)).hom.comp (P.d 1 0).hom = 0 :=
    ModuleCat.hom_ext_iff.mp (P.d_comp_d _ _ _)
  rw [hd, LinearMap.comp_zero]

theorem nullhomotopic_of_coker_factors (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
    (hf : CokerAt.map f 0 ∈ projectiveFactors (k := k)) : Nonempty (Homotopy f 0) := by
  obtain ⟨b₀⟩ := exists_good_component_zero f hp (pproj 0) hf
  exact ⟨CompleteNull.homotopy f hp hq pproj qfin qproj b₀⟩

lemma coker_factors_of_nullhomotopic (h : Homotopy f 0)
    (pfin : Module.Finite R (P.X (-1))) (pproj : Module.Projective R (P.X (-1))) :
    CokerAt.map f 0 ∈ projectiveFactors (k := k) := by
  refine ⟨P.X (-1), pfin, pproj, CokerAt.δ P 0 (-1),
    (CokerAt.π Q 0).comp (h.hom (-1) 0).hom, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := CokerAt.π_surjective P 0 x
  have hc := h.comm 0
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel 0 (-1) by decide),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel 1 0 by decide)] at hc
  have hc' := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hc) y
  change f.f 0 y = h.hom (-1) 0 (P.d 0 (-1) y) +
    Q.d 1 0 (h.hom 0 1 y) + 0 at hc'
  change CokerAt.π Q 0 (h.hom (-1) 0 (P.d 0 (-1) y)) = CokerAt.π Q 0 (f.f 0 y)
  have hz : CokerAt.π Q 0 (Q.d 1 0 (h.hom 0 1 y)) = 0 :=
    LinearMap.congr_fun (CokerAt.π_d Q 0) (h.hom 0 1 y)
  rw [hc', add_zero, map_add, hz, add_zero]

theorem nullhomotopic_iff_coker_factors (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (pfin : Module.Finite R (P.X (-1)))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j)) :
    Nonempty (Homotopy f 0) ↔ CokerAt.map f 0 ∈ projectiveFactors (k := k) := by
  constructor
  · rintro ⟨h⟩
    exact coker_factors_of_nullhomotopic f h pfin (pproj (-1))
  · exact nullhomotopic_of_coker_factors f hp hq pproj qfin qproj

end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {P Q : ChainComplex (ModuleCat.{0} R) ℤ}

include k in
lemma complete_homotopy_of_augmentation (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
    {N : ModuleCat.{0} R} (a : Q.X 0 →ₗ[R] N)
    (he : Function.Exact (Q.d 1 0) a) (hs : Function.Surjective a)
    (f g : P ⟶ Q) (hfg : a.comp (f.f 0).hom = a.comp (g.f 0).hom) :
    Nonempty (Homotopy f g) := by
  have hz : CokerAt.map (f-g) 0 = 0 := by
    ext x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective P 0 x
    apply (CokerAt.augmentationEquiv Q N 0 a he hs).injective
    change a (f.f 0 y-g.f 0 y) = _
    have hy : a (f.f 0 y) = a (g.f 0 y) := LinearMap.congr_fun hfg y
    rw [map_sub,hy,sub_self]
    exact (map_zero _).symm
  obtain ⟨h⟩ := nullhomotopic_of_coker_factors (k := k) (f-g) hp hq pproj qfin qproj
    (by rw [hz]; exact (projectiveFactors (k := k)).zero_mem)
  exact ⟨Homotopy.equivSubZero.symm h⟩

end Tachikawa

end

end OAI
