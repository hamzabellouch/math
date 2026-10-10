import OAI.RingTheory.Tachikawa.Cone

namespace OAI


noncomputable section
namespace Tachikawa.SourceField
open CategoryTheory Construction
open scoped ModuleCat.Algebra
abbrev sourceF := concreteF q (parameter_ne_zero 0) one_add_q_pow_ne_zero
  H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)
abbrev sourceX := finiteX q
abbrev sourceP := xComplete q
local instance sourceF_left : Module.Projective (E q) (Enveloping.Obj sourceF.obj) :=
  (concreteF_side_projective q (parameter_ne_zero 0) one_add_q_pow_ne_zero
    H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)).1
local instance sourceF_right : Module.Projective (E q)ᵐᵒᵖ (Enveloping.Obj sourceF.obj) :=
  (concreteF_side_projective q (parameter_ne_zero 0) one_add_q_pow_ne_zero
    H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)).2
local instance sourceF_finite : FiniteDimensional K (Enveloping.Obj sourceF.obj) :=
  inferInstanceAs (FiniteDimensional K sourceF)
abbrev sourceU := concreteLift q (parameter_ne_zero 0) one_add_q_pow_ne_zero
  H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)
abbrev sourceUZero := concreteVZero q (parameter_ne_zero 0) one_add_q_pow_ne_zero
  H₁ H₂ (parameter_ne_zero 1) (parameter_ne_zero 2)
abbrev sourceTriangle := Triangular.Alg sourceF.obj
abbrev sourceCone := Triangular.cone sourceF.obj sourceU
lemma sourceCone_totallyAcyclic : TotallyAcyclic sourceCone :=
  Triangular.cone_totallyAcyclic sourceF.obj sourceU (sourceX.complete_totallyAcyclic (formE q))
lemma sourceCone_finite (j : ℤ) : Module.Finite sourceTriangle (sourceCone.X j) :=
  Triangular.cone_finite sourceF.obj sourceU (sourceX.complete_finite (formE q)) j
lemma sourceCone_projective (j : ℤ) : Module.Projective sourceTriangle (sourceCone.X j) :=
  Triangular.cone_projective sourceF.obj sourceU (sourceX.complete_finite (formE q))
    (sourceX.complete_projective (formE q)) j

abbrev sourceAug : sourceP.X 0 ⟶ sourceX.obj := ModuleCat.ofHom sourceX.cover.map
lemma sourceAug_exact : Function.Exact (sourceP.d 1 0) sourceAug := by
  change Function.Exact ((sourceX.complete (formE q)).d (0+1) 0) sourceX.cover.map
  rw [sourceX.complete_d]
  exact sourceX.pos_augmentation_exact

lemma sourceAug_zero : sourceP.d 1 0 ≫ sourceAug = 0 := by
  ext x
  exact sourceAug_exact.apply_apply_eq_zero x

lemma sourceCone_closed_boundary (a : ℤ) (ha : 0<a ∨ a≤ -2)
    (f : DownHom.Cochain sourceCone sourceCone a) (hf : DownHom.Closed f) : DownHom.Boundary f := by
  have hd := sourceDelta_vanishing_ranges a ha
  apply Triangular.cone_closed_boundary sourceF.obj sourceU a ?_ ?_ f hf
  · exact DownHom.actionDelta_injective sourceP sourceX.obj sourceAug sourceAug_zero
      (sourceX.complete_totallyAcyclic (formE q)) (sourceX.complete_projective (formE q))
      (sourceX.complete_finite (formE q)) sourceAug_exact sourceX.cover.surjective
      (Enveloping.tensorFunctor sourceF.obj) sourceU sourceUZero
      (Enveloping.tensorCompleteLift_aug sourceF.obj sourceX (formE q) sourceUZero) a hd.1
  · exact DownHom.actionDelta_surjective sourceP sourceX.obj sourceAug sourceAug_zero
      (sourceX.complete_totallyAcyclic (formE q)) (sourceX.complete_projective (formE q))
      (sourceX.complete_finite (formE q)) sourceAug_exact sourceX.cover.surjective
      (Enveloping.tensorFunctor sourceF.obj) sourceU sourceUZero
      (Enveloping.tensorCompleteLift_aug sourceF.obj sourceX (formE q) sourceUZero)
      (Enveloping.tensorComplex_exact sourceF.obj sourceP (sourceX.complete_exact (formE q)))
      (Enveloping.tensorComplex_finite sourceF.obj sourceP (sourceX.complete_finite (formE q)))
      (Enveloping.tensorComplex_projective sourceF.obj sourceP (sourceX.complete_finite (formE q))
        (sourceX.complete_projective (formE q)))
      (Enveloping.tensor_augmentation_exact sourceF.obj sourceX (formE q))
      (Enveloping.tensor_map_surjective sourceF.obj sourceAug sourceX.cover.surjective) (a-1) hd.2

lemma sourceCone_homology_zero (a : ℤ) (ha : 0<a ∨ a≤ -2) :
    Subsingleton (VectorSplit.H (completeHom (k := K) sourceCone
      (ModuleCat.of sourceTriangle (CokerAt sourceCone 0))) a) :=
  DownHom.homology_subsingleton sourceCone sourceCone_totallyAcyclic
    sourceCone_projective sourceCone_finite a (sourceCone_closed_boundary a ha)
end Tachikawa.SourceField



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}
def ofMap (f : P ⟶ Q) : Cochain P Q 0 := fun i j h =>
  (P.XIsoOfEq (show i=j by omega)).hom ≫ f.f j
lemma ofMap_closed (f : P ⟶ Q) : Closed (ofMap f) := by
  intro i j l m hij hlm
  have hi : i=j := by omega
  have hl : l=m := by omega
  cases hi; cases hl
  simp [ofMap]
lemma ofMap_boundary {f : P ⟶ Q} (h : Homotopy f 0) : Boundary (ofMap f) := by
  let c : Cochain P Q (0-1) := fun i j _ => h.hom i j
  refine ⟨c,?_⟩
  intro i j hij
  have hi : i=j := by omega
  cases hi
  have hh := h.comm i
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i-1) by change i-1+1=i; omega),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (i+1) i from rfl)] at hh
  simpa only [ofMap,add_zero,XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp,zero_f,c] using hh
lemma ofMap_nullhomotopic (f : P ⟶ Q) (hb : Boundary (ofMap f)) : Nonempty (Homotopy f 0) := by
  obtain ⟨c,hc⟩ := hb
  classical
  let h : ∀ p q, P.X p ⟶ Q.X q :=
    fun p q => if he : q=p+1 then c p q (by omega) else 0
  refine ⟨{ hom := h, zero := ?_, comm := ?_ }⟩
  · intro p q hpq
    change ¬ p+1=q at hpq
    simp only [h,dite_eq_right (Ne.symm hpq)]
  · intro j
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel j (j-1) by change j-1+1=j; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)]
    simp only [zero_f,add_zero,h,dite_eq_left (show j=j-1+1 by omega),dite_eq_left rfl]
    have hr := hc j j (by omega)
    simpa only [ofMap,add_zero,XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp] using hr
end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat.{0} R) ℤ)
  (hP : TotallyAcyclic P) (fP : ∀ j, Module.Finite R (P.X j))
  (pP : ∀ j, Module.Projective R (P.X j))
include fP in
lemma coker_finite : Module.Finite R (CokerAt P 0) := by
  let := fP 0
  exact Module.Finite.of_surjective (CokerAt.π P 0) (CokerAt.π_surjective P 0)
include hP fP pP k in
lemma id_boundary_of_projective (hp : Module.Projective R (CokerAt P 0)) : Boundary (ofMap (𝟙 P)) := by
  let := coker_finite P fP
  have hf : CokerAt.map (𝟙 P) 0 ∈ projectiveFactors (k := k) := by
    rw [CokerAt.map_id]
    exact id_mem_projectiveFactors_iff.mpr hp
  obtain ⟨h⟩ := nullhomotopic_of_coker_factors (𝟙 P) hP hP.1 pP fP pP hf
  exact ofMap_boundary h
include fP pP k in
lemma projective_of_id_boundary (hb : Boundary (ofMap (𝟙 P))) : Module.Projective R (CokerAt P 0) := by
  let := coker_finite P fP
  obtain ⟨h⟩ := ofMap_nullhomotopic (𝟙 P) hb
  have hf := coker_factors_of_nullhomotopic (k := k) (𝟙 P) h (fP (-1)) (pP (-1))
  rw [CokerAt.map_id] at hf
  exact id_mem_projectiveFactors_iff.mp hf
end Tachikawa.DownHom



namespace Tachikawa.Triangular
open CategoryTheory HomologicalComplex
open DownHom DownCone CompleteCone
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
  {P : ChainComplex (ModuleCat.{0} R) ℤ} (u : P ⟶ Enveloping.tensorComplex F P)
omit [CharP k 2] in
lemma low_identity : low (crossMap F u) (ofMap (𝟙 (cone F u))) = ofMap (𝟙 (D₀Complex F P)) := by
  funext i j h
  have hh : i=j := by omega
  cases hh
  simp [low,ofMap]
omit [CharP k 2] in
lemma down_identity : down₀ F 0 (ofMap (𝟙 (D₀Complex F P))) = ofMap (𝟙 P) := by
  funext i j h
  have hh : i=j := by omega
  cases hh
  change diagonal₀ (ofMap (𝟙 (D₀Complex F P)) i i _) = ofMap (𝟙 P) i i _
  simp only [ofMap,XIsoOfEq,eqToIso_refl,Iso.refl_hom,Category.id_comp,id_f]
  rfl

include k in
lemma cone_id_boundary (hb : Boundary (ofMap (𝟙 (cone F u)))) : Boundary (ofMap (𝟙 P)) := by
  obtain ⟨h,hh⟩ := (boundary_iff_diff _).mp hb
  have he := congrArg (low (crossMap F u)) hh
  rw [low_diff (k := k) _ (fun _ _ f => cross₀₁_zero f),low_identity] at he
  have hB : Boundary (ofMap (𝟙 (D₀Complex F P))) := (boundary_iff_diff _).mpr ⟨_,he⟩
  have hC := (down₀_boundary F _).mpr hB
  rw [down_identity] at hC
  exact hC
end Tachikawa.Triangular



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P : ChainComplex (ModuleCat.{0} R) ℤ) (N : ModuleCat.{0} R)
lemma completeHom_exact_of_zero (a : ℤ)
    [Subsingleton (VectorSplit.H (completeHom (k := k) P N) a)] :
    Function.Exact (homPrecomp (k := k) (Z := N) (P.d a (a-1)).hom)
      (homPrecomp (k := k) (P.d (a+1) a).hom) := by
  intro f
  constructor
  · intro hf
    let z : VectorSplit.Z (completeHom (k := k) P N) a :=
      ⟨ModuleCat.ofHom f,(completeHom_memZ P N a _).mpr (ModuleCat.hom_ext hf)⟩
    have hz : VectorSplit.quotient _ a z = 0 := Subsingleton.elim _ _
    obtain ⟨g,hg⟩ := (VectorSplit.quotient_zero_iff_predecessor a z).mp hz
    exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩
  · rintro ⟨g,rfl⟩
    change (g.comp (P.d a (a-1)).hom).comp (P.d (a+1) a).hom = 0
    rw [LinearMap.comp_assoc]
    have hd : (P.d a (a-1)).hom.comp (P.d (a+1) a).hom = 0 :=
      ModuleCat.hom_ext_iff.mp (P.d_comp_d (a+1) a (a-1))
    rw [hd,LinearMap.comp_zero]
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (C : ChainComplex (ModuleCat.{0} R) ℤ)
lemma transfer_of_completeHom_vanishing [FiniteDimensional k R]
    (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j))
    (van : ∀ a : ℤ, 0<a ∨ a≤ -2 →
      Subsingleton (VectorSplit.H (completeHom (k := k) C (ModuleCat.of R (CokerAt C 0))) a))
    (n : ℕ) :
    Subsingleton (Abelian.Ext
      (ModuleCat.of (TrivialExtension k R) (TrivialInduction.Obj k R (CokerAt C 0)))
      (ModuleCat.of (TrivialExtension k R) (TrivialInduction.Obj k R (CokerAt C 0))) (n+1)) := by
  apply TrivialInduction.transfer (k := k) C hC fin proj
  · intro m
    let := van ((m+1:ℕ):ℤ) (Or.inl (by omega))
    have hx := completeHom_exact_of_zero (k := k) C
      (ModuleCat.of R (CokerAt C 0)) ((m+1:ℕ):ℤ)
    have h1 : ((m+1:ℕ):ℤ)-1 = (m:ℤ) := by omega
    have h2 : ((m+1:ℕ):ℤ)+1 = ((m+2:ℕ):ℤ) := by omega
    rw [h1,h2] at hx
    exact hx
  · intro m
    let := van (-((m+1:ℕ):ℤ)-1) (Or.inr (by omega))
    have hx := completeHom_exact_of_zero (k := k) C
      (ModuleCat.of R (CokerAt C 0)) (-((m+1:ℕ):ℤ)-1)
    have h1 : (-((m+1:ℕ):ℤ)-1)-1 = -((m+2:ℕ):ℤ)-1 := by omega
    have h2 : (-((m+1:ℕ):ℤ)-1)+1 = -(m:ℤ)-1 := by omega
    rw [h1,h2] at hx
    exact hx
end Tachikawa



namespace Tachikawa.SourceField
open CategoryTheory Construction
open scoped ModuleCat.Algebra
abbrev sourceConeModule := CokerAt sourceCone 0
instance sourceConeModule_finite : Module.Finite sourceTriangle sourceConeModule :=
  DownHom.coker_finite sourceCone sourceCone_finite
instance sourceConeModule_finiteK : FiniteDimensional K sourceConeModule :=
  Module.Finite.trans sourceTriangle _
lemma sourceConeModule_nonprojective : ¬ Module.Projective sourceTriangle sourceConeModule := by
  intro hp
  have hb := DownHom.id_boundary_of_projective (k := K) sourceCone sourceCone_totallyAcyclic
    sourceCone_finite sourceCone_projective hp
  have hX := Triangular.cone_id_boundary sourceF.obj sourceU hb
  let := DownHom.projective_of_id_boundary (k := K) sourceP
    (sourceX.complete_finite (formE q)) (sourceX.complete_projective (formE q)) hX
  have h := Module.Projective.of_equiv (sourceX.cokerEquiv (formE q))
  exact X_nonprojective q (parameter_ne_zero 0) one_add_q_pow_ne_zero h

abbrev sourceAlgebra := TrivialExtension K sourceTriangle
abbrev sourceModule := TrivialInduction.Obj K sourceTriangle sourceConeModule
instance sourceModule_finite : FiniteDimensional K sourceModule := inferInstanceAs
  (FiniteDimensional K (TrivialInduction.Obj K sourceTriangle sourceConeModule))
lemma sourceModule_nonprojective : ¬ Module.Projective sourceAlgebra sourceModule := by
  intro hp
  let := hp
  exact sourceConeModule_nonprojective
    (TrivialInduction.projective_of_inducedProjective (k := K) (R := sourceTriangle) (M := sourceConeModule))

lemma sourceModule_ext (n : ℕ) :
    Subsingleton (Abelian.Ext (ModuleCat.of sourceAlgebra sourceModule)
      (ModuleCat.of sourceAlgebra sourceModule) (n+1)) :=
  transfer_of_completeHom_vanishing (k := K) sourceCone sourceCone_totallyAcyclic
    sourceCone_finite sourceCone_projective sourceCone_homology_zero n
end Tachikawa.SourceField



namespace Tachikawa.SourceField
instance sourceAlgebra_finite : Module.Finite K sourceAlgebra := inferInstanceAs
  (Module.Finite K (TrivialExtension K sourceTriangle))
lemma sourceAlgebra_symmetric : SymmetricOver K sourceAlgebra :=
  TrivialExtension.symmetricOver
end Tachikawa.SourceField



namespace Tachikawa

theorem main_theorem : Counterexample :=
  counterexampleOf SourceField.sourceAlgebra SourceField.sourceModule
    SourceField.sourceAlgebra_symmetric SourceField.sourceModule_nonprojective
    SourceField.sourceModule_ext
end Tachikawa

end

end OAI
