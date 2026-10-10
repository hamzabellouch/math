import Mathlib
import OAI.RingTheory.Multiplicity.TotalGhostRowHom

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
namespace Lech
variable {R : Type*} [CommRing R]
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
variable (T : C ⥤ D) [T.Additive] [T.Linear R]
variable (F G : CochainComplex C ℤ)

lemma map_cochain_smul {n : ℤ} (a : R) (f : Cochain F G n) :
    (a • f).map T = a • f.map T := by
  ext p q hpq
  simp only [Cochain.smul_v, Cochain.map_v, Functor.map_smul]

lemma cochain_surj_away (a : R) (s : Finset ℤ)
    (hb : ∀ p, p ∉ s → IsZero (F.X p))
    (hloc : ∀ p q, IsLocalizedModule.Away a (T.mapLinearMap R (X := F.X p) (Y := G.X q)))
    (n : ℤ) (g : Cochain ((T.mapHomologicalComplex _).obj F)
      ((T.mapHomologicalComplex _).obj G) n) :
    ∃ (N : ℕ) (f : Cochain F G n), a ^ N • g = f.map T := by
  classical
  have h (p : s) := @IsLocalizedModule.Away.surj R _ _ _ _ _ _ _
    (T.mapLinearMap R (X := F.X p) (Y := G.X (p + n))) a
    (hloc p (p + n)) (g.v p (p + n) rfl)
  choose e f hf using h
  let N := s.attach.sup e
  have he (p : s) : e p ≤ N := Finset.le_sup (f := e) (Finset.mem_attach s p)
  refine ⟨N, Cochain.mk (fun p q hpq => ?_), ?_⟩
  · subst q
    exact if hp : p ∈ s then a ^ (N - e ⟨p, hp⟩) • f ⟨p, hp⟩ else 0
  · ext p q hpq
    subst q
    simp only [Cochain.smul_v, Cochain.map_v, Cochain.mk_v]
    by_cases hp : p ∈ s
    · have hf' : a ^ e ⟨p, hp⟩ • g.v p (p + n) rfl = T.map (f ⟨p, hp⟩) := hf ⟨p, hp⟩
      rw [dite_eq_left hp, Functor.map_smul, ← hf', smul_smul,
        ← pow_add, Nat.sub_add_cancel (he ⟨p, hp⟩)]
    · exact (T.map_isZero (hb p hp)).eq_of_src _ _

lemma cochain_eq_zero_away (a : R) (s : Finset ℤ)
    (hb : ∀ p, p ∉ s → IsZero (F.X p))
    (hloc : ∀ p q, IsLocalizedModule.Away a (T.mapLinearMap R (X := F.X p) (Y := G.X q)))
    (n : ℤ) (f : Cochain F G n) (h : f.map T = 0) :
    ∃ N : ℕ, a ^ N • f = 0 := by
  classical
  have hx (p : s) : ∃ N : ℕ, a ^ N • f.v p (p + n) rfl = 0 := by
    have := hloc p (p + n)
    have heq : T.mapLinearMap R (f.v p (p + n) rfl) = T.mapLinearMap R 0 := by
      have h' := Cochain.congr_v h p (p + n) rfl
      simpa only [Functor.coe_mapLinearMap, Cochain.map_v, Cochain.zero_v,
        Functor.map_zero] using h'
    simpa only [smul_zero] using IsLocalizedModule.Away.exists_of_eq a heq
  choose e he using hx
  let N := s.attach.sup e
  have heN (p : s) : e p ≤ N := Finset.le_sup (f := e) (Finset.mem_attach s p)
  refine ⟨N, ?_⟩
  ext p q hpq
  subst q
  simp only [Cochain.smul_v, Cochain.zero_v]
  by_cases hp : p ∈ s
  · rw [← Nat.sub_add_cancel (heN ⟨p, hp⟩), pow_add, mul_smul, he ⟨p, hp⟩, smul_zero]
  · exact (hb p hp).eq_of_src _ _

lemma ofHom_smul {F G : CochainComplex C ℤ} (f : F ⟶ G) (a : R) :
    Cochain.ofHom (a • f) = a • Cochain.ofHom f := by
  ext p
  simp

lemma nullhomotopy_away (a : R) (s : Finset ℤ)
    (hb : ∀ p, p ∉ s → IsZero (F.X p))
    (hloc : ∀ p q, IsLocalizedModule.Away a (T.mapLinearMap R (X := F.X p) (Y := F.X q)))
    (h : Homotopy (𝟙 ((T.mapHomologicalComplex _).obj F)) 0) :
    ∃ N : ℕ, Nonempty (Homotopy (a ^ N • 𝟙 F) 0) := by
  obtain ⟨N, f, hf⟩ := cochain_surj_away T F F a s hb hloc (-1) (Cochain.ofHomotopy h)
  have he : (δ (-1) 0 f - a ^ N • Cochain.ofHom (𝟙 F)).map T = 0 := by
    rw [Cochain.map_sub, ← δ_map, ← hf, δ_smul, δ_ofHomotopy, Cochain.ofHom_zero, sub_zero,
      map_cochain_smul, Cochain.map_ofHom, CategoryTheory.Functor.map_id, sub_self]
  obtain ⟨M, hM⟩ := cochain_eq_zero_away T F F a s hb hloc 0 _ he
  refine ⟨M + N, ⟨(Cochain.equivHomotopy _ _).symm ⟨a ^ M • f, ?_⟩⟩⟩
  rw [smul_sub, sub_eq_zero] at hM
  rw [ofHom_smul, δ_smul, hM, smul_smul, ← pow_add, Cochain.ofHom_zero, add_zero]

end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u
variable {R : Type u} [CommRing R]
 

lemma nullhomotopy_of_projective_acyclic_away (a : R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < l ∨ b < j → IsZero (F.X j))
    (ha : ((baseChangeFunctor R (Localization.Away a)).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ N : ℕ, Nonempty (Homotopy (a ^ N • 𝟙 F) 0) := by
  obtain ⟨h⟩ := baseChange_projective_contractible (A := Localization.Away a) F b hp hfin
    (fun j hj => hb j (Or.inr hj)) ha
  apply nullhomotopy_away (baseChangeFunctor R (Localization.Away a)) F a (Finset.Icc l b)
    (fun j hj => hb j (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hj)) _ h
  intro p q
  have := hp p
  have := hfin p
  exact baseChangeFunctor_map_localized_projective (A := Localization.Away a)
    (Submonoid.powers a) (F.X p) (F.X q)
end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

 

lemma uniform_nullhomotopy_of_projective_acyclic_away {h : ℕ} (z : Fin h → R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j < l ∨ b < j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ m : ℕ, ∀ i, Nonempty (Homotopy (z i ^ m • 𝟙 F) 0) := by
  classical
  have hh (i : Fin h) := nullhomotopy_of_projective_acyclic_away (z i) F l b hp hfin hb (ha i)
  choose N H using hh
  refine ⟨∑ i, N i, ?_⟩
  intro i
  have hi : N i ≤ ∑ j, N j := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
  have HH := (H i).some.smul (z i ^ ((∑ j, N j) - N i))
  rw [smul_smul,←pow_add,Nat.sub_add_cancel hi,smul_zero] at HH
  exact ⟨HH⟩
end Lech


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma positive_homologyMap_zero_of_le (m : ℕ) (H : ∀ i, Homotopy (z i^m • 𝟙 F) 0)
    (l b : ℤ) (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (N : ℕ) (hN : b-l<(N:ℤ)) (t M : ℕ) (hM : m*N≤M) (i : ℤ) :
    homologyMap ((TensorTotal.Right.functor F).map
      (positiveInclusion I z hz (show t≤t+M by omega))) i=0 := by
  have h1 : t ≤ t+m*N := by omega
  have h2 : t+m*N ≤ t+M := by omega
  rw [←positiveInclusion_comp I z hz h1 h2,Functor.map_comp,homologyMap_comp,
    positive_homologyMap_zero I z hz F m H l b hb N hN t i,comp_zero]

 

lemma exists_uniform_positive_nilpotence (l b : ℤ)
    (hp : ∀ j, Module.Projective R (F.X j))
    (hfin : ∀ j, Module.Finite R (F.X j))
    (hb : ∀ j, j<l ∨ b<j → IsZero (F.X j))
    (ha : ∀ i, ((baseChangeFunctor R (Localization.Away (z i))).mapHomologicalComplex _ |>.obj F).Acyclic) :
    ∃ MD : ℕ, ∀ t M : ℕ, MD≤M → ∀ i : ℤ,
      homologyMap ((TensorTotal.Right.functor F).map
        (positiveInclusion I z hz (show t≤t+M by omega))) i=0 := by
  classical
  obtain ⟨m,H⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F l b hp hfin hb ha
  let N : ℕ := (b-l).toNat+1
  have hN : b-l<(N:ℤ) := by dsimp [N]; omega
  refine ⟨m*N,?_⟩
  intro t M hM i
  exact positive_homologyMap_zero_of_le I z hz F m (fun i => (H i).some) l b hb N hN t M hM i
end Lech.FilteredCech


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]

lemma dropBottomMap_comp {F G H : CochainComplex C ℤ} (n : ℤ)
    (hf : ∀ i, i<n → IsZero (F.X i)) (hg : ∀ i, i<n → IsZero (G.X i))
    (hh : ∀ i, i<n → IsZero (H.X i)) (f : F ⟶ G) (g : G ⟶ H) :
    dropBottomMap F n hf hg f ≫ dropBottomMap G n hg hh g =
      dropBottomMap F n hf hh (f ≫ g) := by
  apply (cancel_mono (kernel.ι (bottomProjection H n hh))).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (dropBottomMap F n hf hg f ≫ ·) (dropBottomMap_ι G n hg hh g)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ g) (dropBottomMap_ι F n hf hg f)).trans
          ((Category.assoc _ _ _).trans (dropBottomMap_ι F n hf hh (f ≫ g)).symm))))

lemma dropBottomMap_zero {F G : CochainComplex C ℤ} (n : ℤ)
    (hf : ∀ i, i<n → IsZero (F.X i)) (hg : ∀ i, i<n → IsZero (G.X i)) :
    dropBottomMap F n hf hg (0 : F ⟶ G)=0 := by
  apply (cancel_mono (kernel.ι (bottomProjection G n hg))).mp
  exact (dropBottomMap_ι F n hf hg (0 : F ⟶ G)).trans
    ((comp_zero).trans (zero_comp).symm)

variable (S : ShortComplex (CochainComplex C ℤ)) (n : ℤ)
    (h₁ : ∀ i, i<n → IsZero (S.X₁.X i))
    (h₂ : ∀ i, i<n → IsZero (S.X₂.X i))
    (h₃ : ∀ i, i<n → IsZero (S.X₃.X i))

def dropShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (dropBottomMap S.X₁ n h₁ h₂ S.f) (dropBottomMap S.X₂ n h₂ h₃ S.g)
    (by rw [dropBottomMap_comp,S.zero,dropBottomMap_zero])

lemma dropShortComplex_shortExact (hS : S.ShortExact) :
    (dropShortComplex S n h₁ h₂ h₃).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  by_cases hi : i=n
  · subst i
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ (dropBottom_X_bottom S.X₂ n h₂)
            mono_f := (dropBottom_X_bottom S.X₁ n h₁).mono _
            epi_g := (dropBottom_X_bottom S.X₃ n h₃).epi _ }
  · apply ShortComplex.shortExact_of_iso (ShortComplex.isoMk
      (dropBottomXIso S.X₁ n h₁ i hi) (dropBottomXIso S.X₂ n h₂ i hi)
      (dropBottomXIso S.X₃ n h₃ i hi) ?_ ?_).symm (hS.map_of_exact (eval C (.up ℤ) i))
    · exact congrArg (fun f => f.f i) (dropBottomMap_ι S.X₁ n h₁ h₂ S.f).symm
    · exact congrArg (fun f => f.f i) (dropBottomMap_ι S.X₂ n h₂ h₃ S.g).symm
end Lech.FiniteComplex


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

lemma extend_shortExact (S : ShortComplex (HomologicalComplex C c)) (hS : S.ShortExact)
    (e : c.Embedding c') : (S.map (e.extendFunctor C)).ShortExact := by
  classical
  apply shortExact_of_degreewise_shortExact
  intro j
  by_cases hj : ∃ i, e.f i=j
  · obtain ⟨i,hi⟩ := hj
    apply ShortComplex.shortExact_of_iso (ShortComplex.isoMk
      (S.X₁.extendXIso e hi) (S.X₂.extendXIso e hi) (S.X₃.extendXIso e hi)
      ?_ ?_).symm (hS.map_of_exact (eval C c i))
    · change _ = (extendMap S.f e).f j ≫ _
      rw [extendMap_f _ _ hi]
      simp
      rfl
    · change _ = (extendMap S.g e).f j ≫ _
      rw [extendMap_f _ _ hi]
      simp
      rfl
  · have hnone : ∀ i, e.f i≠j := by simpa using hj
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ (S.X₂.isZero_extend_X e j hnone)
            mono_f := (S.X₁.isZero_extend_X e j hnone).mono _
            epi_g := (S.X₃.isZero_extend_X e j hnone).epi _ }
end Lech


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]

lemma dropBottomMap_id (F : CochainComplex C ℤ) (n : ℤ)
    (hf : ∀ i, i<n → IsZero (F.X i)) :
    dropBottomMap F n hf hf (𝟙 F)=𝟙 _ := by
  apply (cancel_mono (kernel.ι (bottomProjection F n hf))).mp
  exact (dropBottomMap_ι F n hf hf (𝟙 F)).trans
    ((Category.comp_id _).trans (Category.id_comp _).symm)

def dropShortComplexMap {S T : ShortComplex (CochainComplex C ℤ)} (n : ℤ)
    (hS₁ : ∀ i, i<n → IsZero (S.X₁.X i))
    (hS₂ : ∀ i, i<n → IsZero (S.X₂.X i))
    (hS₃ : ∀ i, i<n → IsZero (S.X₃.X i))
    (hT₁ : ∀ i, i<n → IsZero (T.X₁.X i))
    (hT₂ : ∀ i, i<n → IsZero (T.X₂.X i))
    (hT₃ : ∀ i, i<n → IsZero (T.X₃.X i)) (f : S ⟶ T) :
    dropShortComplex S n hS₁ hS₂ hS₃ ⟶ dropShortComplex T n hT₁ hT₂ hT₃ where
  τ₁ := dropBottomMap S.X₁ n hS₁ hT₁ f.τ₁
  τ₂ := dropBottomMap S.X₂ n hS₂ hT₂ f.τ₂
  τ₃ := dropBottomMap S.X₃ n hS₃ hT₃ f.τ₃
  comm₁₂ := by
    dsimp only [dropShortComplex]
    rw [dropBottomMap_comp,dropBottomMap_comp,f.comm₁₂]
  comm₂₃ := by
    dsimp only [dropShortComplex]
    rw [dropBottomMap_comp,dropBottomMap_comp,f.comm₂₃]
end Lech.FiniteComplex


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]
  {ι : Type*} {c : ComplexShape ι}
lemma dropBottomMap_extend_id (K : HomologicalComplex C c) (e : c.Embedding (.up ℤ))
    (n : ℤ) (h : ∀ i, i<n → IsZero ((K.extend e).X i)) :
    dropBottomMap (K.extend e) n h h (extendMap (𝟙 K) e)=𝟙 _ := by
  rw [extendMap_id,dropBottomMap_id]
end Lech.FiniteComplex


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]
lemma isIso_dropBottomMap {K L : CochainComplex C ℤ} (n : ℤ)
    (hK : ∀ i, i<n → IsZero (K.X i)) (hL : ∀ i, i<n → IsZero (L.X i))
    (f : K ⟶ L) [IsIso f] : IsIso (dropBottomMap K n hK hL f) := by
  refine ⟨⟨dropBottomMap L n hL hK (inv f), ?_, ?_⟩⟩
  · rw [dropBottomMap_comp,IsIso.hom_inv_id,dropBottomMap_id]
  · rw [dropBottomMap_comp,IsIso.inv_hom_id,dropBottomMap_id]
lemma isIso_dropShortComplexMap_τ₂ {S T : ShortComplex (CochainComplex C ℤ)} (n : ℤ)
    (hS₁ : ∀ i, i<n → IsZero (S.X₁.X i))
    (hS₂ : ∀ i, i<n → IsZero (S.X₂.X i))
    (hS₃ : ∀ i, i<n → IsZero (S.X₃.X i))
    (hT₁ : ∀ i, i<n → IsZero (T.X₁.X i))
    (hT₂ : ∀ i, i<n → IsZero (T.X₂.X i))
    (hT₃ : ∀ i, i<n → IsZero (T.X₃.X i)) (f : S ⟶ T) [IsIso f.τ₂] :
    IsIso (dropShortComplexMap n hS₁ hS₂ hS₃ hT₁ hT₂ hT₃ f).τ₂ :=
  isIso_dropBottomMap n hS₂ hT₂ f.τ₂
end Lech.FiniteComplex


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w} [Category J]

lemma functorCategory_shortExact (S : ShortComplex (J ⥤ C))
    (hS : ∀ j, (S.map ((evaluation J C).obj j)).ShortExact) : S.ShortExact := by
  have hm : ∀ j, Mono (S.f.app j) := fun j => (hS j).mono_f
  have he : ∀ j, Epi (S.g.app j) := fun j => (hS j).epi_g
  refine {exact := ?_, mono_f := ?_, epi_g := ?_}
  · apply S.exact_of_f_is_kernel
    apply evaluationJointlyReflectsLimits
    intro j
    have := (hS j).mono_f
    exact (KernelFork.isLimitMapConeEquiv _ _).symm ((hS j).exact.fIsKernel)
  · exact NatTrans.mono_of_mono_app S.f
  · exact NatTrans.epi_of_epi_app S.g

variable {ι : Type w}
 
def discreteShortComplex (S : ι → ShortComplex C) : ShortComplex (Discrete ι ⥤ C) where
  X₁ := Discrete.functor (fun i => (S i).X₁)
  X₂ := Discrete.functor (fun i => (S i).X₂)
  X₃ := Discrete.functor (fun i => (S i).X₃)
  f := Discrete.natTrans (fun i => (S i.as).f)
  g := Discrete.natTrans (fun i => (S i.as).g)
  zero := by ext i; exact (S i.as).zero

lemma discreteShortComplex_shortExact (S : ι → ShortComplex C)
    (hS : ∀ i, (S i).ShortExact) : (discreteShortComplex S).ShortExact := by
  apply functorCategory_shortExact
  intro i
  exact hS i.as

variable [HasCoproductsOfShape ι C] [HasExactColimitsOfShape (Discrete ι) C]
lemma coproduct_shortExact (S : ι → ShortComplex C) (hS : ∀ i, (S i).ShortExact) :
    ((discreteShortComplex S).map (colim (J:=Discrete ι) (C:=C))).ShortExact :=
  (discreteShortComplex_shortExact S hS).map_of_exact _
end Lech


namespace Lech.TensorTotal.Right
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

 
def degreeSequenceFamily (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (i : ℤ) (pq : {pq : ℤ×ℤ // pq.1+pq.2=i}) : ShortComplex (ModuleCat.{u} R) :=
  (S.map (eval (ModuleCat.{u} R) (.up ℤ) pq.1.2)).map
    ((curriedTensor (ModuleCat.{u} R)).obj (K.X pq.1.1))

def degreeSequenceIso (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (i : ℤ) :
    ((Lech.discreteShortComplex (degreeSequenceFamily K S i)).map
      (colim (C:=ModuleCat.{u} R))) ≅
    ((S.map (functor K)).map (eval (ModuleCat.{u} R) (.up ℤ) i)) := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ ((functor K).map S.f).f i =
      colim.map (Lech.discreteShortComplex (degreeSequenceFamily K S i)).f ≫ 𝟙 _
    refine (Category.id_comp _).trans (Eq.trans ?_ (Category.comp_id _).symm)
    refine mapBifunctor.hom_ext (K₁ := K) (K₂ := S.X₁)
      (F := curriedTensor (ModuleCat.{u} R)) (c := .up ℤ) (fun p q hpq => ?_)
    symm
    change colimit.ι (Lech.discreteShortComplex (degreeSequenceFamily K S i)).X₁
      ⟨⟨(p,q),hpq⟩⟩ ≫ colim.map _ = _
    rw [colimit.ι_map]
    symm
    change ιMapBifunctor K S.X₁ (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫
      ((functor K).map S.f).f i = _
    rw [map_f,ι_degreeMap]
    rfl
  · change 𝟙 _ ≫ ((functor K).map S.g).f i =
      colim.map (Lech.discreteShortComplex (degreeSequenceFamily K S i)).g ≫ 𝟙 _
    refine (Category.id_comp _).trans (Eq.trans ?_ (Category.comp_id _).symm)
    refine mapBifunctor.hom_ext (K₁ := K) (K₂ := S.X₂)
      (F := curriedTensor (ModuleCat.{u} R)) (c := .up ℤ) (fun p q hpq => ?_)
    symm
    change colimit.ι (Lech.discreteShortComplex (degreeSequenceFamily K S i)).X₂
      ⟨⟨(p,q),hpq⟩⟩ ≫ colim.map _ = _
    rw [colimit.ι_map]
    symm
    change ιMapBifunctor K S.X₂ (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫
      ((functor K).map S.g).f i = _
    rw [map_f,ι_degreeMap]
    rfl

 

lemma shortExact (hK : ∀ p, Module.Flat R (K.X p))
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) :
    (S.map (functor K)).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  apply ShortComplex.shortExact_of_iso (degreeSequenceIso K S i)
  apply Lech.coproduct_shortExact
  intro pq
  have := hK pq.1.1
  exact (hS.map_of_exact (eval (ModuleCat.{u} R) (.up ℤ) pq.1.2)).map_of_exact
    (tensorLeft (K.X pq.1.1))
end Lech.TensorTotal.Right
end

end OAI
