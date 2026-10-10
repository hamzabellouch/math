import Mathlib
import OAI.RingTheory.Multiplicity.FilteredFractionReesDenominatorTheory

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
namespace Lech.AlternatingCech
open scoped BigOperators
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
abbrev Alt (n : ℕ) := (ι → R) [⋀^Fin n]→ₗ[R] M
abbrev basis : Module.Basis ι R (ι → R) := Pi.basisFun R ι
def evaluation (n : ℕ) : Alt R M (ι := ι) n →ₗ[R] FiniteCoverCech.Row M (ι := ι) n where
  toFun f a := f (fun i => basis R (a i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [DecidableEq ι] in
lemma evaluation_injective (n : ℕ) : Function.Injective (evaluation R M (ι := ι) n) := by
  intro f g h
  apply (basis R (ι := ι)).ext_alternating
  intro a _
  exact congrFun h a

def epsilon : (ι → R) →ₗ[R] R := ∑ i : ι,LinearMap.proj i
lemma epsilon_basis (i : ι) : epsilon R (basis R i)=1 := by
  simp [epsilon,basis,Pi.basisFun_apply]

def delta (n : ℕ) : Alt R M (ι := ι) n →ₗ[R] Alt R M (ι := ι) (n+1) where
  toFun f := AlternatingMap.alternatizeUncurryFin ((epsilon R).smulRight f)
  map_add' f g := by
    ext v
    simp [AlternatingMap.alternatizeUncurryFin_apply,smul_add,Finset.sum_add_distrib]
  map_smul' r f := by
    ext v
    simp only [AlternatingMap.alternatizeUncurryFin_apply,LinearMap.smulRight_apply,
      AlternatingMap.smul_apply,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_comm (epsilon R (v i)) r,smul_comm ((-1:ℤ)^i.val) r]
lemma evaluation_delta (n : ℕ) (f : Alt R M (ι := ι) n) :
    evaluation R M (n+1) (delta R M n f)=FiniteCoverCech.delta R M n (evaluation R M n f) := by
  ext a
  simp only [evaluation,LinearMap.coe_mk,AddHom.coe_mk,delta,
    AlternatingMap.alternatizeUncurryFin_apply,LinearMap.smulRight_apply,
    epsilon_basis,one_smul,FiniteCoverCech.delta]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Int.cast_smul_eq_zsmul R]
  simp only [Int.cast_pow,Int.cast_neg,Int.cast_one]
  rfl

def extra (j : ι) (n : ℕ) : Alt R M (ι := ι) (n+1) →ₗ[R] Alt R M (ι := ι) n where
  toFun f := f.curryLeft (basis R j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [DecidableEq ι] in
lemma evaluation_extra (j : ι) (n : ℕ) (f : Alt R M (ι := ι) (n+1)) :
    evaluation R M n (extra R M j n f)=FiniteCoverCech.extra R M j n (evaluation R M (n+1) f) := by
  ext a
  change f (Fin.cons (basis R j) (fun i => basis R (a i)))=
    f (fun i => basis R ((Fin.cons j a : Fin (n+1) → ι) i))
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i
lemma delta_square (n : ℕ) (f : Alt R M (ι := ι) n) : delta R M (n+1) (delta R M n f)=0 := by
  apply evaluation_injective R M (n+2)
  rw [evaluation_delta,evaluation_delta,map_zero,FiniteCoverCech.delta_square]
lemma extra_delta (j : ι) (n : ℕ) (f : Alt R M (ι := ι) (n+1)) :
    extra R M j (n+1) (delta R M (n+1) f)+delta R M n (extra R M j n f)=f := by
  apply evaluation_injective R M (n+1)
  rw [map_add,evaluation_extra,evaluation_delta,evaluation_delta,evaluation_extra]
  exact FiniteCoverCech.extra_delta R M j n (evaluation R M (n+1) f)
omit [DecidableEq ι] in
 

lemma eq_zero_above_card (n : ℕ) (hn : Fintype.card ι<n) (f : Alt R M (ι := ι) n) : f=0 := by
  apply (basis R (ι := ι)).ext_alternating
  intro a ha
  have h := Fintype.card_le_of_injective a ha
  simp only [Fintype.card_fin] at h
  omega

variable (F : Finset ι → Submodule R M) (hF : Monotone F)
def cochains (n : ℕ) : Submodule R (Alt R M (ι := ι) n) :=
  (FiniteCoverCech.cochains R M F n).comap (evaluation R M n)
include hF in
lemma delta_mem (n : ℕ) {f : Alt R M (ι := ι) n} (hf : f∈cochains R M F n) :
    delta R M n f∈cochains R M F (n+1) := by
  change evaluation R M (n+1) (delta R M n f)∈FiniteCoverCech.cochains R M F (n+1)
  rw [evaluation_delta]
  exact FiniteCoverCech.delta_mem R M F hF n hf
variable (q : ι → R) (hq : Ideal.span (Set.range q)=⊤)
variable (hclear : ∀ (s : Finset ι) (j : ι) (x : M),x∈F (insert j s) → ∃ N : ℕ,q j^N • x∈F s)
include hq hclear in
 

theorem exact (n : ℕ) (f : cochains R M F (n+1)) (hf : delta R M (n+1) f.val=0) :
    ∃ g : cochains R M F n,delta R M n g.val=f.val := by
  let ef : FiniteCoverCech.cochains R M F (n+1) := ⟨evaluation R M (n+1) f.val,f.property⟩
  obtain ⟨N,hN⟩ := FiniteCoverCech.uniform_clear R M F q hclear n ef
  obtain ⟨c,hc⟩ := FiniteCoverCech.partition R q hq N
  let g : Alt R M (ι := ι) n := ∑ j,c j • (q j^N • extra R M j n f.val)
  have hg : g∈cochains R M F n := by
    intro a
    change (evaluation R M n g) a∈F (FiniteCoverCech.intersection a)
    simp only [g,map_sum,map_smul,evaluation_extra,Finset.sum_apply,Pi.smul_apply]
    exact (F _).sum_mem fun j _ => (F _).smul_mem _ (hN j a)
  refine ⟨⟨g,hg⟩,?_⟩
  have hj (j : ι) : delta R M n (extra R M j n f.val)=f.val := by
    have h := extra_delta R M j n f.val
    rw [hf,map_zero,zero_add] at h
    exact h
  simp only [g,map_sum,map_smul,hj,smul_smul,←Finset.sum_smul,hc,one_smul]
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (F : Finset ι → Submodule R M) (hF : Monotone F)
def differential (n : ℕ) : cochains R M F n →ₗ[R] cochains R M F (n+1) :=
  (delta R M n).restrict (fun _ h => delta_mem R M F hF n h)
lemma differential_square (n : ℕ) (f : cochains R M F n) :
    differential R M F hF (n+1) (differential R M F hF n f)=0 := by
  apply Subtype.ext
  exact delta_square R M n f.val
 

def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (cochains R M F n))
    (fun n => ModuleCat.ofHom (differential R M F hF n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact differential_square R M F hF n f)
lemma complex_d (n : ℕ) : (complex R M F hF).d n (n+1)=
    ModuleCat.ofHom (differential R M F hF n) := by
  change CochainComplex.of.d (fun n => ModuleCat.of R (cochains R M F n))
    (fun n => ModuleCat.ofHom (differential R M F hF n)) n (n+1)=_
  exact CochainComplex.of_d _ _ n
lemma complex_bounded (n : ℕ) (hn : Fintype.card ι<n) : IsZero ((complex R M F hF).X n) := by
  have : Subsingleton (cochains R M F n) := subsingleton_of_forall_eq 0 (fun f =>
    Subtype.ext (eq_zero_above_card R M n hn f.val))
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (cochains R M F n))
variable (q : ι → R) (hq : Ideal.span (Set.range q)=⊤)
variable (hclear : ∀ (s : Finset ι) (j : ι) (x : M),x∈F (insert j s) → ∃ N : ℕ,q j^N • x∈F s)
include hq hclear in
lemma complex_exactAt (n : ℕ) : (complex R M F hF).ExactAt (n+1) := by
  apply ((complex R M F hF).exactAt_iff' (i := n) (j := n+1) (k := n+2)
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change ((complex R M F hF).d (n+1) (n+2)).hom f=0 at hf
  rw [complex_d] at hf
  obtain ⟨g,hg⟩ := exact R M F q hq hclear n f (congrArg Subtype.val hf)
  refine ⟨g,?_⟩
  change ((complex R M F hF).d n (n+1)).hom g=f
  rw [complex_d]
  exact Subtype.ext hg
omit [DecidableEq ι] in
lemma extra_delta_zero (j : ι) (f : Alt R M (ι := ι) 0) :
    extra R M j 0 (delta R M 0 f)=f := by
  classical
  ext v
  change AlternatingMap.alternatizeUncurryFin ((epsilon R).smulRight f)
    (Fin.cons (basis R j) v)=f v
  simp [AlternatingMap.alternatizeUncurryFin_apply]
  change (epsilon R) (basis R j) • f v = f v
  rw [epsilon_basis,one_smul]
include hq in
lemma differential_injective : Function.Injective (differential R M F hF 0) := by
  apply (differential R M F hF 0).ker_eq_bot.mp
  apply (LinearMap.ker_eq_bot').mpr
  intro f hf
  have hδ : delta R M 0 f.val=0 := congrArg Subtype.val hf
  obtain ⟨c,hc⟩ := FiniteCoverCech.partition R q hq 0
  simp only [pow_zero,mul_one] at hc
  have hz (j : ι) : f.val=0 := by
    have h := extra_delta_zero R M j f.val
    rw [hδ,map_zero] at h
    exact h.symm
  apply Subtype.ext
  calc
    f.val = (∑ j,c j) • f.val := by rw [hc,one_smul]
    _ = ∑ j,c j • f.val := Finset.sum_smul
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hz j,smul_zero]
include hq in
lemma complex_exactAt_zero : (complex R M F hF).ExactAt 0 := by
  apply ((complex R M F hF).exactAt_iff' (i := 0) (j := 0) (k := 1)
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro f hf
  change ((complex R M F hF).d 0 1).hom f=0 at hf
  rw [complex_d] at hf
  have hf0 : f=0 := differential_injective R M F hF q hq (hf.trans (map_zero _).symm)
  exact ⟨0,by simp [hf0]⟩
include hq hclear in
 
theorem complex_acyclic : (complex R M F hF).Acyclic := by
  intro n
  cases n with
  | zero => exact complex_exactAt_zero R M F hF q hq
  | succ n => exact complex_exactAt R M F hF q hq hclear n
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open scoped BigOperators
open Set
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable {ι : Type w} [Fintype ι] [LinearOrder ι]
 
def sortedCoordinates (n : ℕ) : Alt R M (ι := ι) n ≃ₗ[R] (powersetCard ι n → M) :=
  exteriorPower.alternatingMapLinearEquiv.trans
    (((basis R (ι := ι)).exteriorPower n).constr R).symm
lemma sortedCoordinates_apply (n : ℕ) (f : Alt R M (ι := ι) n) (s : powersetCard ι n) :
    sortedCoordinates R M n f s = f (fun i => basis R (s.val.orderEmbOfFin s.property i)) := by
  change exteriorPower.alternatingMapLinearEquiv f ((basis R).exteriorPower n s)=_
  rw [exteriorPower.basis_apply,exteriorPower.ιMulti_family,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl
omit [Fintype ι] in
lemma tuple_sort {n : ℕ} (a : Fin n → ι) (ha : Function.Injective a) :
    ∃ s : powersetCard ι n,∃ σ : Equiv.Perm (Fin n),
      FiniteCoverCech.intersection a=s.val ∧ a=(s.val.orderEmbOfFin s.property) ∘ σ := by
  let s : powersetCard ι n := ⟨FiniteCoverCech.intersection a,by
    change (FiniteCoverCech.intersection a).card=n
    rw [FiniteCoverCech.intersection,Finset.card_image_of_injective _ ha,Finset.card_univ,Fintype.card_fin]⟩
  let e : Fin n ≃ s.val := Equiv.ofBijective
    (fun i => ⟨a i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun i j h => ha (congrArg Subtype.val h),by
      intro j
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp j.property
      exact ⟨i,Subtype.ext hi⟩⟩
  let σ : Equiv.Perm (Fin n) := e.trans (s.val.orderIsoOfFin s.property).symm.toEquiv
  refine ⟨s,σ,rfl,?_⟩
  funext i
  change a i = ((s.val.orderIsoOfFin s.property) ((s.val.orderIsoOfFin s.property).symm (e i))).val
  rw [OrderIso.apply_symm_apply]
  rfl
omit [Fintype ι] in
lemma sorted_intersection (n : ℕ) (s : powersetCard ι n) :
    FiniteCoverCech.intersection (s.val.orderEmbOfFin s.property)=s.val := by
  ext i
  simp only [FiniteCoverCech.intersection,Finset.mem_image,Finset.mem_univ,true_and]
  change (∃ j, s.val.orderEmbOfFin s.property j=i) ↔ _
  change i∈Set.range (s.val.orderEmbOfFin s.property) ↔ i∈s.val
  exact Iff.of_eq (congrArg (fun S : Set ι => i∈S) (Finset.range_orderEmbOfFin s.val s.property))

variable (F : Finset ι → Submodule R M)
lemma mem_cochains_iff_sorted (n : ℕ) (f : Alt R M (ι := ι) n) :
    f∈cochains R M F n ↔ ∀ s : powersetCard ι n,sortedCoordinates R M n f s∈F s.val := by
  constructor
  · intro hf s
    rw [sortedCoordinates_apply]
    have h := hf (s.val.orderEmbOfFin s.property)
    rw [sorted_intersection] at h
    exact h
  · intro hf a
    by_cases ha : Function.Injective a
    · obtain ⟨s,σ,hs,hσ⟩ := tuple_sort a ha
      change f (fun i => basis R (a i))∈F (FiniteCoverCech.intersection a)
      rw [hs,hσ]
      change f ((fun i => basis R (s.val.orderEmbOfFin s.property i)) ∘ σ)∈F s.val
      rw [f.map_perm]
      have hh := hf s
      rw [sortedCoordinates_apply] at hh
      change ((Equiv.Perm.sign σ : ℤ) • f (fun i => basis R (s.val.orderEmbOfFin s.property i)))∈F s.val
      rw [←Int.cast_smul_eq_zsmul R]
      exact (F s.val).smul_mem _ hh
    · change f (fun i => basis R (a i))∈F (FiniteCoverCech.intersection a)
      rw [f.map_eq_zero_of_not_injective _ (fun hh => ha (fun i j hij => hh (congrArg (basis R) hij)))]
      exact (F _).zero_mem
 

def cochainsSorted (n : ℕ) : cochains R M F n ≃ₗ[R] (∀ s : powersetCard ι n,F s.val) where
  toFun f s := ⟨sortedCoordinates R M n f.val s,(mem_cochains_iff_sorted R M F n f.val).mp f.property s⟩
  invFun f := ⟨(sortedCoordinates R M n).symm (fun s => (f s).val),
    (mem_cochains_iff_sorted R M F n _).mpr (by
      intro s
      simpa only [LinearEquiv.apply_symm_apply] using (f s).property)⟩
  left_inv f := Subtype.ext ((sortedCoordinates R M n).symm_apply_apply f.val)
  right_inv f := by ext s; exact congrFun ((sortedCoordinates R M n).apply_symm_apply (fun s => (f s).val)) s
  map_add' f g := by
    ext s
    exact congrFun ((sortedCoordinates R M n).map_add f.val g.val) s
  map_smul' r f := by
    ext s
    exact congrFun ((sortedCoordinates R M n).map_smul r f.val) s
end Lech.AlternatingCech


namespace Lech.AlternatingCech
open Set
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι : Type} [Fintype ι] [LinearOrder ι]
def vertexMap (τ : ι → ι) : (ι → R) →ₗ[R] (ι → R) :=
  (basis R).constr R (fun i => basis R (τ i))
omit [LinearOrder ι] in
lemma vertexMap_basis (τ : ι → ι) (i : ι) : vertexMap R τ (basis R i)=basis R (τ i) := by
  simp [vertexMap]
def pullback (τ : ι → ι) (p : ℕ) : Alt R M (ι:=ι) p →ₗ[R] Alt R M (ι:=ι) p where
  toFun f := f.compLinearMap (vertexMap R τ)
  map_add' f g := by ext v;rfl
  map_smul' r f := by ext v;rfl
omit [LinearOrder ι] in
lemma pullback_eval (τ : ι → ι) (p : ℕ) (f : Alt R M (ι:=ι) p) (a : Fin p → ι) :
    evaluation R M p (pullback R M τ p f) a = evaluation R M p f (τ ∘ a) := by
  change f (fun i => vertexMap R τ (basis R (a i)))=f (fun i => basis R (τ (a i)))
  simp only [vertexMap_basis]
omit [LinearOrder ι] in
lemma pullback_delta (τ : ι → ι) (p : ℕ) (f : Alt R M (ι:=ι) p) :
    pullback R M τ (p+1) (delta R M p f)=delta R M p (pullback R M τ p f) := by
  apply evaluation_injective R M (p+1)
  ext a
  rw [pullback_eval,evaluation_delta,evaluation_delta]
  simp only [FiniteCoverCech.delta,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  rw [pullback_eval]
  rfl
 

def prism (τ : ι → ι) : (p : ℕ) → Alt R M (ι:=ι) (p+1) →ₗ[R] Alt R M (ι:=ι) p
  | 0 => 0
  | p+1 =>
    (sortedCoordinates R M (p+1)).symm.toLinearMap.comp
      (LinearMap.pi (fun s : powersetCard ι (p+1) =>
        let c := τ (s.val.orderEmbOfFin s.property 0)
        (LinearMap.proj s).comp ((sortedCoordinates R M (p+1)).toLinearMap.comp
          ((extra R M c (p+1)) - (delta R M p).comp ((prism τ p).comp (extra R M c (p+1)))))))
lemma prism_succ (τ : ι → ι) (p : ℕ) (f : Alt R M (ι:=ι) (p+2)) (s : powersetCard ι (p+1)) :
    sortedCoordinates R M (p+1) (prism R M τ (p+1) f) s =
    let c := τ (s.val.orderEmbOfFin s.property 0)
    sortedCoordinates R M (p+1) (extra R M c (p+1) f - delta R M p (prism R M τ p (extra R M c (p+1) f))) s := by
  change (sortedCoordinates R M (p+1)) ((sortedCoordinates R M (p+1)).symm _) s=_
  rw [LinearEquiv.apply_symm_apply]
  rfl
omit [LinearOrder ι] in
lemma pullback_zero (τ : ι → ι) (f : Alt R M (ι:=ι) 0) : pullback R M τ 0 f=f := by
  ext v
  change f _=f v
  congr 1
  exact Subsingleton.elim _ _
lemma pullback_extra_sorted_zero (τ : ι → ι) (p : ℕ) (f : Alt R M (ι:=ι) (p+2))
    (s : powersetCard ι (p+1)) :
    sortedCoordinates R M (p+1)
      (pullback R M τ (p+1) (extra R M (τ (s.val.orderEmbOfFin s.property 0)) (p+1) f)) s=0 := by
  rw [sortedCoordinates_apply]
  change evaluation R M (p+1)
    (pullback R M τ (p+1) (extra R M (τ (s.val.orderEmbOfFin s.property 0)) (p+1) f))
    (s.val.orderEmbOfFin s.property)=0
  rw [pullback_eval,evaluation_extra]
  let a : Fin (p+1) → ι := s.val.orderEmbOfFin s.property
  change f (fun i => basis R ((Fin.cons (τ (a 0)) (τ ∘ a) : Fin (p+2) → ι) i))=0
  apply f.map_eq_zero_of_eq (i:=0) (j:=Fin.succ 0)
  · rfl
  · exact (Fin.succ_ne_zero (0 : Fin (p+1))).symm
lemma prism_identity_step (τ : ι → ι) (p : ℕ)
    (h : ∀ g : Alt R M (ι:=ι) p,
      delta R M p (prism R M τ p (delta R M p g))=
        delta R M p g-pullback R M τ (p+1) (delta R M p g))
    (f : Alt R M (ι:=ι) (p+1)) :
    prism R M τ (p+1) (delta R M (p+1) f)+delta R M p (prism R M τ p f)=
      f-pullback R M τ (p+1) f := by
  apply (sortedCoordinates R M (p+1)).injective
  ext s
  rw [map_add,Pi.add_apply,prism_succ]
  let c := τ (s.val.orderEmbOfFin s.property 0)
  let g := extra R M c p f
  have he : extra R M c (p+1) (delta R M (p+1) f)=f-delta R M p g :=
    eq_sub_iff_add_eq.mpr (extra_delta R M c p f)
  have hp : pullback R M τ (p+1) (delta R M p g)=
      pullback R M τ (p+1) f - pullback R M τ (p+1) (extra R M c (p+1) (delta R M (p+1) f)) := by
    rw [he,map_sub]
    abel
  have hh : extra R M c (p+1) (delta R M (p+1) f)-
      delta R M p (prism R M τ p (extra R M c (p+1) (delta R M (p+1) f)))+
      delta R M p (prism R M τ p f)=
      f-pullback R M τ (p+1) f+
        pullback R M τ (p+1) (extra R M c (p+1) (delta R M (p+1) f)) := by
    rw [he,map_sub,map_sub,h g,hp,he]
    abel
  have hs := congrArg (fun z => sortedCoordinates R M (p+1) z s) hh
  simpa only [c,map_add,Pi.add_apply,pullback_extra_sorted_zero,add_zero] using hs
 

lemma prism_identity (τ : ι → ι) (p : ℕ) (f : Alt R M (ι:=ι) (p+1)) :
    prism R M τ (p+1) (delta R M (p+1) f)+delta R M p (prism R M τ p f)=
      f-pullback R M τ (p+1) f := by
  induction p with
  | zero =>
    apply prism_identity_step
    intro g
    rw [prism,LinearMap.zero_apply,map_zero,pullback_delta,pullback_zero,sub_self]
  | succ p ih =>
    apply prism_identity_step
    intro g
    have hi := congrArg (delta R M (p+1)) (ih g)
    rw [map_add,delta_square,add_zero,map_sub,←pullback_delta] at hi
    exact hi


lemma sortedCoordinates_eq_evaluation (p : ℕ) (f : Alt R M (ι:=ι) p) (s : powersetCard ι p) :
    sortedCoordinates R M p f s=evaluation R M p f (s.val.orderEmbOfFin s.property) :=
  sortedCoordinates_apply R M p f s
lemma evaluation_mem_of_sorted (T : Finset ι) (P : Submodule R M) (p : ℕ) (f : Alt R M (ι:=ι) p)
    (hf : ∀ s : powersetCard ι p,s.val⊆T → sortedCoordinates R M p f s∈P)
    (a : Fin p → ι) (ha : ∀ i,a i∈T) : evaluation R M p f a∈P := by
  let F : Finset ι → Submodule R M := fun s => if s⊆T then P else ⊤
  have hh : f∈cochains R M F p := (mem_cochains_iff_sorted R M F p f).mpr (by
    intro s
    by_cases hs : s.val⊆T
    · simpa only [F,ite_eq_left hs] using hf s hs
    · simp only [F,ite_eq_right hs,Submodule.mem_top])
  have hs : FiniteCoverCech.intersection a⊆T := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact ha j
  simpa only [F,ite_eq_left hs] using hh a
 

lemma prism_local (τ : ι → ι) (T : Finset ι) (hT : ∀ i∈T,τ i∈T)
    (P : Submodule R M) (p : ℕ) (f : Alt R M (ι:=ι) (p+1))
    (hf : ∀ a : Fin (p+1) → ι,(∀ i,a i∈T) → evaluation R M (p+1) f a∈P)
    (a : Fin p → ι) (ha : ∀ i,a i∈T) : evaluation R M p (prism R M τ p f) a∈P := by
  induction p with
  | zero => simpa only [prism,LinearMap.zero_apply,map_zero,Pi.zero_apply] using P.zero_mem
  | succ p ih =>
    apply evaluation_mem_of_sorted R M T P (p+1) _ ?_ a ha
    intro s hs
    let c := τ (s.val.orderEmbOfFin s.property 0)
    rw [prism_succ]
    change sortedCoordinates R M (p+1)
      (extra R M c (p+1) f-delta R M p (prism R M τ p (extra R M c (p+1) f))) s∈P
    rw [map_sub,Pi.sub_apply]
    have hc : c∈T := hT _ (hs (s.val.orderEmbOfFin_mem s.property 0))
    have hextra : ∀ b : Fin (p+1) → ι,(∀ i,b i∈T) →
        evaluation R M (p+1) (extra R M c (p+1) f) b∈P := by
      intro b hb
      rw [evaluation_extra]
      change evaluation R M (p+2) f (Fin.cons c b)∈P
      apply hf
      intro i
      exact Fin.cases hc (fun i => hb i) i
    apply P.sub_mem
    · rw [sortedCoordinates_eq_evaluation]
      exact hextra _ (fun i => hs (s.val.orderEmbOfFin_mem s.property i))
    · rw [sortedCoordinates_eq_evaluation,evaluation_delta]
      change (∑ i : Fin (p+1),(-1:R)^i.val •
        evaluation R M p (prism R M τ p (extra R M c (p+1) f))
          ((s.val.orderEmbOfFin s.property) ∘ i.succAbove))∈P
      apply P.sum_mem
      intro i _
      apply P.smul_mem
      apply ih (extra R M c (p+1) f) hextra
      intro j
      exact hs (s.val.orderEmbOfFin_mem s.property (i.succAbove j))
 

lemma prism_mem (τ : ι → ι) (hτ : ∀ i,τ (τ i)=τ i)
    (F : Finset ι → Submodule R M) (hF : Monotone F)
    (hcarrier : ∀ s,F (s∪s.image τ)≤F s) (p : ℕ)
    (f : Alt R M (ι:=ι) (p+1)) (hf : f∈cochains R M F (p+1)) :
    prism R M τ p f∈cochains R M F p := by
  apply (mem_cochains_iff_sorted R M F p _).mpr
  intro s
  rw [sortedCoordinates_eq_evaluation]
  apply hcarrier s.val
  have hstable : ∀ i∈s.val∪s.val.image τ,τ i∈s.val∪s.val.image τ := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      rw [hτ]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
  apply prism_local R M τ (s.val∪s.val.image τ) hstable (F (s.val∪s.val.image τ)) p f
  · intro a ha
    apply hF ?_ (hf a)
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact ha j
  · intro i
    exact Finset.mem_union_left _ (s.val.orderEmbOfFin_mem s.property i)
end Lech.AlternatingCech
end

end OAI
