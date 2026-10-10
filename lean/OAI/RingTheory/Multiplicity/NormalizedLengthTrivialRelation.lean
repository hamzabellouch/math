import Mathlib
import OAI.RingTheory.Multiplicity.RootTowerRemainderExponent
import OAI.RingTheory.Multiplicity.RootTowerRootWeight
import OAI.RingTheory.Multiplicity.SignedCechBicRow

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
namespace Lech.NormalizedLength
lemma trivialRelation_of_injective_flat_lift {R M N : Type*}
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Flat R N] (g : N →ₗ[R] M) (hg : Function.Injective g)
    {l : ℕ} {f : Fin l → R} {x : Fin l → M}
    (hx : ∑ i, f i • x i = 0) (y : Fin l → N) (hy : ∀ i, g (y i) = x i) :
    Module.IsTrivialRelation f x := by
  have hz : ∑ i, f i • y i = 0 := by
    apply hg
    simpa only [map_sum, map_smul, hy, map_zero] using hx
  obtain ⟨k, a, z, hz, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hz
  refine ⟨k, a, fun j => g (z j), ?_, ha⟩
  intro i
  rw [← hy i, hz i, map_sum]
  simp only [map_smul]
end Lech.NormalizedLength


namespace Lech.NormalizedLength.Tower
variable {L : Type*} [CommRing L] (T : Lech.NormalizedLength.Tower L)

lemma finite_collection_stage {ι : Type*} [Fintype ι] (x : ι → L) (n : ℕ) :
    ∃ m, n ≤ m ∧ ∀ i, x i ∈ T.ring m := by
  classical
  choose k hk using fun i => T.exhaustive (x i)
  refine ⟨max n (Finset.univ.sup k), le_max_left _ _, fun i => ?_⟩
  exact T.mono ((Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)) (hk i)

include T in
lemma nontrivial_limit : Nontrivial L :=
  (Subtype.val_injective : Function.Injective fun x : T.ring 0 => (x : L)).nontrivial

include T in
lemma local_limit : IsLocalRing L := by
  let := T.nontrivial_limit
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  obtain ⟨n, hn⟩ := T.exhaustive a
  exact (IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨a, hn⟩ : T.ring n)).imp
    (T.ring n).subtype.isUnit_map (T.ring n).subtype.isUnit_map

lemma local_to_limit (n : ℕ) : IsLocalHom (algebraMap (T.ring n) L) := by
  constructor
  intro a ha
  obtain ⟨u, hu⟩ := ha
  change (↑u : L) = (a : L) at hu
  obtain ⟨m, hm⟩ := T.exhaustive (↑u⁻¹ : L)
  let k := max n m
  let b : T.ring k := Subring.inclusion (T.mono (le_max_left n m)) a
  have hb : IsUnit b := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨↑u⁻¹, T.mono (le_max_right n m) hm⟩, ?_⟩
    apply Subtype.ext
    change (a : L) * (↑u⁻¹ : L) = 1
    rw [← hu]
    simp
  let := T.local_inclusion n k (le_max_left n m)
  exact IsLocalHom.map_nonunit a hb

lemma flat_limit (n : ℕ) : Module.Flat (T.ring n) L := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hx
  obtain ⟨m, hnm, hm⟩ := T.finite_collection_stage x n
  let : Algebra (T.ring n) (T.ring m) := (Subring.inclusion (T.mono hnm)).toAlgebra
  let := T.flat n m hnm
  let φ : T.ring m →ₗ[T.ring n] L :=
    { toFun := fun z => (z : L)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact trivialRelation_of_injective_flat_lift φ Subtype.val_injective hx
    (fun i => ⟨x i, hm i⟩) (fun _ => rfl)

lemma faithfullyFlat_limit (n : ℕ) : Module.FaithfullyFlat (T.ring n) L := by
  let := T.local_limit
  let := T.local_to_limit n
  let := T.flat_limit n
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end Lech.NormalizedLength.Tower

open TensorProduct
namespace Lech.NormalizedLength
variable {R S L N : Type*} [CommRing R] [CommRing S] [CommRing L]
  [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
  [AddCommGroup N] [Module R N]

lemma liftBaseChange_mk_injective [Module.FaithfullyFlat S L] :
    Function.Injective ((TensorProduct.mk R L N 1).liftBaseChange S) := by
  have he : (TensorProduct.mk R L N 1).liftBaseChange S =
      (AlgebraTensorModule.cancelBaseChange R S S L N).toLinearMap ∘ₗ
        TensorProduct.mk S L (S ⊗[R] N) 1 := by
    ext x
    simp
  rw [he]
  exact (AlgebraTensorModule.cancelBaseChange R S S L N).injective.comp
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := S) (B := L) (S ⊗[R] N))

lemma length_span_baseChange [Module.FaithfullyFlat S L] (s : Set N)
    (hs : Submodule.span R s = ⊤) :
    Module.length S (Submodule.span S (TensorProduct.mk R L N 1 '' s)) =
      Module.length S (S ⊗[R] N) := by
  let f := (TensorProduct.mk R L N 1).liftBaseChange S
  have hf : f.range = Submodule.span S (TensorProduct.mk R L N 1 '' s) := by
    rw [LinearMap.range_liftBaseChange, ← Submodule.map_top, ← hs,
      Submodule.map_span, Submodule.span_span_of_tower]
  rw [← hf]
  exact (LinearEquiv.ofInjective f liftBaseChange_mk_injective).length_eq.symm

lemma span_baseChange_eq_top (s : Set N) (hs : Submodule.span R s = ⊤) :
    Submodule.span L (TensorProduct.mk R L N 1 '' s) = ⊤ := by
  rw [← Submodule.baseChange_span, hs, Submodule.baseChange_top]

end Lech.NormalizedLength


namespace Lech.NormalizedLength.Tower
open TensorProduct
variable {L : Type*} [CommRing L] (T : Lech.NormalizedLength.Tower L)

lemma stage_baseChange (n m : ℕ) (hnm : n ≤ m) (N : Type*)
    [AddCommGroup N] [Module (T.ring n) N] (s : Finset N)
    (hs : Submodule.span (T.ring n) (s : Set N) = ⊤) :
    T.stage (s.image (TensorProduct.mk (T.ring n) L N 1)) m =
      T.weight n * (Module.length (T.ring n) N).toENNReal := by
  let : Algebra (T.ring n) (T.ring m) := (Subring.inclusion (T.mono hnm)).toAlgebra
  let : IsScalarTower (T.ring n) (T.ring m) L :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let := T.faithfullyFlat_limit m
  let := T.local_inclusion n m hnm
  let := T.flat n m hnm
  rw [stage, Finset.coe_image]
  erw [length_span_baseChange (R := T.ring n) (S := T.ring m) (L := L) _ hs]
  rw [IsLocalRing.length_baseChange (T.ring n) (T.ring m) N, ENat.toENNReal_mul,
    mul_left_comm]
  have hw : T.weight m * (Module.length (T.ring m) ((T.ring m) ⧸
      (IsLocalRing.maximalIdeal (T.ring n)).map (algebraMap (T.ring n) (T.ring m)))).toENNReal =
      T.weight n := T.weight_mul_fiber n m hnm
  rw [hw, mul_comm]

 

lemma length_baseChange (n : ℕ) (N : Type*)
    [AddCommGroup N] [Module (T.ring n) N] [Module.Finite (T.ring n) N] :
    T.length (L ⊗[T.ring n] N) =
      T.weight n * (Module.length (T.ring n) N).toENNReal := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := T.ring n) (M := N)
  let t := s.image (TensorProduct.mk (T.ring n) L N 1)
  have ht : Submodule.span L (t : Set (L ⊗[T.ring n] N)) = ⊤ := by
    rw [Finset.coe_image]
    exact span_baseChange_eq_top _ hs
  rw [T.length_eq_finiteLength_of_span_top t ht]
  apply le_antisymm
  · exact (T.finiteLength_le_stage t n).trans_eq (T.stage_baseChange n n le_rfl N s hs)
  · apply le_iInf
    intro m
    calc
      T.weight n * (Module.length (T.ring n) N).toENNReal = T.stage t (max n m) :=
        (T.stage_baseChange n (max n m) (le_max_left _ _) N s hs).symm
      _ ≤ T.stage t m := T.stage_antitone t (le_max_right _ _)

end Lech.NormalizedLength.Tower


namespace Lech.NormalizedLength.Tower
universe u v
variable {L : Type u} [CommRing L] (T : Lech.NormalizedLength.Tower L)
  (M : Type v) [AddCommGroup M] [Module L M]

 
def presentedLengths : Set ℝ≥0∞ :=
  {a | ∃ P : ModuleCat.{max u v} L, Module.FinitePresentation L P ∧
    ∃ f : P →ₗ[L] M, Function.Surjective f ∧ T.length P = a}

lemma stage_mem_presentedLengths (s : Finset M)
    (hs : Submodule.span L (s : Set M) = ⊤) (n : ℕ) :
    T.stage s n ∈ T.presentedLengths M := by
  let N := Submodule.span (T.ring n) (s : Set M)
  let : Module.Finite (T.ring n) N := Module.Finite.of_fg (Submodule.fg_span s.finite_toSet)
  let := Module.finitePresentation_of_finite (T.ring n) N
  let f := N.subtype.liftBaseChange L
  refine ⟨ModuleCat.of L (L ⊗[T.ring n] N), inferInstance, f, ?_, ?_⟩
  · apply LinearMap.range_eq_top.mp
    rw [LinearMap.range_liftBaseChange, Submodule.range_subtype,
      Submodule.span_span_of_tower]
    exact hs
  · exact T.length_baseChange n N

 

theorem length_eq_sInf_presented [Module.Finite L M] :
    T.length M = sInf (T.presentedLengths M) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := L) (M := M)
  apply le_antisymm
  · apply le_sInf
    rintro a ⟨P, _, f, hf, rfl⟩
    exact T.length_le_of_surjective f hf
  · rw [T.length_eq_finiteLength_of_span_top s hs]
    apply le_iInf
    intro n
    exact sInf_le (T.stage_mem_presentedLengths M s hs n)

end Lech.NormalizedLength.Tower


namespace Lech.NormalizedLength
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

lemma map_le_annihilator_baseChange (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) :
    I.map (algebraMap R S) ≤ Module.annihilator S (S ⊗[R] M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    rw [IsScalarTower.algebraMap_smul S r, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul, Module.mem_annihilator.mp (hI hr) m,
      TensorProduct.tmul_zero]
  | add x y hx hy => simp only [smul_add, hx, hy, add_zero]

lemma le_annihilator_submodule {L : Type*} [CommRing L] [Algebra R L]
    [Module L M] [IsScalarTower R L M] (I : Ideal R)
    (hI : I.map (algebraMap R L) ≤ Module.annihilator L M)
    (N : Submodule R M) : I ≤ Module.annihilator R N := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro m
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_smul L r (m : M)).symm.trans
    (Module.mem_annihilator.mp (hI (Ideal.mem_map_of_mem _ hr)) m)

end Lech.NormalizedLength


namespace Lech.NormalizedLength.Tower
universe u v
variable {L : Type u} [CommRing L] (T : Lech.NormalizedLength.Tower L)
  (M : Type v) [AddCommGroup M] [Module L M]

 
def torsionPresentedLengths (I : Ideal (T.ring 0)) : Set ℝ≥0∞ :=
  {a | ∃ P : ModuleCat.{max u v} L, Module.FinitePresentation L P ∧
    I.map (algebraMap (T.ring 0) L) ≤ Module.annihilator L P ∧
    ∃ f : P →ₗ[L] M, Function.Surjective f ∧ T.length P = a}

lemma stage_mem_torsionPresentedLengths (I : Ideal (T.ring 0))
    (hI : I.map (algebraMap (T.ring 0) L) ≤ Module.annihilator L M)
    (s : Finset M) (hs : Submodule.span L (s : Set M) = ⊤) (n : ℕ) :
    T.stage s n ∈ T.torsionPresentedLengths M I := by
  let : Algebra (T.ring 0) (T.ring n) := (Subring.inclusion (T.mono (Nat.zero_le n))).toAlgebra
  let J := I.map (algebraMap (T.ring 0) (T.ring n))
  have hJ : J.map (algebraMap (T.ring n) L) = I.map (algebraMap (T.ring 0) L) := by
    dsimp only [J]
    rw [Ideal.map_map]
    rfl
  let N := Submodule.span (T.ring n) (s : Set M)
  let : Module.Finite (T.ring n) N := Module.Finite.of_fg (Submodule.fg_span s.finite_toSet)
  let := Module.finitePresentation_of_finite (T.ring n) N
  let f := N.subtype.liftBaseChange L
  have hn : J ≤ Module.annihilator (T.ring n) N :=
    Lech.NormalizedLength.le_annihilator_submodule J (hJ ▸ hI) N
  have hp := Lech.NormalizedLength.map_le_annihilator_baseChange (S := L) J hn
  rw [hJ] at hp
  refine ⟨ModuleCat.of L (L ⊗[T.ring n] N), inferInstance, hp, f, ?_, ?_⟩
  · apply LinearMap.range_eq_top.mp
    rw [LinearMap.range_liftBaseChange, Submodule.range_subtype,
      Submodule.span_span_of_tower]
    exact hs
  · exact T.length_baseChange n N

 

theorem length_eq_sInf_torsionPresented [Module.Finite L M]
    (I : Ideal (T.ring 0))
    (hI : I.map (algebraMap (T.ring 0) L) ≤ Module.annihilator L M) :
    T.length M = sInf (T.torsionPresentedLengths M I) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := L) (M := M)
  apply le_antisymm
  · apply le_sInf
    rintro a ⟨P, _, _, f, hf, rfl⟩
    exact T.length_le_of_surjective f hf
  · rw [T.length_eq_finiteLength_of_span_top s hs]
    apply le_iInf
    intro n
    exact sInf_le (T.stage_mem_torsionPresentedLengths M I hI s hs n)

end Lech.NormalizedLength.Tower


namespace Lech.RootTower
open scoped ENNReal
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

 
def regularTower : Lech.NormalizedLength.Tower (PerfectClosure (MvPowerSeries σ k) p) where
  ring := rootRing (MvPowerSeries σ k) p
  mono := rootRing_mono (MvPowerSeries σ k) p
  localRing := fun n => rootRing_local (MvPowerSeries σ k) p n
  noetherian := fun n => rootRing_noetherian (MvPowerSeries σ k) p n
  exhaustive := rootRing_exhaustive (MvPowerSeries σ k) p
  weight n := ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹
  weight_ne_zero n := by simp
  weight_ne_top n := by
    apply ENNReal.inv_ne_top.mpr
    exact pow_ne_zero _ (by exact_mod_cast (Nat.Prime.ne_zero (Fact.out : p.Prime)))
  local_inclusion := root_inclusion_local (MvPowerSeries σ k) p
  flat n m h := (root_inclusion_flat (MvPowerSeries σ k) p
    (fun j => iterateFrobenius_flat (σ := σ) (R := k) p j) n m h)
  weight_mul_fiber n m h := by
    dsimp only
    rw [root_fiber_length (MvPowerSeries σ k) p n m h]
    have hf := frobenius_fiber_length (σ := σ) (k := k) p (m-n)
    change Module.length (MvPowerSeries σ k)
      ((MvPowerSeries σ k) ⧸ (IsLocalRing.maximalIdeal (MvPowerSeries σ k)).map
        (iterateFrobenius (MvPowerSeries σ k) p (m-n))) = _ at hf
    rw [hf]
    simpa using root_weight_mul p (Fintype.card σ) n m (Nat.Prime.pos Fact.out) h

end Lech.RootTower


namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

 
def normalizedLength (M : Type*) [AddCommGroup M]
    [Module (PerfectClosure (MvPowerSeries σ k) p) M] : ℝ≥0∞ :=
  (regularTower σ k p).length M

lemma normalizedLength_stage (n : ℕ) (M : Type*) [AddCommGroup M]
    [Module (rootRing (MvPowerSeries σ k) p n) M]
    [Module.Finite (rootRing (MvPowerSeries σ k) p n) M] :
    normalizedLength σ k p ((PerfectClosure (MvPowerSeries σ k) p) ⊗[
      rootRing (MvPowerSeries σ k) p n] M) =
    ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹ *
      (Module.length (rootRing (MvPowerSeries σ k) p n) M).toENNReal := by
  let : Module ((regularTower σ k p).ring n) M := by
    change Module (rootRing (MvPowerSeries σ k) p n) M
    infer_instance
  let : Module.Finite ((regularTower σ k p).ring n) M := by
    change Module.Finite (rootRing (MvPowerSeries σ k) p n) M
    infer_instance
  exact (regularTower σ k p).length_baseChange n M

end Lech.RootTower


namespace Lech.TensorTransport
variable {A B P M : Type*} [CommRing A] [CommRing B] [CommRing P]
  [Algebra A B] [Algebra B P] [Algebra A P] [IsScalarTower A B P]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

 

def reindex (h : Function.Surjective (algebraMap A B)) :
    P ⊗[A] M ≃ₗ[P] P ⊗[B] M := by
  let : TensorProduct.CompatibleSMul A B P M :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective P M h
  exact TensorProduct.equivOfCompatibleSMul B A P P M

lemma reindex_tmul (h : Function.Surjective (algebraMap A B)) (x : P) (m : M) :
    reindex h (x ⊗ₜ[A] m) = x ⊗ₜ[B] m := rfl

end Lech.TensorTransport


namespace Lech.TensorTransport
variable {A B P : Type*} [CommRing A] [CommRing B] [CommRing P]
  (e : A ≃+* B) [Algebra B P]
  (M : Type*) [AddCommGroup M] [Module A M]

lemma twist_tower :
    let : Algebra A B := e.toRingHom.toAlgebra
    let : Module B M := Module.compHom M e.symm.toRingHom
    IsScalarTower A B M := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Module B M := Module.compHom M e.symm.toRingHom
  constructor
  intro a b m
  change e.symm (e a * b) • m = a • (e.symm b • m)
  rw [map_mul,e.symm_apply_apply,mul_smul]

lemma twist_length :
    let : Module B M := Module.compHom M e.symm.toRingHom
    Module.length B M = Module.length A M := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Module B M := Module.compHom M e.symm.toRingHom
  let : IsScalarTower A B M := twist_tower e M
  exact (Module.length_eq_of_surjective (R := B) (S := A) e.surjective).symm

lemma twist_finite [Module.Finite A M] :
    let : Module B M := Module.compHom M e.symm.toRingHom
    Module.Finite B M := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Module B M := Module.compHom M e.symm.toRingHom
  let : IsScalarTower A B M := twist_tower e M
  exact Module.Finite.of_restrictScalars_finite A B M

end Lech.TensorTransport


namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]

 

lemma normalizedLength_rootBaseChange (n : ℕ) (M : Type*) [AddCommGroup M]
    [Module (MvPowerSeries σ k) M] [Module.Finite (MvPowerSeries σ k) M] :
    let : Algebra (MvPowerSeries σ k) (PerfectClosure (MvPowerSeries σ k) p) :=
      (rootMap (MvPowerSeries σ k) p n).toAlgebra
    normalizedLength σ k p ((PerfectClosure (MvPowerSeries σ k) p) ⊗[MvPowerSeries σ k] M) =
    ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹ * (Module.length (MvPowerSeries σ k) M).toENNReal := by
  let A := MvPowerSeries σ k
  let P := PerfectClosure A p
  let B := rootRing A p n
  let e : A ≃+* B := rootEquiv A p n
  let : Algebra A P := (rootMap A p n).toAlgebra
  let : Algebra A B := e.toRingHom.toAlgebra
  let : IsScalarTower A B P := IsScalarTower.of_algebraMap_eq' rfl
  let : Module B M := Module.compHom M e.symm.toRingHom
  let : IsScalarTower A B M := Lech.TensorTransport.twist_tower e M
  let : Module.Finite B M := Lech.TensorTransport.twist_finite e M
  have h := Lech.TensorTransport.reindex (P := P) (M := M) e.surjective
  have he := (regularTower σ k p).length_eq_of_equiv h
  change normalizedLength σ k p (P ⊗[A] M) = _ at he
  change normalizedLength σ k p (P ⊗[A] M) = _
  change normalizedLength σ k p (P ⊗[A] M) = normalizedLength σ k p (P ⊗[B] M) at he
  rw [he,normalizedLength_stage]
  congr 1
  exact congrArg ENat.toENNReal (Lech.TensorTransport.twist_length e M)

end Lech.RootTower
end
end

end OAI
