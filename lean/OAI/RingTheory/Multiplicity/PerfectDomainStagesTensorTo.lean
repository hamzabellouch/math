import Mathlib
import OAI.RingTheory.Multiplicity.TraceConductorPerfectOrder

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
open TensorProduct
open scoped TensorProduct nonZeroDivisors
namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped TensorProduct
variable (A D : Type*) [CommRing A] [IsDomain A] [CommRing D] [IsDomain D]
  [Algebra A D] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP D p]

def tensorToStage (n : ℕ) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (PerfectClosure A p) ⊗[A] D →ₐ[PerfectClosure A p] stage A D p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  exact (tensorMap A D p n).codRestrict (stage A D p n) (by
    intro x
    rw [← tensorMap_range A D p n]
    exact ⟨x,rfl⟩)

lemma tensorToStage_bijective (n : ℕ) (hi : Function.Injective (tensorMap A D p n)) :
    Function.Bijective (tensorToStage A D p n) := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  constructor
  · intro x y h
    exact hi (congrArg Subtype.val h)
  · intro b
    have hb := b.property
    have hb' : (b : PerfectClosure D p) ∈ (tensorMap A D p n).range :=
      (tensorMap_range A D p n).symm ▸ hb
    clear hb
    obtain ⟨x,hx⟩ := hb'
    exact ⟨x,Subtype.ext hx⟩

def tensorEquiv (n : ℕ) (hi : Function.Injective (tensorMap A D p n)) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    (PerfectClosure A p) ⊗[A] D ≃ₐ[PerfectClosure A p] stage A D p n := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  exact AlgEquiv.ofBijective (tensorToStage A D p n) (tensorToStage_bijective A D p n hi)

omit [IsDomain A] in
lemma original_mem_stage (n : ℕ) (d : D) : PerfectClosure.of D p d ∈ stage A D p n := by
  change rootMap D p 0 d ∈ _
  rw [← rootMap_transition D p 0 n (Nat.zero_le n) d]
  exact Algebra.subset_adjoin ⟨iterateFrobenius D p (n-0) d,rfl⟩

def originalToStage (n : ℕ) : D →+* stage A D p n :=
  (PerfectClosure.of D p).codRestrict (stage A D p n).toSubring (original_mem_stage A D p n)

lemma tensorEquiv_original (n : ℕ) (hi : Function.Injective (tensorMap A D p n)) (d : D) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    tensorEquiv A D p n hi (1 ⊗ₜ[A] iterateFrobenius D p n d) = originalToStage A D p n d := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply Subtype.ext
  change tensorMap A D p n (1 ⊗ₜ[A] iterateFrobenius D p n d) = PerfectClosure.of D p d
  rw [tensorMap_apply,map_one,one_mul]
  exact rootMap_transition D p 0 n (Nat.zero_le n) d

lemma tensorEquiv_ideal (n : ℕ) (hi : Function.Injective (tensorMap A D p n)) (H : Ideal D) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    H.map (originalToStage A D p n) =
      (H.map ((Algebra.TensorProduct.includeRight (R := A) (A := PerfectClosure A p)).toRingHom.comp
        (iterateFrobenius D p n))).map (tensorEquiv A D p n hi).toRingHom := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  dsimp only
  rw [Ideal.map_map]
  congr 1
  apply DFunLike.ext
  intro d
  exact (tensorEquiv_original A D p n hi d).symm

lemma tensorEquiv_scalar (n : ℕ) (hi : Function.Injective (tensorMap A D p n)) (g : A) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    tensorEquiv A D p n hi (1 ⊗ₜ[A] algebraMap A D g) =
      algebraMap (PerfectClosure A p) (stage A D p n) (rootMap A p n g) := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply Subtype.ext
  change tensorMap A D p n (1 ⊗ₜ[A] algebraMap A D g) =
    perfectMap p (algebraMap A D) (rootMap A p n g)
  rw [tensorMap_apply,map_one,one_mul,perfectMap_root]

def rootToStage (n : ℕ) : D →+* stage A D p n :=
  (rootMap D p n).codRestrict (stage A D p n).toSubring
    (fun d => Algebra.subset_adjoin ⟨d,rfl⟩)

lemma tensorEquiv_root (n : ℕ) (hi : Function.Injective (tensorMap A D p n)) (d : D) :
    let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
    tensorEquiv A D p n hi (1 ⊗ₜ[A] d) = rootToStage A D p n d := by
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  apply Subtype.ext
  change tensorMap A D p n (1 ⊗ₜ[A] d) = rootMap D p n d
  rw [tensorMap_apply,map_one,one_mul]

omit [IsDomain A] in
lemma rootToStage_original (n : ℕ) :
    (rootToStage A D p n).comp (iterateFrobenius D p n) = originalToStage A D p n := by
  apply DFunLike.ext
  intro d
  apply Subtype.ext
  exact rootMap_transition D p 0 n (Nat.zero_le n) d

lemma rootToStage_scalar (n : ℕ) (g : A) :
    rootToStage A D p n (algebraMap A D g) =
      algebraMap (PerfectClosure A p) (stage A D p n) (rootMap A p n g) := by
  apply Subtype.ext
  exact (perfectMap_root p (algebraMap A D) n g).symm

end Lech.PerfectDomainStages


namespace Lech.PerfectDomainStages
open Lech.RootTower
open scoped ENNReal TensorProduct
variable (σ k D : Type*) [Fintype σ] [Field k] [CommRing D] [IsDomain D] [IsLocalRing D]
  [Algebra (MvPowerSeries σ k) D] [IsLocalHom (algebraMap (MvPowerSeries σ k) D)]
  [Module.Finite (MvPowerSeries σ k) D]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]

local instance tensorToStagePowerSeriesIsDomain : IsDomain (MvPowerSeries σ k) :=
  NoZeroDivisors.to_isDomain _

lemma normalizedLength_actual_stage_quotient
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries σ k))
      (IsLocalRing.ResidueField D))) (H : Ideal D) (n : ℕ)
    (hi : Function.Injective (tensorMap (MvPowerSeries σ k) D p n)) :
    normalizedLength σ k p ((stage (MvPowerSeries σ k) D p n) ⧸
      H.map (originalToStage (MvPowerSeries σ k) D p n)) =
    ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹ *
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal := by
  let A := MvPowerSeries σ k
  let : Algebra A (PerfectClosure A p) := (rootMap A p n).toAlgebra
  let e := Ideal.quotientEquivAlg _ _ (tensorEquiv A D p n hi) (tensorEquiv_ideal A D p n hi H)
  have he := (regularTower σ k p).length_eq_of_equiv e.toLinearEquiv
  unfold normalizedLength
  rw [← he]
  exact normalizedLength_stage_quotient σ k D p hres H n

lemma normalizedLength_root_stage_quotient
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries σ k))
      (IsLocalRing.ResidueField D))) (J : Ideal D) (n : ℕ)
    (hi : Function.Injective (tensorMap (MvPowerSeries σ k) D p n)) :
    normalizedLength σ k p ((stage (MvPowerSeries σ k) D p n) ⧸
      J.map (rootToStage (MvPowerSeries σ k) D p n)) =
    ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹ * (Module.length D (D ⧸ J)).toENNReal := by
  let A := MvPowerSeries σ k
  let P := PerfectClosure A p
  let : Algebra A P := (rootMap A p n).toAlgebra
  let inc := Algebra.TensorProduct.includeRight (R := A) (A := P) (B := D)
  have hm : (J.map inc.toRingHom).map (tensorEquiv A D p n hi).toRingHom =
      J.map (rootToStage A D p n) := by
    rw [Ideal.map_map]
    congr 1
    apply DFunLike.ext
    intro d
    exact tensorEquiv_root A D p n hi d
  let e := Ideal.quotientEquivAlg (J.map inc.toRingHom) _ (tensorEquiv A D p n hi) hm.symm
  let e' := Algebra.TensorProduct.tensorQuotientEquiv (R := A) P D P J
  have he := (regularTower σ k p).length_eq_of_equiv (e'.trans e).toLinearEquiv
  unfold normalizedLength
  rw [← he]
  change normalizedLength σ k p (P ⊗[A] (D ⧸ J)) = _
  rw [normalizedLength_rootBaseChange]
  congr 1
  exact congrArg ENat.toENNReal (length_eq_of_residue_surjective hres (D ⧸ J))

lemma normalizedLength_scalar_stage_quotient
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField (MvPowerSeries σ k))
      (IsLocalRing.ResidueField D))) (H : Ideal D) (n : ℕ)
    (hi : Function.Injective (tensorMap (MvPowerSeries σ k) D p n)) (g : MvPowerSeries σ k) :
    normalizedLength σ k p ((stage (MvPowerSeries σ k) D p n) ⧸
      (H.map (originalToStage (MvPowerSeries σ k) D p n) ⊔
        Ideal.span {algebraMap (PerfectClosure (MvPowerSeries σ k) p) _
          (rootMap (MvPowerSeries σ k) p n g)})) =
    ((p : ℝ≥0∞) ^ (n * Fintype.card σ))⁻¹ *
      (Module.length D (D ⧸ (H.map (iterateFrobenius D p n) ⊔
        Ideal.span {algebraMap (MvPowerSeries σ k) D g}))).toENNReal := by
  have he := normalizedLength_root_stage_quotient σ k D p hres
    (H.map (iterateFrobenius D p n) ⊔ Ideal.span {algebraMap (MvPowerSeries σ k) D g}) n hi
  rwa [Ideal.map_sup,Ideal.map_map,rootToStage_original,Ideal.map_span,
    Set.image_singleton,rootToStage_scalar] at he

end Lech.PerfectDomainStages


namespace Lech.NormalizedLength.Tower
variable {L : Type*} [CommRing L] (T : Tower L)
variable {M N P : Type*} [AddCommGroup M] [Module L M]
  [AddCommGroup N] [Module L N] [AddCommGroup P] [Module L P]

 

lemma length_kernel_eq_cokernel (f : M →ₗ[L] M) (hM : T.length M ≠ ⊤) :
    T.length f.ker = T.length (M ⧸ f.range) := by
  have h₁ := T.length_eq_add_of_exact f.rangeRestrict.ker.subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  have hk : f.rangeRestrict.ker = f.ker := by ext x; simp
  rw [hk] at h₁
  have h₂ := T.length_eq_add_of_exact f.range.subtype f.range.mkQ
    (Submodule.subtype_injective _) f.range.mkQ_surjective
    (LinearMap.exact_subtype_mkQ f.range)
  have hr : T.length f.range ≠ ⊤ :=
    ne_top_of_le_ne_top hM (T.length_le_of_injective f.range.subtype
      (Submodule.subtype_injective _))
  exact (ENNReal.add_right_inj hr).mp ((add_comm _ _).trans (h₁.symm.trans h₂))

 

lemma length_torsion_subquotient_le (i : N →ₗ[L] M) (q : N →ₗ[L] P)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (g : L) (hg : ∀ x : P, g • x = 0) (hM : T.length M ≠ ⊤) :
    T.length P ≤ T.length (M ⧸ (LinearMap.lsmul L M g).range) := by
  let fN := LinearMap.lsmul L N g
  let fM := LinearMap.lsmul L M g
  have hqker : fN.range ≤ q.ker := by
    rintro x ⟨y,rfl⟩
    change q (g • y) = 0
    rw [map_smul,hg]
  let q' := fN.range.liftQ q hqker
  have hq' : Function.Surjective q' := by
    intro x
    obtain ⟨y,rfl⟩ := hq x
    exact ⟨fN.range.mkQ y,rfl⟩
  let i' : fN.ker →ₗ[L] fM.ker :=
    (i.comp fN.ker.subtype).codRestrict fM.ker (by
      intro x
      change g • i x = 0
      rw [← map_smul]
      simpa only [fN, LinearMap.lsmul_apply, map_zero] using congrArg i x.property)
  have hi' : Function.Injective i' := by
    intro x y h
    apply Subtype.ext
    apply hi
    exact congrArg Subtype.val h
  have hN : T.length N ≠ ⊤ :=
    ne_top_of_le_ne_top hM (T.length_le_of_injective i hi)
  calc
    T.length P ≤ T.length (N ⧸ fN.range) :=
      T.length_le_of_surjective q' hq'
    _ = T.length fN.ker := (T.length_kernel_eq_cokernel fN hN).symm
    _ ≤ T.length fM.ker := T.length_le_of_injective i' hi'
    _ = _ := T.length_kernel_eq_cokernel fM hM
end Lech.NormalizedLength.Tower


namespace Lech.NormalizedLength.Tower
open Filter
open scoped Topology
variable {L : Type*} [CommRing L] (T : Tower L)
  (M : ℕ → Type*) [∀ n, AddCommGroup (M n)] [∀ n, Module L (M n)]
  {N : Type*} [AddCommGroup N] [Module L N]

 

theorem length_stage_tendsto (f : ∀ n, M n →ₗ[L] N)
    (hm : Monotone (fun n => (f n).range))
    (hex : ∀ x : N, ∃ n, x ∈ (f n).range)
    (e : ℕ → ℝ≥0∞) (he : Tendsto e atTop (𝓝 0))
    (hker : ∀ n, T.length (f n).ker ≤ e n) :
    Tendsto (fun n => T.length (M n)) atTop (𝓝 (T.length N)) := by
  have hmono : Monotone (fun n => T.length (f n).range) := by
    intro n m hnm
    exact T.length_le_of_injective (Submodule.inclusion (hm hnm))
      (Submodule.inclusion_injective (hm hnm))
  have hr : Tendsto (fun n => T.length (f n).range) atTop (𝓝 (T.length N)) := by
    rw [T.length_eq_iSup_of_directed _ hm.directed_le hex]
    exact tendsto_atTop_iSup hmono
  have hup := he.add hr
  rw [zero_add] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hr hup
  · intro n
    exact T.length_range_le (f n)
  · intro n
    have h := T.length_eq_kernel_add (f n).rangeRestrict (f n).surjective_rangeRestrict
    have hk : (f n).rangeRestrict.ker = (f n).ker := by ext x; simp
    rw [hk] at h
    change T.length (M n) ≤ e n + T.length (f n).range
    rw [h]
    exact add_le_add (hker n) le_rfl

end Lech.NormalizedLength.Tower


namespace Lech
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

 
def colengthMap (I : Ideal R) (f : M →ₗ[R] N) :
    (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] (N ⧸ I • (⊤ : Submodule R N)) :=
  Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top I f)

lemma colengthMap_mk (I : Ideal R) (f : M →ₗ[R] N) (x : M) :
    colengthMap I f ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (f x) := rfl

lemma colengthMap_scalar_composition (I : Ideal R) (u : M →ₗ[R] N) (v : N →ₗ[R] M)
    (g : R) (hvu : v.comp u = g • LinearMap.id) :
    (colengthMap I v).comp (colengthMap I u) = g • LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with | _ x =>
  change (I • (⊤ : Submodule R M)).mkQ (v (u x)) = g • _
  rw [show v (u x) = g • x from LinearMap.congr_fun hvu x, map_smul]
  rfl

lemma colengthMap_kernel_killed (I : Ideal R) (u : M →ₗ[R] N) (v : N →ₗ[R] M)
    (g : R) (hvu : v.comp u = g • LinearMap.id) :
    ∀ x : (colengthMap I u).ker, g • x = 0 := by
  intro x
  apply Subtype.ext
  have h := LinearMap.congr_fun (colengthMap_scalar_composition I u v g hvu) x
  change colengthMap I v (colengthMap I u x) = g • (x : M ⧸ _) at h
  rw [x.property,map_zero] at h
  exact h.symm

end Lech


namespace Lech.Conductor
variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
  (B : Subalgebra R C) (g : R) (hg : ∀ c : C, g • c ∈ B)

 
def linearMap : C →ₗ[B] B where
  toFun c := ⟨g • c,hg c⟩
  map_add' x y := Subtype.ext (smul_add g x y)
  map_smul' b c := by
    apply Subtype.ext
    change g • ((b : C)*c) = (b : C)*(g • c)
    exact (mul_smul_comm g (b : C) c).symm

lemma composition : (linearMap B g hg).comp (Algebra.linearMap B C) =
    (algebraMap R B g) • LinearMap.id := by
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  change g • (b : C) = _
  simp only [Algebra.smul_def]
  rfl

include hg in
lemma quotient_kernel_killed (I : Ideal B)
    (x : B ⧸ I • (⊤ : Submodule B B))
    (hx : Lech.colengthMap I (Algebra.linearMap B C) x = 0) :
    (algebraMap R B g) • x = 0 := by
  have h := LinearMap.congr_fun (Lech.colengthMap_scalar_composition I
    (Algebra.linearMap B C) (linearMap B g hg) (algebraMap R B g)
      (composition B g hg)) x
  change Lech.colengthMap I (linearMap B g hg)
    (Lech.colengthMap I (Algebra.linearMap B C) x) = (algebraMap R B g) • x at h
  rw [hx,map_zero] at h
  exact h.symm

end Lech.Conductor


namespace Lech.Conductor
variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
  (B : Subalgebra R C) (g : R) (hg : ∀ c : C, g • c ∈ B)

include hg in
lemma quotient_ideal_kernel_killed (I : Ideal B)
    (x : B ⧸ I)
    (hx : Ideal.quotientMapₐ (I.map (algebraMap B C)) B.val
      (Ideal.le_comap_map : I ≤ (I.map (algebraMap B C)).comap (algebraMap B C)) x = 0) :
    g • x = 0 := by
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective x
  have hb : (b : C) ∈ I.map (algebraMap B C) := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hh := Submodule.smul_top_le_comap_smul_top I (linearMap B g hg)
  have hb' : (b : C) ∈ I • (⊤ : Submodule B C) := by
    rw [Ideal.smul_top_eq_map]
    exact hb
  have hc := hh hb'
  have hc' : (linearMap B g hg) (b : C) ∈ I := by
    simpa only [Submodule.mem_comap, Ideal.smul_eq_mul, Ideal.mul_top] using hc
  change Ideal.Quotient.mk I (g • b) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact hc'
end Lech.Conductor


namespace Lech
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

 
lemma scalar_quotient_exact (I : Ideal B) (g : R) :
    Function.Exact (LinearMap.lsmul R (B ⧸ I) g)
      (Ideal.quotientMapₐ (I ⊔ Ideal.span {algebraMap R B g}) (AlgHom.id R B)
        (le_sup_left : I ≤ I ⊔ Ideal.span {algebraMap R B g})).toLinearMap := by
  intro x
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hb
    have hb' : b ∈ I ⊔ Ideal.span {algebraMap R B g} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hb
    obtain ⟨i,hi,t,ht,rfl⟩ := Submodule.mem_sup.mp hb'
    obtain ⟨c,rfl⟩ := Ideal.mem_span_singleton'.mp ht
    refine ⟨Ideal.Quotient.mk I c,?_⟩
    change g • Ideal.Quotient.mk I c = Ideal.Quotient.mk I (i+c*algebraMap R B g)
    rw [← Ideal.Quotient.mkₐ_eq_mk R, ← map_smul]
    apply Ideal.Quotient.eq.mpr
    simpa only [Algebra.smul_def,mul_comm,sub_add_cancel_right,sub_self,zero_sub] using I.neg_mem hi
  · rintro ⟨y,hy⟩
    rw [← hy]
    obtain ⟨c,rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk (I ⊔ Ideal.span {algebraMap R B g}) (g • c) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (show Ideal.span {algebraMap R B g} ≤ I ⊔ Ideal.span {algebraMap R B g} from le_sup_right)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right c _ (Ideal.subset_span (Set.mem_singleton (algebraMap R B g)))

lemma quotientMap_surjective (I J : Ideal B) (h : I ≤ J) :
    Function.Surjective (Ideal.quotientMapₐ J (AlgHom.id R B) h) := by
  intro x
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk I b,rfl⟩
end Lech


namespace Lech.NormalizedLength.Tower
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (T : Tower R)
lemma length_scalar_cokernel (I : Ideal B) (g : R) :
    T.length ((B ⧸ I) ⧸ (LinearMap.lsmul R (B ⧸ I) g).range) =
      T.length (B ⧸ (I ⊔ Ideal.span {algebraMap R B g})) := by
  let v := (Ideal.quotientMapₐ (I ⊔ Ideal.span {algebraMap R B g}) (AlgHom.id R B)
    (le_sup_left : I ≤ I ⊔ Ideal.span {algebraMap R B g})).toLinearMap
  have he := Lech.scalar_quotient_exact I g
  have hk : v.ker = (LinearMap.lsmul R (B ⧸ I) g).range := LinearMap.exact_iff.mp he
  exact T.length_eq_of_equiv ((Submodule.quotEquivOfEq _ _ hk.symm).trans
    (v.quotKerEquivOfSurjective (Lech.quotientMap_surjective I _ le_sup_left)))
end Lech.NormalizedLength.Tower
end
end

end OAI
