import Mathlib

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
namespace Lech.RootTower
lemma root_weight_mul (p d n m : ℕ) (hp : 0 < p) (h : n ≤ m) :
    ((p : ℝ≥0∞) ^ (m*d))⁻¹ * (p : ℝ≥0∞) ^ ((m-n)*d) =
      ((p : ℝ≥0∞) ^ (n*d))⁻¹ := by
  have hs : m*d = (m-n)*d + n*d := by rw [← Nat.add_mul, Nat.sub_add_cancel h]
  have hz : (p : ℝ≥0∞) ^ ((m-n)*d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
  have ht : (p : ℝ≥0∞) ^ ((m-n)*d) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  rw [hs, pow_add, ENNReal.mul_inv (Or.inl hz) (Or.inl ht), mul_right_comm, ENNReal.inv_mul_cancel hz ht, one_mul]
end Lech.RootTower

open scoped ENNReal TensorProduct Classical DirectSum
namespace Lech.NormalizedLength

section BaseChange
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Module.Flat R S] [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M]

lemma length_span_le_baseChange (s : Set M) :
    Module.length S (Submodule.span S s) ≤
      Module.length R (Submodule.span R s) *
        Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  let f := (Submodule.span R s).subtype.liftBaseChange S
  have hf : f.range = Submodule.span S s := by
    rw [LinearMap.range_liftBaseChange, Submodule.range_subtype,
      Submodule.span_span_of_tower]
  rw [← IsLocalRing.length_baseChange R S (Submodule.span R s), ← hf]
  exact Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict

end BaseChange

 

structure Tower (L : Type*) [CommRing L] where
  ring : ℕ → Subring L
  mono : Monotone ring
  localRing : ∀ n, IsLocalRing (ring n)
  noetherian : ∀ n, IsNoetherianRing (ring n)
  exhaustive : ∀ x : L, ∃ n, x ∈ ring n
  weight : ℕ → ℝ≥0∞
  weight_ne_zero : ∀ n, weight n ≠ 0
  weight_ne_top : ∀ n, weight n ≠ ⊤
  local_inclusion : ∀ n m (h : n ≤ m), IsLocalHom (Subring.inclusion (mono h))
  flat : ∀ n m (h : n ≤ m),
    let : Algebra (ring n) (ring m) := (Subring.inclusion (mono h)).toAlgebra
    Module.Flat (ring n) (ring m)
  weight_mul_fiber : ∀ n m (h : n ≤ m),
    let : IsLocalRing (ring n) := localRing n
    weight m * (Module.length (ring m)
      ((ring m) ⧸ (IsLocalRing.maximalIdeal (ring n)).map
        (Subring.inclusion (mono h)))).toENNReal = weight n

namespace Tower
variable {L : Type*} [CommRing L] (T : Tower L)
attribute [instance] localRing noetherian

variable {M N : Type*} [AddCommGroup M] [Module L M]
  [AddCommGroup N] [Module L N]

 
noncomputable def stage (s : Finset M) (n : ℕ) : ℝ≥0∞ :=
  T.weight n * (Module.length (T.ring n) (Submodule.span (T.ring n) (s : Set M))).toENNReal

 
noncomputable def finiteLength (s : Finset M) : ℝ≥0∞ := ⨅ n, T.stage s n

 
noncomputable def length (M : Type*) [AddCommGroup M] [Module L M] : ℝ≥0∞ :=
  ⨆ s : Finset M, T.finiteLength s

lemma span_mono_stage {s : Set M} {n m : ℕ} (h : n ≤ m) :
    (Submodule.span (T.ring n) s : Set M) ⊆ Submodule.span (T.ring m) s := by
  let : Algebra (T.ring n) (T.ring m) := (Subring.inclusion (T.mono h)).toAlgebra
  let : IsScalarTower (T.ring n) (T.ring m) M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Submodule.span_le_restrictScalars (T.ring n) (T.ring m) s

lemma stage_antitone (s : Finset M) : Antitone (T.stage s) := by
  intro n m h
  let : Algebra (T.ring n) (T.ring m) := (Subring.inclusion (T.mono h)).toAlgebra
  let : IsScalarTower (T.ring n) (T.ring m) M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsLocalHom (algebraMap (T.ring n) (T.ring m)) := T.local_inclusion n m h
  let : Module.Flat (T.ring n) (T.ring m) := T.flat n m h
  have hh := ENat.toENNReal_mono
    (length_span_le_baseChange (R := T.ring n) (S := T.ring m) (s : Set M))
  calc
    T.stage s m ≤ T.weight m *
        ((Module.length (T.ring n) (Submodule.span (T.ring n) (s : Set M))).toENNReal *
        (Module.length (T.ring m) ((T.ring m) ⧸
          (IsLocalRing.maximalIdeal (T.ring n)).map
            (Subring.inclusion (T.mono h)))).toENNReal) := by
      rw [ENat.toENNReal_mul] at hh
      exact mul_le_mul_right hh (T.weight m)
    _ = T.stage s n := by
      rw [mul_left_comm, T.weight_mul_fiber n m h]
      rw [mul_comm]
      rfl

lemma stage_mono {s t : Finset M} (h : s ⊆ t) (n : ℕ) : T.stage s n ≤ T.stage t n := by
  apply mul_le_mul_right
  apply ENat.toENNReal_mono
  exact Module.length_le_of_injective
    (Submodule.inclusion (Submodule.span_mono (Finset.coe_subset.mpr h)))
    (Submodule.inclusion_injective _)

lemma finiteLength_mono {s t : Finset M} (h : s ⊆ t) : T.finiteLength s ≤ T.finiteLength t :=
  iInf_mono fun n => T.stage_mono h n

lemma finiteLength_le_stage (s : Finset M) (n : ℕ) : T.finiteLength s ≤ T.stage s n :=
  iInf_le _ _

lemma finiteLength_le_length (s : Finset M) : T.finiteLength s ≤ T.length M := le_iSup _ s

lemma mem_span_iff_exists_stage {s : Set M} {x : M} :
    x ∈ Submodule.span L s ↔ ∃ n, x ∈ Submodule.span (T.ring n) s := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨0, Submodule.subset_span hy⟩
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨n, hn⟩ := ihx
        obtain ⟨m, hm⟩ := ihy
        exact ⟨max n m, add_mem (T.span_mono_stage (le_max_left n m) hn)
          (T.span_mono_stage (le_max_right n m) hm)⟩
    | smul a x hx ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨m, hm⟩ := T.exhaustive a
        exact ⟨max n m, (Submodule.span (T.ring (max n m)) s).smul_mem
          ⟨a, T.mono (le_max_right n m) hm⟩
          (T.span_mono_stage (le_max_left n m) hn)⟩
  · rintro ⟨n, hn⟩
    exact Submodule.span_le_restrictScalars (T.ring n) L s hn

lemma finite_subset_span_stage {s : Finset M} {t : Set M}
    (h : (s : Set M) ⊆ Submodule.span L t) :
    ∃ n, (s : Set M) ⊆ Submodule.span (T.ring n) t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x s hx ih =>
      obtain ⟨n, hn⟩ := T.mem_span_iff_exists_stage.mp (h (a := x) (Finset.mem_insert_self x s))
      obtain ⟨m, hm⟩ := ih (fun y hy => h (by simp [hy]))
      refine ⟨max n m, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact T.span_mono_stage (le_max_left n m) hn
      · exact T.span_mono_stage (le_max_right n m) (hm hy)

 
lemma finiteLength_le_of_span_le {s t : Finset M}
    (h : Submodule.span L (s : Set M) ≤ Submodule.span L (t : Set M)) :
    T.finiteLength s ≤ T.finiteLength t := by
  obtain ⟨n, hn⟩ := T.finite_subset_span_stage
    (fun x hx => h (Submodule.subset_span hx))
  apply le_iInf
  intro k
  have hs : Submodule.span (T.ring (max n k)) (s : Set M) ≤
      Submodule.span (T.ring (max n k)) (t : Set M) :=
    Submodule.span_le.mpr fun x hx => T.span_mono_stage (le_max_left n k) (hn hx)
  calc
    T.finiteLength s ≤ T.stage s (max n k) := T.finiteLength_le_stage _ _
    _ ≤ T.stage t (max n k) := mul_le_mul_right
      (ENat.toENNReal_mono (Module.length_le_of_injective (Submodule.inclusion hs)
        (Submodule.inclusion_injective hs))) _
    _ ≤ T.stage t k := T.stage_antitone t (le_max_right n k)

lemma finiteLength_eq_of_span_eq {s t : Finset M}
    (h : Submodule.span L (s : Set M) = Submodule.span L (t : Set M)) :
    T.finiteLength s = T.finiteLength t :=
  le_antisymm (T.finiteLength_le_of_span_le h.le) (T.finiteLength_le_of_span_le h.ge)

lemma stage_image_le (f : M →ₗ[L] N) (s : Finset M) (n : ℕ) :
    T.stage (s.image f) n ≤ T.stage s n := by
  classical
  let g := (f.restrictScalars (T.ring n)).domRestrict
    (Submodule.span (T.ring n) (s : Set M))
  have hg : g.range = Submodule.span (T.ring n) (s.image f : Set N) := by
    rw [LinearMap.range_domRestrict, Submodule.map_span]
    simp
  unfold stage
  apply mul_le_mul_right
  apply ENat.toENNReal_mono
  rw [← hg]
  exact Module.length_le_of_surjective g.rangeRestrict g.surjective_rangeRestrict

lemma stage_image_eq (f : M →ₗ[L] N) (hf : Function.Injective f)
    (s : Finset M) (n : ℕ) : T.stage (s.image f) n = T.stage s n := by
  classical
  have h := (Submodule.equivMapOfInjective (f.restrictScalars (T.ring n)) hf
    (Submodule.span (T.ring n) (s : Set M))).length_eq
  rw [Submodule.map_span] at h
  unfold stage
  rw [Finset.coe_image]
  exact congrArg (fun a : ℕ∞ => T.weight n * a.toENNReal) h.symm

lemma finiteLength_image_le (f : M →ₗ[L] N) (s : Finset M) :
    T.finiteLength (s.image f) ≤ T.finiteLength s :=
  iInf_mono fun n => T.stage_image_le f s n

lemma finiteLength_image_eq (f : M →ₗ[L] N) (hf : Function.Injective f) (s : Finset M) :
    T.finiteLength (s.image f) = T.finiteLength s := by
  unfold finiteLength
  simp_rw [T.stage_image_eq f hf]

lemma length_le_of_injective (f : M →ₗ[L] N) (hf : Function.Injective f) :
    T.length M ≤ T.length N := by
  classical
  apply iSup_le
  intro s
  rw [← T.finiteLength_image_eq f hf s]
  exact T.finiteLength_le_length _

lemma length_le_of_surjective (f : M →ₗ[L] N) (hf : Function.Surjective f) :
    T.length N ≤ T.length M := by
  classical
  apply iSup_le
  intro t
  let s := t.image (Function.surjInv hf)
  have hs : s.image f = t := by
    ext x
    simp only [s, Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [Function.surjInv_eq hf] using hz
    · intro hx
      exact ⟨Function.surjInv hf x, ⟨x, hx, rfl⟩, Function.surjInv_eq hf x⟩
  rw [← hs]
  exact (T.finiteLength_image_le f s).trans (T.finiteLength_le_length s)

lemma length_eq_of_equiv (e : M ≃ₗ[L] N) : T.length M = T.length N :=
  le_antisymm (T.length_le_of_injective e e.injective)
    (T.length_le_of_injective e.symm e.symm.injective)

lemma stage_zero [Subsingleton M] (s : Finset M) (n : ℕ) : T.stage s n = 0 := by
  simp [stage, Module.length_eq_zero]

lemma length_zero [Subsingleton M] : T.length M = 0 := by
  simp [length, finiteLength, T.stage_zero]

lemma length_eq_finiteLength_of_span_top (s : Finset M)
    (hs : Submodule.span L (s : Set M) = ⊤) : T.length M = T.finiteLength s := by
  apply le_antisymm _ (T.finiteLength_le_length s)
  apply iSup_le
  intro t
  exact T.finiteLength_le_of_span_le (hs.symm ▸ le_top)

variable {P : Type*} [AddCommGroup P] [Module L P]

lemma stage_add_le (f : N →ₗ[L] M) (g : M →ₗ[L] P)
    (hf : Function.Injective f) (hfg : ∀ x, g (f x) = 0)
    (s : Finset N) (t : Finset M) (n : ℕ) :
    T.stage s n + T.stage (t.image g) n ≤ T.stage (s.image f ∪ t) n := by
  let R := T.ring n
  let u := s.image f ∪ t
  let X := Submodule.span R (u : Set M)
  let Y := Submodule.span R (s : Set N)
  let G : X →ₗ[R] P := (g.restrictScalars R).domRestrict X
  have hY : ∀ x : N, x ∈ Y → f x ∈ X := by
    intro x hx
    have hh : Y.map (f.restrictScalars R) ≤ X := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro y ⟨z, hz, rfl⟩
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    exact hh ⟨x, hx, rfl⟩
  let F₀ : Y →ₗ[R] X := ((f.restrictScalars R).domRestrict Y).codRestrict X
    (fun x => hY x x.property)
  let F : Y →ₗ[R] G.ker := F₀.codRestrict G.ker (fun x => hfg x)
  have hF : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    apply hf
    exact congrArg (fun z : G.ker => ((z : X) : M)) h
  have ht : Submodule.span R (t.image g : Set P) ≤ G.range := by
    apply Submodule.span_le.mpr
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨⟨x, Submodule.subset_span (Finset.mem_union_right _ hx)⟩, rfl⟩
  have he : Module.length R X = Module.length R G.ker + Module.length R G.range := by
    exact Module.length_eq_add_of_exact G.ker.subtype G.rangeRestrict
      (Submodule.subtype_injective _) G.surjective_rangeRestrict
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  have hb : Module.length R Y + Module.length R (Submodule.span R (t.image g : Set P)) ≤
      Module.length R X := by
    rw [he]
    exact add_le_add (Module.length_le_of_injective F hF)
      (Module.length_le_of_injective (Submodule.inclusion ht) (Submodule.inclusion_injective ht))
  have hb' := mul_le_mul_right (ENat.toENNReal_mono hb) (T.weight n)
  simpa only [stage, ENat.toENNReal_add, mul_add] using hb'

lemma finiteLength_add_le (f : N →ₗ[L] M) (g : M →ₗ[L] P)
    (hf : Function.Injective f) (hfg : ∀ x, g (f x) = 0)
    (s : Finset N) (t : Finset M) :
    T.finiteLength s + T.finiteLength (t.image g) ≤ T.finiteLength (s.image f ∪ t) := by
  unfold finiteLength
  rw [ENNReal.iInf_add_iInf (fun i j => ⟨max i j,
    add_le_add (T.stage_antitone s (le_max_left i j))
      (T.stage_antitone (t.image g) (le_max_right i j))⟩)]
  exact iInf_mono fun n => T.stage_add_le f g hf hfg s t n

lemma length_add_le (f : N →ₗ[L] M) (g : M →ₗ[L] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : ∀ x, g (f x) = 0) : T.length N + T.length P ≤ T.length M := by
  unfold length
  rw [ENNReal.iSup_add]
  apply iSup_le
  intro s
  rw [ENNReal.add_iSup]
  apply iSup_le
  intro t
  let u := t.image (Function.surjInv hg)
  have hu : u.image g = t := by
    simp only [u, Finset.image_image]
    simp only [Function.comp_def, Function.surjInv_eq hg, Finset.image_id']
  rw [← hu]
  exact (T.finiteLength_add_le f g hf hfg s u).trans (T.finiteLength_le_length _)

 

lemma stage_le_add_kernel (q : M →ₗ[L] N) (s k : Finset M) {n m : ℕ} (hnm : n ≤ m)
    (hk : Submodule.span (T.ring n) (k : Set M) =
      Submodule.span (T.ring n) (s : Set M) ⊓ (q.restrictScalars (T.ring n)).ker) :
    T.stage s m ≤ T.stage k m + T.stage (s.image q) n := by
  let R := T.ring n
  let S := T.ring m
  let : Algebra R S := (Subring.inclusion (T.mono hnm)).toAlgebra
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsLocalHom (algebraMap R S) := T.local_inclusion n m hnm
  let : Module.Flat R S := T.flat n m hnm
  let X₀ := Submodule.span R (s : Set M)
  let X₁ := Submodule.span S (s : Set M)
  let U := Submodule.span S (k : Set M)
  let F : X₀ →ₗ[R] N := (q.restrictScalars R).domRestrict X₀
  let G : X₁ →ₗ[S] M ⧸ U := U.mkQ.domRestrict X₁
  have hu : U ≤ X₁ := by
    apply Submodule.span_le.mpr
    intro x hx
    have hx' : x ∈ Submodule.span R (k : Set M) := Submodule.subset_span hx
    rw [hk] at hx'
    exact T.span_mono_stage hnm hx'.1
  let L₀ : X₀ →ₗ[R] M ⧸ U := (U.mkQ.restrictScalars R).comp X₀.subtype
  have hvanish : F.ker ≤ L₀.ker := by
    intro x hx
    change U.mkQ (x : M) = 0
    apply (Submodule.Quotient.mk_eq_zero U).mpr
    apply T.span_mono_stage hnm
    rw [hk]
    exact ⟨x.property, hx⟩
  let H : (X₀ ⧸ F.ker) →ₗ[R] M ⧸ U := F.ker.liftQ L₀ hvanish
  let B : S ⊗[R] (X₀ ⧸ F.ker) →ₗ[S] M ⧸ U := H.liftBaseChange S
  have hB : B.range = G.range := by
    change (H.liftBaseChange S).range = G.range
    rw [LinearMap.range_liftBaseChange]
    change Submodule.span S (F.ker.liftQ L₀ hvanish).range = G.range
    rw [Submodule.range_liftQ]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro y ⟨x, rfl⟩
      exact ⟨⟨x, T.span_mono_stage hnm x.property⟩, rfl⟩
    · rw [LinearMap.range_domRestrict, Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      intro x hx
      exact Submodule.subset_span ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
  have htarget : Module.length S G.range ≤ Module.length S (S ⊗[R] (X₀ ⧸ F.ker)) := by
    rw [← hB]
    exact Module.length_le_of_surjective B.rangeRestrict B.surjective_rangeRestrict
  have hF : F.range = Submodule.span R (s.image q : Set N) := by
    rw [LinearMap.range_domRestrict, Submodule.map_span]
    simp
  have hquot : Module.length R (X₀ ⧸ F.ker) =
      Module.length R (Submodule.span R (s.image q : Set N)) := by
    rw [F.quotKerEquivRange.length_eq, hF]
  let ι : U →ₗ[S] X₁ := Submodule.inclusion hu
  have he : Function.Exact ι G.rangeRestrict := by
    rw [LinearMap.exact_iff, Submodule.range_inclusion, LinearMap.ker_rangeRestrict]
    ext x
    simp [G, LinearMap.mem_ker]
  have hadd : Module.length S X₁ = Module.length S U + Module.length S G.range :=
    Module.length_eq_add_of_exact ι G.rangeRestrict (Submodule.inclusion_injective hu)
      G.surjective_rangeRestrict he
  have hlen : Module.length S X₁ ≤ Module.length S U +
      Module.length R (Submodule.span R (s.image q : Set N)) *
      Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
    rw [hadd]
    apply add_le_add_right
    convert htarget using 1
    rw [IsLocalRing.length_baseChange, hquot]
  have hh := mul_le_mul_right (ENat.toENNReal_mono hlen) (T.weight m)
  rw [ENat.toENNReal_add, ENat.toENNReal_mul, mul_add] at hh
  have hw : T.weight m *
      (Module.length S (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))).toENNReal =
      T.weight n := T.weight_mul_fiber n m hnm
  rw [mul_left_comm (T.weight m) _ _, hw, mul_comm _ (T.weight n)] at hh
  exact hh

lemma finiteLength_le_length_of_subset (s : Finset M) (Q : Submodule L M)
    (hs : (s : Set M) ⊆ Q) : T.finiteLength s ≤ T.length Q := by
  let t : Finset Q := s.attach.image (fun x : {x // x ∈ s} => (⟨x.1, hs x.2⟩ : Q))
  have ht : t.image Q.subtype = s := by
    ext x
    simp only [t, Finset.mem_image, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact z.property
    · intro hx
      exact ⟨⟨x, hs hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  rw [← ht, T.finiteLength_image_eq Q.subtype Q.subtype_injective]
  exact T.finiteLength_le_length t

 
lemma finiteLength_le_length_kernel_add_stage (q : M →ₗ[L] N) (s : Finset M) (n : ℕ) :
    T.finiteLength s ≤ T.length q.ker + T.stage (s.image q) n := by
  have hfg : (Submodule.span (T.ring n) (s : Set M) ⊓
      (q.restrictScalars (T.ring n)).ker).FG :=
    (Submodule.fg_span s.finite_toSet).of_le inf_le_left
  obtain ⟨k, hk⟩ := hfg
  have hf : T.finiteLength s ≤ T.finiteLength k + T.stage (s.image q) n := by
    change T.finiteLength s ≤ (⨅ m, T.stage k m) + T.stage (s.image q) n
    rw [ENNReal.iInf_add]
    apply le_iInf
    intro m
    calc
      T.finiteLength s ≤ T.stage s (max n m) := T.finiteLength_le_stage _ _
      _ ≤ T.stage k (max n m) + T.stage (s.image q) n :=
        T.stage_le_add_kernel q s k (le_max_left n m) hk
      _ ≤ T.stage k m + T.stage (s.image q) n :=
        add_le_add_left (T.stage_antitone k (le_max_right n m)) _
  have hker : T.finiteLength k ≤ T.length q.ker := by
    apply T.finiteLength_le_length_of_subset k q.ker
    intro x hx
    have hx' := Submodule.subset_span (R := T.ring n) (s := (k : Set M)) hx
    rw [hk] at hx'
    exact hx'.2
  exact hf.trans (add_le_add_left hker _)

lemma length_le_kernel_add (q : M →ₗ[L] N) : T.length M ≤ T.length q.ker + T.length N := by
  apply iSup_le
  intro s
  have hs : T.finiteLength s ≤ T.length q.ker + T.finiteLength (s.image q) := by
    change T.finiteLength s ≤ T.length q.ker + (⨅ n, T.stage (s.image q) n)
    rw [ENNReal.add_iInf]
    exact le_iInf fun n => T.finiteLength_le_length_kernel_add_stage q s n
  exact hs.trans (add_le_add_right (T.finiteLength_le_length _) _)

 
theorem length_eq_kernel_add (q : M →ₗ[L] N) (hq : Function.Surjective q) :
    T.length M = T.length q.ker + T.length N := by
  apply le_antisymm (T.length_le_kernel_add q)
  exact T.length_add_le q.ker.subtype q q.ker.subtype_injective hq (fun x => x.property)

lemma length_eq_add_of_exact (f : P →ₗ[L] M) (q : M →ₗ[L] N)
    (hf : Function.Injective f) (hq : Function.Surjective q) (he : Function.Exact f q) :
    T.length M = T.length P + T.length N := by
  rw [T.length_eq_kernel_add q hq, LinearMap.exact_iff.mp he]
  congr 1
  exact (T.length_eq_of_equiv (LinearEquiv.ofInjective f hf)).symm

lemma length_prod : T.length (M × N) = T.length M + T.length N := by
  apply T.length_eq_add_of_exact (LinearMap.inl L M N) (LinearMap.snd L M N)
  · exact fun x y h => congrArg Prod.fst h
  · exact fun y => ⟨(0, y), rfl⟩
  · rw [LinearMap.exact_iff]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.snd_apply, LinearMap.mem_range,
      LinearMap.inl_apply]
    constructor
    · intro h
      exact ⟨x.1, Prod.ext rfl h.symm⟩
    · rintro ⟨y, rfl⟩
      rfl

lemma length_sup_le (U V : Submodule L M) :
    T.length (U ⊔ V : Submodule L M) ≤ T.length U + T.length V := by
  let f : U × V →ₗ[L] M := U.subtype.comp (LinearMap.fst L U V) +
    V.subtype.comp (LinearMap.snd L U V)
  have hf : f.range = U ⊔ V := by
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_sup]
    constructor
    · rintro ⟨⟨u, v⟩, rfl⟩
      exact ⟨u, u.property, v, v.property, rfl⟩
    · rintro ⟨u, hu, v, hv, rfl⟩
      exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  rw [← hf, ← T.length_prod]
  exact T.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict

lemma finite_subset_directed {ι : Type*} [Nonempty ι]
    (U : ι → Submodule L M) (hd : Directed (· ≤ ·) U)
    (hc : ∀ x : M, ∃ i, x ∈ U i) (s : Finset M) :
    ∃ i, (s : Set M) ⊆ U i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := hc a
    obtain ⟨k, hik, hjk⟩ := hd i j
    refine ⟨k, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hjk hj
    · exact hik (hi hx)

 
lemma length_eq_iSup_of_directed {ι : Type*} [Nonempty ι]
    (U : ι → Submodule L M) (hd : Directed (· ≤ ·) U)
    (hc : ∀ x : M, ∃ i, x ∈ U i) :
    T.length M = ⨆ i, T.length (U i) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    obtain ⟨i, hi⟩ := finite_subset_directed U hd hc s
    exact le_iSup_of_le i (T.finiteLength_le_length_of_subset s (U i) hi)
  · exact iSup_le fun i => T.length_le_of_injective (U i).subtype (U i).subtype_injective

lemma length_range_le (f : M →ₗ[L] N) : T.length f.range ≤ T.length M :=
  T.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict

lemma length_directed_iSup {ι : Type*} [Nonempty ι]
    (U : ι → Submodule L M) (hd : Directed (· ≤ ·) U) :
    T.length (⨆ i, U i : Submodule L M) = ⨆ i, T.length (U i) := by
  let W := ⨆ i, U i
  let V := fun i => (U i).comap W.subtype
  have hd' : Directed (· ≤ ·) V := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, Submodule.comap_mono hik, Submodule.comap_mono hjk⟩
  have hc : ∀ x : W, ∃ i, x ∈ V i := by
    intro x
    exact (Submodule.mem_iSup_of_directed U hd).mp x.property
  rw [T.length_eq_iSup_of_directed V hd' hc]
  apply iSup_congr
  intro i
  exact T.length_eq_of_equiv (Submodule.comapSubtypeEquivOfLe (le_iSup U i))

lemma length_bot : T.length (⊥ : Submodule L M) = 0 := T.length_zero

lemma length_top : T.length (⊤ : Submodule L M) = T.length M :=
  T.length_eq_of_equiv Submodule.topEquiv

 
theorem length_iSup_eq_zero {ι : Type*} (U : ι → Submodule L M)
    (hU : ∀ i, T.length (U i) = 0) : T.length (⨆ i, U i : Submodule L M) = 0 := by
  let V : Finset ι → Submodule L M := fun s => s.sup U
  have hd : Directed (· ≤ ·) V := fun s t =>
    ⟨s ∪ t, Finset.sup_mono Finset.subset_union_left,
      Finset.sup_mono Finset.subset_union_right⟩
  have hz : ∀ s, T.length (V s) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact T.length_bot
    | @insert a s _ ih =>
      change T.length ((insert a s).sup U : Submodule L M) = 0
      rw [Finset.sup_insert]
      apply le_antisymm _ bot_le
      calc
        T.length (U a ⊔ s.sup U : Submodule L M) ≤
            T.length (U a) + T.length (s.sup U : Submodule L M) := T.length_sup_le _ _
        _ = 0 := by rw [hU a, show T.length (s.sup U : Submodule L M) = 0 from ih, add_zero]
  have heq : (⨆ s, V s) = ⨆ i, U i := by
    apply le_antisymm
    · exact iSup_le fun s => Finset.sup_le fun i _ => le_iSup U i
    · refine iSup_le fun i => ?_
      have hi : V {i} = U i := by simp [V]
      rw [← hi]
      exact le_iSup V {i}
  rw [← heq, T.length_directed_iSup V hd]
  simp only [hz, iSup_const]

 
theorem length_directSum_eq_zero {ι : Type*}
    (G : ι → Type*) [∀ i, AddCommGroup (G i)] [∀ i, Module L (G i)]
    (hG : ∀ i, T.length (G i) = 0) : T.length (⨁ i, G i) = 0 := by
  let U : ι → Submodule L (⨁ i, G i) := fun i => (DirectSum.lof L ι G i).range
  have hU : ∀ i, T.length (U i) = 0 := by
    intro i
    apply le_antisymm _ bot_le
    exact (T.length_range_le (DirectSum.lof L ι G i)).trans_eq (hG i)
  have htop : (⨆ i, U i) = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of i x => exact Submodule.mem_iSup_of_mem i ⟨x, rfl⟩
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have hh := T.length_iSup_eq_zero U hU
  rw [htop, T.length_top] at hh
  exact hh

 

theorem length_directLimit_eq_zero_of_tendsto
    (G : ℕ → Type*) [∀ i, AddCommGroup (G i)] [∀ i, Module L (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[L] G j)
    (h : Filter.Tendsto (fun i => T.length (G i)) Filter.atTop (nhds 0)) :
    T.length (Module.DirectLimit G f) = 0 := by
  let φ := Module.DirectLimit.of L ℕ G f
  have hm : Monotone (fun i => (φ i).range) := by
    intro i j hij y hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨f i j hij x, Module.DirectLimit.of_f⟩
  have hc : ∀ y : Module.DirectLimit G f, ∃ i, y ∈ (φ i).range := by
    intro y
    obtain ⟨i, x, hx⟩ := Module.DirectLimit.exists_of y
    exact ⟨i, x, hx⟩
  rw [T.length_eq_iSup_of_directed (fun i => (φ i).range) hm.directed_le hc]
  apply le_antisymm _ bot_le
  apply iSup_le
  intro i
  apply ge_of_tendsto h
  filter_upwards [Filter.eventually_ge_atTop i] with j hij
  exact (T.length_le_of_injective (Submodule.inclusion (hm hij))
    (Submodule.inclusion_injective (hm hij))).trans (T.length_range_le (φ j))

end Tower
end Lech.NormalizedLength
end
end

end OAI
