import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.SimpleModules
import OAI.RepresentationTheory.RestrictedTilting.BinarySequences

namespace OAI

/-! Highest weights, irreducible representations and bounded-weight tilting. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

noncomputable def steinbergStepIso (m : ℕ) :
    costandard k (p-1) ⊗ (frobeniusTwist k p).obj (steinberg k p m) ≅
      steinberg k p (m+1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hm : 0 < p^m := pow_pos hp m
  have he : p-1+p*(p^m-1) = p^(m+1)-1 := by
    rw [pow_succ]
    have hpM : 0 < p^m*p := mul_pos hm hp
    nlinarith [Nat.sub_add_cancel hp, Nat.sub_add_cancel hm, Nat.sub_add_cancel hpM]
  exact frobeniusCostandardIso k p (p^m-1) ≪≫
    eqToIso (congrArg (costandard k) he)

omit [Infinite k] in
noncomputable def frobeniusTensorIso (A B : FDRep k (SL2 k)) :
    (frobeniusTwist k p).obj (A ⊗ B) ≅
      (frobeniusTwist k p).obj A ⊗ (frobeniusTwist k p).obj B := Iso.refl _

 

theorem steinberg_tensor_simple_tilting (m h : ℕ) (hh : h < p^(m+1)) :
    IsTilting k (steinberg k p m ⊗ simpleSL2 k h) := by
  induction m generalizing h with
  | zero =>
    have hh' : h < p := by simpa using hh
    obtain ⟨e⟩ := simpleSL2_eq_costandard_of_choose k h
      (fun i => choose_cast_ne_zero_of_lt_char k p hh' (Nat.le_of_lt_succ i.isLt))
    exact (steinberg_tilting k p 0).tensor k ((small_costandard_tilting k p h hh').of_iso k e.symm)
  | succ m ih =>
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have ha : h%p < p := Nat.mod_lt _ hp
    have hb : h/p < p^(m+1) := by
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      simpa only [pow_succ] using hh
    have ht := (ih (h/p) hb).steinberg_frobenius k p
    have hS : IsTilting k (costandard k (h%p) ⊗
        (costandard k (p-1) ⊗
          ((frobeniusTwist k p).obj (steinberg k p m) ⊗
            (frobeniusTwist k p).obj (simpleSL2 k (h/p))))) :=
      (small_costandard_tilting k p (h%p) ha).tensor k
        (ht.of_iso k (tensorIso (Iso.refl _) (frobeniusTensorIso k p _ _)))
    let A := costandard k (h%p)
    let B := costandard k (p-1)
    let C := (frobeniusTwist k p).obj (steinberg k p m)
    let D := (frobeniusTwist k p).obj (simpleSL2 k (h/p))
    let swap : (B ⊗ A) ⊗ (C ⊗ D) ≅ (B ⊗ C) ⊗ (A ⊗ D) :=
      { hom := tensorμ B A C D
        inv := tensorδ B A C D
        hom_inv_id := tensorμ_tensorδ B A C D
        inv_hom_id := tensorδ_tensorμ B A C D }
    let eL : A ⊗ D ≅ simpleSL2 k h :=
      simpleDigitIso k p (h%p) (h/p) ha ≪≫
        eqToIso (congrArg (simpleSL2 k) (Nat.mod_add_div h p))
    let e : A ⊗ (B ⊗ (C ⊗ D)) ≅ steinberg k p (m+1) ⊗ simpleSL2 k h :=
      (α_ A B (C ⊗ D)).symm ≪≫ tensorIso (β_ A B) (Iso.refl _) ≪≫ swap ≪≫
        tensorIso (steinbergStepIso k p m) eL
    exact hS.of_iso k e
end

section
universe u
variable (k : Type u) [Field k]
noncomputable def weylReflection : SL2 k :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

lemma diagonalTorus_weylReflection (a : kˣ) :
    diagonalTorus k a * weylReflection k = weylReflection k * diagonalTorus k a⁻¹ := by
  apply Subtype.ext
  change !![(a : k),0;0,(↑a⁻¹ : k)] * !![0,-1;1,0] =
    !![0,-1;1,0] * !![(↑a⁻¹ : k),0;0,(↑(a⁻¹)⁻¹ : k)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma reflected_weight {V : Type*} [AddCommGroup V] [Module k V]
    (σ : Representation k (SL2 k) V) (n : ℤ) (v : V)
    (hv : ∀ a : kˣ, σ (diagonalTorus k a) v = integerCharacter k n a • v) :
    ∀ a : kˣ, σ (diagonalTorus k a) (σ (weylReflection k) v) =
      integerCharacter k (-n) a • σ (weylReflection k) v := by
  intro a
  rw [← Module.End.mul_apply, ← map_mul, diagonalTorus_weylReflection, map_mul,
    Module.End.mul_apply, hv, map_smul]
  congr 1
  simp [integerCharacter, zpow_neg]

lemma weights_between_of_upper {V : Type*} [AddCommGroup V] [Module k V]
    (σ : Representation k (SL2 k) V) (d : ℤ)
    (hσ : ∀ (n : ℤ), d < n → ∀ v : V,
      (∀ a, σ (diagonalTorus k a) v = integerCharacter k n a • v) → v = 0) :
    HasWeightsBetween σ (-d) d := by
  intro n v hn hv
  rcases hn with hn | hn
  · have hz := hσ (-n) (by omega) (σ (weylReflection k) v) (reflected_weight k σ n v hv)
    exact (σ.apply_bijective (weylReflection k)).1 (hz.trans (map_zero _).symm)
  · exact hσ n hn v hv

end

section
universe u
variable (k : Type u) [Field k] [Infinite k]

lemma integer_coefficient_eigen {M : Type u} [AddCommGroup M] [Module k M]
    (ρ : Representation k (SL2 k) M) (v : M) (c : ℤ →₀ M)
    (hc : ∀ a, ρ (diagonalTorus k a) v = c.sum (fun n x => integerCharacter k n a • x))
    (n : ℤ) (a : kˣ) :
    ρ (diagonalTorus k a) (c n) = integerCharacter k n a • c n := by
  let e : ℤ ↪ (kˣ →* k) := ⟨integerCharacter k, integerCharacter_injective k⟩
  have he : ∀ a, (ρ.comp (diagonalTorus k)) a v =
      (c.embDomain e).sum (fun χ x => χ a • x) := by
    intro a
    rw [Finsupp.sum_embDomain]
    exact hc a
  have h := character_coefficient_eigen (ρ.comp (diagonalTorus k)) v
    (c.embDomain e) he (e n) a
  rw [Finsupp.embDomain_apply_self] at h
  exact h

 

lemma exists_highest_in_bound {M : Type u} [AddCommGroup M] [Module k M]
    [Module.Finite k M] [Nontrivial M] (ρ : Representation k (SL2 k) M)
    (hρ : IsRational k ρ) (d : ℕ) (hd : HasWeightsBetween ρ (-(d : ℤ)) d) :
    ∃ n : ℕ, n ≤ d ∧ HasWeightsBetween ρ (-(n : ℤ)) n ∧
      ∃ v : M, v ≠ 0 ∧ ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v := by
  classical
  let S := (Finset.Icc (-(d : ℤ)) d).filter (fun n =>
    ∃ v : M, v ≠ 0 ∧ ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v)
  have hmem {n : ℤ} {v : M} (hv : v ≠ 0)
      (hw : ∀ a, ρ (diagonalTorus k a) v = integerCharacter k n a • v) : n ∈ S := by
    have hn : -(d : ℤ) ≤ n ∧ n ≤ d := by
      constructor <;> by_contra h
      · exact hv (hd n v (Or.inl (lt_of_not_ge h)) hw)
      · exact hv (hd n v (Or.inr (lt_of_not_ge h)) hw)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hn, v, hv, hw⟩
  have hS : S.Nonempty := by
    obtain ⟨v,hv⟩ := exists_ne (0 : M)
    obtain ⟨c,hc⟩ := rational_torus_integerExpansions k ρ hρ v
    have hc0 : c ≠ 0 := by
      intro h
      have := hc 1
      simp only [h,Finsupp.sum_zero_index,map_one,Module.End.one_apply] at this
      exact hv this
    obtain ⟨n,hn⟩ := Finsupp.support_nonempty_iff.mpr hc0
    exact ⟨n,hmem (Finsupp.mem_support_iff.mp hn) (integer_coefficient_eigen k ρ v c hc n)⟩
  let m := S.max' hS
  have hm : m ∈ S := Finset.max'_mem _ _
  obtain ⟨v,hv,hw⟩ := (Finset.mem_filter.mp hm).2
  have upper : ∀ l : ℤ, m < l → ∀ w : M,
      (∀ a, ρ (diagonalTorus k a) w = integerCharacter k l a • w) → w = 0 := by
    intro l hl w hw
    by_contra h
    exact (not_lt_of_ge (Finset.le_max' _ _ (hmem h hw))) hl
  have hm0 : 0 ≤ m := by
    by_contra hn
    have hzero := upper (-m) (by omega) (ρ (weylReflection k) v)
      (reflected_weight k ρ m v hw)
    exact hv ((ρ.apply_bijective (weylReflection k)).1 (hzero.trans (map_zero _).symm))
  have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
  refine ⟨m.toNat, ?_, ?_, v,hv, ?_⟩
  · have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    omega
  · rw [he]
    exact weights_between_of_upper k ρ m upper
  · simpa only [he] using hw

omit [Infinite k] in
lemma exists_costandard_dual_embedding (A : FDRep k (SL2 k)) (n : ℕ)
    (f : Module.Dual k (MvPolynomial.homogeneousSubmodule (Fin 2) k n) →ₗ[k] A)
    (hf : ∀ g v, f (standardRepresentation k n g v) = A.ρ g (f v))
    (hfs : Function.Surjective f) :
    ∃ e : Module.Dual k A →ₗ[k] MvPolynomial.homogeneousSubmodule (Fin 2) k n,
      Function.Injective e ∧ ∀ g l, e (Representation.dual A.ρ g l) =
        ((homogeneousRepresentation n).comp (dualMatrix k)) g (e l) := by
  let H := MvPolynomial.homogeneousSubmodule (Fin 2) k n
  let e : Module.Dual k A →ₗ[k] H :=
    (Module.evalEquiv k H).symm.toLinearMap.comp f.dualMap
  have hei : Function.Injective e := (Module.evalEquiv k H).symm.injective.comp
    (LinearMap.dualMap_injective_of_surjective hfs)
  have heq (l : Module.Dual k A) : Module.Dual.eval k H (e l) = f.dualMap l :=
    (Module.evalEquiv k H).apply_symm_apply _
  have heρ : ∀ g l, e (Representation.dual A.ρ g l) =
      ((homogeneousRepresentation n).comp (dualMatrix k)) g (e l) := by
    intro g l
    apply (Module.evalEquiv k H).injective
    change Module.Dual.eval k H (e (Representation.dual A.ρ g l)) =
      Module.Dual.eval k H (((homogeneousRepresentation n).comp (dualMatrix k)) g (e l))
    rw [heq,eval_intertwines,heq]
    exact dual_intertwines k (standardRepresentation k n) A.ρ f hf g l
  exact ⟨e, hei, heρ⟩

lemma exists_socle_dual_embedding (A : FDRep k (SL2 k)) [Nontrivial A] (n : ℕ)
    (e : Module.Dual k A →ₗ[k] MvPolynomial.homogeneousSubmodule (Fin 2) k n)
    (hei : Function.Injective e)
    (heρ : ∀ g l, e (Representation.dual A.ρ g l) =
      ((homogeneousRepresentation n).comp (dualMatrix k)) g (e l)) :
    ∃ s : (costandardSocle k n).toSubmodule →ₗ[k] Module.Dual k A,
      Function.Injective s ∧ ∀ g x, s ((costandardSocle k n).toRepresentation g x) =
        Representation.dual A.ρ g (s x) := by
  let e' := e.intertwiningMap_of_isIntertwiningMap (Representation.dual A.ρ)
    ((homogeneousRepresentation n).comp (dualMatrix k)) heρ
  have her : e'.range ≠ ⊥ := by
    intro h
    obtain ⟨l,hl⟩ := exists_ne (0 : Module.Dual k A)
    have hz : e l = 0 := by
      have hm : e l ∈ e'.range := ⟨l,rfl⟩
      rw [h] at hm
      exact hm
    exact hl (hei (hz.trans (map_zero e).symm))
  have hle := costandardSocle_le_of_ne_bot k n e'.range her
  let E := LinearEquiv.ofInjective e hei
  let inc : (costandardSocle k n).toSubmodule →ₗ[k] LinearMap.range e :=
    Submodule.inclusion hle
  let s : (costandardSocle k n).toSubmodule →ₗ[k] Module.Dual k A :=
    E.symm.toLinearMap.comp inc
  have hs (x : (costandardSocle k n).toSubmodule) : e (s x) = x.val := by
    have h := E.apply_symm_apply (inc x)
    exact congrArg Subtype.val h
  have hsi : Function.Injective s := E.symm.injective.comp (Submodule.inclusion_injective hle)
  have hsρ : ∀ g x, s ((costandardSocle k n).toRepresentation g x) =
      Representation.dual A.ρ g (s x) := by
    intro g x
    apply hei
    rw [hs,heρ,hs]
    rfl
  exact ⟨s, hsi, hsρ⟩

omit [Infinite k] in
lemma dual_eval_surjective {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [Module.Finite k W]
    (s : V →ₗ[k] Module.Dual k W) (hs : Function.Injective s) :
    Function.Surjective (s.dualMap.comp (Module.Dual.eval k W)) :=
  (LinearMap.dualMap_surjective_of_injective hs).comp (Module.evalEquiv k W).surjective

lemma exists_simple_dual_surjection (A : FDRep k (SL2 k)) [Nontrivial A] (n : ℕ)
    (e : Module.Dual k A →ₗ[k] MvPolynomial.homogeneousSubmodule (Fin 2) k n)
    (hei : Function.Injective e)
    (heρ : ∀ g l, e (Representation.dual A.ρ g l) =
      ((homogeneousRepresentation n).comp (dualMatrix k)) g (e l)) :
    ∃ r : A →ₗ[k] Module.Dual k (costandardSocle k n).toSubmodule,
      Function.Surjective r ∧ ∀ g x, r (A.ρ g x) =
        Representation.dual (costandardSocle k n).toRepresentation g (r x) := by
  obtain ⟨s,hsi,hsρ⟩ := exists_socle_dual_embedding k A n e hei heρ
  refine ⟨s.dualMap.comp (Module.Dual.eval k A),
    dual_eval_surjective k (V := (costandardSocle k n).toSubmodule) (W := A) s hsi, ?_⟩
  intro g x
  apply LinearMap.ext
  intro y
  change s y (A.ρ g x) = s ((costandardSocle k n).toRepresentation g⁻¹ y) x
  rw [hsρ]
  change s y (A.ρ g x) = s y (A.ρ (g⁻¹)⁻¹ x)
  rw [inv_inv]

lemma irreducible_iso_simple_dual (A : FDRep k (SL2 k))
    [Representation.IsIrreducible A.ρ] (n : ℕ)
    (r : A →ₗ[k] Module.Dual k (costandardSocle k n).toSubmodule)
    (hrs : Function.Surjective r)
    (hrρ : ∀ g x, r (A.ρ g x) =
      Representation.dual (costandardSocle k n).toRepresentation g (r x)) :
    Nonempty (A ≅ (simpleSL2 k n)ᘁ) := by
  let r' := r.intertwiningMap_of_isIntertwiningMap A.ρ
    (Representation.dual (costandardSocle k n).toRepresentation) hrρ
  let : Nontrivial (costandardSocle k n).toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr (by
      intro hz
      apply costandardSocle_ne_bot k n
      apply Subrepresentation.ext
      exact hz)
  let : Module.Free k (costandardSocle k n).toSubmodule := Module.Free.of_divisionRing k (costandardSocle k n).toSubmodule
  let : Nontrivial (Module.Dual k (costandardSocle k n).toSubmodule) :=
    (Module.nontrivial_dual_iff k).mpr inferInstance
  have hri : Function.Injective r := by
    rcases Representation.IsIrreducible.injective_or_eq_zero r' with h | h
    · exact h
    · obtain ⟨l,hl⟩ := exists_ne (0 : Module.Dual k (costandardSocle k n).toSubmodule)
      obtain ⟨x,hx⟩ := hrs l
      have hz : r x = 0 := congrArg (fun g => g x) h
      exact (hl (hx.symm.trans hz)).elim
  let q : A ⟶ (simpleSL2 k n)ᘁ := fdrepHom k r (by
    intro g x
    rw [fdrep_dual_repr]
    exact hrρ g x)
  have : IsIso q := fdrepHom_isIso_of_bijective k q ⟨hri,hrs⟩
  exact ⟨asIso q⟩

 

theorem irreducible_eq_simple_dual (A : FDRep k (SL2 k))
    (hA : IsRational k A.ρ) [Representation.IsIrreducible A.ρ]
    (d : ℕ) (hd : HasWeightsBetween A.ρ (-(d : ℤ)) d) :
    ∃ n : ℕ, n ≤ d ∧ Nonempty (A ≅ (simpleSL2 k n)ᘁ) := by
  let : Nontrivial (Representation.asModule A.ρ) :=
    IsSimpleModule.nontrivial (MonoidAlgebra k (SL2 k)) (Representation.asModule A.ρ)
  let : Nontrivial A := (Representation.asModuleEquiv A.ρ).symm.toEquiv.nontrivial
  obtain ⟨n,hn,hb,v,hv,hw⟩ := exists_highest_in_bound k A.ρ hA d hd
  obtain ⟨f,hfv,hf⟩ := exists_standard_lift k A.ρ hA n hb v hw
  let f' := f.intertwiningMap_of_isIntertwiningMap (standardRepresentation k n) A.ρ hf
  have hfs : Function.Surjective f := by
    rcases Representation.IsIrreducible.surjective_or_eq_zero f' with h | h
    · exact h
    · have hz : f (standardHighest k n) = 0 := congrArg (fun g => g (standardHighest k n)) h
      exact (hv (hfv.symm.trans hz)).elim
  obtain ⟨e,hei,heρ⟩ := exists_costandard_dual_embedding k A n f hf hfs
  obtain ⟨r,hrs,hrρ⟩ := exists_simple_dual_surjection k A n e hei heρ
  exact ⟨n,hn,irreducible_iso_simple_dual k A n r hrs hrρ⟩
end

section
universe u
variable (k : Type u) [Field k]

lemma hasWeightsBetween_of_injective {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (ρ : Representation k (SL2 k) M) (σ : Representation k (SL2 k) N)
    (f : M →ₗ[k] N) (hf : Function.Injective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) (lo hi : ℤ)
    (hσ : HasWeightsBetween σ lo hi) : HasWeightsBetween ρ lo hi := by
  intro n v hn hv
  apply hf
  rw [map_zero]
  apply hσ n (f v) hn
  intro a
  rw [← he,hv,map_smul]

lemma hasWeightsBetween_of_surjective [Infinite k]
    {M N : Type u} [AddCommGroup M] [Module k M] [Module.Finite k M]
    [AddCommGroup N] [Module k N]
    (ρ : Representation k (SL2 k) M) (σ : Representation k (SL2 k) N)
    (hρ : IsRational k ρ) (f : M →ₗ[k] N) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) (lo hi : ℤ)
    (hb : HasWeightsBetween ρ lo hi) : HasWeightsBetween σ lo hi := by
  intro n w hn hw
  obtain ⟨v,hv,hvw⟩ := rational_weight_lift k ρ σ hρ f he hf (integerCharacter k n) w hw
  rw [← hv,hb n v hn hvw,map_zero]

lemma fdrep_isZero_of_subsingleton {G : Type u} [Monoid G]
    (A : FDRep k G) [Subsingleton A] : IsZero A := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply fdrep_hom_ext k
  intro x
  exact Subsingleton.elim _ _

lemma IsTilting.of_subsingleton (A : FDRep k (SL2 k)) [Subsingleton A]
    (hA : IsRational k A.ρ) : IsTilting k A := by
  refine ⟨hA, .zero _ (fdrep_isZero_of_subsingleton k A), .zero _ ?_⟩
  let : Subsingleton (Aᘁ : FDRep k (SL2 k)) := by
    change Subsingleton (Module.Dual k A)
    infer_instance
  exact fdrep_isZero_of_subsingleton k Aᘁ

lemma IsTilting.extension {A B C : FDRep k (SL2 k)}
    (hA : IsTilting k A) (hC : IsTilting k C) (hB : IsRational k B.ρ)
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) : IsTilting k B := by
  refine ⟨hB,hA.2.1.extension k hC.2.1 f g w hS, ?_⟩
  exact hC.2.2.extension k hA.2.2 (fdrepDualMap k g) (fdrepDualMap k f)
    (fdrepDualMap_zero_comp k f g w) (fdrep_dual_shortExact k f g w hS)

end

section
universe u
variable (k : Type u) [Field k]
variable {G : Type u} [Monoid G]

lemma exists_proper_subrepresentation (A : FDRep k G) [Nontrivial A]
    (h : ¬ Representation.IsIrreducible A.ρ) :
    ∃ S : Subrepresentation A.ρ, S ≠ ⊥ ∧ S ≠ ⊤ := by
  classical
  let : Nontrivial (Subrepresentation A.ρ) := ⟨⟨⊥, ⊤, fun he =>
    bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩⟩
  by_contra hn
  apply h
  refine { eq_bot_or_eq_top := ?_ }
  intro S
  by_cases hs : S = ⊥
  · exact Or.inl hs
  · exact Or.inr (by by_contra ht; exact hn ⟨S,hs,ht⟩)

 

lemma fdrep_proper_shortExact (A : FDRep k G) (S : Subrepresentation A.ρ)
    (hb : S ≠ ⊥) (ht : S ≠ ⊤) :
    ∃ (L N : FDRep k G) (f : L ⟶ A) (g : A ⟶ N) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧
      Module.finrank k L < Module.finrank k A ∧
      Module.finrank k N < Module.finrank k A := by
  let L := FDRep.of S.toRepresentation
  let N := FDRep.of (Representation.quotient A.ρ S.toSubmodule S.apply_mem_toSubmodule)
  let f : L ⟶ A := fdrepHom k S.toSubmodule.subtype (by intros; rfl)
  let g : A ⟶ N := fdrepHom k S.toSubmodule.mkQ (by intros; rfl)
  have w : f ≫ g = 0 := by
    apply fdrep_hom_ext k
    intro x
    exact (Submodule.Quotient.mk_eq_zero _).mpr x.property
  have hb' : S.toSubmodule ≠ ⊥ := fun h => hb (Subrepresentation.ext h)
  have ht' : S.toSubmodule ≠ ⊤ := fun h => ht (Subrepresentation.ext h)
  have hdim := S.toSubmodule.finrank_quotient_add_finrank
  have hp : 0 < Module.finrank k S.toSubmodule :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hb')
  refine ⟨L,N,f,g,w,fdrep_shortExact k _ Subtype.val_injective
    S.toSubmodule.mkQ_surjective ?_, Submodule.finrank_lt ht', ?_⟩
  · change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
    simp
  · change Module.finrank k (A ⧸ S.toSubmodule) < Module.finrank k A
    omega

 

theorem fdrep_induction (P : FDRep k G → Prop)
    (hz : ∀ A : FDRep k G, (Subsingleton A) → P A)
    (hi : ∀ A, Representation.IsIrreducible A.ρ → P A)
    (he : ∀ (A B C : FDRep k G) (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact → P A → P C → P B) (A : FDRep k G) : P A := by
  classical
  generalize hn : Module.finrank k A = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hzA : Subsingleton A
    · exact hz A hzA
    let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hzA
    by_cases hiA : Representation.IsIrreducible A.ρ
    · exact hi A hiA
    obtain ⟨S,hb,ht⟩ := exists_proper_subrepresentation k A hiA
    obtain ⟨L,N,f,g,w,hS,hL,hN⟩ := fdrep_proper_shortExact k A S hb ht
    apply he L A N f g w hS
    · exact ih (Module.finrank k L) (hn ▸ hL) L rfl
    · exact ih (Module.finrank k N) (hn ▸ hN) N rfl
end

universe u
variable (k : Type u) [Field k] [Infinite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

lemma steinberg_tensor_simple_dual_tilting (m n : ℕ) (hn : n < p^(m+1)) :
    IsTilting k (steinberg k p m ⊗ (simpleSL2 k n)ᘁ) := by
  obtain ⟨eS⟩ := steinberg_self_dual k p m
  let e : (steinberg k p m ⊗ simpleSL2 k n)ᘁ ≅
      steinberg k p m ⊗ (simpleSL2 k n)ᘁ :=
    rightDualTensorIso _ _ ≪≫ tensorIso (Iso.refl _) eS ≪≫ β_ _ _
  exact ((steinberg_tensor_simple_tilting k p m n hn).dual k).of_iso k e

lemma steinberg_tensor_irreducible_tilting (m d : ℕ) (hd : d < p^(m+1))
    (A : FDRep k (SL2 k)) [Representation.IsIrreducible A.ρ]
    (hA : IsRational k A.ρ) (hb : HasWeightsBetween A.ρ (-(d : ℤ)) d) :
    IsTilting k (steinberg k p m ⊗ A) := by
  obtain ⟨n,hn,⟨e⟩⟩ := irreducible_eq_simple_dual k A hA d hb
  exact (steinberg_tensor_simple_dual_tilting k p m n (hn.trans_lt hd)).of_iso k
    (tensorIso (Iso.refl _) e.symm)

 

theorem bounded_weights_tilting (m d : ℕ) (hd : d < p^(m+1))
    (A : FDRep k (SL2 k)) (hA : IsRational k A.ρ)
    (hb : HasWeightsBetween A.ρ (-(d : ℤ)) d) :
    IsTilting k (steinberg k p m ⊗ A) := by
  let P : FDRep k (SL2 k) → Prop := fun B => IsRational k B.ρ →
    HasWeightsBetween B.ρ (-(d : ℤ)) d → IsTilting k (steinberg k p m ⊗ B)
  apply fdrep_induction k P ?_ ?_ ?_ A hA hb
  · intro B hB hr _
    let : Subsingleton B := hB
    let : Subsingleton (steinberg k p m ⊗ B : FDRep k (SL2 k)) := by
      change Subsingleton (TensorProduct k (steinberg k p m) B)
      infer_instance
    exact IsTilting.of_subsingleton k (steinberg k p m ⊗ B)
      (IsRational.tensor k (steinberg k p m).ρ B.ρ (steinberg_tilting k p m).1 hr)
  · intro B hi hr hw
    let : Representation.IsIrreducible B.ρ := hi
    exact steinberg_tensor_irreducible_tilting k p m d hd B hr hw
  · intro L B N f g w hS hL hN hr hw
    have := hS.mono_f
    have := hS.epi_g
    have hrL := IsRational.of_injective k L.ρ B.ρ (fdrepLinear k f)
      (fdrep_injective k f) (fdrepLinear_comm k f) hr
    have hrN := IsRational.of_surjective k B.ρ N.ρ (fdrepLinear k g)
      (fdrep_surjective k g) (fdrepLinear_comm k g) hr
    have hwL := hasWeightsBetween_of_injective k L.ρ B.ρ (fdrepLinear k f)
      (fdrep_injective k f) (fdrepLinear_comm k f) _ _ hw
    have hwN := hasWeightsBetween_of_surjective k B.ρ N.ρ hr (fdrepLinear k g)
      (fdrep_surjective k g) (fdrepLinear_comm k g) _ _ hw
    let F := tensorLeft (steinberg k p m)
    let := tensorLeft_preservesFiniteLimits (steinberg k p m)
    let := tensorLeft_preservesFiniteColimits (steinberg k p m)
    have hT := hS.map_of_exact F
    exact (hL hrL hwL).extension k (hN hrN hwN)
      (IsRational.tensor k (steinberg k p m).ρ B.ρ (steinberg_tilting k p m).1 hr) _ _ _ hT
end FiberFunctorProof
end

end OAI
