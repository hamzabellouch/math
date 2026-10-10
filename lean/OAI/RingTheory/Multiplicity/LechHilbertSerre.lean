import Mathlib
import OAI.RingTheory.Multiplicity.SeparableOrderNormalizedLength

namespace OAI

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
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech
open DirectSum
universe u v w
variable (K : Type u) [Field K]

theorem hilbertSerre (n : ℕ) (S : Type v) (M : Type w)
    [CommRing S] [Algebra K S] [IsNoetherianRing S]
    [AddCommGroup M] [Module S M] [Module K M] [IsScalarTower K S M]
    [Module.Finite S M]
    (x : Fin n → S) (hx : Algebra.adjoin K (Set.range x) = ⊤)
    (G : ℕ → Submodule K M) [Decomposition G]
    [∀ i, Module.Finite K (G i)]
    (hG : ∀ j i (m : M), m ∈ G i → x j • m ∈ G (i + 1)) :
    EventuallyPolynomial (fun i => (Module.finrank K (G i) : ℚ)) := by
  induction n generalizing S M with
  | zero =>
      have hx0 : Algebra.adjoin K (∅ : Set S) = ⊤ := by simpa using hx
      let : Module.Finite K M := finite_of_no_generators hx0
      refine ⟨0, ?_⟩
      filter_upwards [Grading.eventually_eq_bot G] with i hi
      rw [hi]
      simp
  | succ n ih =>
      let fS : M →ₗ[S] M := LinearMap.lsmul S M (x 0)
      let f : M →ₗ[K] M := fS.restrictScalars K
      have hf : ∀ i, (G i).map f ≤ G (i + 1) := by
        rintro i _ ⟨m, hm, rfl⟩
        exact hG 0 i m hm
      let P : Submodule S M := fS.ker
      let Q : Submodule S M := fS.range
      let V := M ⧸ Q
      let q : M →ₗ[K] V := Q.mkQ.restrictScalars K
      let S' := S ⧸ Ideal.span {x 0}
      let x' : Fin n → S' := fun j => Ideal.Quotient.mk _ (x j.succ)
      have hx' : Algebra.adjoin K (Set.range x') = ⊤ := quotient_generators x hx
      let hPkill : Module.IsTorsionBy S P (x 0) := ker_smul_killed (M := M) (x 0)
      let hVkill : Module.IsTorsionBy S V (x 0) := coker_smul_killed (M := M) (x 0)
      let : Module S' P := hPkill.module
      let : Module S' V := hVkill.module
      have : IsScalarTower K S' P := inferInstance
      have : IsScalarTower K S' V := inferInstance
      have : IsScalarTower S S' P := inferInstance
      have : IsScalarTower S S' V := inferInstance
      have : Module.Finite S' P := Module.Finite.of_restrictScalars_finite S S' P
      have : Module.Finite S' V := Module.Finite.of_restrictScalars_finite S S' V
      let GP : ℕ → Submodule K P := fun i => (G i).comap (P.subtype.restrictScalars K)
      let GV : ℕ → Submodule K V := Grading.imagePiece G q
      have hPhom : (P.restrictScalars K).IsHomogeneous G := by
        exact Grading.ker_homogeneous G G f hf
      have hQhom : q.ker.IsHomogeneous G := by
        have hker : q.ker = f.range := by
          change (Q.mkQ.restrictScalars K).ker = f.range
          rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
          rfl
        rw [hker]
        exact Grading.range_homogeneous G G f hf
      let : Decomposition GP := Grading.subDecomposition G (P.restrictScalars K) hPhom
      let : Decomposition GV := Grading.imageDecomposition G q Q.mkQ_surjective hQhom
      have (i : ℕ) : Module.Finite K (GP i) := by
        exact Module.Finite.of_injective (Grading.subPieceMap G (P.restrictScalars K) i)
          (by
            intro a b h
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z : G i => (z : M)) h)
      have (i : ℕ) : Module.Finite K (GV i) := by
        exact Module.Finite.of_surjective (Grading.pieceMap G q i)
          (Grading.pieceMap_surjective G q i)
      have hGP : ∀ j i (m : P), m ∈ GP i → x' j • m ∈ GP (i + 1) := by
        intro j i m hm
        change x j.succ • (m : M) ∈ G (i + 1)
        exact hG j.succ i m hm
      have hGV : ∀ j i (m : V), m ∈ GV i → x' j • m ∈ GV (i + 1) := by
        rintro j i _ ⟨m, hm, rfl⟩
        refine ⟨x j.succ • m, hG j.succ i m hm, ?_⟩
        exact Q.mkQ.map_smul _ _
      have hpolP := ih S' P x' hx' GP hGP
      have hpolV := ih S' V x' hx' GV hGV
      apply EventuallyPolynomial.of_recurrence hpolP hpolV
      intro i
      have hker : q.ker = f.range := by
        rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
        rfl
      have he := Grading.finrank_recurrence G f hf q hker i
      exact_mod_cast he



namespace IdealGraded

variable {A : Type*} [CommRing A]

end IdealGraded
end Lech






namespace Lech.IdealGraded
variable {R : Type*} [CommRing R] [IsNoetherianRing R]
lemma eventuallyPolynomial_piece (I : Ideal R) [I.IsMaximal] :
    Lech.EventuallyPolynomial (fun n => (Module.finrank (R ⧸ I) (Piece I n) : ℚ)) := by
  let := Ideal.Quotient.field I
  obtain ⟨n, x, hx, hxmem⟩ := exists_generators I
  have h := Lech.hilbertSerre (R ⧸ I) n (Ring I) (Ring I) x hx (grade I) (by
    intro j i m hm
    simpa only [smul_eq_mul, add_comm] using grade_mul I (hxmem j) hm)
  have he (n : ℕ) : Module.finrank (R ⧸ I) (Piece I n) =
      Module.finrank (R ⧸ I) (grade I n) := (pieceEquiv I n).finrank_eq
  simpa only [he] using h

lemma eventuallyPolynomial_length (I : Ideal R) [I.IsMaximal] :
    Lech.EventuallyPolynomial (fun n => ((Module.length R (R ⧸ I ^ n)).toNat : ℚ)) := by
  have hp := eventuallyPolynomial_piece I
  have he (N : ℕ) : ((Module.length R (R ⧸ I ^ N)).toNat : ℚ) =
      ∑ n ∈ Finset.range N, (Module.finrank (R ⧸ I) (Piece I n) : ℚ) := by
    rw [length_eq_sum]
    simp only [length_piece_eq_finrank]
    rw [← Nat.cast_sum, ENat.toNat_natCast, Nat.cast_sum]
  apply Lech.EventuallyPolynomial.of_sub_succ
  have heq : (fun N => ((Module.length R (R ⧸ I ^ (N + 1))).toNat : ℚ) -
      ((Module.length R (R ⧸ I ^ N)).toNat : ℚ)) =
      (fun N => (Module.finrank (R ⧸ I) (Piece I N) : ℚ)) := by
    funext N
    rw [he, he, Finset.sum_range_succ, add_sub_cancel_left]
  rwa [heq]
end Lech.IdealGraded


namespace Lech
open Filter Polynomial
open scoped Topology

lemma degree_le_of_nat_bound (P : ℝ[X]) (d : ℕ) (C : ℝ)
    (hb : ∀ᶠ n : ℕ in atTop, |P.eval (n : ℝ)| ≤ C * (n : ℝ) ^ d) :
    P.degree ≤ d := by
  by_contra hn
  have hd : (Polynomial.X ^ d : ℝ[X]).degree < P.degree := by
    simpa only [degree_X_pow] using lt_of_not_ge hn
  have ht := (P.abs_div_tendsto_atTop_atTop_of_degree_gt (Polynomial.X ^ d) hd
    (pow_ne_zero d X_ne_zero)).comp tendsto_natCast_atTop_atTop
  have hh : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hb, ht.eventually (eventually_gt_atTop C), eventually_gt_atTop 0]
      with n hn hlarge hnpos
    have hpos : 0 < (n : ℝ) ^ d := pow_pos (by exact_mod_cast hnpos) _
    have hle : |P.eval (n : ℝ) / (n : ℝ) ^ d| ≤ C := by
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      exact hn
    simp only [Function.comp_apply, eval_pow, eval_X] at hlarge
    exact (not_lt_of_ge hle) hlarge
  obtain ⟨n, hn⟩ := hh.exists
  exact hn

lemma exists_polynomial_div_limit (P : ℝ[X]) (d : ℕ) (hd : P.degree ≤ d) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => P.eval (n : ℝ) / (n : ℝ) ^ d) atTop (𝓝 L) := by
  have hd' : P.degree ≤ (Polynomial.X ^ d : ℝ[X]).degree := by
    simpa only [degree_X_pow] using hd
  rcases lt_or_eq_of_le hd' with hlt | heq
  · refine ⟨0, ?_⟩
    simpa only [Function.comp_def, eval_pow, eval_X] using
      (P.div_tendsto_atTop_zero_of_degree_lt (Polynomial.X ^ d) hlt).comp
        tendsto_natCast_atTop_atTop
  · refine ⟨P.leadingCoeff / (Polynomial.X ^ d : ℝ[X]).leadingCoeff, ?_⟩
    simpa only [Function.comp_def, eval_pow, eval_X] using
      (P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq (Polynomial.X ^ d) heq).comp
        tendsto_natCast_atTop_atTop

lemma exists_div_limit_of_eventually_polynomial (f : ℕ → ℕ) (d : ℕ)
    (hp : ∃ p : ℚ[X], ∀ᶠ n in atTop, (f n : ℚ) = p.eval (n : ℚ))
    (hb : ∃ C : ℕ, ∀ n, f n ≤ n ^ d * C) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ) ^ d) atTop (𝓝 L) := by
  obtain ⟨p, hp⟩ := hp
  obtain ⟨C, hC⟩ := hb
  let P := p.map (algebraMap ℚ ℝ)
  have he : ∀ᶠ n in atTop, (f n : ℝ) = P.eval (n : ℝ) := by
    filter_upwards [hp] with n hn
    have h := congrArg (algebraMap ℚ ℝ) hn
    simpa only [map_natCast, ← eval₂_at_apply, ← Polynomial.eval_map] using h
  have hbd : ∀ᶠ n : ℕ in atTop, |P.eval (n : ℝ)| ≤ (C : ℝ) * (n : ℝ) ^ d := by
    filter_upwards [he] with n hn
    rw [← hn, abs_of_nonneg (Nat.cast_nonneg _), mul_comm]
    exact_mod_cast hC n
  obtain ⟨L, hL⟩ := exists_polynomial_div_limit P d (degree_le_of_nat_bound P d C hbd)
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [he] with n hn
  rw [hn]
end Lech


namespace Lech
open Filter
open scoped Topology

theorem multiplicity_is_limit (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] :
    Tendsto (normalizedColength R) atTop (𝓝 (multiplicity R)) := by
  obtain ⟨L, hL⟩ := exists_div_limit_of_eventually_polynomial (colength R) (dimension R)
    (IdealGraded.eventuallyPolynomial_length (IsLocalRing.maximalIdeal R))
    (colength_polynomial_bound R)
  have ht : Tendsto (normalizedColength R) atTop
      (𝓝 ((Nat.factorial (dimension R) : ℝ) * L)) := by
    change Tendsto (fun N => (Nat.factorial (dimension R) : ℝ) *
      (colength R N : ℝ) / (N : ℝ) ^ dimension R) atTop
        (𝓝 ((Nat.factorial (dimension R) : ℝ) * L))
    simpa only [mul_div_assoc] using
      hL.const_mul (Nat.factorial (dimension R) : ℝ)
  have he : multiplicity R = (Nat.factorial (dimension R) : ℝ) * L := ht.limUnder_eq
  rw [he]
  exact ht
end Lech


namespace Lech.LengthHilbert
open Lech.Grading DirectSum Filter
variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
variable (G : ℕ → Submodule K M) [Decomposition G]

lemma eventually_eq_bot [Module.Finite K M] : ∀ᶠ n in atTop, G n = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := M)
  let t := s.biUnion (fun x => (decompose G x).support)
  refine Filter.eventually_atTop.mpr ⟨t.sup id + 1, fun n hn => ?_⟩
  have hp : projection G n = 0 := by
    apply (Submodule.linearMap_eq_zero_iff_of_span_eq_top _ hs).mpr
    intro x
    have hnot : n ∉ (decompose G x.val).support := by
      intro hx
      have hnt : n ∈ t := Finset.mem_biUnion.mpr ⟨x.val, x.property, hx⟩
      have ht := Finset.le_sup (f := id) hnt
      dsimp at ht
      omega
    have hz : decompose G x.val n = 0 := DFinsupp.notMem_support_iff.mp hnot
    exact congrArg (fun z : G n => (z : M)) hz
  apply eq_bot_iff.mpr
  intro x hx
  rw [Submodule.mem_bot]
  have he := DFunLike.congr_fun hp x
  simpa [proj_of_mem G hx] using he

omit [Decomposition G] in
lemma subPiece_length (P : Submodule K M) (i : ℕ) :
    Module.length K (subPiece G P i) = Module.length K (P.comap (G i).subtype) := by
  let e : subPiece G P i ≃ₗ[K] P.comap (G i).subtype :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.length_eq

variable {N : Type*} [AddCommGroup N] [Module K N]
omit [Decomposition G] in
lemma pieceMap_surjective (q : M →ₗ[K] N) (i : ℕ) :
    Function.Surjective (pieceMap G q i) := by
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

omit [Decomposition G] in
lemma pieceMap_ker (q : M →ₗ[K] N) (i : ℕ) :
    (pieceMap G q i).ker = q.ker.comap (G i).subtype := by
  ext x
  simp [LinearMap.mem_ker, Subtype.ext_iff]

lemma length_range_add_length_ker {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] (g : V →ₗ[K] W) :
    Module.length K g.range + Module.length K g.ker = Module.length K V := by
  have he := Module.length_eq_add_of_exact (LinearMap.ker g.rangeRestrict).subtype
    g.rangeRestrict (Submodule.subtype_injective _) g.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map g.rangeRestrict)
  rw [LinearMap.ker_rangeRestrict] at he
  simpa only [add_comm] using he.symm

lemma length_recurrence [IsArtinianRing K] [IsNoetherianRing K]
    [∀ i, Module.Finite K (G i)]
    (f : M →ₗ[K] M) (hf : ∀ i, (G i).map f ≤ G (i + 1))
    (q : M →ₗ[K] N) (hq : q.ker = f.range) (i : ℕ) :
    (Module.length K (G (i + 1))).toNat + (Module.length K (subPiece G f.ker i)).toNat =
      (Module.length K (G i)).toNat + (Module.length K (imagePiece G q (i + 1))).toNat := by
  have h1 := length_range_add_length_ker (step G G f hf i)
  have h2 := length_range_add_length_ker (pieceMap G q (i + 1))
  have he : Module.length K (pieceMap G q (i + 1)).range =
      Module.length K (imagePiece G q (i + 1)) := by
    rw [LinearMap.range_eq_top.mpr (pieceMap_surjective G q (i + 1))]
    simp
  have h1' := congrArg ENat.toNat h1
  have h2' := congrArg ENat.toNat h2
  rw [ENat.toNat_add Module.length_ne_top Module.length_ne_top] at h1' h2'
  rw [he, pieceMap_ker, hq, ← step_range G G f hf i] at h2'
  rw [step_ker] at h1'
  rw [subPiece_length]
  omega

end Lech.LengthHilbert


namespace Lech.LengthHilbert

variable {K S M : Type*} [CommRing K] [CommRing S] [Algebra K S]
  [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]

lemma quotient_generators {n : ℕ} (x : Fin (n + 1) → S)
    (hx : Algebra.adjoin K (Set.range x) = ⊤) :
    Algebra.adjoin K (Set.range (fun i : Fin n =>
      Ideal.Quotient.mk (Ideal.span {x 0}) (x i.succ))) = ⊤ := by
  let q := Ideal.Quotient.mkₐ K (Ideal.span {x 0})
  have he := congrArg (Subalgebra.map q) hx
  rw [AlgHom.map_adjoin, Algebra.map_top,
    (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mk_surjective)] at he
  rw [Fin.range_fin_succ, Set.image_insert_eq, ← Set.range_comp] at he
  have hzero : q (x 0) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hzero, Algebra.adjoin_insert_zero] at he
  exact he

lemma finite_of_no_generators [Module.Finite S M]
    (hx : Algebra.adjoin K (∅ : Set S) = ⊤) : Module.Finite K M := by
  have hs : Function.Surjective (algebraMap K S) := by
    apply Algebra.surjective_algebraMap_iff.mpr
    simpa only [Algebra.adjoin_empty] using hx.symm
  exact ⟨by simpa using (Module.Finite.fg_top (R := S) (M := M)).restrictScalars_of_surjective hs⟩

variable (x : S)

lemma ker_smul_killed : Module.IsTorsionBy S (LinearMap.lsmul S M x).ker x := by
  intro m
  apply Subtype.ext
  exact LinearMap.mem_ker.mp m.property

lemma coker_smul_killed : Module.IsTorsionBy S (M ⧸ (LinearMap.lsmul S M x).range) x := by
  apply (Module.isTorsionBy_quotient_iff _ _).mpr
  intro m
  exact ⟨m, rfl⟩

end Lech.LengthHilbert


namespace Lech.LengthHilbert
open DirectSum
universe u v w
variable (K : Type u) [CommRing K] [IsArtinianRing K] [IsNoetherianRing K]

theorem hilbertSerre (n : ℕ) (S : Type v) (M : Type w)
    [CommRing S] [Algebra K S] [IsNoetherianRing S]
    [AddCommGroup M] [Module S M] [Module K M] [IsScalarTower K S M]
    [Module.Finite S M]
    (x : Fin n → S) (hx : Algebra.adjoin K (Set.range x) = ⊤)
    (G : ℕ → Submodule K M) [Decomposition G]
    [∀ i, Module.Finite K (G i)]
    (hG : ∀ j i (m : M), m ∈ G i → x j • m ∈ G (i + 1)) :
    EventuallyPolynomial (fun i => ((Module.length K (G i)).toNat : ℚ)) := by
  induction n generalizing S M with
  | zero =>
      have hx0 : Algebra.adjoin K (∅ : Set S) = ⊤ := by simpa using hx
      let : Module.Finite K M := finite_of_no_generators hx0
      refine ⟨0, ?_⟩
      filter_upwards [LengthHilbert.eventually_eq_bot G] with i hi
      rw [hi, Module.length_bot]
      simp
  | succ n ih =>
      let fS : M →ₗ[S] M := LinearMap.lsmul S M (x 0)
      let f : M →ₗ[K] M := fS.restrictScalars K
      have hf : ∀ i, (G i).map f ≤ G (i + 1) := by
        rintro i _ ⟨m, hm, rfl⟩
        exact hG 0 i m hm
      let P : Submodule S M := fS.ker
      let Q : Submodule S M := fS.range
      let V := M ⧸ Q
      let q : M →ₗ[K] V := Q.mkQ.restrictScalars K
      let S' := S ⧸ Ideal.span {x 0}
      let x' : Fin n → S' := fun j => Ideal.Quotient.mk _ (x j.succ)
      have hx' : Algebra.adjoin K (Set.range x') = ⊤ := quotient_generators x hx
      let hPkill : Module.IsTorsionBy S P (x 0) := ker_smul_killed (M := M) (x 0)
      let hVkill : Module.IsTorsionBy S V (x 0) := coker_smul_killed (M := M) (x 0)
      let : Module S' P := hPkill.module
      let : Module S' V := hVkill.module
      have : IsScalarTower K S' P := inferInstance
      have : IsScalarTower K S' V := inferInstance
      have : IsScalarTower S S' P := inferInstance
      have : IsScalarTower S S' V := inferInstance
      have : Module.Finite S' P := Module.Finite.of_restrictScalars_finite S S' P
      have : Module.Finite S' V := Module.Finite.of_restrictScalars_finite S S' V
      let GP : ℕ → Submodule K P := fun i => (G i).comap (P.subtype.restrictScalars K)
      let GV : ℕ → Submodule K V := Grading.imagePiece G q
      have hPhom : (P.restrictScalars K).IsHomogeneous G := by
        exact Grading.ker_homogeneous G G f hf
      have hQhom : q.ker.IsHomogeneous G := by
        have hker : q.ker = f.range := by
          change (Q.mkQ.restrictScalars K).ker = f.range
          rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
          rfl
        rw [hker]
        exact Grading.range_homogeneous G G f hf
      let : Decomposition GP := Grading.subDecomposition G (P.restrictScalars K) hPhom
      let : Decomposition GV := Grading.imageDecomposition G q Q.mkQ_surjective hQhom
      have (i : ℕ) : Module.Finite K (GP i) := by
        exact Module.Finite.of_injective (Grading.subPieceMap G (P.restrictScalars K) i)
          (by
            intro a b h
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z : G i => (z : M)) h)
      have (i : ℕ) : Module.Finite K (GV i) := by
        exact Module.Finite.of_surjective (Grading.pieceMap G q i)
          (LengthHilbert.pieceMap_surjective G q i)
      have hGP : ∀ j i (m : P), m ∈ GP i → x' j • m ∈ GP (i + 1) := by
        intro j i m hm
        change x j.succ • (m : M) ∈ G (i + 1)
        exact hG j.succ i m hm
      have hGV : ∀ j i (m : V), m ∈ GV i → x' j • m ∈ GV (i + 1) := by
        rintro j i _ ⟨m, hm, rfl⟩
        refine ⟨x j.succ • m, hG j.succ i m hm, ?_⟩
        exact Q.mkQ.map_smul _ _
      have hpolP := ih S' P x' hx' GP hGP
      have hpolV := ih S' V x' hx' GV hGV
      apply EventuallyPolynomial.of_recurrence hpolP hpolV
      intro i
      have hker : q.ker = f.range := by
        rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
        rfl
      have he := LengthHilbert.length_recurrence G f hf q hker i
      exact_mod_cast he

end Lech.LengthHilbert
end

end OAI
