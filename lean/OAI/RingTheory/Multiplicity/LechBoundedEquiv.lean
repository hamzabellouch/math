import Mathlib
import OAI.RingTheory.Multiplicity.LechLevel

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
namespace Lech
universe u
variable {R : Type u} [CommRing R]
namespace MonomialSpanning

noncomputable def boundedEquivTotal (h a n : ℕ) (hn : n < a) :
    Bounded h a n ≃ {e : Fin h → ℕ // ∑ i, e i = n} where
  toFun e := ⟨fun i => (e.val i : ℕ), e.property⟩
  invFun e := ⟨fun i => ⟨e.val i, by
    have hi : e.val i ≤ ∑ j, e.val j := Finset.single_le_sum
      (fun j _ => Nat.zero_le (e.val j)) (Finset.mem_univ i)
    exact (hi.trans_eq e.property).trans_lt hn⟩, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma bounded_card_of_lt (h a n : ℕ) (hn : n < a) :
    Fintype.card (Bounded h a n) = h.multichoose n := by
  have e := (boundedEquivTotal h a n hn).trans (Sym.equivNatSumOfFintype (Fin h) n).symm
  exact (Fintype.card_congr e).trans (Sym.card_sym_fin_eq_multichoose h n)

variable {h : ℕ} (z : Fin h → R)

lemma powers_le_power (a : ℕ) :
    Ideal.span (Set.range (fun i => z i ^ a)) ≤ Ideal.span (Set.range z) ^ a := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.pow_mem_pow (show z i ∈ Ideal.span (Set.range z) from
    Ideal.subset_span ⟨i, rfl⟩) a

lemma piece_value_eq_of_levels (ℓ : TorsionLength (Ideal.span (Set.range z)))
    (a n : ℕ) (hn : n < a) :
    ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z))
      (Ideal.span (Set.range (fun i => z i ^ a))) n)) =
    ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z)) ⊥ n)) := by
  let I := Ideal.span (Set.range z)
  let J := Ideal.span (Set.range (fun i => z i ^ a))
  have hJ : J ≤ I ^ (n+1) := (powers_le_power z a).trans (Ideal.pow_le_pow_right hn)
  have h₁ : IdealFiltration.level I J n = IdealFiltration.level I ⊥ n := by
    simp only [IdealFiltration.level, sup_bot_eq]
    exact sup_eq_left.mpr (hJ.trans (Ideal.pow_le_pow_right (Nat.le_succ n)))
  have h₂ : IdealFiltration.level I J (n+1) = IdealFiltration.level I ⊥ (n+1) := by
    exact (sup_eq_left.mpr hJ).trans (sup_bot_eq _).symm
  exact congrArg₂ (fun (P Q : Ideal R) =>
    ℓ.value (ModuleCat.of R (P ⧸ Submodule.comap P.subtype Q))) h₁ h₂

lemma ordinary_piece_value (ℓ : TorsionLength (Ideal.span (Set.range z)))
    (hh : 0 < h)
    (hμ : ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))))
    (n : ℕ) :
    ℓ.value (ModuleCat.of R (IdealFiltration.Piece (Ideal.span (Set.range z)) ⊥ n)) =
      h.multichoose n • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
  rw [← piece_value_eq_of_levels z ℓ (n+1) n (Nat.lt_succ_self n)]
  have hn : n < h*(n+1)+1 := by nlinarith
  rw [piece_value_eq z ℓ (n+1) hμ (ha _ (Nat.succ_pos n)) n hn,
    bounded_card_of_lt _ _ _ (Nat.lt_succ_self n)]

 
lemma power_colength (ℓ : TorsionLength (Ideal.span (Set.range z)))
    (hh : 0 < h)
    (hμ : ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≠ ⊤)
    (ha : ∀ a : ℕ, 0 < a →
      ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun i => z i ^ a)))) =
      a ^ h • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))))
    (M : ℕ) (hM : 0 < M) :
    ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z) ^ M)) =
      (M+h-1).choose h • ℓ.value (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
  have he := IdealFiltration.length_eq_sum (Ideal.span (Set.range z)) ⊥ ℓ M
  have hlev : IdealFiltration.level (Ideal.span (Set.range z)) ⊥ M =
      Ideal.span (Set.range z) ^ M := sup_bot_eq _
  have hv := congrArg (fun J : Ideal R => ℓ.value (ModuleCat.of R (R ⧸ J))) hlev
  rw [← hv, he]
  simp_rw [ordinary_piece_value z ℓ hh hμ ha]
  rw [Finset.sum_nsmul_assoc]
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  rw [Nat.sum_range_multichoose]
  congr 2
  omega

end MonomialSpanning
end Lech


namespace Lech.Grading
open DirectSum
variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [DecidableEq ι]
variable (G : ι → Submodule R M) [Decomposition G]
variable (f : M →ₗ[R] N)

def imagePiece (i : ι) : Submodule R N := (G i).map f

def pieceMap (i : ι) : G i →ₗ[R] imagePiece G f i :=
  (f.comp (G i).subtype).codRestrict _ (fun x => Submodule.mem_map_of_mem x.property)

omit [DecidableEq ι] [Decomposition G] in
@[simp] lemma pieceMap_coe (i : ι) (x : G i) :
    (pieceMap G f i x : N) = f (x : M) := rfl

def beforeQuotient : M →ₗ[R] ⨁ i, imagePiece G f i :=
  (DirectSum.lmap (pieceMap G f)).comp (decomposeLinearEquiv G).toLinearMap

@[simp] lemma beforeQuotient_piece (i : ι) (x : G i) :
    beforeQuotient G f x = DirectSum.lof R ι (fun i => ↥(imagePiece G f i)) i (pieceMap G f i x) := by
  simp [beforeQuotient]

lemma kernel_le_beforeQuotient (hf : f.ker.IsHomogeneous G) :
    f.ker ≤ (beforeQuotient G f).ker := by
  intro x hx
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  change f (decompose G x i : M) = 0
  exact hf i hx

noncomputable def imageDecompose (hs : Function.Surjective f)
    (hf : f.ker.IsHomogeneous G) : N →ₗ[R] ⨁ i, imagePiece G f i :=
  ((f.ker).liftQ (beforeQuotient G f) (kernel_le_beforeQuotient G f hf)).comp
    (f.quotKerEquivOfSurjective hs).symm.toLinearMap

@[simp] lemma imageDecompose_map (hs : Function.Surjective f)
    (hf : f.ker.IsHomogeneous G) (x : M) :
    imageDecompose G f hs hf (f x) = beforeQuotient G f x := by
  simp only [imageDecompose, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

lemma recompose_beforeQuotient :
    (DirectSum.coeLinearMap (imagePiece G f)).comp (beforeQuotient G f) = f := by
  apply DirectSum.decompose_lhom_ext G
  intro i
  ext x
  simp [beforeQuotient_piece]

@[instance_reducible]
noncomputable def imageDecomposition (hs : Function.Surjective f)
    (hf : f.ker.IsHomogeneous G) : Decomposition (imagePiece G f) :=
  Decomposition.ofLinearMap (imagePiece G f) (imageDecompose G f hs hf)
    (by
      ext y
      obtain ⟨x, rfl⟩ := hs y
      simpa only [LinearMap.comp_apply, LinearMap.id_apply, imageDecompose_map] using
        DFunLike.congr_fun (recompose_beforeQuotient G f) x)
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      obtain ⟨a, ha, he⟩ := x.property
      have hx : x = pieceMap G f i ⟨a, ha⟩ := Subtype.ext he.symm
      rw [hx]
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof,
        LinearMap.id_apply, pieceMap_coe, imageDecompose_map]
      exact beforeQuotient_piece G f i ⟨a, ha⟩)

variable (P : Submodule R M)

def subPiece (i : ι) : Submodule R P := Submodule.comap P.subtype (G i)

def subPieceMap (i : ι) : subPiece G P i →ₗ[R] G i :=
  { toFun := fun x => ⟨x.val.val, x.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def subDecompose (hP : P.IsHomogeneous G) : P →ₗ[R] ⨁ i, subPiece G P i where
  toFun x :=
    { toFun := fun i => ⟨⟨decompose G x i, hP i x.property⟩, (decompose G x i).property⟩
      support' := (decompose G x).support'.map fun s =>
        ⟨s.val, fun i => (s.property i).imp id (fun hz => by
          apply Subtype.ext
          apply Subtype.ext
          change (decompose G x i : M) = 0
          exact congrArg (fun y : G i => (y : M)) hz)⟩ }
  map_add' x y := by
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    apply Subtype.ext
    change (decompose G ((x : M) + (y : M)) i : M) =
      (decompose G x i : M) + (decompose G y i : M)
    exact congrArg (fun z : G i => (z : M)) (DFunLike.congr_fun (map_add (decomposeAddEquiv G) (x : M) (y : M)) i)
  map_smul' a x := by
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    apply Subtype.ext
    change (decompose G (a • (x : M)) i : M) = a • (decompose G x i : M)
    exact congrArg (fun z : G i => (z : M)) (DFunLike.congr_fun (decompose_smul G a x) i)

@[simp] lemma subDecompose_lmap (hP : P.IsHomogeneous G) (x : P) :
    DirectSum.lmap (subPieceMap G P) (subDecompose G P hP x) = decompose G x := by
  apply DFinsupp.ext
  intro i
  rfl

omit [Decomposition G] in
lemma sub_lmap_recompose :
    P.subtype.comp (DirectSum.coeLinearMap (subPiece G P)) =
      (DirectSum.coeLinearMap G).comp (DirectSum.lmap (subPieceMap G P)) := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, DirectSum.lmap_lof]
  rfl

@[instance_reducible]
noncomputable def subDecomposition (hP : P.IsHomogeneous G) :
    Decomposition (subPiece G P) :=
  Decomposition.ofLinearMap (subPiece G P) (subDecompose G P hP)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have h := DFunLike.congr_fun (sub_lmap_recompose G P) (subDecompose G P hP x)
      simp only [LinearMap.comp_apply, subDecompose_lmap] at h
      exact h.trans ((decompose G).symm_apply_apply x))
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
      apply DFinsupp.ext
      intro j
      apply Subtype.ext
      apply Subtype.ext
      change (decompose G (x.val : M) j : M) = ((DirectSum.of (fun i => ↥(subPiece G P i)) i x) j : M)
      have hx : ((x : P) : M) ∈ G i := x.property
      rw [decompose_of_mem G hx]
      by_cases hij : i = j
      · subst j
        simp
      · simp [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij)])


end Lech.Grading


namespace Lech
namespace IdealGraded

variable {A : Type*} [CommRing A]

def nextPower (I : Ideal A) (n : ℕ) : Submodule A ↥(I ^ n) :=
  Submodule.comap (I ^ n).subtype (I ^ (n + 1))

abbrev Piece (I : Ideal A) (n : ℕ) := ↥(I ^ n) ⧸ nextPower I n

lemma pow_succ_le (I : Ideal A) (n : ℕ) : I ^ (n + 1) ≤ I ^ n := by
  exact Ideal.pow_le_pow_right (Nat.le_succ n)

lemma torsion_piece (I : Ideal A) (n : ℕ) :
    Module.IsTorsionBySet A (Piece I n) I := by
  rw [Module.isTorsionBySet_quotient_iff]
  intro x a ha
  change a * (x : A) ∈ I ^ (n + 1)
  rw [pow_succ']
  exact Ideal.mul_mem_mul ha x.property

noncomputable instance pieceModule (I : Ideal A) (n : ℕ) :
    Module (A ⧸ I) (Piece I n) := (torsion_piece I n).module

instance pieceTower (I : Ideal A) (n : ℕ) :
    IsScalarTower A (A ⧸ I) (Piece I n) :=
  (torsion_piece I n).isScalarTower

def inclusion (I : Ideal A) (n : ℕ) : Piece I n →ₗ[A] A ⧸ I ^ (n + 1) :=
  (nextPower I n).liftQ (((I ^ (n + 1)).mkQ).comp (I ^ n).subtype) (by
    intro x hx
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, nextPower, Submodule.mem_comap] using hx)

lemma inclusion_injective (I : Ideal A) (n : ℕ) :
    Function.Injective (inclusion I n) := by
  rw [← LinearMap.ker_eq_bot, inclusion, Submodule.ker_liftQ_eq_bot]
  simpa only [LinearMap.ker_comp, Submodule.ker_mkQ, nextPower] using (le_refl (nextPower I n))

def transition (I : Ideal A) (n : ℕ) :
    (A ⧸ I ^ (n + 1)) →ₗ[A] (A ⧸ I ^ n) :=
  (I ^ (n + 1)).mapQ (I ^ n) LinearMap.id (pow_succ_le I n)

lemma transition_surjective (I : Ideal A) (n : ℕ) :
    Function.Surjective (transition I n) := by
  intro x
  obtain ⟨a, rfl⟩ := (I ^ n).mkQ_surjective x
  exact ⟨(I ^ (n + 1)).mkQ a, rfl⟩

lemma piece_exact (I : Ideal A) (n : ℕ) :
    Function.Exact (inclusion I n) (transition I n) := by
  rw [LinearMap.exact_iff]
  simp only [inclusion, transition, Submodule.ker_mapQ, Submodule.range_liftQ,
    LinearMap.range_comp, Submodule.range_subtype, Submodule.comap_id]

lemma length_successor (I : Ideal A) (n : ℕ) :
    Module.length A (A ⧸ I ^ (n + 1)) =
      Module.length A (Piece I n) + Module.length A (A ⧸ I ^ n) :=
  Module.length_eq_add_of_exact (inclusion I n) (transition I n)
    (inclusion_injective I n) (transition_surjective I n) (piece_exact I n)

lemma length_eq_sum (I : Ideal A) (N : ℕ) :
    Module.length A (A ⧸ I ^ N) =
      ∑ n ∈ Finset.range N, Module.length A (Piece I n) := by
  induction N with
  | zero => simp
  | succ N ih => rw [length_successor, ih, Finset.sum_range_succ, add_comm]

instance pieceFinite [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    Module.Finite (A ⧸ I) (Piece I n) :=
  Module.Finite.of_restrictScalars_finite A (A ⧸ I) (Piece I n)

lemma length_piece_eq_finrank [IsNoetherianRing A] (I : Ideal A) [I.IsMaximal] (n : ℕ) :
    Module.length A (Piece I n) = (Module.finrank (A ⧸ I) (Piece I n) : ℕ∞) := by
  let := Ideal.Quotient.field I
  rw [Module.length_eq_of_surjective (R := A ⧸ I)
    (by simpa only [Ideal.Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective),
    Module.length_eq_finrank]

end IdealGraded
end Lech


namespace Lech.IdealGraded
open Polynomial DirectSum
open scoped Classical
variable {R : Type*} [CommRing R] (I : Ideal R)

def monomial (i : ℕ) : ↥(I ^ i) →ₗ[R] reesAlgebra I :=
  ((Polynomial.monomial i).comp (I ^ i).subtype).codRestrict (reesAlgebra I).toSubmodule
    (fun x => reesAlgebra.monomial_mem.mpr x.property)

@[simp] lemma monomial_coe (i : ℕ) (x : ↥(I ^ i)) :
    (monomial I i x : R[X]) = Polynomial.monomial i (x : R) := rfl

def coefficient (i : ℕ) : reesAlgebra I →ₗ[R] ↥(I ^ i) :=
  ((Polynomial.lcoeff R i).comp (reesAlgebra I).val.toLinearMap).codRestrict _
    (fun p => p.property i)

@[simp] lemma coefficient_coe (i : ℕ) (p : reesAlgebra I) :
    (coefficient I i p : R) = (p : R[X]).coeff i := rfl

@[simp] lemma coefficient_monomial (i : ℕ) (x : ↥(I ^ i)) :
    coefficient I i (monomial I i x) = x := by
  apply Subtype.ext
  change (Polynomial.monomial i (x : R)).coeff i = (x : R)
  simp

lemma monomial_injective (i : ℕ) : Function.Injective (monomial I i) :=
  Function.LeftInverse.injective (coefficient_monomial I i)

abbrev reesGrade (i : ℕ) : Submodule R (reesAlgebra I) := (monomial I i).range

def component (i : ℕ) : reesAlgebra I →ₗ[R] reesGrade I i :=
  (monomial I i).rangeRestrict.comp (coefficient I i)

@[simp] lemma component_coe (i : ℕ) (p : reesAlgebra I) :
    ((component I i p : reesAlgebra I) : R[X]) = Polynomial.monomial i ((p : R[X]).coeff i) := rfl

noncomputable def reesDecompose : reesAlgebra I →ₗ[R] ⨁ i, reesGrade I i where
  toFun p :=
    { toFun := fun i => component I i p
      support' := by
        classical
        exact Trunc.mk ⟨(p : R[X]).support.val, fun i => by
          by_cases hi : i ∈ (p : R[X]).support
          · exact Or.inl hi
          · apply Or.inr
            apply Subtype.ext
            apply Subtype.ext
            simp [component_coe, Polynomial.notMem_support_iff.mp hi]⟩ }
  map_add' p q := by apply DFinsupp.ext; intro i; exact (component I i).map_add p q
  map_smul' a p := by apply DFinsupp.ext; intro i; exact (component I i).map_smul a p

@[simp] lemma reesDecompose_apply (p : reesAlgebra I) (i : ℕ) :
    reesDecompose I p i = component I i p := rfl

lemma reesDecompose_support (p : reesAlgebra I) :
    (reesDecompose I p).support = (p : R[X]).support := by
  classical
  ext i
  simp only [DFinsupp.mem_support_iff, Polynomial.mem_support_iff, reesDecompose_apply]
  have he : component I i p = 0 ↔ (p : R[X]).coeff i = 0 := by
    rw [← Subtype.val_inj, ← Subtype.val_inj]
    simp only [component_coe, ZeroMemClass.coe_zero, Polynomial.monomial_eq_zero_iff]
  exact not_congr he

lemma reesDecompose_monomial (i : ℕ) (x : ↥(I ^ i)) :
    reesDecompose I (monomial I i x) =
      DirectSum.lof R ℕ (fun i => ↥(reesGrade I i)) i ((monomial I i).rangeRestrict x) := by
  rw [DirectSum.lof_eq_of]
  apply DFinsupp.ext
  intro j
  apply Subtype.ext
  apply Subtype.ext
  by_cases hij : i = j
  · subst j
    simp [component_coe]
  · simp [component_coe, Polynomial.coeff_monomial, hij,
      DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij)]

noncomputable instance reesDecomposition : Decomposition (reesGrade I) :=
  Decomposition.ofLinearMap _ (reesDecompose I)
    (by
      classical
      apply LinearMap.ext
      intro p
      apply Subtype.ext
      rw [LinearMap.comp_apply, DirectSum.coeLinearMap_eq_dfinsuppSum]
      change (∑ i ∈ (reesDecompose I p).support,
        (reesDecompose I p i : reesAlgebra I) : reesAlgebra I).val = (p : R[X])
      rw [reesDecompose_support]
      change (reesAlgebra I).val (∑ i ∈ (p : R[X]).support,
        (reesDecompose I p i : reesAlgebra I)) = (p : R[X])
      rw [map_sum]
      simp only [reesDecompose_apply]
      exact (Polynomial.as_sum_support p.val).symm)
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      rintro ⟨p, x, rfl⟩
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
      change reesDecompose I (monomial I i x) = _
      convert reesDecompose_monomial I i x using 1
      rfl)

@[simp] lemma rees_decompose_val (p : reesAlgebra I) (i : ℕ) :
    ((decompose (reesGrade I) p i : reesAlgebra I) : R[X]) =
      Polynomial.monomial i (p.val.coeff i) := rfl

 
def shifted : Ideal (reesAlgebra I) where
  carrier := {p | ∀ i, (p : R[X]).coeff i ∈ I ^ (i + 1)}
  zero_mem' i := by simp
  add_mem' hp hq i := by simpa using (I ^ (i + 1)).add_mem (hp i) (hq i)
  smul_mem' p q hq i := by
    change ((p : R[X]) * (q : R[X])).coeff i ∈ _
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ hjk
    have hi : j + k = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hjk
    have hh := Ideal.mul_mem_mul (p.property j) (hq k)
    rw [← pow_add] at hh
    simpa only [← hi, Nat.add_assoc] using hh

lemma shifted_homogeneous : SetLike.IsHomogeneous (reesGrade I) (shifted I) := by
  intro i p hp j
  change (Polynomial.monomial i (p.val.coeff i)).coeff j ∈ I ^ (j + 1)
  by_cases hij : i = j
  · subst j
    simpa using hp i
  · simp [Polynomial.coeff_monomial, hij]

end Lech.IdealGraded
end

end OAI
