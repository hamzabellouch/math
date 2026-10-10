import Mathlib
import OAI.RepresentationTheory.Unitary.Basic

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

namespace SignedTensor

/- p even basis symbols followed by p odd ones, exactly E⊕O in05. -/
abbrev Letter (p : ℕ) := Fin (2*p)
abbrev Word (p l : ℕ) := Fin l → Letter p

def odd {p : ℕ} (a : Letter p) : Prop := p ≤ a.val

/- The sign from reordering the odd factors, with positions ordered as in
ordinary tensor words. There is no choice of orientation hidden here. -/
def koszulExponent {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) : ℕ :=
  ((Equiv.Perm.finPairsLT l).filter (fun ij =>
    odd (w ij.1) ∧ odd (w ij.2) ∧ σ ij.1 < σ ij.2)).card

def phase {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) : ℂ :=
  (-1)^koszulExponent σ w

/- The underlying ordinary slot permutation; gh applies h first. -/
def wordPerm {p l : ℕ} (σ : Equiv.Perm (Fin l)) : Equiv.Perm (Word p l) where
  toFun w i := w (σ⁻¹ i)
  invFun w i := w (σ i)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

/- Matrix of the exact parity-signed action in the tensor word basis. -/
def matrix {p l : ℕ} (σ : Equiv.Perm (Fin l)) : Matrix (Word p l) (Word p l) ℂ :=
  fun u w => if u=wordPerm σ w then phase σ w else 0

lemma phase_star_mul {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) :
    star (phase σ w)*phase σ w=1 := by
  simp only [phase,star_pow,star_neg,star_one]
  rw [← mul_pow]
  simp

lemma phase_prod {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) :
    phase σ w = ∏ ij ∈ Equiv.Perm.finPairsLT l,
      (if odd (w ij.1) ∧ odd (w ij.2) ∧ σ ij.1 < σ ij.2 then (-1 : ℂ) else 1) := by
  rw [Finset.prod_ite]
  simp [phase,koszulExponent]

lemma wordPerm_mul {p l : ℕ} (σ τ : Equiv.Perm (Fin l)) :
    wordPerm (p := p) (σ*τ) = wordPerm σ * wordPerm τ := by
  ext w i
  simp [wordPerm]

/- The exact Koszul cocycle, proved from pair inversions, not an action axiom. -/
theorem phase_mul {p l : ℕ} (σ τ : Equiv.Perm (Fin l)) (w : Word p l) :
    phase (σ*τ) w = phase σ (wordPerm τ w) * phase τ w := by
  rw [phase_prod,phase_prod,phase_prod]
  have hreindex :
      (∏ ij ∈ Equiv.Perm.finPairsLT l,
        (if odd (wordPerm τ w ij.1) ∧ odd (wordPerm τ w ij.2) ∧ σ ij.1 < σ ij.2
        then (-1 : ℂ) else 1)) =
      ∏ ij ∈ Equiv.Perm.finPairsLT l,
        (if odd (wordPerm τ w (Equiv.Perm.signBijAux τ ij).1) ∧
          odd (wordPerm τ w (Equiv.Perm.signBijAux τ ij).2) ∧
          σ (Equiv.Perm.signBijAux τ ij).1 < σ (Equiv.Perm.signBijAux τ ij).2
        then (-1 : ℂ) else 1) := by
    symm
    exact Finset.prod_nbij (Equiv.Perm.signBijAux τ)
      Equiv.Perm.signBijAux_mem Equiv.Perm.signBijAux_injOn
      Equiv.Perm.signBijAux_surj (fun _ _ => rfl)
  rw [hreindex,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  rintro ⟨i,j⟩ hij
  have hji : j < i := Equiv.Perm.mem_finPairsLT.mp hij
  have hne : τ j ≠ τ i := τ.injective.ne hji.ne
  have hneσ : σ (τ j) ≠ σ (τ i) := σ.injective.ne hne
  by_cases hi : odd (w i)
  · by_cases hj : odd (w j)
    · by_cases ht : τ j < τ i
      · simp [Equiv.Perm.signBijAux,wordPerm,Equiv.Perm.mul_apply,ht,hi,hj,ht.not_gt]
      · have ht' : τ i < τ j := lt_of_le_of_ne (le_of_not_gt ht) hne.symm
        by_cases hs : σ (τ i) < σ (τ j)
        · simp [Equiv.Perm.signBijAux,wordPerm,Equiv.Perm.mul_apply,ht,ht',hi,hj,hs,hs.not_gt]
        · have hs' : σ (τ j) < σ (τ i) := lt_of_le_of_ne (le_of_not_gt hs) hneσ
          simp [Equiv.Perm.signBijAux,wordPerm,Equiv.Perm.mul_apply,ht,ht',hi,hj,hs,hs']
    · by_cases ht : τ j < τ i <;>
        simp [Equiv.Perm.signBijAux,wordPerm,Equiv.Perm.mul_apply,ht,hi,hj]
  · by_cases ht : τ j < τ i <;>
      simp [Equiv.Perm.signBijAux,wordPerm,Equiv.Perm.mul_apply,ht,hi]

/- Unitarity follows directly, without assuming the Schur-Weyl
or Pieri decomposition. -/
theorem matrix_unitary {p l : ℕ} (σ : Equiv.Perm (Fin l)) :
    (matrix (p := p) σ).conjTranspose * matrix σ=1 := by
  ext u w
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,matrix]
  rw [Finset.sum_eq_single (wordPerm σ u)]
  · by_cases hu : u=w
    · subst w
      simp only [ite_true,Matrix.one_apply_eq,phase_star_mul]
    · have hne : wordPerm σ u ≠ wordPerm σ w :=
        fun hh => hu ((wordPerm σ).injective hh)
      simp [hne,hu]
  · intro v hv hne
    simp [hne]
  · simp

lemma phase_one {p l : ℕ} (w : Word p l) : phase (1 : Equiv.Perm (Fin l)) w=1 := by
  rw [phase_prod]
  apply Finset.prod_eq_one
  intro ij hij
  have hji := Equiv.Perm.mem_finPairsLT.mp hij
  simp [Equiv.Perm.one_apply,hji.not_gt]

theorem matrix_one (p l : ℕ) : matrix (p := p) (1 : Equiv.Perm (Fin l))=1 := by
  ext u w
  simp [matrix,wordPerm,phase_one,Matrix.one_apply]

theorem matrix_mul {p l : ℕ} (σ τ : Equiv.Perm (Fin l)) :
    matrix (p := p) (σ*τ)=matrix σ * matrix τ := by
  ext u w
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single (wordPerm τ w)]
  · simp only [ite_true,wordPerm_mul,Equiv.Perm.mul_apply,phase_mul]
    split_ifs <;> simp
  · intro v hv hne
    simp [hne]
  · simp

/- Exact signed tensor representation of the symmetric group. -/
def action (p l : ℕ) : Equiv.Perm (Fin l) →* Matrix (Word p l) (Word p l) ℂ where
  toFun := matrix
  map_one' := matrix_one p l
  map_mul' := matrix_mul

/- Ordinary (not graded) tensor power of a one-site density, as in05. -/
def densityPower {p : ℕ} (l : ℕ) (r : Matrix (Letter p) (Letter p) ℂ) :
    Matrix (Word p l) (Word p l) ℂ := fun u w => ∏ i, r (u i) (w i)

lemma densityPower_mul {p : ℕ} (l : ℕ) (a b : Matrix (Letter p) (Letter p) ℂ) :
    densityPower l (a*b)=densityPower l a * densityPower l b := by
  ext u w
  simp only [densityPower,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.prod_mul_distrib

lemma densityPower_star {p : ℕ} (l : ℕ) (r : Matrix (Letter p) (Letter p) ℂ) :
    densityPower l r.conjTranspose=(densityPower l r).conjTranspose := by
  ext u w
  simp [densityPower,Matrix.conjTranspose_apply]

lemma densityPower_trace {p : ℕ} (l : ℕ) (r : Matrix (Letter p) (Letter p) ℂ) :
    Matrix.trace (densityPower l r)=(Matrix.trace r)^l := by
  change (∑ w : Word p l, ∏ i, r (w i) (w i))=(∑ i, r i i)^l
  exact (Fintype.sum_pow (fun i : Letter p => r i i) l).symm

open scoped MatrixOrder in
lemma densityPower_posSemidef {p : ℕ} (l : ℕ) (r : Matrix (Letter p) (Letter p) ℂ)
    (hr : r.PosSemidef) : (densityPower l r).PosSemidef := by
  obtain ⟨b,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hr.nonneg
  rw [densityPower_mul,Matrix.star_eq_conjTranspose,densityPower_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/- Even means positive trace-one and block diagonal for E,O, exactly as in05. -/
def EvenDensity (p : ℕ) := {r : Matrix (Letter p) (Letter p) ℂ //
  r.PosSemidef ∧ Matrix.trace r=1 ∧
    ∀ i j, (odd i ↔ ¬ odd j) → r i j=0}

instance (p : ℕ) : MeasurableSpace (EvenDensity p) :=
  MeasurableSpace.comap Subtype.val (borel (Matrix (Letter p) (Letter p) ℂ))

lemma phase_eq_of_parity {p l : ℕ} (σ : Equiv.Perm (Fin l))
    (u w : Word p l) (h : ∀ i, odd (u i) ↔ odd (w i)) : phase σ u=phase σ w := by
  simp only [phase,koszulExponent]
  congr 2
  apply Finset.filter_congr
  intro ij hij
  rw [h ij.1,h ij.2]

lemma densityPower_parity_of_ne_zero {p l : ℕ} (r : EvenDensity p)
    {u w : Word p l} (h : densityPower l r.val u w ≠ 0) :
    ∀ i, odd (u i) ↔ odd (w i) := by
  intro i
  have he : r.val (u i) (w i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ _)
  by_contra hn
  apply he
  apply r.property.2.2
  tauto

lemma densityPower_permute {p l : ℕ} (σ : Equiv.Perm (Fin l))
    (r : Matrix (Letter p) (Letter p) ℂ) (u w : Word p l) :
    densityPower l r (wordPerm σ u) (wordPerm σ w)=densityPower l r u w := by
  simp only [densityPower,wordPerm,Equiv.coe_fn_mk]
  exact Equiv.prod_comp σ⁻¹ (fun i => r (u i) (w i))

/- Even densities commute with the signed action; omission of evenness here
would be false. This is also the block-reordering claim at the end of05. -/
theorem densityPower_commute {p l : ℕ} (r : EvenDensity p)
    (σ : Equiv.Perm (Fin l)) :
    matrix σ * densityPower l r.val=densityPower l r.val * matrix σ := by
  ext u w
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single ((wordPerm σ).symm u),
    Finset.sum_eq_single (wordPerm σ w)]
  · simp only [(wordPerm σ).apply_symm_apply,ite_true]
    have hd : densityPower l r.val u (wordPerm σ w)=
        densityPower l r.val ((wordPerm σ).symm u) w := by
      simpa using densityPower_permute σ r.val ((wordPerm σ).symm u) w
    rw [hd]
    by_cases hn : densityPower l r.val ((wordPerm σ).symm u) w=0
    · simp [hn]
    · rw [phase_eq_of_parity σ _ _ (densityPower_parity_of_ne_zero r hn),mul_comm]
  · intro v hv hne
    simp [hne]
  · simp
  · intro v hv hne
    have hh : u ≠ wordPerm σ v := by
      intro he
      apply hne
      exact (Equiv.eq_symm_apply _).mpr he.symm
    simp [hh]
  · simp

lemma evenDensityPower_trace {p : ℕ} (l : ℕ) (r : EvenDensity p) :
    Matrix.trace (densityPower l r.val)=1 := by
  rw [densityPower_trace,r.property.2.1,one_pow]

/- The standard central character formula for the isotypic projection. Its
projection properties require the signed action laws (not assumed here). -/
def isotypic {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    Matrix (Word p l) (Word p l) ℂ :=
  ((ρ.dimension : ℂ)/(Fintype.card (Equiv.Perm (Fin l)) : ℂ)) •
    ∑ σ, Matrix.trace (ρ.matrix σ⁻¹) • matrix σ

/- Exact signed-density domination05 eq13, expressed for every irreducible
(including absent ones whose projection is zero). The mixture is a genuine
probability measure on the source's even density matrices, not an unproved
positive operator supplied as a hypothesis. -/
def Domination : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ s p : ℕ, 1 ≤ p → p ≤ s → ∀ l : ℕ, l ≤ s →
    ∀ ρ : UnitaryIrrep (Equiv.Perm (Fin l)),
      ∃ μ : MeasureTheory.Measure (EvenDensity p), MeasureTheory.IsProbabilityMeasure μ ∧
        (Complex.ofReal (Real.exp (Real.log ρ.dimension+C*p^2*Real.log (s+1))) •
          (∫ r : EvenDensity p, densityPower l r.val ∂μ) - isotypic (p := p) ρ).PosSemidef

end SignedTensor
end CoordinateSweeps

/- A direct counting approach to the polynomial multiplicity bound in05,
without replacing Schur-Weyl or the density inequality by an axiom.
The signed tensor commutant is determined by pair-word histograms. -/
namespace CoordinateSweeps.SignedTensor

lemma phase_ne_zero {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) : phase σ w ≠ 0 := by
  intro h
  have hh := phase_star_mul σ w
  simp [h] at hh

lemma mul_signed_entry {p l : ℕ} (A : Matrix (Word p l) (Word p l) ℂ)
    (σ : Equiv.Perm (Fin l)) (u w : Word p l) :
    (A*matrix (p := p) σ) u w=A u (wordPerm σ w)*phase σ w := by
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single (wordPerm σ w)]
  · simp
  · intro v hv hne; simp [hne]
  · simp

lemma signed_mul_entry {p l : ℕ} (A : Matrix (Word p l) (Word p l) ℂ)
    (σ : Equiv.Perm (Fin l)) (u w : Word p l) :
    (matrix (p := p) σ*A) (wordPerm σ u) w=phase σ u*A u w := by
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single u]
  · simp
  · intro v hv hne
    have hne' : wordPerm σ u ≠ wordPerm σ v :=
      fun hh => hne (((wordPerm σ).injective hh).symm)
    simp [hne']
  · simp

/- The actual signed-action commutant as a linear subspace of matrices. -/
def commutant (p l : ℕ) : Submodule ℂ (Matrix (Word p l) (Word p l) ℂ) where
  carrier := {A | ∀ σ : Equiv.Perm (Fin l), A*matrix σ=matrix σ*A}
  zero_mem' := by simp
  add_mem' hA hB := by intro σ; simp only [add_mul,mul_add,hA σ,hB σ]
  smul_mem' c A hA := by intro σ; simp only [smul_mul_assoc,mul_smul_comm,hA σ]

lemma commutant_zero_transport {p l : ℕ} (A : commutant p l)
    (σ : Equiv.Perm (Fin l)) {u w : Word p l} (h : A.val u w=0) :
    A.val (wordPerm σ u) (wordPerm σ w)=0 := by
  have hh := congrArg (fun B : Matrix (Word p l) (Word p l) ℂ => B (wordPerm σ u) w)
    (A.property σ)
  rw [mul_signed_entry,signed_mul_entry,h,mul_zero] at hh
  exact (mul_eq_zero.mp hh).resolve_right (phase_ne_zero σ w)

abbrev Profile (p l : ℕ) := (Letter p × Letter p) → Fin (l+1)

def profile {p l : ℕ} (u w : Word p l) : Profile p l := fun a =>
  ⟨(Finset.univ.filter (fun i => (u i,w i)=a)).card,
    Nat.lt_succ_iff.mpr (by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin l))
        (fun i => (u i,w i)=a))⟩

lemma profile_fiber_card {p l : ℕ} (u w : Word p l) (a : Letter p × Letter p) :
    Fintype.card {i : Fin l // (u i,w i)=a}=(profile u w a).val := by
  simp [profile,Fintype.card_subtype]

/- Two word pairs have the same histogram exactly when a position permutation
carries one to the other. This supplies the finite orbit-counting parameter. -/
lemma profile_eq_exists_perm {p l : ℕ} {u w u' w' : Word p l}
    (hh : profile u w=profile u' w') :
    ∃ σ : Equiv.Perm (Fin l), wordPerm σ u=u' ∧ wordPerm σ w=w' := by
  have hc (a : Letter p × Letter p) : Fintype.card {i : Fin l // (u i,w i)=a}=
      Fintype.card {i : Fin l // (u' i,w' i)=a} := by
    rw [profile_fiber_card,profile_fiber_card,hh]
  let e (a : Letter p × Letter p) : {i : Fin l // (u i,w i)=a} ≃
      {i : Fin l // (u' i,w' i)=a} := Fintype.equivOfCardEq (hc a)
  let σ : Equiv.Perm (Fin l) := Equiv.ofFiberEquiv e
  have he (i : Fin l) : (u' (σ i),w' (σ i))=(u i,w i) := Equiv.ofFiberEquiv_map e i
  refine ⟨σ,?_,?_⟩
  · funext i
    have hi := congrArg Prod.fst (he (σ⁻¹ i))
    simpa [wordPerm] using hi.symm
  · funext i
    have hi := congrArg Prod.snd (he (σ⁻¹ i))
    simpa [wordPerm] using hi.symm

abbrev OccurringProfile (p l : ℕ) :=
  {q : Profile p l // q ∈ Set.range (fun uw : Word p l × Word p l => profile uw.1 uw.2)}

def profileRep {p l : ℕ} (q : OccurringProfile p l) : Word p l × Word p l :=
  Classical.choose q.property

lemma profileRep_spec {p l : ℕ} (q : OccurringProfile p l) :
    profile (profileRep q).1 (profileRep q).2=q.val := Classical.choose_spec q.property

def commutantEval (p l : ℕ) : commutant p l →ₗ[ℂ] (OccurringProfile p l → ℂ) where
  toFun A q := A.val (profileRep q).1 (profileRep q).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma commutantEval_injective (p l : ℕ) : Function.Injective (commutantEval p l) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro A hA
  apply Subtype.ext
  ext u w
  let q : OccurringProfile p l := ⟨profile u w,Set.mem_range_self (u,w)⟩
  have he : A.val (profileRep q).1 (profileRep q).2=0 := congrFun hA q
  have hp : profile (profileRep q).1 (profileRep q).2=profile u w := profileRep_spec q
  obtain ⟨σ,hσu,hσw⟩ := profile_eq_exists_perm hp
  have hh := commutant_zero_transport A σ he
  simpa [hσu,hσw] using hh

/- Polynomial signed-commutant bound of exactly the O(p² log(s+1)) scale
required by the main induction. No classification of partitions is used. -/
theorem commutant_finrank_le (p l : ℕ) :
    Module.finrank ℂ (commutant p l) ≤ (l+1)^((2*p)*(2*p)) := by
  have h := LinearMap.finrank_le_finrank_of_injective (commutantEval_injective p l)
  have hc : Fintype.card (OccurringProfile p l) ≤ Fintype.card (Profile p l) :=
    Fintype.card_subtype_le _
  have he : Fintype.card (Profile p l)=(l+1)^((2*p)*(2*p)) := by
    simp [Profile,Letter]
  simpa [he] using h.trans (by simpa using hc)

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor

lemma matrix_inv {p l : ℕ} (σ : Equiv.Perm (Fin l)) :
    matrix (p := p) σ⁻¹=(matrix (p := p) σ).conjTranspose := by
  calc
    matrix σ⁻¹=1*matrix (p := p) σ⁻¹ := (one_mul _).symm
    _ = ((matrix σ).conjTranspose*matrix σ)*matrix (p := p) σ⁻¹ := by rw [matrix_unitary]
    _ = (matrix (p := p) σ).conjTranspose := by
      rw [mul_assoc,← matrix_mul,mul_inv_cancel,matrix_one,mul_one]

abbrev tensorRepresentation (p l : ℕ) := UnitaryIrrep.matrixRepresentation (action p l)

/- An actual intertwining endomorphism has its coefficient matrix in the
signed commutant. This is not an assumed decomposition of the tensor action. -/
def endomorphismMatrix (p l : ℕ) :
    (tensorRepresentation p l).IntertwiningMap (tensorRepresentation p l) →ₗ[ℂ]
      commutant p l where
  toFun F := ⟨LinearMap.toMatrixAlgEquiv' F.toLinearMap,by
    intro σ
    apply Matrix.toLinAlgEquiv'.injective
    simp only [map_mul,Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
    exact F.isIntertwining' σ⟩
  map_add' F H := by
    apply Subtype.ext
    exact map_add LinearMap.toMatrixAlgEquiv' _ _
  map_smul' c F := by
    apply Subtype.ext
    exact map_smul LinearMap.toMatrixAlgEquiv'.toLinearMap c _

lemma endomorphismMatrix_injective (p l : ℕ) :
    Function.Injective (endomorphismMatrix p l) := by
  intro F H hh
  apply Representation.IntertwiningMap.ext
  exact LinearMap.toMatrixAlgEquiv'.injective (congrArg Subtype.val hh)

theorem tensor_endomorphisms_finrank_le (p l : ℕ) :
    Module.finrank ℂ ((tensorRepresentation p l).IntertwiningMap (tensorRepresentation p l)) ≤
      (l+1)^((2*p)*(2*p)) :=
  (LinearMap.finrank_le_finrank_of_injective (endomorphismMatrix_injective p l)).trans
    (commutant_finrank_le p l)

/- The polynomial multiplicity clause of05 signed density lemma, proved
without Young diagrams. Multiplicity is the actual space of equivariant embeddings. -/
theorem multiplicity_le (p l : ℕ) (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (tensorRepresentation p l)) ≤
      (l+1)^((2*p)*(2*p)) := by
  have hh := ρ.multiplicity_sq_le_commutant (action p l)
    (fun σ => matrix_inv σ |>.symm)
  have hm : Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (tensorRepresentation p l)) ≤
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (tensorRepresentation p l)))^2 := by
    exact Nat.le_self_pow (by omega) _
  exact hm.trans (hh.trans (tensor_endomorphisms_finrank_le p l))

lemma isotypic_eq_projector {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    isotypic (p := p) ρ=ρ.projector (action p l) := by
  simp only [isotypic,UnitaryIrrep.projector,UnitaryIrrep.coefficient,Finset.smul_sum,mul_smul]
  rfl

theorem isotypic_posSemidef {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    (isotypic (p := p) ρ).PosSemidef := by
  rw [isotypic_eq_projector]
  exact ρ.projector_posSemidef (action p l) (fun σ => (matrix_inv σ).symm)

theorem isotypic_trace {p l : ℕ} (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) :
    Matrix.trace (isotypic (p := p) ρ)=(ρ.dimension : ℂ)*
      Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (tensorRepresentation p l)) := by
  rw [isotypic_eq_projector]
  simp only [UnitaryIrrep.projector,Matrix.trace_sum,Matrix.trace_smul,
    UnitaryIrrep.coefficient,smul_eq_mul]
  calc
    _ = ((ρ.dimension : ℂ)/(Fintype.card (Equiv.Perm (Fin l)) : ℂ)) *
        ∑ σ, Matrix.trace (action p l σ)*Matrix.trace (ρ.matrix σ⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    _ = _ := by
      rw [ρ.character_sum_multiplicity (action p l)]
      have hN : (Fintype.card (Equiv.Perm (Fin l)) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      field_simp

end CoordinateSweeps.SignedTensor

/- Mismatched symbols in a purification
obey a Pauli exclusion rule. This is derived from the literal Koszul action. -/
namespace CoordinateSweeps.SignedTensor

lemma swap01_inversion_iff (n : ℕ) (i j : Fin (n+2)) :
    (j < i ∧ Equiv.swap (0 : Fin (n+2)) 1 i < Equiv.swap 0 1 j) ↔
      i = 1 ∧ j = 0 := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all
  omega

lemma phase_swap01 {p n : ℕ} (w : Word p (n+2)) :
    phase (Equiv.swap (0 : Fin (n+2)) 1) w =
      if odd (w 1) ∧ odd (w 0) then (-1 : ℂ) else 1 := by
  have he : ((Equiv.Perm.finPairsLT (n+2)).filter (fun ij =>
      odd (w ij.1) ∧ odd (w ij.2) ∧
        Equiv.swap (0 : Fin (n+2)) 1 ij.1 < Equiv.swap 0 1 ij.2)) =
      if odd (w 1) ∧ odd (w 0) then {⟨1,0⟩} else ∅ := by
    ext ⟨i,j⟩
    simp only [Finset.mem_filter, Equiv.Perm.mem_finPairsLT]
    have hi := swap01_inversion_iff n i j
    split_ifs with hw
    · simp only [Finset.mem_singleton, Sigma.mk.inj_iff, heq_eq_eq]
      constructor
      · rintro ⟨hji,hiw,hjw,hs⟩
        exact hi.mp ⟨hji,hs⟩
      · rintro ⟨rfl,rfl⟩
        exact ⟨by simp, hw.1, hw.2, by simp⟩
    · simp only [Finset.notMem_empty, iff_false]
      rintro ⟨hji,hiw,hjw,hs⟩
      obtain ⟨rfl,rfl⟩ := hi.mp ⟨hji,hs⟩
      exact hw ⟨hiw,hjw⟩
  unfold phase koszulExponent
  rw [he]
  split_ifs <;> simp

lemma wordPerm_swap01_of_equal {p n : ℕ} (w : Word p (n+2)) (hw : w 0 = w 1) :
    wordPerm (Equiv.swap (0 : Fin (n+2)) 1) w = w := by
  ext i
  simp only [wordPerm, Equiv.coe_fn_mk, Equiv.swap_inv, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/- Two repeated, parity-mismatched pair symbols force a zero entry in every
commuting matrix, hence in the canonical purification of an isotypic projector. -/
theorem commutant_entry_zero_adjacent_mismatch {p n : ℕ} (A : commutant p (n+2))
    (u w : Word p (n+2)) (hu : u 0 = u 1) (hw : w 0 = w 1)
    (hm : odd (u 0) ↔ ¬ odd (w 0)) : A.val u w = 0 := by
  let σ := Equiv.swap (0 : Fin (n+2)) 1
  have h := congrArg (fun B : Matrix (Word p (n+2)) (Word p (n+2)) ℂ =>
    B (wordPerm σ u) w) (A.property σ)
  rw [mul_signed_entry, signed_mul_entry,
    wordPerm_swap01_of_equal u hu, wordPerm_swap01_of_equal w hw] at h
  dsimp [σ] at h
  rw [phase_swap01, phase_swap01, ← hu, ← hw] at h
  by_cases ho : odd (u 0)
  · have hw' : ¬ odd (w 0) := hm.mp ho
    simp only [ho, hw', and_self, ↓reduceIte, mul_one, neg_one_mul] at h
    linear_combination (1/2 : ℂ)*h
  · have hw' : odd (w 0) := Classical.byContradiction (fun hh => ho (hm.mpr hh))
    simp only [ho, hw', and_self, ↓reduceIte, one_mul, mul_neg_one] at h
    linear_combination (-1/2 : ℂ)*h

/- An explicit two-point transporter, avoiding any unproved transitivity
principle or choice of ordering of the other positions. -/
lemma exists_perm_pair {X : Type*} [DecidableEq X] (a b c d : X)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : Equiv.Perm X, g a = c ∧ g b = d := by
  let s := Equiv.swap a c
  have hs : s b ≠ c := by
    intro h
    have he : s a = c := by simp [s]
    exact hab (s.injective (he.trans h.symm))
  refine ⟨Equiv.swap (s b) d * s, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    have he : s a = c := by simp [s]
    rw [he, Equiv.swap_apply_of_ne_of_ne hs.symm hcd]
  · simp

/- All repeated parity-mismatched pair symbols are impossible, at arbitrary
positions. Distinct mismatched symbols will therefore account for every
exceptional slot in the postselection argument. -/
theorem commutant_entry_zero_repeated_mismatch {p l : ℕ} (A : commutant p l)
    (u w : Word p l) (i j : Fin l) (hij : i ≠ j) (hu : u i = u j) (hw : w i = w j)
    (hm : odd (u i) ↔ ¬ odd (w i)) : A.val u w = 0 := by
  have hl : 2 ≤ l := by
    have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hi := i.isLt
    have hj := j.isLt
    omega
  obtain ⟨n, rfl⟩ : ∃ n, l = n+2 := ⟨l-2, by omega⟩
  obtain ⟨g,hi,hj⟩ := exists_perm_pair i j (0 : Fin (n+2)) 1 hij (by simp)
  let u' := wordPerm g u
  let w' := wordPerm g w
  have hue (x : Fin (n+2)) : u' (g x) = u x := by simp [u',wordPerm]
  have hwe (x : Fin (n+2)) : w' (g x) = w x := by simp [w',wordPerm]
  have hui : u' 0 = u i := hi ▸ hue i
  have huj : u' 1 = u j := hj ▸ hue j
  have hwi : w' 0 = w i := hi ▸ hwe i
  have hwj : w' 1 = w j := hj ▸ hwe j
  have hz : A.val u' w' = 0 := by
    apply commutant_entry_zero_adjacent_mismatch A u' w'
    · exact hui.trans (hu.trans huj.symm)
    · exact hwi.trans (hw.trans hwj.symm)
    · simpa [hui,hwi] using hm
  have hz' := commutant_zero_transport A g⁻¹ hz
  simpa [u',w',wordPerm] using hz'
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
/- Exceptional slots of a vectorized commuting matrix. -/
def mismatchSlots {p l : ℕ} (u w : Word p l) : Finset (Fin l) :=
  Finset.univ.filter (fun i => odd (u i) ↔ ¬ odd (w i))

/- The exclusion bound needed for even-density postselection. The coarse
constant four rather than two is harmless in the source's absolute Cp² error. -/
theorem mismatchSlots_card_le {p l : ℕ} (A : commutant p l)
    (u w : Word p l) (hne : A.val u w ≠ 0) :
    (mismatchSlots u w).card ≤ (2*p)*(2*p) := by
  classical
  let f : {i // i ∈ mismatchSlots u w} → Letter p × Letter p := fun i => (u i.val,w i.val)
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hij
    apply hne
    exact commutant_entry_zero_repeated_mismatch A u w i.val j.val hij
      (congrArg Prod.fst he) (congrArg Prod.snd he) (Finset.mem_filter.mp i.property).2
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using hc
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
/- The actual Koszul regrouping phase from (V⊗V̄)^⊗l to
V^⊗l⊗V̄^⊗l. It will cancel, not be dropped, under partial trace. -/
def regroupPhase {p l : ℕ} (u w : Word p l) : ℂ :=
  ∏ ij ∈ Equiv.Perm.finPairsLT l,
    if odd (u ij.1) ∧ odd (w ij.2) then (-1 : ℂ) else 1

lemma phase_square {p l : ℕ} (σ : Equiv.Perm (Fin l)) (u : Word p l) :
    phase σ u * phase σ u = 1 := by
  simpa only [phase,star_pow,star_neg,star_one] using phase_star_mul σ u

lemma regroupPhase_square {p l : ℕ} (u w : Word p l) :
    regroupPhase u w * regroupPhase u w = 1 := by
  unfold regroupPhase
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro ij _
  split_ifs <;> norm_num

lemma regroupPhase_star {p l : ℕ} (u w : Word p l) :
    star (regroupPhase u w) = regroupPhase u w := by
  unfold regroupPhase
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro ij _
  split_ifs <;> simp

/- Permutations of the matched slots have no residual super-sign after
literal Koszul regrouping; the positions of mismatched symbols are fixed. -/
theorem regroupPhase_permute {p l : ℕ} (σ : Equiv.Perm (Fin l)) (u w : Word p l)
    (hfix : ∀ i, (odd (u i) ↔ ¬ odd (w i)) → σ i = i) :
    regroupPhase (wordPerm σ u) (wordPerm σ w) * phase σ u * phase σ w =
      regroupPhase u w := by
  unfold regroupPhase
  rw [phase_prod,phase_prod]
  have hreindex :
      (∏ ij ∈ Equiv.Perm.finPairsLT l,
        (if odd (wordPerm σ u ij.1) ∧ odd (wordPerm σ w ij.2) then (-1 : ℂ) else 1)) =
      ∏ ij ∈ Equiv.Perm.finPairsLT l,
        (if odd (wordPerm σ u (Equiv.Perm.signBijAux σ ij).1) ∧
          odd (wordPerm σ w (Equiv.Perm.signBijAux σ ij).2) then (-1 : ℂ) else 1) := by
    symm
    exact Finset.prod_nbij (Equiv.Perm.signBijAux σ)
      Equiv.Perm.signBijAux_mem Equiv.Perm.signBijAux_injOn
      Equiv.Perm.signBijAux_surj (fun _ _ => rfl)
  rw [hreindex,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  rintro ⟨i,j⟩ hij
  have hji : j < i := Equiv.Perm.mem_finPairsLT.mp hij
  have hne : σ j ≠ σ i := σ.injective.ne hji.ne
  by_cases ht : σ j < σ i
  · simp [Equiv.Perm.signBijAux,wordPerm,ht,ht.not_gt]
  · have ht' : σ i < σ j := lt_of_le_of_ne (le_of_not_gt ht) hne.symm
    have hm : ¬ ((odd (u i) ↔ ¬ odd (w i)) ∧ (odd (u j) ↔ ¬ odd (w j))) := by
      rintro ⟨hi,hj⟩
      have hi' := hfix i hi
      have hj' := hfix j hj
      rw [hi',hj'] at ht'
      exact hji.not_gt ht'
    by_cases hui : odd (u i) <;> by_cases huj : odd (u j) <;>
      by_cases hwi : odd (w i) <;> by_cases hwj : odd (w j) <;>
      simp [Equiv.Perm.signBijAux,wordPerm,ht,ht',hui,huj,hwi,hwj] at hm ⊢

lemma commutant_transport {p l : ℕ} (A : commutant p l) (σ : Equiv.Perm (Fin l))
    (u w : Word p l) :
    A.val (wordPerm σ u) (wordPerm σ w) = phase σ u * phase σ w * A.val u w := by
  have hh := congrArg (fun B : Matrix (Word p l) (Word p l) ℂ => B (wordPerm σ u) w)
    (A.property σ)
  rw [mul_signed_entry,signed_mul_entry] at hh
  calc
    _ = (A.val (wordPerm σ u) (wordPerm σ w) * phase σ w) * phase σ w := by
      rw [mul_assoc,phase_square,mul_one]
    _ = (phase σ u * A.val u w) * phase σ w := by rw [hh]
    _ = _ := by ring

/- Rephased purification components are ordinary symmetric on the free,
matched-pair slots, a proved conclusion from the signed commutant relation. -/
theorem regrouped_commutant_invariant {p l : ℕ} (A : commutant p l)
    (σ : Equiv.Perm (Fin l)) (u w : Word p l)
    (hfix : ∀ i, (odd (u i) ↔ ¬ odd (w i)) → σ i = i) :
    regroupPhase (wordPerm σ u) (wordPerm σ w) *
        A.val (wordPerm σ u) (wordPerm σ w) = regroupPhase u w * A.val u w := by
  rw [commutant_transport]
  calc
    _ = (regroupPhase (wordPerm σ u) (wordPerm σ w) * phase σ u * phase σ w) * A.val u w := by ring
    _ = _ := by rw [regroupPhase_permute σ u w hfix]

/- Equal local parities in the system copies give equal regrouping signs.
This is what justifies cancellation under the actual auxiliary partial trace. -/
lemma regroupPhase_of_same_parity {p l : ℕ} (u u' w : Word p l)
    (h : ∀ i, odd (u i) ↔ odd (u' i)) : regroupPhase u w = regroupPhase u' w := by
  unfold regroupPhase
  apply Finset.prod_congr rfl
  intro ij _
  rw [h ij.1]
end CoordinateSweeps.SignedTensor

end
open scoped Matrix.Norms.L2Operator

end OAI
