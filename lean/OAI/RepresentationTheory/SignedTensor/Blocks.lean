import Mathlib
import OAI.RepresentationTheory.SignedTensor.Domination

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace CoordinateSweeps.SignedTensor
variable {B : Type} [Fintype B] [DecidableEq B]

/- Tensorization of finite density domination, preserving
finite probability normalization and the exact product of local dimensions. -/
theorem finite_block_density_domination (s p : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (l : B → ℕ) (hl : ∀ i, l i ≤ s) (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (l i)))) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (r : K → B → EvenDensity p),
      (((∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(Fintype.card B*(41*p^2))) •
        ((Fintype.card K : ℂ)⁻¹ • ∑ x, DependentTensor.tensor (fun i => densityPower (l i) (r x i).val))-
          DependentTensor.tensor (fun i => isotypic (p := p) (ρ i))).PosSemidef := by
  choose K fK nK r hr using fun i => finite_density_domination s p (l i) hp hps (hl i) (ρ i)
  let : ∀ i, Fintype (K i) := fK
  let : ∀ i, Nonempty (K i) := nK
  refine ⟨(∀ i, K i),inferInstance,inferInstance,fun x i => r i (x i),?_⟩
  have hh := DependentTensor.tensor_mono
    (fun i => isotypic (p := p) (ρ i))
    (fun i => (((ρ i).dimension : ℂ)*((s+1 : ℕ) : ℂ)^(41*p^2)) •
      ((Fintype.card (K i) : ℂ)⁻¹ • ∑ x, densityPower (l i) (r i x).val))
    (fun i => isotypic_posSemidef (ρ i)) hr
  rw [DependentTensor.tensor_smul] at hh
  have hm : DependentTensor.tensor (fun i => (Fintype.card (K i) : ℂ)⁻¹ •
      ∑ x, densityPower (l i) (r i x).val) =
      (Fintype.card (∀ i, K i) : ℂ)⁻¹ • ∑ x : ∀ i, K i,
        DependentTensor.tensor (fun i => densityPower (l i) (r i (x i)).val) := by
    simp only [Finset.smul_sum]
    rw [DependentTensor.tensor_mixture]
    rw [Fintype.card_pi,Nat.cast_prod,Finset.prod_inv_distrib]
  have hc : (∏ i, ((ρ i).dimension : ℂ)*((s+1 : ℕ) : ℂ)^(41*p^2)) =
      (∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(Fintype.card B*(41*p^2)) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,← pow_mul,mul_comm (41*p^2)]
  rwa [hm,hc] at hh

end CoordinateSweeps.SignedTensor

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.OrderedBlocks
variable {r : ℕ} (n : Fin r → ℕ)

def offset (i : Fin r) : ℕ := ∑ j ∈ Finset.Iio i, n j

lemma offset_next_le (i j : Fin r) (hij : i < j) : offset n i+n i ≤ offset n j := by
  have he : Finset.Iic i=insert i (Finset.Iio i) := by ext x; simp [le_iff_lt_or_eq,or_comm]
  have hh : ∑ k ∈ Finset.Iic i, n k ≤ ∑ k ∈ Finset.Iio j, n k :=
    Finset.sum_le_sum_of_subset (fun k hk => Finset.mem_Iio.mpr (lt_of_le_of_lt (Finset.mem_Iic.mp hk) hij))
  rw [he,Finset.sum_insert (by simp)] at hh
  simpa only [offset,add_comm] using hh

lemma offset_next_le_total (i : Fin r) : offset n i+n i ≤ ∑ j, n j := by
  have he : Finset.Iic i=insert i (Finset.Iio i) := by ext x; simp [le_iff_lt_or_eq,or_comm]
  have hh : ∑ k ∈ Finset.Iic i, n k ≤ ∑ k, n k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [he,Finset.sum_insert (by simp)] at hh
  simpa only [offset,add_comm] using hh

def encode (x : (i : Fin r) × Fin (n i)) : Fin (∑ i, n i) :=
  ⟨offset n x.1+x.2,lt_of_lt_of_le (Nat.add_lt_add_left x.2.isLt _) (offset_next_le_total n x.1)⟩

lemma encode_lt_of_block {i j : Fin r} (hij : i < j) (a : Fin (n i)) (b : Fin (n j)) :
    encode n ⟨i,a⟩ < encode n ⟨j,b⟩ := by
  change offset n i+a.val < offset n j+b.val
  have hh := offset_next_le n i j hij
  have ha := a.isLt
  omega

lemma encode_lt_same {i : Fin r} (a b : Fin (n i)) :
    encode n ⟨i,a⟩ < encode n ⟨i,b⟩ ↔ a < b := by
  change offset n i+a.val < offset n i+b.val ↔ a.val < b.val
  omega

lemma encode_injective : Function.Injective (encode n) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hi : i=j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((ne_of_lt (encode_lt_of_block n hij a b)) h)
    · exact hij
    · exact False.elim ((ne_of_lt (encode_lt_of_block n hij b a)) h.symm)
  subst j
  have hab : a=b := Fin.ext (by have hh := congrArg Fin.val h; dsimp [encode] at hh; omega)
  subst b
  rfl

/- Explicit contiguous coordinate chart, including zero-length blocks. -/
def positions : ((i : Fin r) × Fin (n i)) ≃ Fin (∑ i, n i) :=
  Equiv.ofBijective (encode n) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨encode_injective n,by simp [Fintype.card_sigma]⟩)

lemma positions_apply (x : (i : Fin r) × Fin (n i)) : positions n x=encode n x := rfl

lemma positions_lt_of_block {i j : Fin r} (hij : i < j) (a : Fin (n i)) (b : Fin (n j)) :
    positions n ⟨i,a⟩ < positions n ⟨j,b⟩ := encode_lt_of_block n hij a b

lemma positions_lt_same {i : Fin r} (a b : Fin (n i)) :
    positions n ⟨i,a⟩ < positions n ⟨i,b⟩ ↔ a < b := encode_lt_same n a b

def perm (σ : ∀ i, Equiv.Perm (Fin (n i))) : Equiv.Perm (Fin (∑ i, n i)) :=
  (positions n).permCongr (Equiv.sigmaCongrRight σ)

@[simp] lemma perm_apply (σ : ∀ i, Equiv.Perm (Fin (n i))) (i : Fin r) (j : Fin (n i)) :
    perm n σ (positions n ⟨i,j⟩)=positions n ⟨i,σ i j⟩ := by
  simp [perm,Equiv.permCongr_apply]

lemma perm_inv (σ : ∀ i, Equiv.Perm (Fin (n i))) :
    (perm n σ)⁻¹=perm n (fun i => (σ i)⁻¹) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,j⟩,rfl⟩ := (positions n).surjective x
  apply (perm n σ).injective
  simp

def permHom : (∀ i, Equiv.Perm (Fin (n i))) →* Equiv.Perm (Fin (∑ i, n i)) where
  toFun := perm n
  map_one' := by
    apply Equiv.ext; intro x
    obtain ⟨⟨i,j⟩,rfl⟩ := (positions n).surjective x
    simp
  map_mul' σ τ := by
    apply Equiv.ext; intro x
    obtain ⟨⟨i,j⟩,rfl⟩ := (positions n).surjective x
    simp

end CoordinateSweeps.OrderedBlocks

namespace CoordinateSweeps.SignedTensor

lemma phase_double_prod {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l) :
    phase σ w=∏ i : Fin l, ∏ j : Fin l,
      if j < i ∧ odd (w i) ∧ odd (w j) ∧ σ i < σ j then (-1 : ℂ) else 1 := by
  have he : Equiv.Perm.finPairsLT l=(Finset.univ : Finset ((i : Fin l) × Fin l)).filter (fun x => x.2 < x.1) := by
    ext x
    simp only [Equiv.Perm.mem_finPairsLT,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [phase_prod,he,Finset.prod_filter,Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  split_ifs <;> simp_all

def blockPerm {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m+n)) := finSumFinEquiv.permCongr (Equiv.Perm.sumCongr σ τ)

@[simp] lemma blockPerm_left {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) (i : Fin m) :
    blockPerm σ τ (Fin.castAdd n i)=Fin.castAdd n (σ i) := by
  simp [blockPerm,Equiv.permCongr_apply]

@[simp] lemma blockPerm_right {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    blockPerm σ τ (Fin.natAdd m i)=Fin.natAdd m (τ i) := by
  simp [blockPerm,Equiv.permCongr_apply]

lemma blockPerm_inv {m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    (blockPerm σ τ)⁻¹=blockPerm σ⁻¹ τ⁻¹ := by
  apply Equiv.ext
  intro i
  apply (blockPerm σ τ).injective
  induction i using Fin.addCases <;> simp

lemma phase_blockPerm {p m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (w : Word p (m+n)) :
    phase (blockPerm σ τ) w=phase σ (fun i => w (Fin.castAdd n i))*
      phase τ (fun i => w (Fin.natAdd m i)) := by
  have hlr (i : Fin m) (j : Fin n) : ¬ Fin.natAdd m j<Fin.castAdd n i := by
    simp only [Fin.lt_def,Fin.val_natAdd,Fin.val_castAdd]
    omega
  have hll (i j : Fin m) : Fin.castAdd n i<Fin.castAdd n j ↔ i<j := Iff.rfl
  have hrr (i j : Fin n) : Fin.natAdd m i<Fin.natAdd m j ↔ i<j := by
    simp only [Fin.lt_def,Fin.val_natAdd,Nat.add_lt_add_iff_left]
  simp only [phase_double_prod]
  rw [Fin.prod_univ_add]
  simp_rw [Fin.prod_univ_add]
  simp only [blockPerm_left,blockPerm_right,hlr,false_and,and_false,ite_false,
    Finset.prod_const_one,mul_one,one_mul,hll,hrr]

/- The explicit unitary reindexing between a concatenated tensor word and
its two block words. The Koszul signs are retained in phase_blockPerm. -/
def splitWord (p m n : ℕ) : Word p (m+n) ≃ Word p m × Word p n where
  toFun w := (fun i => w (Fin.castAdd n i),fun i => w (Fin.natAdd m i))
  invFun w := Fin.addCases w.1 w.2
  left_inv w := by funext i; induction i using Fin.addCases <;> simp
  right_inv w := by ext <;> simp

lemma splitWord_wordPerm {p m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (w : Word p (m+n)) :
    splitWord p m n (wordPerm (blockPerm σ τ) w)=
      (wordPerm σ (splitWord p m n w).1,wordPerm τ (splitWord p m n w).2) := by
  ext i <;> simp [splitWord,wordPerm,blockPerm_inv]

def blockMatrix {p m n : ℕ} (A : Matrix (Word p m) (Word p m) ℂ)
    (B : Matrix (Word p n) (Word p n) ℂ) : Matrix (Word p (m+n)) (Word p (m+n)) ℂ :=
  fun u w => A (splitWord p m n u).1 (splitWord p m n w).1 *
    B (splitWord p m n u).2 (splitWord p m n w).2

/- Exact block multiplicativity of the signed permutation action. -/
theorem matrix_blockPerm {p m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    matrix (p := p) (blockPerm σ τ)=blockMatrix (matrix σ) (matrix τ) := by
  ext u w
  have he : u=wordPerm (blockPerm σ τ) w ↔
      (splitWord p m n u).1=wordPerm σ (splitWord p m n w).1 ∧
      (splitWord p m n u).2=wordPerm τ (splitWord p m n w).2 := by
    rw [← (splitWord p m n).injective.eq_iff,splitWord_wordPerm,Prod.mk.injEq]
  simp only [matrix,blockMatrix,he,phase_blockPerm]
  split_ifs <;> simp_all [splitWord]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks
variable {p r : ℕ} (n : Fin r → ℕ)

lemma prod_positions (f : Fin (∑ i, n i) → ℂ) :
    ∏ x, f x=∏ i, ∏ j : Fin (n i), f (positions n ⟨i,j⟩) := by
  rw [← Equiv.prod_comp (positions n) f,Fintype.prod_sigma]

lemma phase_grouped (σ : ∀ i, Equiv.Perm (Fin (n i))) (w : Word p (∑ i, n i)) :
    phase (perm n σ) w=∏ i, phase (σ i) (fun j => w (positions n ⟨i,j⟩)) := by
  rw [phase_double_prod,prod_positions n]
  apply Finset.prod_congr rfl
  intro i hi
  rw [phase_double_prod]
  apply Finset.prod_congr rfl
  intro a ha
  rw [prod_positions n,Finset.prod_eq_single i]
  · apply Finset.prod_congr rfl
    intro b hb
    simp only [perm_apply,positions_lt_same]
  · intro j hj hji
    apply Finset.prod_eq_one
    intro b hb
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hn : ¬ positions n ⟨i,σ i a⟩ < positions n ⟨j,σ j b⟩ :=
        not_lt_of_ge (positions_lt_of_block n hlt _ _).le
      simp [hn]
    · have hn : ¬ positions n ⟨j,b⟩ < positions n ⟨i,a⟩ :=
        not_lt_of_ge (positions_lt_of_block n hgt _ _).le
      simp [hn]
  · simp

def groupWord (p : ℕ) : Word p (∑ i, n i) ≃ (∀ i, Word p (n i)) where
  toFun w i j := w (positions n ⟨i,j⟩)
  invFun w x := w ((positions n).symm x).1 ((positions n).symm x).2
  left_inv w := by funext x; simp
  right_inv w := by
    funext i j
    change (fun x : (i : Fin r) × Fin (n i) => w x.1 x.2) ((positions n).symm (positions n ⟨i,j⟩)) = _
    rw [Equiv.symm_apply_apply]

lemma groupWord_wordPerm (σ : ∀ i, Equiv.Perm (Fin (n i))) (w : Word p (∑ i, n i)) :
    groupWord n p (wordPerm (perm n σ) w)=fun i => wordPerm (σ i) (groupWord n p w i) := by
  funext i j
  simp [groupWord,wordPerm,perm_inv]

/- Genuine product-subgroup action, with no suppressed Koszul signs. -/
theorem matrix_grouped (σ : ∀ i, Equiv.Perm (Fin (n i))) :
    matrix (p := p) (perm n σ)=
      Matrix.reindex (groupWord n p).symm (groupWord n p).symm
        (DependentTensor.tensor (fun i => matrix (σ i))) := by
  ext u w
  have he : u=wordPerm (perm n σ) w ↔
      ∀ i, groupWord n p u i=wordPerm (σ i) (groupWord n p w i) := by
    rw [← (groupWord n p).injective.eq_iff,groupWord_wordPerm]
    exact funext_iff
  change (if u=wordPerm (perm n σ) w then phase (perm n σ) w else 0)=
    ∏ i, if groupWord n p u i=wordPerm (σ i) (groupWord n p w i)
      then phase (σ i) (groupWord n p w i) else 0
  simp only [he]
  by_cases h : ∀ i, groupWord n p u i=wordPerm (σ i) (groupWord n p w i)
  · rw [ite_eq_left h,phase_grouped]
    simp only [h,ite_true]
    rfl
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks UnitaryIrrep
variable {p r : ℕ} (n : Fin r → ℕ)

/- The subgroup operator is an actual group-algebra average on the full set
of slots, not an operator posited to factor. -/
def groupedAverage {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    Matrix (Word p (∑ i, n i)) (Word p (∑ i, n i)) ℂ :=
  averageMatrix (action p (∑ i, n i)) (fun ω : ∀ i, Ω i => ∏ i, w i (ω i))
    (fun ω => perm n (fun i => g i (ω i)))

lemma groupedAverage_factor {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    groupedAverage (p := p) n w g=
      Matrix.reindex (groupWord n p).symm (groupWord n p).symm
        (DependentTensor.tensor (fun i => averageMatrix (action p (n i)) (w i) (g i))) := by
  ext u v
  simp only [groupedAverage,averageMatrix,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_symm,DependentTensor.tensor,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  change (∑ ω : ∀ i, Ω i, (∏ i, w i (ω i))*
    matrix (perm n (fun i => g i (ω i))) u v)=
      ∏ i, ∑ ω : Ω i, w i ω*matrix (g i ω) (groupWord n p u i) (groupWord n p v i)
  have he (σ : ∀ i, Equiv.Perm (Fin (n i))) :
      matrix (perm n σ) u v=∏ i, matrix (σ i) (groupWord n p u i) (groupWord n p v i) := by
    have hh := congrArg (fun A : Matrix (Word p (∑ i, n i)) (Word p (∑ i, n i)) ℂ => A u v)
      (matrix_grouped (p := p) n σ)
    exact hh
  simp only [he]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  exact (Finset.prod_mul_distrib :
    (∏ i, w i (ω i)*matrix (g i (ω i)) (groupWord n p u i) (groupWord n p v i))=_).symm

def groupedProjector (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    Matrix (Word p (∑ i, n i)) (Word p (∑ i, n i)) ℂ :=
  groupedAverage n (fun i => (ρ i).coefficient) (fun _ => id)

lemma groupedProjector_factor (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    groupedProjector (p := p) n ρ=
      Matrix.reindex (groupWord n p).symm (groupWord n p).symm
        (DependentTensor.tensor (fun i => (ρ i).projector (action p (n i)))) := by
  exact groupedAverage_factor n _ _

lemma matrix_trace_reindex {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y)
    (A : Matrix X X ℂ) : Matrix.trace (Matrix.reindex e e A)=Matrix.trace A := by
  exact Equiv.sum_comp e.symm (fun i => A i i)

lemma reindex_moment {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (A : Matrix X X ℂ) (q : ℕ) :
    Matrix.trace ((((Matrix.reindexAlgEquiv ℂ ℂ e A).conjTranspose)*(Matrix.reindexAlgEquiv ℂ ℂ e A))^q)=
      Matrix.trace ((A.conjTranspose*A)^q) := by
  have hs : (Matrix.reindexAlgEquiv ℂ ℂ e A).conjTranspose=
      Matrix.reindexAlgEquiv ℂ ℂ e A.conjTranspose := by ext i j; rfl
  rw [hs,← map_mul,← map_pow]
  exact matrix_trace_reindex e _

/- Exact isotypic child moment factorization, including the true Hom
multiplicities and all zero-length blocks. -/
theorem grouped_projected_moment {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i)))
    {q : ℕ} (hq : q ≠ 0) :
    Matrix.trace (((groupedProjector (p := p) n ρ*groupedAverage n w g).conjTranspose*
      (groupedProjector n ρ*groupedAverage n w g))^q)=
      ∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
        (matrixRepresentation (action p (n i)))) : ℂ)*
        Matrix.trace (((averageMatrix (ρ i).matrix (w i) (g i)).conjTranspose*
          averageMatrix (ρ i).matrix (w i) (g i))^q) := by
  rw [groupedProjector_factor,groupedAverage_factor]
  let e := (groupWord n p).symm
  change Matrix.trace (((Matrix.reindexAlgEquiv ℂ ℂ e _*Matrix.reindexAlgEquiv ℂ ℂ e _).conjTranspose*
    (Matrix.reindexAlgEquiv ℂ ℂ e _*Matrix.reindexAlgEquiv ℂ ℂ e _))^q)=_
  rw [← map_mul,reindex_moment,← DependentTensor.tensor_mul,DependentTensor.tensor_moment]
  apply Finset.prod_congr rfl
  intro i hi
  exact (ρ i).projected_operator_moment _ (fun σ => (matrix_inv σ).symm) (w i) (g i) hq

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p : ℕ}

def IsEven (A : Matrix (Letter p) (Letter p) ℂ) : Prop :=
  ∀ i j, (odd i ↔ ¬ odd j) → A i j=0

def grading (p : ℕ) : Matrix (Letter p) (Letter p) ℂ :=
  Matrix.diagonal (fun i => if odd i then 1 else 0)

lemma isEven_iff_commute (A : Matrix (Letter p) (Letter p) ℂ) :
    IsEven A ↔ Commute A (grading p) := by
  constructor
  · intro h
    show A*grading p=grading p*A
    ext i j
    simp only [grading,Matrix.mul_diagonal,Matrix.diagonal_mul]
    by_cases hi : odd i
    · by_cases hj : odd j
      · simp [hi,hj]
      · simp [hi,hj,h i j (by tauto)]
    · by_cases hj : odd j
      · simp [hi,hj,h i j (by tauto)]
      · simp [hi,hj]
  · intro h i j hij
    have hh := congrArg (fun M : Matrix (Letter p) (Letter p) ℂ => M i j) h.eq
    simp only [grading,Matrix.mul_diagonal,Matrix.diagonal_mul] at hh
    by_cases hi : odd i
    · have hj : ¬ odd j := hij.mp hi
      simpa [hi,hj] using hh.symm
    · have hj : odd j := by tauto
      simpa [hi,hj] using hh

lemma isEven_add {A B : Matrix (Letter p) (Letter p) ℂ} (hA : IsEven A) (hB : IsEven B) :
    IsEven (A+B) := by intro i j hij; simp only [Matrix.add_apply,hA i j hij,hB i j hij,add_zero]

lemma isEven_smul (c : ℂ) {A : Matrix (Letter p) (Letter p) ℂ} (hA : IsEven A) :
    IsEven (c • A) := by intro i j hij; simp only [Matrix.smul_apply,smul_eq_mul,hA i j hij,mul_zero]

lemma isEven_sum {I : Type*} [Fintype I] (A : I → Matrix (Letter p) (Letter p) ℂ)
    (hA : ∀ i, IsEven (A i)) : IsEven (∑ i, A i) := by
  intro i j hij
  simp only [Matrix.sum_apply]
  exact Finset.sum_eq_zero (fun a _ => hA a i j hij)

lemma isEven_one : IsEven (1 : Matrix (Letter p) (Letter p) ℂ) := by
  intro i j hij
  apply Matrix.one_apply_ne
  intro he
  subst j
  tauto

lemma densityPower_commute_of_even {l : ℕ} (r : Matrix (Letter p) (Letter p) ℂ)
    (hr : IsEven r) (σ : Equiv.Perm (Fin l)) :
    matrix σ*densityPower l r=densityPower l r*matrix σ := by
  have hpar {u w : Word p l} (h : densityPower l r u w ≠ 0) :
      ∀ i, odd (u i) ↔ odd (w i) := by
    intro i
    have he : r (u i) (w i) ≠ 0 := (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ _)
    by_contra hn
    exact he (hr _ _ (by tauto))
  ext u w
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single ((wordPerm σ).symm u),Finset.sum_eq_single (wordPerm σ w)]
  · simp only [(wordPerm σ).apply_symm_apply,ite_true]
    have hd : densityPower l r u (wordPerm σ w)=densityPower l r ((wordPerm σ).symm u) w := by
      simpa using densityPower_permute σ r ((wordPerm σ).symm u) w
    rw [hd]
    by_cases hn : densityPower l r ((wordPerm σ).symm u) w=0
    · simp [hn]
    · rw [phase_eq_of_parity σ _ _ (hpar hn),mul_comm]
  · intro v hv hne; simp [hne]
  · simp
  · intro v hv hne
    have hh : u ≠ wordPerm σ v := by
      intro he
      exact hne ((Equiv.eq_symm_apply _).mpr he.symm)
    simp [hh]
  · simp

lemma densityPower_commute_lift {l : ℕ} (r : Matrix (Letter p) (Letter p) ℂ)
    (hr : IsEven r) (x : MonoidAlgebra ℂ (Equiv.Perm (Fin l))) :
    (MonoidAlgebra.lift ℂ _ _ (action p l) x)*densityPower l r =
      densityPower l r*(MonoidAlgebra.lift ℂ _ _ (action p l) x) := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simpa [action] using densityPower_commute_of_even r hr g
  | add x y hx hy => simp only [map_add,add_mul,mul_add,hx,hy]
  | smul c x hx => simp only [map_smul,smul_mul_assoc,mul_smul_comm,hx]

/- Constructed even whitening of the regularized empirical row density. -/
theorem exists_even_whitening {R : Type*} [Fintype R] [Nonempty R]
    (r : R → EvenDensity p) {ε : ℝ} (hε : 0 < ε) :
    let B := (Fintype.card R : ℂ)⁻¹ • ∑ i, (r i).val + (ε : ℂ) • (1 : Matrix (Letter p) (Letter p) ℂ)
    ∃ A : Matrix (Letter p) (Letter p) ℂ, A.PosSemidef ∧ IsEven A ∧ A*B*A=1 ∧
      ((Fintype.card R : ℂ) • (1 : Matrix (Letter p) (Letter p) ℂ)-
        ∑ i, A*(r i).val*A).PosSemidef := by
  dsimp only
  let B := (Fintype.card R : ℂ)⁻¹ • ∑ i, (r i).val + (ε : ℂ) • (1 : Matrix (Letter p) (Letter p) ℂ)
  have hBp : B.PosDef := TensorBoard.average_regularization_posDef (fun i => (r i).val)
    (fun i => (r i).property.1) hε
  have hBe : IsEven B := isEven_add (isEven_smul _ (isEven_sum _ (fun i => (r i).property.2.2)))
    (isEven_smul _ isEven_one)
  obtain ⟨A,hA,hABA,hcomm⟩ := TensorBoard.exists_whitening B hBp
  refine ⟨A,hA,(isEven_iff_commute A).mpr (hcomm _ ((isEven_iff_commute B).mp hBe)),hABA,?_⟩
  apply TensorBoard.whitening_sum_bound _ B A hA.isHermitian hABA
  dsimp [B]
  convert (Matrix.PosSemidef.one (n := Letter p) (R := ℂ)).smul hε.le using 1
  module

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p l : ℕ}

/- Even inhomogeneous site tensors transform by the *signed* permutation
matrix with no residual phase. This is what permits regrouping deleted rows
and columns without identifying the two Koszul charts by an unsigned map. -/
lemma tensor_covariance (A : Fin l → Matrix (Letter p) (Letter p) ℂ)
    (hA : ∀ i, IsEven (A i)) (σ : Equiv.Perm (Fin l)) :
    matrix σ*TensorBoard.tensor A=
      TensorBoard.tensor (fun i => A (σ⁻¹ i))*matrix σ := by
  have hpar {u w : Word p l} (h : TensorBoard.tensor A u w ≠ 0) :
      ∀ i, odd (u i) ↔ odd (w i) := by
    intro i
    have he : A i (u i) (w i) ≠ 0 := (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ _)
    by_contra hn
    exact he (hA i _ _ (by tauto))
  ext u w
  simp only [Matrix.mul_apply,matrix]
  rw [Finset.sum_eq_single ((wordPerm σ).symm u),Finset.sum_eq_single (wordPerm σ w)]
  · simp only [(wordPerm σ).apply_symm_apply,ite_true]
    have hd : TensorBoard.tensor (fun i => A (σ⁻¹ i)) u (wordPerm σ w)=
        TensorBoard.tensor A ((wordPerm σ).symm u) w := by
      change (∏ i, A (σ⁻¹ i) (u i) (w (σ⁻¹ i)))=∏ i, A i (u (σ i)) (w i)
      simpa using (Equiv.prod_comp σ (fun i => A (σ⁻¹ i) (u i) (w (σ⁻¹ i)))).symm
    rw [hd]
    by_cases hn : TensorBoard.tensor A ((wordPerm σ).symm u) w=0
    · simp [hn]
    · rw [phase_eq_of_parity σ _ _ (hpar hn),mul_comm]
  · intro v hv hne; simp [hne]
  · simp
  · intro v hv hne
    have hh : u ≠ wordPerm σ v := by
      intro he
      exact hne ((Equiv.eq_symm_apply _).mpr he.symm)
    simp [hh]
  · simp

lemma tensor_signed_conjugate (A : Fin l → Matrix (Letter p) (Letter p) ℂ)
    (hA : ∀ i, IsEven (A i)) (σ : Equiv.Perm (Fin l)) :
    matrix σ*TensorBoard.tensor A*(matrix σ).conjTranspose=
      TensorBoard.tensor (fun i => A (σ⁻¹ i)) := by
  rw [tensor_covariance A hA σ,mul_assoc,← matrix_inv,← matrix_mul,mul_inv_cancel,matrix_one,mul_one]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks
variable {p r : ℕ} (n : Fin r → ℕ)

def groupedSite (a : Fin r → EvenDensity p) (k : Fin (∑ i, n i)) : EvenDensity p :=
  a ((positions n).symm k).1

lemma grouped_densityPower (a : Fin r → EvenDensity p) :
    (DependentTensor.tensor (fun i => densityPower (n i) (a i).val)).submatrix
      (groupWord n p) (groupWord n p)=TensorBoard.tensor (fun k => (groupedSite n a k).val) := by
  ext u v
  change (∏ i, ∏ j : Fin (n i), (a i).val (u (positions n ⟨i,j⟩)) (v (positions n ⟨i,j⟩)))=
    ∏ k, (a ((positions n).symm k).1).val (u k) (v k)
  rw [prod_positions]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  rw [Equiv.symm_apply_apply]

/- Literal contiguous-block projectors are dominated by independent finite
mixtures of even site densities, with all local dimension factors. -/
theorem finite_grouped_density_domination (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hn : ∀ i, n i ≤ s) (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (a : K → Fin r → EvenDensity p),
      (((∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(r*(41*p^2))) •
        ((Fintype.card K : ℂ)⁻¹ • ∑ x,
          TensorBoard.tensor (fun k => (groupedSite n (a x) k).val))-
          groupedProjector (p := p) n ρ).PosSemidef := by
  obtain ⟨K,hK,nK,a,ha⟩ := finite_block_density_domination s p hp hps n hn ρ
  let := hK
  let := nK
  refine ⟨K,hK,nK,a,?_⟩
  have hh := ha.submatrix (groupWord n p)
  have hm : (∑ x, DependentTensor.tensor (fun i => densityPower (n i) (a x i).val)).submatrix
      (groupWord n p) (groupWord n p)=∑ x, TensorBoard.tensor (fun k => (groupedSite n (a x) k).val) := by
    ext u v
    simp only [Matrix.submatrix_apply,Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    exact congrArg (fun M => M u v) (grouped_densityPower n (a x))
  simp only [Fintype.card_fin,Matrix.submatrix_sub,Matrix.submatrix_smul,
    Pi.sub_apply,Pi.smul_apply,hm] at hh
  have he : (DependentTensor.tensor (fun i => isotypic (p := p) (ρ i))).submatrix
      (groupWord n p) (groupWord n p)=groupedProjector (p := p) n ρ := by
    simp only [groupedProjector_factor,isotypic_eq_projector]
    rfl
  rwa [he] at hh

/- The same domination after an arbitrary *signed* change of slot chart. -/
theorem finite_regrouped_density_domination (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hn : ∀ i, n i ≤ s) (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (σ : Equiv.Perm (Fin (∑ i, n i))) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (a : K → Fin r → EvenDensity p),
      (((∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(r*(41*p^2))) •
        ((Fintype.card K : ℂ)⁻¹ • ∑ x,
          TensorBoard.tensor (fun k => (groupedSite n (a x) (σ⁻¹ k)).val))-
          matrix σ*groupedProjector (p := p) n ρ*(matrix σ).conjTranspose).PosSemidef := by
  obtain ⟨K,hK,nK,a,ha⟩ := finite_grouped_density_domination n s hp hps hn ρ
  let := hK
  let := nK
  refine ⟨K,hK,nK,a,?_⟩
  have hh := ha.mul_mul_conjTranspose_same (matrix σ)
  simp only [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sum,Matrix.sum_mul] at hh
  have ht (x : K) : matrix σ*TensorBoard.tensor (fun k => (groupedSite n (a x) k).val)*(matrix σ).conjTranspose=
      TensorBoard.tensor (fun k => (groupedSite n (a x) (σ⁻¹ k)).val) :=
    tensor_signed_conjugate _ (fun k => (groupedSite n (a x) k).property.2.2) σ
  simpa only [ht] using hh

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p r : ℕ} (n : Fin r → ℕ)

lemma groupedProjector_posSemidef (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    (groupedProjector (p := p) n ρ).PosSemidef := by
  rw [groupedProjector_factor]
  exact (DependentTensor.tensor_posSemidef _ (fun i => (ρ i).projector_posSemidef _
    (fun σ => (matrix_inv σ).symm))).submatrix _

lemma groupedProjector_idempotent (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    groupedProjector (p := p) n ρ*groupedProjector n ρ=groupedProjector n ρ := by
  rw [groupedProjector_factor]
  change Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _*
    Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _=Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _
  rw [← map_mul,← DependentTensor.tensor_mul]
  simp only [UnitaryIrrep.projector_idempotent]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks UnitaryIrrep
variable {p r l : ℕ} (n : Fin r → ℕ)

def lengthMatrix {a b : ℕ} (h : a=b) (M : Matrix (Word p a) (Word p a) ℂ) :
    Matrix (Word p b) (Word p b) ℂ := h ▸ M

def ambientProjector (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) : Matrix (Word p l) (Word p l) ℂ :=
  matrix σ*lengthMatrix h (groupedProjector n ρ)*(matrix σ).conjTranspose

def ambientProjectorAlgebra (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) : MonoidAlgebra ℂ (Equiv.Perm (Fin l)) :=
  averageAlgebra (fun ω : ∀ i, Equiv.Perm (Fin (n i)) => ∏ i, (ρ i).coefficient (ω i))
    (fun ω => σ*(Equiv.permCongr (finCongr h) (perm n ω))*σ⁻¹)

lemma ambientProjectorAlgebra_lift (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    MonoidAlgebra.lift ℂ _ _ (action p l) (ambientProjectorAlgebra n h σ ρ)=
      ambientProjector (p := p) n h σ ρ := by
  subst l
  simp only [ambientProjectorAlgebra,lift_averageAlgebra,averageMatrix,ambientProjector,
    lengthMatrix,groupedProjector,groupedAverage,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  change matrix (σ*(Equiv.permCongr (finCongr rfl) (perm n ω))*σ⁻¹)=_
  simp only [finCongr_refl,matrix_mul,matrix_inv]
  rfl

lemma ambientProjector_posSemidef (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    (ambientProjector (p := p) n h σ ρ).PosSemidef := by
  subst l
  exact (groupedProjector_posSemidef n ρ).mul_mul_conjTranspose_same (matrix σ)

lemma ambientProjector_idempotent (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) :
    ambientProjector (p := p) n h σ ρ*ambientProjector n h σ ρ=ambientProjector n h σ ρ := by
  subst l
  unfold ambientProjector lengthMatrix
  calc
    _ = matrix σ*(groupedProjector n ρ*((matrix σ).conjTranspose*matrix σ)*groupedProjector n ρ)*
      (matrix (p := p) σ).conjTranspose := by noncomm_ring
    _ = _ := by rw [matrix_unitary,mul_one,groupedProjector_idempotent]

/- Actual ambient projectors, not hypothesized density mixtures. -/
theorem finite_ambient_density_domination (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hn : ∀ i, n i ≤ s) (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l)) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (a : K → Fin r → EvenDensity p),
      (((∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(r*(41*p^2))) •
        ((Fintype.card K : ℂ)⁻¹ • ∑ x,
          TensorBoard.tensor (fun k => (groupedSite n (a x) ((finCongr h).symm (σ⁻¹ k))).val))-
          ambientProjector (p := p) n h σ ρ).PosSemidef := by
  subst l
  simpa [ambientProjector,lengthMatrix] using
    finite_regrouped_density_domination n s hp hps hn ρ σ

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open OrderedBlocks UnitaryIrrep
variable {p r l : ℕ} (n : Fin r → ℕ)

def ambientAverage (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    Matrix (Word p l) (Word p l) ℂ :=
  averageMatrix (action p l) (fun ω : ∀ i, Ω i => ∏ i, w i (ω i))
    (fun ω => σ*Equiv.permCongr (finCongr h) (perm n (fun i => g i (ω i)))*σ⁻¹)

lemma ambientAverage_factor (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    ambientAverage (p := p) n h σ w g=
      matrix σ*lengthMatrix h (groupedAverage n w g)*(matrix σ).conjTranspose := by
  subst l
  simp only [ambientAverage,averageMatrix,groupedAverage,lengthMatrix,
    Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  change matrix (σ*Equiv.permCongr (finCongr rfl) (perm n (fun i => g i (ω i)))*σ⁻¹)=_
  simp only [finCongr_refl,matrix_mul,matrix_inv]
  rfl

lemma matrix_unitary_reverse (σ : Equiv.Perm (Fin l)) :
    matrix (p := p) σ*(matrix σ).conjTranspose=1 := by
  rw [← matrix_inv,← matrix_mul,mul_inv_cancel,matrix_one]

lemma conjugate_mul {X : Type*} [Fintype X] [DecidableEq X]
    (U A B : Matrix X X ℂ) (hU : U.conjTranspose*U=1) :
    (U*A*U.conjTranspose)*(U*B*U.conjTranspose)=U*(A*B)*U.conjTranspose := by
  calc
    _ = U*A*(U.conjTranspose*U)*B*U.conjTranspose := by noncomm_ring
    _ = _ := by rw [hU,mul_one]; noncomm_ring

lemma conjugate_pow {X : Type*} [Fintype X] [DecidableEq X]
    (U A : Matrix X X ℂ) (hU : U.conjTranspose*U=1) (hU' : U*U.conjTranspose=1) (q : ℕ) :
    (U*A*U.conjTranspose)^q=U*A^q*U.conjTranspose := by
  induction q with
  | zero => simpa using hU'.symm
  | succ q ih => rw [pow_succ,ih,conjugate_mul U _ _ hU,pow_succ]

lemma conjugate_moment {X : Type*} [Fintype X] [DecidableEq X]
    (U A : Matrix X X ℂ) (hU : U.conjTranspose*U=1) (hU' : U*U.conjTranspose=1) (q : ℕ) :
    Matrix.trace (((U*A*U.conjTranspose).conjTranspose*(U*A*U.conjTranspose))^q)=
      Matrix.trace ((A.conjTranspose*A)^q) := by
  have hs : (U*A*U.conjTranspose).conjTranspose=U*A.conjTranspose*U.conjTranspose := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  rw [hs,conjugate_mul U _ _ hU,conjugate_pow U _ hU hU']
  rw [Matrix.trace_mul_cycle,hU,one_mul]

/- The child moment formula survives the literal slot chart, with actual Hom multiplicities. -/
theorem ambient_projected_moment (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i)))
    {q : ℕ} (hq : q ≠ 0) :
    Matrix.trace (((ambientProjector (p := p) n h σ ρ*ambientAverage n h σ w g).conjTranspose*
      (ambientProjector n h σ ρ*ambientAverage n h σ w g))^q)=
      ∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
        (matrixRepresentation (action p (n i)))) : ℂ)*
        Matrix.trace (((averageMatrix (ρ i).matrix (w i) (g i)).conjTranspose*
          averageMatrix (ρ i).matrix (w i) (g i))^q) := by
  subst l
  rw [ambientAverage_factor]
  unfold ambientProjector lengthMatrix
  rw [conjugate_mul _ _ _ (matrix_unitary σ),conjugate_moment _ _
    (matrix_unitary σ) (matrix_unitary_reverse σ)]
  exact grouped_projected_moment n ρ w g hq

end CoordinateSweeps.SignedTensor

/-!
All definitions are finite and use ordinary probability and trace normalizations.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.FiberBlocks
open OrderedBlocks
variable {L : Type*} [Fintype L] {r : ℕ} (f : L → Fin r)

def size (i : Fin r) : ℕ := Fintype.card {x : L // f x=i}
def cards (i : Fin r) : Fin (size f i) ≃ {x : L // f x=i} := (Fintype.equivFin _).symm

/- Contiguous finite label fibers give a genuine ordered slot chart. -/
def slots : Fin (∑ i, size f i) ≃ L :=
  (positions (size f)).symm.trans
    ((Equiv.sigmaCongrRight (cards f)).trans (Equiv.sigmaFiberEquiv f))

lemma total : ∑ i, size f i=Fintype.card L := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (slots f)

lemma label_slots (k : Fin (∑ i, size f i)) :
    f (slots f k)=((positions (size f)).symm k).1 := by
  exact (cards f ((positions (size f)).symm k).1 ((positions (size f)).symm k).2).property

/- The same chart with the literal cardinal as ambient length. -/
def chart : Fin (Fintype.card L) ≃ L :=
  (finCongr (total f).symm).trans (slots f)

/- Permutation changing the contiguous fiber chart to any given ambient chart. -/
def regroup (e : Fin (Fintype.card L) ≃ L) : Equiv.Perm (Fin (Fintype.card L)) :=
  (chart f).trans e.symm

lemma label_regroup (e : Fin (Fintype.card L) ≃ L) (k : Fin (Fintype.card L)) :
    ((positions (size f)).symm ((finCongr (total f)).symm ((regroup f e)⁻¹ k))).1=f (e k) := by
  have he : slots f ((finCongr (total f)).symm ((regroup f e)⁻¹ k))=e k := by
    change chart f ((regroup f e).symm k)=e k
    simp [regroup]
  rw [← label_slots f,he]

end CoordinateSweeps.FiberBlocks

namespace CoordinateSweeps.FiberBlocks
open OrderedBlocks
variable {L : Type*} [Fintype L] {r : ℕ} (f : L → Fin r)

lemma slots_positions (i : Fin r) (j : Fin (size f i)) :
    slots f (positions (size f) ⟨i,j⟩)=(cards f i j).val := by
  simp [slots]

/- Independent permutations of the actual fibers, on the literal ambient set. -/
def action : (∀ i, Equiv.Perm (Fin (size f i))) →* Equiv.Perm L :=
  (slots f).permCongrHom.toMonoidHom.comp (permHom (size f))

lemma action_apply (σ : ∀ i, Equiv.Perm (Fin (size f i))) (i : Fin r) (j : Fin (size f i)) :
    action f σ (cards f i j).val=(cards f i (σ i j)).val := by
  rw [← slots_positions f i j,← slots_positions f i (σ i j)]
  change slots f (perm (size f) σ ((slots f).symm (slots f (positions (size f) ⟨i,j⟩))))=_
  rw [Equiv.symm_apply_apply,perm_apply]

lemma ambient_action (e : Fin (Fintype.card L) ≃ L)
    (σ : ∀ i, Equiv.Perm (Fin (size f i))) :
    Equiv.permCongr e.symm (action f σ)=
      regroup f e*Equiv.permCongr (finCongr (total f)) (perm (size f) σ)*(regroup f e)⁻¹ := by
  apply Equiv.ext
  intro x
  change e.symm (slots f (perm (size f) σ ((slots f).symm (e x))))=_
  simp only [Equiv.Perm.mul_apply,Equiv.permCongr_apply,regroup,chart,
    Equiv.trans_apply,Equiv.symm_trans_apply,Equiv.Perm.coe_inv]
  simp

/- A label-preserving permutation has genuine induced local permutations. -/
def restrict (σ : Equiv.Perm L) (hσ : ∀ x, f (σ x)=f x) (i : Fin r) : Equiv.Perm (Fin (size f i)) :=
  Equiv.permCongr (cards f i).symm (Equiv.subtypeEquiv σ (by
    intro x
    change f x=i ↔ f (σ x)=i
    rw [hσ x]))

lemma restrict_apply (σ : Equiv.Perm L) (hσ : ∀ x, f (σ x)=f x)
    (i : Fin r) (j : Fin (size f i)) :
    (cards f i (restrict f σ hσ i j)).val=σ (cards f i j).val := by
  simp [restrict,Equiv.permCongr_apply]

lemma action_restrict (σ : Equiv.Perm L) (hσ : ∀ x, f (σ x)=f x) :
    action f (restrict f σ hσ)=σ := by
  apply Equiv.ext
  intro x
  let i := f x
  let j := (cards f i).symm ⟨x,rfl⟩
  have hx : (cards f i j).val=x := congrArg Subtype.val ((cards f i).apply_symm_apply ⟨x,rfl⟩)
  rw [← hx,action_apply,restrict_apply]

end CoordinateSweeps.FiberBlocks
namespace CoordinateSweeps.SignedTensor
open UnitaryIrrep
variable {p r l : ℕ} (n : Fin r → ℕ)
lemma groupedProjector_commute_average {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    groupedProjector (p := p) n ρ*groupedAverage n w g=groupedAverage n w g*groupedProjector n ρ := by
  rw [groupedProjector_factor,groupedAverage_factor]
  change Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _*
      Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _=
    Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _*
      Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm _
  rw [← map_mul,← map_mul,← DependentTensor.tensor_mul,← DependentTensor.tensor_mul]
  congr 1
  apply congrArg DependentTensor.tensor
  funext i
  simp only [averageMatrix,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro ω _
  exact congrArg (fun A => w i ω • A) ((ρ i).projector_commute (action p (n i)) (g i ω)).symm

lemma ambientProjector_commute_average (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l))
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i))))
    (w : ∀ i, Ω i → ℂ) (g : ∀ i, Ω i → Equiv.Perm (Fin (n i))) :
    ambientProjector (p := p) n h σ ρ*ambientAverage n h σ w g=
      ambientAverage n h σ w g*ambientProjector n h σ ρ := by
  subst l
  rw [ambientAverage_factor]
  unfold ambientProjector lengthMatrix
  rw [conjugate_mul _ _ _ (matrix_unitary σ),conjugate_mul _ _ _ (matrix_unitary σ)]
  rw [groupedProjector_commute_average]
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open UnitaryIrrep
variable {p r : ℕ} (n : Fin r → ℕ)
lemma child_product_bound (s : ℕ) (hn : ∀ i, n i ≤ s)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (n i)))) (T E : Fin r → ℝ)
    (hT : ∀ i, 0 ≤ T i) (hE : ∀ i, T i ≤ Real.exp (E i)) :
    (∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
      (matrixRepresentation (action p (n i)))) : ℝ)*T i) ≤
        ((s+1 : ℕ) : ℝ)^(r*((2*p)*(2*p)))*Real.exp (∑ i, E i) := by
  rw [Finset.prod_mul_distrib]
  have hm : (∏ i, (Module.finrank ℂ ((ρ i).asRepresentation.IntertwiningMap
      (matrixRepresentation (action p (n i)))) : ℝ)) ≤ ((s+1 : ℕ) : ℝ)^(r*((2*p)*(2*p))) := by
    calc
      _ ≤ ∏ _ : Fin r, ((s+1 : ℕ) : ℝ)^((2*p)*(2*p)) := Finset.prod_le_prod₀
        (fun _ _ => Nat.cast_nonneg _) (fun i _ => by
          exact_mod_cast (multiplicity_le p (n i) (ρ i)).trans
            (Nat.pow_le_pow_left (Nat.add_le_add_right (hn i) 1) _))
      _ = _ := by rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul,Nat.mul_comm]
  have ht : (∏ i, T i) ≤ Real.exp (∑ i, E i) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun i _ => hT i) (fun i _ => hE i)
  exact mul_le_mul hm ht (Finset.prod_nonneg (fun i _ => hT i)) (by positivity)
end CoordinateSweeps.SignedTensor
namespace CoordinateSweeps.SignedTensor
variable {p r : ℕ} {L : Type*} [Fintype L] (f : L → Fin r)

def fiberProjector (e : Fin (Fintype.card L) ≃ L)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :=
  ambientProjector (p := p) (FiberBlocks.size f) (FiberBlocks.total f) (FiberBlocks.regroup f e) ρ

def fiberProjectorAlgebra (e : Fin (Fintype.card L) ≃ L)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :=
  ambientProjectorAlgebra (FiberBlocks.size f) (FiberBlocks.total f) (FiberBlocks.regroup f e) ρ

lemma fiberProjectorAlgebra_lift (e : Fin (Fintype.card L) ≃ L)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :
    MonoidAlgebra.lift ℂ _ _ (action p (Fintype.card L)) (fiberProjectorAlgebra f e ρ)=
      fiberProjector (p := p) f e ρ := ambientProjectorAlgebra_lift _ _ _ _

lemma fiberProjector_posSemidef (e : Fin (Fintype.card L) ≃ L)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :
    (fiberProjector (p := p) f e ρ).PosSemidef := ambientProjector_posSemidef _ _ _ _

lemma fiberProjector_idempotent (e : Fin (Fintype.card L) ≃ L)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :
    fiberProjector (p := p) f e ρ*fiberProjector f e ρ=fiberProjector f e ρ :=
  ambientProjector_idempotent _ _ _ _

/- Exact regrouping connects local isotypic products to the literal site labels. -/
theorem finite_fiber_density_domination (e : Fin (Fintype.card L) ≃ L)
    (s : ℕ) (hp : 0 < p) (hps : p ≤ s) (hn : ∀ i, FiberBlocks.size f i ≤ s)
    (ρ : ∀ i, UnitaryIrrep (Equiv.Perm (Fin (FiberBlocks.size f i)))) :
    ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (a : K → Fin r → EvenDensity p),
      (((∏ i, ((ρ i).dimension : ℂ))*((s+1 : ℕ) : ℂ)^(r*(41*p^2))) •
        ((Fintype.card K : ℂ)⁻¹ • ∑ x,
          TensorBoard.tensor (fun k => (a x (f (e k))).val))-fiberProjector (p := p) f e ρ).PosSemidef := by
  obtain ⟨K,hK,nK,a,ha⟩ := finite_ambient_density_domination (FiberBlocks.size f) s hp hps hn ρ
    (FiberBlocks.total f) (FiberBlocks.regroup f e)
  let := hK
  let := nK
  refine ⟨K,hK,nK,a,?_⟩
  simpa only [groupedSite,FiberBlocks.label_regroup,fiberProjector] using ha

end CoordinateSweeps.SignedTensor
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
