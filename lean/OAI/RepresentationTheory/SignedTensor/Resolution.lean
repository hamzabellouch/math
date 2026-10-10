import Mathlib
import OAI.RepresentationTheory.SignedTensor.Overlap
import OAI.Analysis.Matrix.Holder
import OAI.RepresentationTheory.Young.Classification

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
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.SignedTensor

def ActiveType (p l : ℕ) :=
  { a : Nat.Partition (Fintype.card (Fin l)) // (YoungCorner.partitionUnitary (Fin l) a).projector (action p l) ≠ 0 }

instance (p l : ℕ) : Fintype (ActiveType p l) := by
  unfold ActiveType
  infer_instance

instance (p l : ℕ) : DecidableEq (ActiveType p l) := Classical.decEq _

def activeIrrep {p l : ℕ} (a : ActiveType p l) : UnitaryIrrep (Equiv.Perm (Fin l)) :=
  YoungCorner.partitionUnitary (Fin l) a.val

def activeProjector {p l : ℕ} (a : ActiveType p l) : commutant p l :=
  ⟨(activeIrrep a).projector (action p l),fun σ =>
    ((activeIrrep a).projector_commute (action p l) σ).symm⟩

lemma activeProjector_nonzero {p l : ℕ} (a : ActiveType p l) :
    (activeProjector a).val ≠ 0 := a.property

lemma active_inequivalent {p l : ℕ} (a b : ActiveType p l) (hab : a ≠ b) :
    ¬Nonempty (Representation.Equiv (activeIrrep a).asRepresentation (activeIrrep b).asRepresentation) := by
  apply YoungCorner.partitionUnitary_inequivalent
  intro h
  apply hab
  apply Subtype.ext
  simpa using h

lemma activeProjector_mul {p l : ℕ} (a b : ActiveType p l) :
    (activeProjector a).val*(activeProjector b).val=
      if a=b then (activeProjector a).val else 0 := by
  split_ifs with h
  · subst b; exact (activeIrrep a).projector_idempotent _
  · exact (activeIrrep a).projector_orthogonal (activeIrrep b)
      (active_inequivalent b a (Ne.symm h)) _

lemma activeProjector_independent (p l : ℕ) :
    LinearIndependent ℂ (activeProjector (p := p) (l := l)) := by
  apply linearIndependent_iff'.mpr
  intro t c hc a ha
  have hh := congrArg (fun A : commutant p l => (activeProjector a).val*A.val) hc
  have hv : ∑ b ∈ t, c b • ((activeProjector a).val*(activeProjector b).val)=0 := by
    simpa only [Submodule.coe_sum,Submodule.coe_smul,ZeroMemClass.coe_zero,
      Matrix.mul_sum,Matrix.mul_smul,mul_zero] using hh
  simp only [activeProjector_mul,smul_ite,smul_zero] at hv
  have he : c a • (activeProjector a).val=0 := by simpa [ha] using hv
  exact (smul_eq_zero.mp he).resolve_right (activeProjector_nonzero a)

/- Number of actually occurring local types is polynomial even without a
hook-support classification; this is exactly the term-count scale in06:eq20. -/
theorem active_card_le (p l : ℕ) :
    Fintype.card (ActiveType p l) ≤ (l+1)^((2*p)*(2*p)) :=
  (activeProjector_independent p l).fintype_card_le_finrank.trans (commutant_finrank_le p l)

/- Omitting zero type projections preserves the actual identity resolution. -/
theorem active_resolution (p l : ℕ) :
    ∑ a : ActiveType p l, (activeProjector a).val=1 := by
  let f (a : Nat.Partition (Fintype.card (Fin l))) :=
    (YoungCorner.partitionUnitary (Fin l) a).projector (action p l)
  have he : ∑ a : ActiveType p l, (activeProjector a).val=∑ a : Nat.Partition (Fintype.card (Fin l)), f a := by
    change (∑ a : {a : Nat.Partition (Fintype.card (Fin l)) // f a ≠ 0}, f a.val)=∑ a, f a
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a => f a ≠ 0)) (by simp),Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h
    · rfl
    · exact (not_ne_iff.mp h).symm
  rw [he]
  have hh := YoungCorner.partition_matrix_resolution (Fin l) (action p l)
  simpa [f] using hh

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
variable {p r : ℕ} (n : Fin r → ℕ)
abbrev BlockType (p : ℕ) := ∀ i, ActiveType p (n i)

abbrev blockProjector (α : BlockType n p) := groupedProjector (p := p) n (fun i => activeIrrep (α i))

/- Actual polynomial-size identity resolution of each product subgroup. -/
lemma block_resolution : ∑ α : BlockType n p, blockProjector n α=1 := by
  simp only [blockProjector,groupedProjector_factor]
  change (∑ α : BlockType n p, Matrix.reindexAlgEquiv ℂ ℂ (groupWord n p).symm
    (DependentTensor.tensor (fun i => (activeIrrep (α i)).projector (action p (n i)))))=1
  rw [← map_sum]
  rw [← DependentTensor.tensor_sum (fun i (a : ActiveType p (n i)) => (activeIrrep a).projector (action p (n i)))]
  have hh (i : Fin r) : ∑ a : ActiveType p (n i), (activeIrrep a).projector (action p (n i))=1 :=
    active_resolution p (n i)
  simp only [hh,DependentTensor.tensor_one,map_one]

lemma block_card_le (s : ℕ) (hn : ∀ i, n i ≤ s) :
    Fintype.card (BlockType n p) ≤ (s+1)^(r*((2*p)*(2*p))) := by
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ i : Fin r, (s+1)^((2*p)*(2*p)) := Finset.prod_le_prod (fun i hi =>
      (active_card_le p (n i)).trans (Nat.pow_le_pow_left (Nat.succ_le_succ (hn i)) _))
    _ = _ := by rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul,Nat.mul_comm]

end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
open UnitaryIrrep FiberBlocks
variable {p r l : ℕ} (n : Fin r → ℕ)
lemma ambient_block_resolution (h : (∑ i, n i)=l) (σ : Equiv.Perm (Fin l)) :
    (∑ α : BlockType n p, ambientProjector (p := p) n h σ (fun i => activeIrrep (α i)))=1 := by
  subst l
  unfold ambientProjector lengthMatrix
  rw [← Matrix.sum_mul,← Matrix.mul_sum,block_resolution,mul_one,matrix_unitary_reverse]

variable {L : Type*} [Fintype L]
lemma fiber_block_resolution (f : L → Fin r) (e : Fin (Fintype.card L) ≃ L) :
    (∑ α : BlockType (size f) p, fiberProjector (p := p) f e (fun i => activeIrrep (α i)))=1 :=
  ambient_block_resolution _ _ _

def blockEntropy {n : Fin r → ℕ} (α : BlockType n p) : ℝ :=
  ∑ i, Real.log (activeIrrep (α i)).dimension

lemma exp_blockEntropy {n : Fin r → ℕ} (α : BlockType n p) :
    Real.exp (blockEntropy α)=∏ i, ((activeIrrep (α i)).dimension : ℝ) := by
  rw [blockEntropy,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (Nat.cast_pos.mpr (activeIrrep (α i)).positive)

lemma nat_pow_eq_exp (s t : ℕ) : ((s+1 : ℕ) : ℝ)^t=Real.exp ((t : ℝ)*Real.log (s+1 : ℕ)) := by
  rw [mul_comm,Real.exp_mul,Real.exp_log (by positivity),Real.rpow_natCast]

lemma block_card_real_le (f : L → Fin r) (s : ℕ) (hn : ∀ i, size f i ≤ s) :
    (Fintype.card (BlockType (size f) p) : ℝ) ≤
      Real.exp ((r*((2*p)*(2*p)) : ℕ)*Real.log (s+1 : ℕ)) := by
  rw [← nat_pow_eq_exp]
  exact_mod_cast block_card_le (size f) s hn

lemma actual_label_overlap_exp {c : ℕ} [NeZero r]
    (f : L → Fin r) (g : L → Fin c) (hinj : Function.Injective (fun x => (f x,g x)))
    (e : Fin (Fintype.card L) ≃ L) (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hnR : ∀ i, size f i ≤ s) (hnC : ∀ j, size g j ≤ s)
    (α : BlockType (size f) p) (β : BlockType (size g) p)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card L)))) :
    ‖fiberProjector g e (fun j => activeIrrep (β j))*ρ.projector (action p (Fintype.card L))*
      fiberProjector f e (fun i => activeIrrep (α i))‖^2 ≤
        Real.exp (blockEntropy α+blockEntropy β-Real.log ρ.dimension+
          ((r : ℝ)*c-Fintype.card L)+((r+c)*(41*p^2) : ℕ)*Real.log (s+1 : ℕ)) := by
  have hh := actual_label_overlap f g hinj e s hp hps hnR hnC
    (fun i => activeIrrep (α i)) (fun j => activeIrrep (β j)) ρ
  have hD : 0 < (ρ.dimension : ℝ) := Nat.cast_pos.mpr ρ.positive
  apply (mul_le_mul_iff_right₀ hD).mp
  apply hh.trans_eq
  rw [← exp_blockEntropy α,← exp_blockEntropy β,nat_pow_eq_exp,nat_pow_eq_exp]
  nth_rw 1 [← Real.exp_log hD]
  simp only [← Real.exp_add]
  congr 1
  push_cast
  ring

lemma actual_label_overlap_contract {c : ℕ} (f : L → Fin r) (g : L → Fin c)
    (e : Fin (Fintype.card L) ≃ L) (hp : 0 < p)
    (α : BlockType (size f) p) (β : BlockType (size g) p)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card L)))) :
    ‖fiberProjector g e (fun j => activeIrrep (β j))*ρ.projector (action p (Fintype.card L))*
      fiberProjector f e (fun i => activeIrrep (α i))‖ ≤ 1 := by
  let : NeZero (2*p) := ⟨by omega⟩
  have hR := TraceHolder.projector_norm_le _ (fiberProjector_posSemidef f e _).isHermitian
    (fiberProjector_idempotent (p := p) f e (fun i => activeIrrep (α i)))
  have hC := TraceHolder.projector_norm_le _ (fiberProjector_posSemidef g e _).isHermitian
    (fiberProjector_idempotent (p := p) g e (fun i => activeIrrep (β i)))
  have hP := TraceHolder.projector_norm_le _ (ρ.projector_posSemidef _ (fun σ => (matrix_inv σ).symm)).isHermitian
    (ρ.projector_idempotent (action p (Fintype.card L)))
  calc
    _ ≤ (‖fiberProjector g e (fun j => activeIrrep (β j))‖*‖ρ.projector (action p (Fintype.card L))‖)*
      ‖fiberProjector f e (fun i => activeIrrep (α i))‖ := by
        exact (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*1)*1 := mul_le_mul (mul_le_mul hC hP (norm_nonneg _) (by positivity)) hR
      (norm_nonneg _) (by positivity)
    _ = 1 := by norm_num

/- The actual two-product-subgroup inequality. Its only analytic inputs are
child moments; the resolution, polynomial number of types and board overlap
are all constructed above. This is the row/column step of the main induction. -/
theorem labeled_projected_moment_bound {c : ℕ} [NeZero r]
    (f : L → Fin r) (g : L → Fin c) (hinj : Function.Injective (fun x => (f x,g x)))
    (e : Fin (Fintype.card L) ≃ L) (s : ℕ) (hp : 0 < p) (hps : p ≤ s)
    (hnR : ∀ i, size f i ≤ s) (hnC : ∀ j, size g j ≤ s)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card L)))) (q : ℕ) (hq : 0 < q)
    (c₀ ER EC : ℝ) (hc : 0 ≤ c₀) (hcq : c₀ ≤ q)
    (X Y : Matrix (Word p (Fintype.card L)) (Word p (Fintype.card L)) ℂ)
    (hR : ∀ α : BlockType (size f) p,
      (Matrix.trace (((fiberProjector f e (fun i => activeIrrep (α i))*X).conjTranspose*
        (fiberProjector f e (fun i => activeIrrep (α i))*X))^q)).re ≤ Real.exp (-c₀*blockEntropy α+ER))
    (hC : ∀ β : BlockType (size g) p,
      (Matrix.trace (((Y*fiberProjector g e (fun j => activeIrrep (β j))).conjTranspose*
        (Y*fiberProjector g e (fun j => activeIrrep (β j))))^q)).re ≤ Real.exp (-c₀*blockEntropy β+EC)) :
    (Matrix.trace (((Y*ρ.projector (action p (Fintype.card L))*X).conjTranspose*
      (Y*ρ.projector (action p (Fintype.card L))*X))^q)).re ≤
      Real.exp (-c₀*Real.log ρ.dimension+ER+EC+c₀*((r : ℝ)*c-Fintype.card L)+
        ((2*q : ℕ)*((r+c)*((2*p)*(2*p)) : ℕ)+c₀*((r+c)*(41*p^2) : ℕ))*Real.log (s+1 : ℕ)) := by
  let : NeZero (2*p) := ⟨by omega⟩
  have hh := TraceHolder.row_column_moment q hq
    (fun α : BlockType (size f) p => fiberProjector f e (fun i => activeIrrep (α i)))
    (fun β : BlockType (size g) p => fiberProjector g e (fun j => activeIrrep (β j)))
    (fiber_block_resolution f e) (fiber_block_resolution g e)
    (fun α => fiberProjector_idempotent f e _) (fun β => fiberProjector_idempotent g e _)
    (ρ.projector (action p (Fintype.card L))) X Y blockEntropy blockEntropy (Real.log ρ.dimension)
    (ER+EC) (((r : ℝ)*c-Fintype.card L)+((r+c)*(41*p^2) : ℕ)*Real.log (s+1 : ℕ)) c₀ hc hcq
    (fun α β => (mul_le_mul (hR α) (hC β)
      (by exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _ |>.pow q |>.trace_nonneg)).1)
      (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add]; congr 1; ring))
    (fun α β => by simpa only [add_assoc] using actual_label_overlap_exp f g hinj e s hp hps hnR hnC α β ρ)
    (fun α β => actual_label_overlap_contract f g e hp α β ρ)
  apply hh.trans
  have hcard := mul_le_mul (block_card_real_le (p := p) f s hnR) (block_card_real_le (p := p) g s hnC)
    (Nat.cast_nonneg _) (Real.exp_pos _).le
  rw [← Real.exp_add] at hcard
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤
    (Fintype.card (BlockType (size f) p) : ℝ)*(Fintype.card (BlockType (size g) p) : ℝ)) hcard (2*q)
  rw [← Real.exp_nat_mul] at hpow
  rw [Nat.cast_mul]
  apply (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring
end CoordinateSweeps.SignedTensor

namespace CoordinateSweeps.SignedTensor
lemma phase_eq_of_same_parity {p l : ℕ} (σ : Equiv.Perm (Fin l)) (u w : Word p l)
    (h : ∀ i, odd (u i) ↔ odd (w i)) : phase σ u=phase σ w := by
  rw [phase_prod,phase_prod]
  apply Finset.prod_congr rfl
  intro ij hij
  simp only [h]

lemma wordPerm_same_parity {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l)
    (h : ∀ i, odd (w (σ i)) ↔ odd (w i)) :
    ∀ i, odd (wordPerm σ w i) ↔ odd (w i) := by
  intro i
  simpa [wordPerm] using (h (σ⁻¹ i)).symm

lemma phase_conj_of_parity_stable {p l : ℕ} (σ g : Equiv.Perm (Fin l)) (w : Word p l)
    (h : ∀ i, odd (w (σ i)) ↔ odd (w i)) :
    phase (g*σ*g⁻¹) (wordPerm g w)=phase σ w := by
  have he : (g*σ*g⁻¹)*g=g*σ := by simp [mul_assoc]
  have hh := phase_mul (g*σ*g⁻¹) g w
  rw [he,phase_mul,phase_eq_of_same_parity g _ w (wordPerm_same_parity σ w h)] at hh
  apply mul_right_cancel₀ (phase_ne_zero g w)
  rw [← hh,mul_comm]

lemma phase_of_fix_odd {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l)
    (h : ∀ i, odd (w i) → σ i=i) : phase σ w=1 := by
  rw [phase_prod]
  apply Finset.prod_eq_one
  intro ij hij
  have hj := Equiv.Perm.mem_finPairsLT.mp hij
  split_ifs with hh
  · rw [h _ hh.1,h _ hh.2.1] at hh
    exact False.elim (hj.not_gt hh.2.2)
  · rfl

lemma phase_swap_odd {p l : ℕ} (w : Word p l) (i j : Fin l) (hij : i ≠ j)
    (hi : odd (w i)) (hj : odd (w j)) : phase (Equiv.swap i j) w = -1 := by
  have hl : 2 ≤ l := by
    have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hi := i.isLt
    have hj := j.isLt
    omega
  obtain ⟨n,rfl⟩ : ∃ n, l=n+2 := ⟨l-2,by omega⟩
  obtain ⟨g,hgi,hgj⟩ := exists_perm_pair i j (0 : Fin (n+2)) 1 hij (by simp)
  have hp : ∀ x, odd (w (Equiv.swap i j x)) ↔ odd (w x) := by
    intro x
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have he : g*Equiv.swap i j*g⁻¹=Equiv.swap (0 : Fin (n+2)) 1 := by
    rw [Equiv.mul_swap_eq_swap_mul,mul_assoc,mul_inv_cancel,mul_one,hgi,hgj]
  have hh:=phase_conj_of_parity_stable (Equiv.swap i j) g w hp
  rw [he,phase_swap01] at hh
  have h0 : wordPerm g w 0=w i := by rw [← hgi]; simp [wordPerm]
  have h1 : wordPerm g w 1=w j := by rw [← hgj]; simp [wordPerm]
  simpa [h0,h1,hi,hj] using hh.symm

lemma phase_ofSubtype {p l : ℕ} (w : Word p l)
    (σ : Equiv.Perm {i : Fin l // odd (w i)}) :
    phase (Equiv.Perm.ofSubtype σ) w = YoungCorner.signScalar σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp [phase_one]
  | swap_mul σ i j hij ih =>
    rw [map_mul,phase_mul,Equiv.Perm.ofSubtype_swap_eq]
    have hp := wordPerm_same_parity (Equiv.Perm.ofSubtype σ) w
      (Equiv.Perm.ofSubtype_apply_mem_iff_mem σ)
    rw [phase_eq_of_same_parity _ _ w hp,
      phase_swap_odd w i j (fun he => hij (Subtype.ext he)) i.property j.property,
      ih,map_mul,YoungCorner.signScalar_swap i j hij]

lemma phase_of_fix_even {p l : ℕ} (σ : Equiv.Perm (Fin l)) (w : Word p l)
    (h : ∀ i, ¬ odd (w i) → σ i=i) : phase σ w=YoungCorner.signScalar σ := by
  have hp : ∀ i, odd (w (σ i)) ↔ odd (w i) := by
    intro i
    by_cases hi : odd (w i)
    · have hs : odd (w (σ i)) := by
        by_contra hn
        have hh := h (σ i) hn
        have he := σ.injective hh
        rw [he] at hn
        exact hn hi
      simp [hi,hs]
    · rw [h i hi]
  let υ := Equiv.Perm.subtypePerm (p := fun i => odd (w i)) σ hp
  have he : Equiv.Perm.ofSubtype υ=σ := Equiv.Perm.ofSubtype_subtypePerm (p := fun i => odd (w i)) hp (by
    intro i hi
    exact Classical.byContradiction (fun hn => hi (h i hn)))
  rw [← he,phase_ofSubtype]
  simp [YoungCorner.signScalar,Equiv.Perm.sign_ofSubtype]

end CoordinateSweeps.SignedTensor
namespace CoordinateSweeps.YoungCorner
variable {μ : YoungDiagram} {p : ℕ}

def Hook (μ : YoungDiagram) (p : ℕ) : Prop := ∀ x : Boxes μ, x.val.1<p ∨ x.val.2<p

def hookLetter (h : Hook μ p) (x : Boxes μ) : SignedTensor.Letter p :=
  if hx : x.val.1<p then ⟨x.val.1,by omega⟩ else ⟨p+x.val.2,by have hh:=(h x).resolve_left hx; omega⟩

lemma hookLetter_odd (h : Hook μ p) (x : Boxes μ) :
    SignedTensor.odd (hookLetter h x) ↔ p≤x.val.1 := by
  simp only [hookLetter,SignedTensor.odd]
  split_ifs <;> simp_all
  omega

lemma hookLetter_row_eq (h : Hook μ p) (x y : Boxes μ)
    (hx : x.val.1<p) (he : hookLetter h x=hookLetter h y) : x.val.1=y.val.1 := by
  have he' := congrArg Fin.val he
  simp only [hookLetter] at he'
  split_ifs at he' <;> simp_all
  omega

lemma hookLetter_col_eq (h : Hook μ p) (x y : Boxes μ)
    (hx : p≤x.val.1) (he : hookLetter h x=hookLetter h y) : x.val.2=y.val.2 := by
  have he' := congrArg Fin.val he
  simp only [hookLetter] at he'
  split_ifs at he' <;> simp_all <;> omega

/- The geometric reason all diagonal Young-corner coefficients have positive
sign on the actual even-row/odd-column hook word. -/
lemma hook_corner_fixed {X : Type*} (t : X ≃ Boxes μ) (h : Hook μ p)
    (r : colorStabilizer (rowColor t)) (c : colorStabilizer (colColor t))
    (hw : ∀ x, hookLetter h (t ((r : Equiv.Perm X) (c.val x)))=hookLetter h (t x)) :
    (∀ x, (t x).val.1<p → c.val x=x) ∧ (∀ x, p≤(t x).val.1 → r.val x=x) := by
  have hc : ∀ x, (t x).val.1<p → c.val x=x := by
    intro x hx
    apply t.injective
    apply Subtype.ext
    apply Prod.ext
    · have hr:=r.property (c.val x)
      have hh:=hookLetter_row_eq h (t x) (t (r.val (c.val x))) hx (hw x).symm
      exact hr.symm.trans hh.symm
    · exact c.property x
  refine ⟨hc,?_⟩
  intro y hy
  let x := (c : Equiv.Perm X)⁻¹ y
  have hxy : c.val x=y := by simp [x]
  have hx : p≤(t x).val.1 := by
    by_contra hn
    have he := hc x (by omega)
    rw [hxy] at he
    rw [← he] at hn
    omega
  apply t.injective
  apply Subtype.ext
  apply Prod.ext
  · exact r.property y
  · have hh:=hookLetter_col_eq h (t x) (t (r.val (c.val x))) hx (hw x).symm
    have hh' :=c.property x
    change (t (c.val x)).val.2=(t x).val.2 at hh'
    rw [hxy] at hh hh'
    exact hh.symm.trans hh'.symm

lemma hook_corner_phase {l : ℕ} (t : Fin l ≃ Boxes μ) (h : Hook μ p)
    (r : colorStabilizer (rowColor t)) (c : colorStabilizer (colColor t))
    (hw : ∀ x, hookLetter h (t ((r : Equiv.Perm (Fin l)) (c.val x)))=hookLetter h (t x)) :
    SignedTensor.phase ((r : Equiv.Perm (Fin l))*c.val) (fun x => hookLetter h (t x))=
      signScalar (c : Equiv.Perm (Fin l)) := by
  obtain ⟨hc,hr⟩ := hook_corner_fixed t h r c hw
  let w : SignedTensor.Word p l := fun x => hookLetter h (t x)
  have hce : ∀ i, ¬ SignedTensor.odd (w i) → (c : Equiv.Perm (Fin l)) i=i := by
    intro i hi
    exact hc i (by simpa only [w,hookLetter_odd,not_le] using hi)
  have hcp : ∀ i, SignedTensor.odd (w (c.val i)) ↔ SignedTensor.odd (w i) := by
    intro i
    by_cases hi : SignedTensor.odd (w i)
    · have hh : SignedTensor.odd (w (c.val i)) := by
        by_contra hn
        have he := c.val.injective (hce (c.val i) hn)
        rw [he] at hn
        exact hn hi
      simp [hi,hh]
    · rw [hce i hi]
  rw [SignedTensor.phase_mul,SignedTensor.phase_eq_of_same_parity _ _ w
    (SignedTensor.wordPerm_same_parity c.val w hcp),SignedTensor.phase_of_fix_odd _ w]
  · rw [one_mul,SignedTensor.phase_of_fix_even c.val w hce]
  · intro i hi
    exact hr i ((hookLetter_odd h (t i)).mp hi)

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
variable {μ : YoungDiagram} {p l : ℕ}

lemma signScalar_square {X : Type*} [Fintype X] [DecidableEq X] (c : Equiv.Perm X) :
    signScalar c * signScalar c=1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign c) with h|h <;> simp [signScalar,h]

lemma hook_contribution (t : Fin l ≃ Boxes μ) (h : Hook μ p)
    (r : colorStabilizer (rowColor t)) (c : colorStabilizer (colColor t)) :
    let w : SignedTensor.Word p l := fun x => hookLetter h (t x)
    signScalar c.val * SignedTensor.matrix (r.val*c.val) w w =
      if w=SignedTensor.wordPerm (r.val*c.val) w then 1 else 0 := by
  dsimp only
  rw [SignedTensor.matrix]
  split_ifs with he
  · have hw : ∀ x, hookLetter h (t (r.val (c.val x)))=hookLetter h (t x) := by
      intro x
      have hh := congrFun he ((r.val*c.val) x)
      simpa [SignedTensor.wordPerm,Equiv.Perm.mul_apply] using hh
    rw [hook_corner_phase t h r c hw,signScalar_square]
  · simp

lemma hook_corner_matrix_ne (t : Fin l ≃ Boxes μ) (h : Hook μ p) :
    fixedSum (rowColor t) (SignedTensor.action p l) *
      alternatingSum (colColor t) (SignedTensor.action p l) ≠ 0 := by
  let w : SignedTensor.Word p l := fun x => hookLetter h (t x)
  have he : (fixedSum (rowColor t) (SignedTensor.action p l) *
      alternatingSum (colColor t) (SignedTensor.action p l)) w w =
      ∑ r : colorStabilizer (rowColor t), ∑ c : colorStabilizer (colColor t),
        if w=SignedTensor.wordPerm (r.val*c.val) w then (1 : ℂ) else 0 := by
    rw [fixedSum,alternatingSum,Finset.sum_mul]
    simp only [Finset.mul_sum,mul_smul_comm,← map_mul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro c hc
    exact hook_contribution t h r c
  have hpos : 0 < ((fixedSum (rowColor t) (SignedTensor.action p l) *
      alternatingSum (colColor t) (SignedTensor.action p l)) w w).re := by
    rw [he]
    simp only [Complex.re_sum,apply_ite,Complex.one_re,Complex.zero_re]
    apply Finset.sum_pos'
    · intro r hr
      apply Finset.sum_nonneg
      intro c hc
      split_ifs <;> norm_num
    · refine ⟨1,Finset.mem_univ _,?_⟩
      apply Finset.sum_pos'
      · intro c hc
        split_ifs <;> norm_num
      · refine ⟨1,Finset.mem_univ _,?_⟩
        simp [SignedTensor.wordPerm]
  intro hz
  rw [hz] at hpos
  simp at hpos

/- The literal signed action, as a linear representation. -/
def signedRep (p l : ℕ) : Representation ℂ (Equiv.Perm (Fin l)) (SignedTensor.Word p l → ℂ) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (SignedTensor.action p l)

lemma signedRep_hasShape (t : Fin l ≃ Boxes μ) (h : Hook μ p) :
    hasShape μ t (signedRep p l) := by
  have he : fixedSum (rowColor t) (signedRep p l) * alternatingSum (colColor t) (signedRep p l) =
      Matrix.toLinAlgEquiv' (fixedSum (rowColor t) (SignedTensor.action p l) *
        alternatingSum (colColor t) (SignedTensor.action p l)) := by
    simp [fixedSum,alternatingSum,signedRep,map_sum,map_mul]
  intro hz
  rw [he] at hz
  exact hook_corner_matrix_ne t h (Matrix.toLinAlgEquiv'.injective (hz.trans (map_zero _).symm))

lemma detecting_shape_constituent {X V : Type*} [Fintype X] [DecidableEq X]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ (Equiv.Perm X) V) (t : X ≃ Boxes μ) (h : hasShape μ t τ) :
    ∃ S : Subrepresentation τ, S.toRepresentation.IsIrreducible ∧ hasShape μ t S.toRepresentation := by
  obtain ⟨S,hS,v,hv⟩ := RepDetection.exists_irreducible_detecting τ
    (fixedSum (rowColor t) τ*alternatingSum (colColor t) τ) h
  refine ⟨S,hS,?_⟩
  intro hh
  apply hv
  have hz := congrArg (fun A : Module.End ℂ S.toSubmodule => (A v : V)) hh
  simp only [Module.End.mul_apply,fixedSum_subrepresentation,alternatingSum_subrepresentation] at hz
  exact hz

/- Source05 hook occurrence, derived for actual irreps in the exact Koszul
representation. No Pieri/Schur--Weyl or hook classification is assumed. -/
theorem hook_occurs {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin l)) V) [ρ.IsIrreducible]
    (t : Fin l ≃ Boxes μ) (hρ : hasShape μ t ρ) (h : Hook μ p) :
    ∃ S : Subrepresentation (signedRep p l),
      Nonempty (Representation.Equiv ρ S.toRepresentation) := by
  obtain ⟨S,hS,hSh⟩ := detecting_shape_constituent (signedRep p l) t (signedRep_hasShape t h)
  let := hS
  exact ⟨S,equiv_of_same_shape ρ S.toRepresentation μ t t hρ hSh⟩

end CoordinateSweeps.YoungCorner

namespace CoordinateSweeps.YoungCorner
open UnitaryIrrep SignedTensor
lemma hook_multiplicity_pos {p l : ℕ} {μ : YoungDiagram}
    (ρ : UnitaryIrrep (Equiv.Perm (Fin l))) (t : Fin l ≃ Boxes μ)
    (hρ : hasShape μ t ρ.asRepresentation) (hhook : Hook μ p) :
    0 < Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (matrixRepresentation (action p l))) := by
  obtain ⟨S,⟨e⟩⟩ := hook_occurs ρ.asRepresentation t hρ hhook
  let inc : S.toRepresentation.IntertwiningMap (signedRep p l) :=
    ⟨S.toSubmodule.subtype,fun _ => rfl⟩
  let f := inc.comp e.toIntertwiningMap
  have hf : f ≠ 0 := by
    intro hz
    have hzero : ∀ v : Fin ρ.dimension → ℂ, v=0 := by
      intro v
      apply e.toLinearEquiv.injective
      apply Subtype.val_injective
      have hh := congrArg (fun g : ρ.asRepresentation.IntertwiningMap (signedRep p l) => g v) hz
      change ((e.toLinearEquiv v : S.toSubmodule) : SignedTensor.Word p l → ℂ)=0 at hh
      rw [map_zero]
      exact hh
    have : Nonempty (Fin ρ.dimension) := Fin.pos_iff_nonempty.mp ρ.positive
    exact one_ne_zero (congrFun (hzero (fun _ => 1)) (Classical.arbitrary (Fin ρ.dimension)))
  let : Nontrivial (ρ.asRepresentation.IntertwiningMap (signedRep p l)) := nontrivial_of_ne f 0 hf
  change 0 < Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap (signedRep p l))
  exact Module.finrank_pos
end CoordinateSweeps.YoungCorner
end
end
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
