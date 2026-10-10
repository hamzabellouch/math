import OAI.RepresentationTheory.RowColumn.TensorFilter
import OAI.RepresentationTheory.RowColumn.HookIsometry

namespace OAI

section
noncomputable section
open scoped BigOperators Classical
namespace RowColumn.Postselection
open WordOrbits
variable {S L A : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  [Fintype A] [DecidableEq A]

def allocationPerm (line b : S → L) (hb : counts b = counts line) : Equiv.Perm S :=
  (same_counts_permutation line b hb.symm).choose

omit [DecidableEq S] [Fintype L] in
lemma allocationPerm_spec (line b : S → L) (hb : counts b = counts line) (i : S) :
    b (allocationPerm line b hb i) = line i :=
  (same_counts_permutation line b hb.symm).choose_spec i

omit [DecidableEq S] [Fintype A] in
lemma counts_precomp (w : S → A) (p : Equiv.Perm S) : counts (w ∘ p) = counts w := by
  funext c
  apply Fin.ext
  exact Fintype.card_congr
    { toFun := fun i => ⟨p i.1,i.2⟩
      invFun := fun i => ⟨p.symm i.1,by simpa using i.2⟩
      left_inv := by intro i; apply Subtype.ext; simp
      right_inv := by intro i; apply Subtype.ext; simp }

def symExtension (line : S → L) (v : (S → A) → ℂ) (w : S → L × A) : ℂ :=
  if hb : counts (fun i => (w i).1) = counts line then
    v (fun i => (w (allocationPerm line _ hb i)).2) else 0

omit [Fintype A] [DecidableEq A] in
omit [DecidableEq S] in
lemma symExtension_on_line (line : S → L) (v : (S → A) → ℂ)
    (hv : ∀ p : Equiv.Perm S, (∀ i, line (p i) = line i) → ∀ w, v (w ∘ p) = v w)
    (w : S → A) : symExtension line v (fun i => (line i,w i)) = v w := by
  simp only [symExtension]
  exact hv (allocationPerm line line rfl) (allocationPerm_spec line line rfl) w

omit [Fintype A] [DecidableEq A] in
omit [DecidableEq S] in
lemma symExtension_invariant (line : S → L) (v : (S → A) → ℂ)
    (hv : ∀ p : Equiv.Perm S, (∀ i, line (p i) = line i) → ∀ w, v (w ∘ p) = v w)
    (p : Equiv.Perm S) (w : S → L × A) : symExtension line v (w ∘ p) = symExtension line v w := by
  have hc : counts (fun i => (w (p i)).1) = counts (fun i => (w i).1) := counts_precomp (fun i => (w i).1) p
  by_cases hb : counts (fun i => (w i).1) = counts line
  · have hb' : counts (fun i => (w (p i)).1) = counts line := hc.trans hb
    simp only [symExtension, Function.comp_apply, dite_eq_left hb, dite_eq_left hb']
    let e := allocationPerm line (fun i => (w i).1) hb
    let e' := allocationPerm line (fun i => (w (p i)).1) hb'
    let q : Equiv.Perm S := e'.trans (p.trans e.symm)
    have hq (i : S) : line (q i) = line i := by
      rw [← allocationPerm_spec line (fun i => (w i).1) hb (q i)]
      change (w (e (e.symm (p (e' i))))).1 = line i
      rw [Equiv.apply_symm_apply]
      exact allocationPerm_spec line (fun i => (w (p i)).1) hb' i
    have hh := hv q hq (fun i => (w (e i)).2)
    change v (fun i => (w (p (e' i))).2) = v (fun i => (w (e i)).2)
    convert hh using 1
    congr 1
    ext i
    simp only [q, Equiv.trans_apply, Function.comp_apply, Equiv.apply_symm_apply]
  · have hb' : ¬ counts (fun i => (w (p i)).1) = counts line := fun hh => hb (hc.symm.trans hh)
    simp only [symExtension, Function.comp_apply, dite_eq_right hb, dite_eq_right hb']

omit [Fintype A] in
omit [DecidableEq S] in
lemma symExtension_counts (line : S → L) (v : (S → A) → ℂ)
    (hv : ∀ p : Equiv.Perm S, (∀ i, line (p i) = line i) → ∀ w, v (w ∘ p) = v w)
    (w z : S → L × A) (he : counts w = counts z) : symExtension line v w = symExtension line v z := by
  obtain ⟨p,hp⟩ := same_counts_permutation w z he
  have hh : z ∘ p = w := funext hp
  rw [← hh]
  exact symExtension_invariant line v hv p z

abbrev Allocations (line : S → L) := {b : S → L // counts b = counts line}

def labelWordEquiv : (S → L × A) ≃ (S → L) × (S → A) where
  toFun w := (fun i => (w i).1, fun i => (w i).2)
  invFun w i := (w.1 i,w.2 i)
  left_inv := by intro w; rfl
  right_inv := by intro w; rfl

def precompWordEquiv (p : Equiv.Perm S) : Equiv.Perm (S → A) where
  toFun w := w ∘ p
  invFun w := w ∘ p.symm
  left_inv := by intro w; ext i; simp
  right_inv := by intro w; ext i; simp

omit [DecidableEq A] in
lemma symExtension_norm (line : S → L) (v : (S → A) → ℂ) :
    (∑ w : S → L × A, Complex.normSq (symExtension line v w)) =
      (Fintype.card (Allocations line) : ℝ) * ∑ w : S → A, Complex.normSq (v w) := by
  rw [← (labelWordEquiv (S := S) (L := L) (A := A)).symm.sum_comp,
    Fintype.sum_prod_type]
  change (∑ b : S → L, ∑ w : S → A, Complex.normSq
    (if hb : counts b=counts line then v (w ∘ allocationPerm line b hb) else 0)) = _
  have he (b : S → L) : (∑ w : S → A, Complex.normSq
      (if hb : counts b=counts line then v (w ∘ allocationPerm line b hb) else 0)) =
        if counts b=counts line then ∑ w : S → A, Complex.normSq (v w) else 0 := by
    split_ifs with hb
    · exact Equiv.sum_comp (precompWordEquiv (A := A) (allocationPerm line b hb)) (fun w => Complex.normSq (v w))
    · simp
  simp_rw [he]
  simp [Finset.sum_ite, Fintype.card_subtype, Allocations]


def labelTest (line : S → L) (x : (S → A) → ℂ) (w : S → L × A) : ℂ :=
  if (fun i => (w i).1)=line then x (fun i => (w i).2) else 0

omit [DecidableEq A] in
lemma labeled_pair (line : S → L) (x : (S → A) → ℂ) (f : (S → L × A) → ℂ) :
    (∑ w, f w * labelTest line x w) = ∑ w : S → A, f (fun i => (line i,w i)) * x w := by
  rw [← (labelWordEquiv (S := S) (L := L) (A := A)).symm.sum_comp,
    Fintype.sum_prod_type]
  change (∑ b : S → L, ∑ w : S → A, f (fun i => (b i,w i)) *
    (if b=line then x w else 0)) = _
  simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp

lemma allocation_probability (line : S → L) (r : L → ℝ)
    (hr : ∀ l, 0 ≤ r l) (hs : ∑ l, r l ≤ 1) :
    (Fintype.card (Allocations line) : ℝ) * (∏ i, r (line i)) ≤ 1 := by
  have he (b : S → L) (hb : counts b=counts line) :
      (∏ i, r (b i)) = ∏ i, r (line i) := by
    rw [prod_by_counts, prod_by_counts, hb]
  have hh : (∑ b : S → L, if counts b=counts line then ∏ i, r (line i) else 0) ≤
      ∑ b : S → L, ∏ i, r (b i) := by
    apply Finset.sum_le_sum
    intro b _
    split_ifs with hb
    · exact le_of_eq (he b hb).symm
    · exact Finset.prod_nonneg (fun _ _ => hr _)
  have hl : (∑ b : S → L, if counts b=counts line then ∏ i, r (line i) else 0) =
      (Fintype.card (Allocations line) : ℝ) * (∏ i, r (line i)) := by
    simp [Finset.sum_ite, Fintype.card_subtype, Allocations]
  rw [hl, ← Fintype.prod_sum] at hh
  exact hh.trans (Finset.prod_le_one₀ (fun _ _ => Finset.sum_nonneg (fun l _ => hr l)) (fun _ _ => hs))

def lineMass (z : L × A → ℂ) (l : L) : ℝ := ∑ a, Complex.normSq (z (l,a))
def normalizedLine (z : L × A → ℂ) (l : L) (a : A) : ℂ :=
  (Real.sqrt (lineMass z l) : ℂ)⁻¹ * z (l,a)

omit [Fintype L] [DecidableEq L] [DecidableEq A] in
lemma lineMass_nonneg (z : L × A → ℂ) (l : L) : 0 ≤ lineMass z l :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

omit [Fintype L] [DecidableEq L] [DecidableEq A] in
lemma lineMass_zero (z : L × A → ℂ) (l : L) (h : lineMass z l=0) (a : A) : z (l,a)=0 := by
  apply Complex.normSq_eq_zero.mp
  have hh : Complex.normSq (z (l,a)) ≤ lineMass z l :=
    Finset.single_le_sum (fun b _ => Complex.normSq_nonneg (z (l,b))) (Finset.mem_univ a)
  exact le_antisymm (h ▸ hh) (Complex.normSq_nonneg _)

omit [Fintype L] [DecidableEq L] [DecidableEq A] in
lemma line_reconstruction (z : L × A → ℂ) (l : L) (a : A) :
    z (l,a) = (Real.sqrt (lineMass z l) : ℂ) * normalizedLine z l a := by
  by_cases hz : lineMass z l=0
  · simp [normalizedLine, hz, lineMass_zero z l hz a]
  · have h : (Real.sqrt (lineMass z l) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (lineMass_nonneg z l) (Ne.symm hz)))
    simp [normalizedLine, h]

omit [Fintype L] [DecidableEq L] [DecidableEq A] in
lemma normalizedLine_norm (z : L × A → ℂ) (l : L) :
    (∑ a, Complex.normSq (normalizedLine z l a)) ≤ 1 := by
  by_cases hz : lineMass z l=0
  · simp [normalizedLine, hz]
  · have hp : 0 < lineMass z l := lt_of_le_of_ne (lineMass_nonneg z l) (Ne.symm hz)
    simp_rw [normalizedLine, map_mul, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt (le_of_lt hp)]
    rw [← Finset.mul_sum]
    change (lineMass z l)⁻¹ * lineMass z l ≤ 1
    rw [inv_mul_cancel₀ hz]

omit [Fintype L] [DecidableEq L] [DecidableEq A] in
lemma labeled_tensor_pair (line : S → L) (z : L × A → ℂ) (x : (S → A) → ℂ) :
    Complex.normSq (∑ w : S → A, tensorVector z (fun i => (line i,w i)) * x w) =
      (∏ i, lineMass z (line i)) *
        Complex.normSq (∑ w : S → A, (∏ i, normalizedLine z (line i) (w i)) * x w) := by
  have he (w : S → A) : tensorVector z (fun i => (line i,w i)) =
      (∏ i, (Real.sqrt (lineMass z (line i)) : ℂ)) * ∏ i, normalizedLine z (line i) (w i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => line_reconstruction z (line i) (w i))
  simp_rw [he, mul_assoc]
  rw [← Finset.mul_sum, map_mul]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (Complex.normSq_ofReal _).trans (Real.mul_self_sqrt (lineMass_nonneg z (line i)))


omit [DecidableEq S] [Fintype A] [DecidableEq A] in
lemma symExtension_supported (line : S → L) (v : (S → A) → ℂ)
    (good : A → Prop) [DecidablePred good]
    (hv : ∀ w, ¬ (∀ i, good (w i)) → v w=0)
    (w : S → L × A) (hw : ¬ ∀ i, good (w i).2) : symExtension line v w=0 := by
  unfold symExtension
  split_ifs with hb
  · apply hv
    intro h
    apply hw
    intro i
    simpa using h ((allocationPerm line _ hb).symm i)
  · rfl

def lineAmplitude (line : S → L) (a₀ : S → A) (good : A → Prop) [DecidablePred good]
    (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) (l : L) (a : A) : ℂ :=
  normalizedLine (truncateAmplitude (fun c : L × A => good c.2)
    (twistedAmplitude (typeRepresentative (fun i => (line i,a₀ i)) q) θ)) l a

omit [DecidableEq S] in
omit [Fintype L] in
lemma lineAmplitude_norm (line : S → L) (a₀ : S → A) (good : A → Prop) [DecidablePred good]
    (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) (l : L) :
    (∑ a, Complex.normSq (lineAmplitude line a₀ good q θ l a)) ≤ 1 :=
  normalizedLine_norm _ _

omit [DecidableEq S] [Fintype L] in
lemma lineAmplitude_support (line : S → L) (a₀ : S → A) (good : A → Prop) [DecidablePred good]
    (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) (l : L) (a : A)
    (ha : ¬ good a) : lineAmplitude line a₀ good q θ l a=0 := by
  simp [lineAmplitude, normalizedLine, truncateAmplitude, ha]

/-- Independent fibre postselection, with the allocation factorial cancelled
by the exact multinomial probability rather than included in the overhead. -/
theorem line_symmetric_postselection (line : S → L) (a₀ : S → A) (hn : 0 < Fintype.card S)
    (good : A → Prop) [DecidablePred good] (v x : (S → A) → ℂ)
    (hv : ∀ p : Equiv.Perm S, (∀ i, line (p i)=line i) → ∀ w, v (w ∘ p)=v w)
    (hsupp : ∀ w, ¬ (∀ i, good (w i)) → v w=0) :
    Complex.normSq (∑ w, v w*x w) ≤
      (∑ w, Complex.normSq (v w)) *
      (((Fintype.card S+1)^(Fintype.card (L × A)) : ℕ) /
        (Fintype.card (Phases (L × A) (Fintype.card S)) : ℝ) *
      ∑ q : Types (S := S) (A := L × A), ∑ θ : Phases (L × A) (Fintype.card S),
        Complex.normSq (∑ w : S → A, (∏ i, lineAmplitude line a₀ good q θ (line i) (w i)) * x w)) := by
  let z (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) :=
    truncateAmplitude (fun c : L × A => good c.2)
      (twistedAmplitude (typeRepresentative (fun i => (line i,a₀ i)) q) θ)
  let R (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) :=
    Complex.normSq (∑ w : S → A, (∏ i, normalizedLine (z q θ) (line i) (w i)) * x w)
  have hz (q : Types (S := S) (A := L × A)) (θ : Phases (L × A) (Fintype.card S)) :
      (Fintype.card (Allocations line) : ℝ) * (∏ i, lineMass (z q θ) (line i)) ≤ 1 := by
    apply allocation_probability line _ (lineMass_nonneg _)
    rw [show (∑ l, lineMass (z q θ) l) = ∑ c : L × A, Complex.normSq (z q θ c) from
      (Fintype.sum_prod_type (fun c : L × A => Complex.normSq (z q θ c))).symm]
    exact truncated_twisted_subnormalized _ _ hn _
  have hh := supported_symmetric_postselection (fun i => (line i,a₀ i)) hn
    (fun c : L × A => good c.2) (symExtension line v) (labelTest line x)
    (symExtension_counts line v hv) (symExtension_supported line v good hsupp)
  rw [labeled_pair] at hh
  simp_rw [symExtension_on_line line v hv] at hh
  rw [symExtension_norm] at hh
  simp_rw [labeled_pair, labeled_tensor_pair] at hh
  let c : ℝ := ((Fintype.card S+1)^(Fintype.card (L × A)) : ℕ) /
    (Fintype.card (Phases (L × A) (Fintype.card S)) : ℝ)
  change _ ≤ ((Fintype.card (Allocations line) : ℝ) * ∑ w, Complex.normSq (v w)) *
    (c * ∑ q, ∑ θ, (∏ i, lineMass (z q θ) (line i)) * R q θ) at hh
  change _ ≤ (∑ w, Complex.normSq (v w)) * (c * ∑ q, ∑ θ, R q θ)
  apply hh.trans
  rw [show ((Fintype.card (Allocations line) : ℝ) * ∑ w, Complex.normSq (v w)) *
      (c * ∑ q, ∑ θ, (∏ i, lineMass (z q θ) (line i)) * R q θ) =
    (∑ w, Complex.normSq (v w)) * (c * ((Fintype.card (Allocations line) : ℝ) *
      ∑ q, ∑ θ, (∏ i, lineMass (z q θ) (line i)) * R q θ)) by ring]
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ c)
  simp_rw [Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun θ _ =>
    (mul_le_mul_of_nonneg_right (hz q θ) (Complex.normSq_nonneg _)).trans_eq (one_mul _)))

end RowColumn.Postselection

end
end


section
noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator ComplexOrder MatrixOrder
namespace RowColumn.Postselection
open MatrixState WordOrbits
variable {S L C : Type*} [Fintype S] [DecidableEq S] [Fintype L] [DecidableEq L]
  [Fintype C] [DecidableEq C]

def lineState (line : S → L) (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := L × (C × C))) (θ : Phases (L × (C × C)) (Fintype.card S))
    (l : L) : Matrix C C ℂ :=
  gramState (lineAmplitude line a₀ (fun p : C × C => odd p.1 ↔ odd p.2) q θ l)

omit [DecidableEq S] [Fintype L] in
lemma lineState_positive (line : S → L) (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := L × (C × C))) (θ : Phases (L × (C × C)) (Fintype.card S)) (l : L) :
    (lineState line a₀ odd q θ l).PosSemidef := gramState_posSemidef _

omit [DecidableEq S] in
omit [Fintype L] in
lemma lineState_trace (line : S → L) (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := L × (C × C))) (θ : Phases (L × (C × C)) (Fintype.card S)) (l : L) :
    (lineState line a₀ odd q θ l).trace.re ≤ 1 := by
  rw [lineState, gramState_trace]
  exact lineAmplitude_norm _ _ _ _ _ _

omit [DecidableEq S] [Fintype L] in
lemma lineState_even (line : S → L) (a₀ : S → C × C) (odd : C → Prop) [DecidablePred odd]
    (q : Types (S := S) (A := L × (C × C))) (θ : Phases (L × (C × C)) (Fintype.card S))
    (l : L) (c d : C) (h : ¬ (odd c ↔ odd d)) : lineState line a₀ odd q θ l c d=0 := by
  apply gramState_parity_supported odd _ _ c d h
  exact fun c d h => lineAmplitude_support _ _ _ _ _ _ _ h

lemma variable_purification_pair (z : S → C × C → ℂ) (x : (S → C) → ℂ) (v : S → C) :
    (∑ a : S → C × C, (∏ i, z i (a i)) * purificationTest x v a) =
      ∑ w : S → C, tensorMatrix (fun i => letterMatrix (z i)) w v * x w := by
  exact purification_pair (tensorMatrix (fun i => letterMatrix (z i))) x v

lemma variable_purification_quadratic (z : S → C × C → ℂ) (x : (S → C) → ℂ) :
    (∑ v : S → C, Complex.normSq (∑ a : S → C × C,
      (∏ i, z i (a i)) * purificationTest x v a)) =
      quadratic (tensorMatrix (fun i => gramState (z i))) x := by
  simp_rw [variable_purification_pair]
  change factorQuadratic (tensorMatrix (fun i => letterMatrix (z i))) x = _
  rw [factorQuadratic_eq, tensorMatrix_star, tensorMatrix_mul]
  rfl

/-- Explicit local domination for independent row/column permutation fibres.
All mixture terms are genuine even positive identical-slot substates within
each fibre, irrespective of its size and the deletion layout. -/
theorem positive_line_postselection (line : S → L) (a₀ : S → C × C) (hn : 0 < Fintype.card S)
    (odd : C → Prop) [DecidablePred odd] (A : Matrix (S → C) (S → C) ℂ)
    (hA : A.PosSemidef)
    (hinv : ∀ (p : Equiv.Perm S), (∀ i, line (p i)=line i) → ∀ (w v : S → C),
      A (w ∘ p) (v ∘ p)=A w v)
    (hsupp : ∀ w v, ¬ (∀ i, odd (w i) ↔ odd (v i)) → A w v=0)
    (x : (S → C) → ℂ) :
    quadratic A x ≤ A.trace.re *
      (((Fintype.card S+1)^(Fintype.card (L × (C × C))) : ℕ) /
        (Fintype.card (Phases (L × (C × C)) (Fintype.card S)) : ℝ) *
      ∑ q : Types (S := S) (A := L × (C × C)),
      ∑ θ : Phases (L × (C × C)) (Fintype.card S),
        quadratic (tensorMatrix (fun i : S => lineState line a₀ odd q θ (line i))) x) := by
  let B : Matrix (S → C) (S → C) ℂ := CFC.sqrt A
  have hi (p : Equiv.Perm S) (hp : ∀ i, line (p i)=line i) (w v : S → C) :
      B (w ∘ p) (v ∘ p)=B w v :=
    sqrt_permutation_invariant A hA (reindexWord p) (hinv p hp) w v
  have hz (w v : S → C) (hh : ¬ ∀ i, odd (w i) ↔ odd (v i)) : B w v=0 := by
    apply sqrt_block_supported (fun u : S → C => fun i => odd (u i)) A hA
      (fun u v he => hsupp u v (fun ht => he (funext fun i => propext (ht i)))) w v
    intro he
    exact hh (fun i => Iff.of_eq (congrFun he i))
  have hv (p : Equiv.Perm S) (hp : ∀ i, line (p i)=line i) (w : S → C × C) :
      purificationVector B (w ∘ p)=purificationVector B w :=
    hi p hp (fun i => (w i).1) (fun i => (w i).2)
  have hs (w : S → C × C) (hw : ¬ ∀ i, odd (w i).1 ↔ odd (w i).2) : purificationVector B w=0 :=
    hz _ _ hw
  have hh (v : S → C) := line_symmetric_postselection line a₀ hn
    (fun p : C × C => odd p.1 ↔ odd p.2) (purificationVector B) (purificationTest x v) hv hs
  simp only [purification_pair B x, purification_normSq B] at hh
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hh v)
  change factorQuadratic B x ≤ _ at hsum
  have ht : purifierTrace B=A.trace.re := sqrt_trace A hA
  rw [ht] at hsum
  change factorQuadratic (CFC.sqrt A) x ≤ _ at hsum
  rw [sqrt_factorQuadratic A hA] at hsum
  apply hsum.trans_eq
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ _
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  exact variable_purification_quadratic _ x

end RowColumn.Postselection

end
end

end OAI
