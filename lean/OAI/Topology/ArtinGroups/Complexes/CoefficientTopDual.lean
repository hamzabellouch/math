import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PureCoefficientCohomology
import OAI.Topology.ArtinGroups.Complexes.CoefficientSocle

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

def coefficientTopDual (E : BasedComplex Q (K := K) I) (α : V) (c : ℤ) :
    Submodule K (I → K) where
  carrier := {x | (∀ i, (E.placement i).color ≠ α ∨ (E.placement i).cochain ≠ c → x i = 0) ∧
    ∀ i a, ∑ j, (E.differential i j).arrow a * x j = 0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    rintro x y ⟨hx,hxd⟩ ⟨hy,hyd⟩
    constructor
    · intro i hi; simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]
    · intro i a
      simp only [Pi.add_apply, _root_.mul_add, Finset.sum_add_distrib, hxd i a, hyd i a, add_zero]
  smul_mem' := by
    rintro r x ⟨hx,hxd⟩
    constructor
    · intro i hi; simp only [Pi.smul_apply, hx i hi, smul_zero]
    · intro i a
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ r, ← Finset.mul_sum, hxd i a,
        MulZeroClass.mul_zero]

noncomputable def topSocleMatrix (α : V) (x : I → K) (y : J → K) :
    Matrix I J (Q.Zigzag K) := fun i j => (x i * y j) • vertexId Q α

omit [Fintype V] [DecidableEq A] in
lemma topSocleMatrix_mem_homSpace (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) {x : I → K} {y : J → K}
    (hx : x ∈ coefficientTopDual Q E α c) (hy : y ∈ coefficientSocle Q F α d) :
    topSocleMatrix Q α x y ∈ homSpace Q E F (d-c) (k-l-(d-c)) := by
  have hs i j : x i * y j ≠ 0 →
      (E.placement i).color = α ∧ (E.placement i).cochain = c ∧
      (F.placement j).color = α ∧ (F.placement j).cochain = d := by
    intro h
    obtain ⟨hi,hj⟩ := mul_ne_zero_iff.mp h
    exact ⟨not_ne_iff.mp (fun hh => hi (hx.1 i (Or.inl hh))),
      not_ne_iff.mp (fun hh => hi (hx.1 i (Or.inr hh))),
      not_ne_iff.mp (fun hh => hj (hy.1 j (Or.inl hh))),
      not_ne_iff.mp (fun hh => hj (hy.1 j (Or.inr hh)))⟩
  constructor
  · constructor
    · intro i j
      by_cases hh : x i * y j = 0
      · simp only [topSocleMatrix, hh, zero_smul, MulZeroClass.mul_zero]
      · rw [(hs i j hh).1]
        simp only [topSocleMatrix, mul_smul, vertexId_mul_self]
    · intro i j
      by_cases hh : x i * y j = 0
      · simp only [topSocleMatrix, hh, zero_smul, MulZeroClass.zero_mul]
      · rw [(hs i j hh).2.2.1]
        simp only [topSocleMatrix, smul_mul_assoc, vertexId_mul_self]
  · intro i j
    by_cases hh : x i * y j = 0
    · simp only [topSocleMatrix, hh, zero_smul]
      exact ⟨fun _ => trivial, ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩
    · obtain ⟨_,hi,_,hj⟩ := hs i j hh
      constructor
      · intro h; exact (h (by omega)).elim
      · have hl := hE i
        have hk := hF j
        dsimp only [GeneratorPlacement.level] at hl hk
        have heq : k-l-(d-c)+(E.placement i).internal-(F.placement j).internal = 0 := by omega
        rw [heq]
        exact homogeneous_smul Q (homogeneous_vertexId Q α) _

omit [Fintype V] [DecidableEq A] in
lemma pure_differential_linear (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level = l) : LinearMatrix Q E.differential :=
  pure_homSpace_linear Q E E hE hE (by omega) ⟨E.entries,E.degree⟩

omit [Fintype V] [DecidableEq A] in
lemma token_sum {T : Type*} (s : Finset T) (f : T → Q.Zigzag K) :
    (∑ t ∈ s, f t).token = ∑ t ∈ s, (f t).token :=
  map_sum ({ toFun := token
             map_add' := fun _ _ => rfl
             map_smul' := fun _ _ => rfl } : Q.Zigzag K →ₗ[K] (V → K)) f s

omit [Fintype V] [DecidableEq A] [Fintype J] in
lemma differential_topSocleMatrix (E : BasedComplex Q (K := K) I) {l : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (α : V) (c : ℤ)
    {x : I → K} (hx : x ∈ coefficientTopDual Q E α c) (y : J → K) :
    E.differential * topSocleMatrix Q α x y = 0 := by
  have hlin := pure_differential_linear Q E hE
  apply Matrix.ext
  intro i j
  apply ext
  · ext β
    simp only [Matrix.mul_apply, vertex_sum, Finset.sum_apply, vertex_mul,
      (hlin i _).1, Pi.zero_apply, MulZeroClass.zero_mul, Finset.sum_const_zero]
    rfl
  · ext a
    simp only [Matrix.mul_apply, arrow_sum, Finset.sum_apply, arrow_mul, Pi.add_apply,
      leftScale, rightScale, (hlin i _).1, Pi.zero_apply, MulZeroClass.zero_mul, zero_add,
      topSocleMatrix, vertex_smul, Pi.smul_apply, smul_eq_mul, vertexId_eval]
    by_cases ha : Q.target a = α
    · simp only [ha, ← _root_.mul_assoc, ← Finset.sum_mul, hx.2 i a,
        MulZeroClass.zero_mul]
      rfl
    · simp only [ite_eq_right ha, MulZeroClass.mul_zero, Finset.sum_const_zero]
      rfl
  · ext β
    simp only [Matrix.mul_apply, token_sum, Finset.sum_apply, token_mul,
      (hlin i _).1, (hlin i _).2, Pi.zero_apply, MulZeroClass.zero_mul,
      zero_add, topSocleMatrix, arrow_smul, arrow_vertexId, smul_zero, backtrack,
      Pi.zero_apply, MulZeroClass.mul_zero, ite_self, Finset.sum_const_zero]
    rfl

omit [Fintype V] [DecidableEq A] [Fintype I] in
lemma topSocleMatrix_differential (F : BasedComplex Q (K := K) J) {k : ℤ}
    (hF : ∀ j, (F.placement j).level = k) (α : V) (d : ℤ)
    (x : I → K) {y : J → K} (hy : y ∈ coefficientSocle Q F α d) :
    topSocleMatrix Q α x y * F.differential = 0 := by
  have hlin := pure_differential_linear Q F hF
  apply Matrix.ext
  intro i j
  apply ext
  · ext β
    simp only [Matrix.mul_apply, vertex_sum, Finset.sum_apply, vertex_mul,
      (hlin _ j).1, Pi.zero_apply, MulZeroClass.mul_zero, Finset.sum_const_zero]
    rfl
  · ext a
    simp only [Matrix.mul_apply, arrow_sum, Finset.sum_apply, arrow_mul, Pi.add_apply,
      leftScale, rightScale, (hlin _ j).1, Pi.zero_apply, MulZeroClass.mul_zero, add_zero,
      topSocleMatrix, vertex_smul, Pi.smul_apply, smul_eq_mul, vertexId_eval]
    by_cases ha : Q.source a = α
    · simp only [ite_eq_left ha, _root_.mul_one, _root_.mul_assoc, ← Finset.mul_sum, hy.2 j a ha,
        MulZeroClass.mul_zero]
      rfl
    · simp only [ite_eq_right ha, MulZeroClass.mul_zero, MulZeroClass.zero_mul, Finset.sum_const_zero]
      rfl
  · ext β
    simp only [Matrix.mul_apply, token_sum, Finset.sum_apply, token_mul,
      (hlin _ j).1, (hlin _ j).2, Pi.zero_apply, MulZeroClass.mul_zero,
      zero_add, topSocleMatrix, arrow_smul, arrow_vertexId, smul_zero, backtrack,
      Pi.zero_apply, MulZeroClass.zero_mul, ite_self, Finset.sum_const_zero]
    rfl

omit [Fintype V] [DecidableEq A] in
lemma topSocleMatrix_mem_homCycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) {x : I → K} {y : J → K}
    (hx : x ∈ coefficientTopDual Q E α c) (hy : y ∈ coefficientSocle Q F α d) :
    topSocleMatrix Q α x y ∈ homCycles Q E F (d-c) (k-l-(d-c)) := by
  refine ⟨topSocleMatrix_mem_homSpace Q E F hE hF α c d hx hy, ?_⟩
  change E.differential * topSocleMatrix Q α x y -
    cochainSign (K := K) (d-c) • (topSocleMatrix Q α x y * F.differential) = 0
  rw [differential_topSocleMatrix Q E hE α c hx,
    topSocleMatrix_differential Q F hF α d x hy, smul_zero, sub_self]

omit [Fintype V] [DecidableEq A] [Fintype I] [Fintype J] in
lemma topSocleMatrix_ne_zero (α : V) {x : I → K} {y : J → K}
    (hx : x ≠ 0) (hy : y ≠ 0) : topSocleMatrix Q α x y ≠ 0 := by
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (funext hn)
  obtain ⟨j,hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hy (funext hn)
  intro hz
  have he := congrArg (fun f : Matrix I J (Q.Zigzag K) => (f i j).vertex α) hz
  have h : x i * y j = 0 := by
    simpa [topSocleMatrix, vertexId_eval] using he
  exact (mul_ne_zero hi hj) h

omit [DecidableEq A] in
lemma pure_top_socle_homDimension_pos (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) (ht : coefficientTopDual Q E α c ≠ ⊥)
    (hs : coefficientSocle Q F α d ≠ ⊥) :
    0 < homDimension Q E F (d-c) (k-l-(d-c)) := by
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht
  obtain ⟨y,hy,hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  let f : homCycles Q E F (d-c) (k-l-(d-c)) :=
    ⟨topSocleMatrix Q α x y, topSocleMatrix_mem_homCycles Q E F hE hF α c d hx hy⟩
  have hf : f ≠ 0 := fun h => topSocleMatrix_ne_zero Q α hx0 hy0 (congrArg Subtype.val h)
  unfold homDimension
  rw [(pureCoefficientCohomology Q E F hE hF (by omega)).finrank_eq]
  exact Module.finrank_pos_iff.mpr ⟨⟨f,0,hf⟩⟩

omit [Fintype V] [DecidableEq A] in
lemma homDimension_le_totalHomDimension (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (n v : ℤ) :
    homDimension Q E F n v ≤ totalHomDimension Q E F (n+v) := by
  classical
  by_cases hv : v ∈ homInternalSupport Q E F
  · unfold totalHomDimension
    have h' := Finset.single_le_sum (f := fun w => homDimension Q E F (n+v-w) w)
      (fun _ _ => Nat.zero_le _) hv
    simpa only [add_sub_cancel_right] using h'
  · rw [homDimension_off_internal_support Q E F n v hv]
    exact Nat.zero_le _

omit [DecidableEq A] in
lemma pure_top_socle_totalHomDimension_pos (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) (ht : coefficientTopDual Q E α c ≠ ⊥)
    (hs : coefficientSocle Q F α d ≠ ⊥) :
    0 < totalHomDimension Q E F (k-l) := by
  have h := lt_of_lt_of_le (pure_top_socle_homDimension_pos Q E F hE hF α c d ht hs)
    (homDimension_le_totalHomDimension Q E F (d-c) (k-l-(d-c)))
  convert h using 1
  congr 1
  omega

omit [DecidableEq A] in
lemma pure_top_zero_of_socle_hom_zero (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (α : V) (c d : ℤ) (hs : coefficientSocle Q F α d ≠ ⊥)
    (hh : totalHomDimension Q E F (k-l) = 0) : coefficientTopDual Q E α c = ⊥ := by
  by_contra ht
  have h := pure_top_socle_totalHomDimension_pos Q E F hE hF α c d ht hs
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
