import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PureHomSpaceHomogeneous
import OAI.Topology.ArtinGroups.Complexes.HomInternalSupport

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

def coefficientSocle (E : BasedComplex Q (K := K) I) (α : V) (c : ℤ) :
    Submodule K (I → K) where
  carrier := {x | (∀ i, (E.placement i).color ≠ α ∨ (E.placement i).cochain ≠ c → x i = 0) ∧
    ∀ j a, Q.source a = α → ∑ i, x i * (E.differential i j).arrow a = 0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    rintro x y ⟨hx,hxd⟩ ⟨hy,hyd⟩
    constructor
    · intro i hi; simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]
    · intro j a ha
      simp only [Pi.add_apply, _root_.add_mul, Finset.sum_add_distrib, hxd j a ha, hyd j a ha, add_zero]
  smul_mem' := by
    rintro r x ⟨hx,hxd⟩
    constructor
    · intro i hi; simp only [Pi.smul_apply, hx i hi, smul_zero]
    · intro j a ha
      simp only [Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, ← Finset.mul_sum, hxd j a ha,
        MulZeroClass.mul_zero]

omit [Fintype V] [DecidableEq A] [Fintype I] [Fintype J] in
lemma entry_vertex_left_support {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q p q f)
    (i : I) (j : J) (α : V) (hα : α ≠ (p i).color) : (f i j).vertex α = 0 := by
  have hh := congrArg (fun z : Q.Zigzag K => z.vertex α) (hf.1 i j)
  change (vertexId Q (p i).color).vertex α * (f i j).vertex α = _ at hh
  rw [vertexId_eval, ite_eq_right hα, MulZeroClass.zero_mul] at hh
  exact hh.symm

omit [Fintype V] [DecidableEq A] [Fintype I] [Fintype J] in
lemma entry_vertex_right_support {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q p q f)
    (i : I) (j : J) (α : V) (hα : α ≠ (q j).color) : (f i j).vertex α = 0 := by
  have hh := congrArg (fun z : Q.Zigzag K => z.vertex α) (hf.2 i j)
  change (f i j).vertex α * (vertexId Q (q j).color).vertex α = _ at hh
  rw [vertexId_eval, ite_eq_right hα, MulZeroClass.mul_zero] at hh
  exact hh.symm

omit [Fintype V] [DecidableEq A] in
lemma coefficient_row_zero {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q E.placement F.placement f)
    (hc : CoefficientMatrix Q f) (i : I)
    (hz : ∀ j, (f i j).vertex (E.placement i).color = 0) : ∀ j, f i j = 0 := by
  intro j
  apply ext
  · funext α
    by_cases ha : α = (E.placement i).color
    · subst α; exact hz j
    · exact entry_vertex_left_support Q hf i j α ha
  · exact (hc i j).1
  · exact (hc i j).2

omit [Fintype V] [DecidableEq A] in

lemma coefficient_cocycle_zero_of_socle_zero
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (n v : ℤ) (active : Set V)
    (hE : ∀ i, (E.placement i).color ∈ active)
    (hF : ∀ α ∈ active, ∀ c, coefficientSocle Q F α c = ⊥)
    {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homCycles Q E F n v)
    (hc : CoefficientMatrix Q f) : f = 0 := by
  classical
  by_contra hne
  let support : Finset I := Finset.univ.filter fun i => ∃ j, f i j ≠ 0
  have hs : support.Nonempty := by
    by_contra hh
    apply hne
    apply Matrix.ext
    intro i j
    by_contra hz
    exact hh ⟨i, by simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j,hz⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image support (fun i => (E.placement i).cochain) hs
  have hrow : ∀ j, (E.differential * f) i j = 0 := by
    intro j
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : t ∈ support
    · have htdeg := hmax t ht
      have hz := (E.degree i t).1 (by omega)
      rw [hz, MulZeroClass.zero_mul]
    · have hz : f t j = 0 := by
        by_contra hh
        exact ht (by simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨j,hh⟩)
      rw [hz, MulZeroClass.mul_zero]
  have hout : ∀ j, (f * F.differential) i j = 0 := by
    intro j
    have hh := congrArg (fun m : Matrix I J (Q.Zigzag K) => m i j) hf.2
    change (E.differential*f) i j - cochainSign (K := K) n • (f*F.differential) i j = 0 at hh
    rw [hrow j, zero_sub, neg_eq_zero] at hh
    exact (smul_eq_zero.mp hh).resolve_left (cochainSign_ne_zero (K := K) n)
  let x : J → K := fun j => (f i j).vertex (E.placement i).color
  have hx : x ∈ coefficientSocle Q F (E.placement i).color ((E.placement i).cochain+n) := by
    constructor
    · intro j hj
      rcases hj with hj | hj
      · exact entry_vertex_right_support Q hf.1.1 i j _ (Ne.symm hj)
      · change (f i j).vertex _ = 0
        rw [(hf.1.2 i j).1 hj]
        rfl
    · intro j a ha
      have hh := congrArg (fun z : Q.Zigzag K => z.arrow a) (hout j)
      rw [Matrix.mul_apply, arrow_sum] at hh
      simp only [Finset.sum_apply, arrow_mul, Pi.add_apply, leftScale, rightScale,
        (hc i _).1, Pi.zero_apply, MulZeroClass.zero_mul, add_zero, ha] at hh
      exact hh
  have hxzero : x = 0 := by
    simpa only [hF _ (hE i) _, Submodule.mem_bot] using hx
  obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hi).2
  apply hj
  exact coefficient_row_zero Q hf.1.1 hc i (fun j => congrFun hxzero j) j

omit [Fintype V] [DecidableEq A] in
lemma pure_coefficient_homDimension_zero_of_socle_zero
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l k n v : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k) (h : n+v=k-l)
    (active : Set V) (hsE : ∀ i, (E.placement i).color ∈ active)
    (hsF : ∀ α ∈ active, ∀ c, coefficientSocle Q F α c = ⊥) :
    homDimension Q E F n v = 0 := by
  have hz : homCycles Q E F n v = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    exact coefficient_cocycle_zero_of_socle_zero Q E F n v active hsE hsF hf
      (pure_homSpace_coefficient Q E F hE hF h hf.1)
  unfold homDimension
  have : Subsingleton (homCycles Q E F n v) := by rw [hz]; infer_instance
  have : Subsingleton (homCohomology Q E F n v) := inferInstance
  exact Module.finrank_zero_of_subsingleton

omit [Fintype V] [DecidableEq A] in
lemma pure_total_coefficient_homDimension_zero_of_socle_zero
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    {l k : ℤ} (hE : ∀ i, (E.placement i).level = l)
    (hF : ∀ j, (F.placement j).level = k)
    (active : Set V) (hsE : ∀ i, (E.placement i).color ∈ active)
    (hsF : ∀ α ∈ active, ∀ c, coefficientSocle Q F α c = ⊥) :
    totalHomDimension Q E F (k-l) = 0 := by
  unfold totalHomDimension
  apply Finset.sum_eq_zero
  intro v _
  exact pure_coefficient_homDimension_zero_of_socle_zero Q E F hE hF (by omega)
    active hsE hsF

omit [Fintype V] [DecidableEq A] in

lemma coefficientSocle_nonzero_at_max (E : BasedComplex Q (K := K) I)
    (i : I) (hi : ∀ j, (E.placement j).cochain ≤ (E.placement i).cochain) :
    coefficientSocle Q E (E.placement i).color (E.placement i).cochain ≠ ⊥ := by
  classical
  let x : I → K := Pi.single i 1
  have hx : x ∈ coefficientSocle Q E (E.placement i).color (E.placement i).cochain := by
    constructor
    · intro j hj
      have hji : j ≠ i := by rintro rfl; simp at hj
      simp [x, hji]
    · intro j a _
      change ∑ t, Pi.single (M := fun _ : I => K) i (1 : K) t * (E.differential t j).arrow a = 0
      simp only [Pi.single_apply, ite_mul, _root_.one_mul, MulZeroClass.zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have hd := (E.degree i j).1 (by have := hi j; omega)
      rw [hd]
      rfl
  intro hs
  have hz : x = 0 := by simpa only [hs, Submodule.mem_bot] using hx
  have hh := congrFun hz i
  simp [x] at hh

omit [Fintype V] [DecidableEq A] in
lemma exists_coefficientSocle_nonzero (E : BasedComplex Q (K := K) I) [Nonempty I] :
    ∃ α c, coefficientSocle Q E α c ≠ ⊥ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => (E.placement i).cochain) Finset.univ_nonempty
  exact ⟨_,_,coefficientSocle_nonzero_at_max Q E i (fun j => hi j (Finset.mem_univ j))⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
