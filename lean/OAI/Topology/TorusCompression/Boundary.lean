import Mathlib

namespace OAI

/-! Boundary restoration, bundle rank bounds and elementary torus compression. -/

noncomputable section

namespace TorusCompression

open Set Metric
open scoped Classical

abbrev Slot (t : ℕ) := Fin t → ℝ
abbrev Slots (t n : ℕ) := Fin n → Slot t

def cubeSet (t n : ℕ) : Set (Slots t n) := {x | ∀ j, ‖x j‖ ≤ 1}
abbrev Cube (t n : ℕ) := {x : Slots t n // x ∈ cubeSet t n}

def OnBoundary {t : ℕ} (v : Slot t) : Prop := ‖v‖ = 1

lemma slot_unit_ball (t : ℕ) :
    {v : Slot t | ∀ i, v i ∈ Icc (-1 : ℝ) 1} = closedBall 0 1 := by
  ext v
  simp only [mem_ofPred_eq, mem_Icc, mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [Real.norm_eq_abs, abs_le]

lemma onBoundary_iff_frontier {t : ℕ} (v : Slot t) :
    OnBoundary v ↔ v ∈ frontier {w : Slot t | ∀ i, w i ∈ Icc (-1 : ℝ) 1} := by
  rw [slot_unit_ball, frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
  simp [OnBoundary]

def support {t n : ℕ} (x : Slots t n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j ≠ 0)

def Sparse {t n : ℕ} (s : ℕ) : Set (Slots t n) := {x | (support x).card ≤ s}

def sparseParameters (t n : ℕ) (s : ℝ) : Set (Slots t n) :=
  {z | (∀ j, ‖z j‖ ≤ 2) ∧ ((support z).card : ℝ) ≤ s}

def boundarySlots {t n : ℕ} (x : Slots t n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => OnBoundary (x j))

@[simp] lemma mem_support {t n : ℕ} (x : Slots t n) (j : Fin n) :
    j ∈ support x ↔ x j ≠ 0 := by simp [support]

@[simp] lemma mem_boundarySlots {t n : ℕ} (x : Slots t n) (j : Fin n) :
    j ∈ boundarySlots x ↔ OnBoundary (x j) := by simp [boundarySlots]

@[simp] lemma support_zero (t n : ℕ) : support (0 : Slots t n) = ∅ := by
  ext j
  simp

lemma sparse_nonempty (t n s : ℕ) : (Sparse (t := t) (n := n) s).Nonempty := by
  exact ⟨0, by simp [Sparse]⟩

lemma sparse_eq_union (t n s : ℕ) :
    Sparse (t := t) (n := n) s =
      ⋃ A : {A : Finset (Fin n) // A.card ≤ s},
        {x : Slots t n | ∀ j, j ∉ A.val → x j = 0} := by
  ext x
  constructor
  · intro hx
    refine mem_iUnion.mpr ⟨⟨support x, hx⟩, ?_⟩
    intro j hj
    simpa using hj
  · intro hx
    obtain ⟨A, hA⟩ := mem_iUnion.mp hx
    exact (Finset.card_le_card (show support x ⊆ A.val from by
      intro j hj
      by_contra hjA
      exact (mem_support x j).mp hj (hA j hjA))).trans A.property

lemma isClosed_sparse (t n s : ℕ) : IsClosed (Sparse (t := t) (n := n) s) := by
  rw [sparse_eq_union]
  apply isClosed_iUnion_of_finite
  intro A
  simp only [ofPred_forall]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply j)
      (continuous_const : Continuous (fun _ : Slots t n => (0 : Slot t)))

lemma sparseParameters_eq_empty {t n : ℕ} {s : ℝ} (hs : s < 0) :
    sparseParameters t n s = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hcard : (0 : ℝ) ≤ (support x).card := Nat.cast_nonneg _
  exact (not_le_of_gt hs) (hcard.trans hx.2)

lemma sparseParameters_eq_inter {t n : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    sparseParameters t n s = closedBall (0 : Slots t n) 2 ∩ Sparse ⌊s⌋₊ := by
  ext x
  simp only [sparseParameters, Sparse, mem_ofPred_eq, mem_inter_iff,
    mem_closedBall, dist_zero_right]
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact and_congr Iff.rfl (Nat.le_floor_iff hs).symm

lemma isCompact_sparseParameters (t n : ℕ) (s : ℝ) :
    IsCompact (sparseParameters t n s) := by
  by_cases hs : 0 ≤ s
  · rw [sparseParameters_eq_inter hs]
    exact (isCompact_closedBall (0 : Slots t n) 2).inter_right (isClosed_sparse t n ⌊s⌋₊)
  · rw [sparseParameters_eq_empty (lt_of_not_ge hs)]
    exact isCompact_empty

lemma sparseParameters_eq_parameterCube {t n : ℕ} {s : ℝ} (hs : (n : ℝ) ≤ s) :
    sparseParameters t n s = {z : Slots t n | ∀ j, ‖z j‖ ≤ 2} := by
  ext z
  refine ⟨fun hz => hz.1, fun hz => ⟨hz, ?_⟩⟩
  have hcard : (support z).card ≤ n := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin n)
  exact (Nat.cast_le.mpr hcard).trans hs

def restorationRadius {t n : ℕ} (s : ℕ) (x : Slots t n) : ℝ :=
  min (1 / 2) (infDist x (Sparse s) / 2)

lemma continuous_restorationRadius (t n s : ℕ) :
    Continuous (restorationRadius (t := t) (n := n) s) := by
  unfold restorationRadius
  exact continuous_const.min ((continuous_infDist_pt (Sparse s)).div_const 2)

lemma restorationRadius_pos {t n s : ℕ} {x : Slots t n} (hx : x ∉ Sparse s) :
    0 < restorationRadius s x := by
  have h := (isClosed_sparse t n s).notMem_iff_infDist_pos (sparse_nonempty t n s) |>.mp hx
  exact lt_min (by norm_num) (by positivity)

lemma restorationRadius_le_half {t n s : ℕ} (x : Slots t n) :
    restorationRadius s x ≤ 1 / 2 := min_le_left _ _

lemma restorationRadius_lt_infDist {t n s : ℕ} {x : Slots t n}
    (hx : x ∉ Sparse s) : restorationRadius s x < infDist x (Sparse s) := by
  have h := (isClosed_sparse t n s).notMem_iff_infDist_pos (sparse_nonempty t n s) |>.mp hx
  exact (min_le_right _ _).trans_lt (by linarith)

lemma many_large_slots {t n s : ℕ} {x : Slots t n} (hx : x ∉ Sparse s) :
    s < (Finset.univ.filter (fun j => restorationRadius s x ≤ ‖x j‖)).card := by
  let δ := restorationRadius s x
  have hδ : 0 < δ := restorationRadius_pos hx
  let A : Finset (Fin n) := Finset.univ.filter (fun j => δ ≤ ‖x j‖)
  let y : Slots t n := fun j => if j ∈ A then x j else 0
  by_contra h
  have hA : A.card ≤ s := Nat.le_of_not_lt h
  have hy : y ∈ Sparse s := by
    apply le_trans (Finset.card_le_card (show support y ⊆ A from ?_)) hA
    intro j hj
    by_contra hjA
    have hnonzero := (mem_support y j).mp hj
    exact hnonzero (by simp [y, hjA])
  have hdist : dist x y ≤ δ := by
    rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hδ.le]
    intro j
    by_cases hj : j ∈ A
    · simp [y, hj, hδ.le]
    · have hj' : ‖x j‖ < δ := by simpa [A] using hj
      simpa [y, hj] using hj'.le
  have hlt := restorationRadius_lt_infDist hx
  exact not_lt_of_ge ((infDist_le_dist_of_mem hy).trans hdist) hlt

def radial {t : ℕ} (δ : ℝ) (v : Slot t) : Slot t :=
  (max δ ‖v‖)⁻¹ • v

lemma norm_radial_le_one {t : ℕ} {δ : ℝ} (hδ : 0 < δ) (v : Slot t) :
    ‖radial δ v‖ ≤ 1 := by
  have hden : 0 < max δ ‖v‖ := hδ.trans_le (le_max_left _ _)
  rw [radial, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hden, ← div_eq_inv_mul]
  exact (div_le_one hden).mpr (le_max_right _ _)

lemma radial_boundary {t : ℕ} {δ : ℝ} (hδ : 0 < δ) {v : Slot t}
    (hv : δ ≤ ‖v‖) : OnBoundary (radial δ v) := by
  have hn : 0 < ‖v‖ := hδ.trans_le hv
  simp [OnBoundary, radial, max_eq_right hv, norm_smul, inv_mul_cancel₀ hn.ne']

lemma radial_fixes_boundary {t : ℕ} {δ : ℝ} (hδ : δ ≤ 1) {v : Slot t}
    (hv : OnBoundary v) : radial δ v = v := by
  simp [radial, show ‖v‖ = 1 from hv, max_eq_right hδ]

def cutoff {t : ℕ} (v : Slot t) : ℝ := max 0 (4 * ‖v‖ - 3)

def blend {t : ℕ} (v w : Slot t) : Slot t :=
  (1 - cutoff v) • w + cutoff v • v

lemma cutoff_range {t : ℕ} {v : Slot t} (hv : ‖v‖ ≤ 1) :
    0 ≤ cutoff v ∧ cutoff v ≤ 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  linarith

lemma blend_sub {t : ℕ} (v w : Slot t) :
    blend v w - v = (1 - cutoff v) • (w - v) := by
  simp only [blend, smul_sub, sub_smul, one_smul]
  abel

lemma norm_blend_sub_le {t : ℕ} {v w : Slot t} (hv : ‖v‖ ≤ 1) :
    ‖blend v w - v‖ ≤ ‖w - v‖ := by
  obtain ⟨h0, h1⟩ := cutoff_range hv
  rw [blend_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h1)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

lemma blend_nonzero {t : ℕ} {v w : Slot t} (hv : ‖v‖ ≤ 1)
    (hvw : ‖w - v‖ < 1 / 2) (hw : w ≠ 0) : blend v w ≠ 0 := by
  by_cases hχ : cutoff v = 0
  · simpa [blend, hχ] using hw
  · have hχpos : 0 < cutoff v := lt_of_le_of_ne (cutoff_range hv).1 (Ne.symm hχ)
    have hnorm : 3 / 4 < ‖v‖ := by
      have h := (lt_max_iff.mp hχpos).resolve_left (lt_irrefl 0)
      linarith
    intro hzero
    have h := (norm_blend_sub_le hv).trans_lt hvw
    rw [hzero, zero_sub, norm_neg] at h
    linarith

lemma blend_fixes_boundary {t : ℕ} {v w : Slot t} (hv : OnBoundary v) :
    blend v w = v := by
  have hχ : cutoff v = 1 := by simp [cutoff, show ‖v‖ = 1 from hv]; norm_num
  simp [blend, hχ]

lemma continuous_blend {t : ℕ} : Continuous (fun p : Slot t × Slot t => blend p.1 p.2) := by
  unfold blend cutoff
  fun_prop

lemma continuous_blend_of {X : Type*} [TopologicalSpace X] {t : ℕ}
    {v w : X → Slot t} (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x => blend (v x) (w x)) := by
  have hc : Continuous (fun x => cutoff (v x)) :=
    continuous_const.max ((continuous_const.mul hv.norm).sub continuous_const)
  exact ((continuous_const.sub hc).smul hw).add (hc.smul hv)

theorem boundary_restoration {X : Type*} [TopologicalSpace X]
    {t n s : ℕ} (f : X → Cube t n) (g : X → Slots t n)
    (hf : Continuous f) (hg : Continuous g)
    (havoid : ∀ x, g x ∉ Sparse s)
    (hclose : ∀ x, ‖g x - (f x).val‖ < 1 / 2) :
    ∃ G : X → Cube t n, Continuous G ∧
      (∀ x, s + 1 ≤ (boundarySlots (G x).val).card) ∧
      (∀ x j, OnBoundary ((f x).val j) → (G x).val j = (f x).val j) := by
  let g' : X → Slots t n := fun x j => blend ((f x).val j) (g x j)
  have hfj : ∀ j, Continuous (fun x => (f x).val j) := fun j =>
    (continuous_apply j).comp hf.subtype_val
  have hgj : ∀ j, Continuous (fun x => g x j) := fun j =>
    (continuous_apply j).comp hg
  have hg' : Continuous g' := by
    apply continuous_pi
    intro j
    exact continuous_blend_of (hfj j) (hgj j)
  have havoid' : ∀ x, g' x ∉ Sparse s := by
    intro x hx
    apply havoid x
    apply le_trans (Finset.card_le_card (show support (g x) ⊆ support (g' x) from ?_)) hx
    intro j hj
    apply (mem_support _ _).mpr
    apply blend_nonzero ((f x).property j) _ ((mem_support _ _).mp hj)
    exact (norm_le_pi_norm (g x - (f x).val) j).trans_lt (hclose x)
  let G : X → Cube t n := fun x =>
    ⟨fun j => radial (restorationRadius s (g' x)) (g' x j),
      fun j => norm_radial_le_one (restorationRadius_pos (havoid' x)) (g' x j)⟩
  refine ⟨G, ?_, ?_, ?_⟩
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    have hden : ∀ x, max (restorationRadius s (g' x)) ‖g' x j‖ ≠ 0 := by
      intro x
      exact ne_of_gt ((restorationRadius_pos (havoid' x)).trans_le (le_max_left _ _))
    exact (((continuous_restorationRadius t n s).comp hg').max
      (((continuous_apply j).comp hg').norm)).inv₀ hden |>.smul
        ((continuous_apply j).comp hg')
  · intro x
    apply (Nat.succ_le_of_lt (many_large_slots (havoid' x))).trans
    apply Finset.card_le_card
    intro j hj
    exact (mem_boundarySlots _ _).mpr
      (radial_boundary (restorationRadius_pos (havoid' x)) ((Finset.mem_filter.mp hj).2))
  · intro x j hj
    change radial (restorationRadius s (g' x)) (blend ((f x).val j) (g x j)) = _
    rw [blend_fixes_boundary hj]
    exact radial_fixes_boundary ((restorationRadius_le_half (g' x)).trans (by norm_num)) hj

theorem boundary_restoration_of_sparseParameters {X : Type*} [TopologicalSpace X]
    {t n s : ℕ} (f : X → Cube t n) (g : X → Slots t n)
    (hf : Continuous f) (hg : Continuous g)
    (havoid : ∀ x, g x ∉ sparseParameters t n (s : ℝ))
    (hclose : ∀ x, ‖g x - (f x).val‖ < 1 / 2) :
    ∃ G : X → Cube t n, Continuous G ∧
      (∀ x, s + 1 ≤ (boundarySlots (G x).val).card) ∧
      (∀ x j, OnBoundary ((f x).val j) → (G x).val j = (f x).val j) := by
  apply boundary_restoration f g hf hg ?_ hclose
  intro x hx
  apply havoid x
  refine ⟨?_, ?_⟩
  · intro j
    have hj := (norm_le_pi_norm (g x - (f x).val) j).trans_lt (hclose x)
    have hfbound := (f x).property j
    have hadd := norm_le_norm_sub_add (g x j) ((f x).val j)
    dsimp only [Pi.sub_apply] at hj
    linarith
  · exact_mod_cast hx

def torusLocus {Y : Type*} {t n : ℕ} (f : Y → Cube t n)
    (L : Set (Slot t)) (Z : Set (Slots t n)) : Set (Y × Z) :=
  {q | ∀ j, (f q.1).val j - q.2.val j ∈ L}

abbrev TorusLocus {Y : Type*} {t n : ℕ} (f : Y → Cube t n)
    (L : Set (Slot t)) (Z : Set (Slots t n)) := ↥(torusLocus f L Z)

def locusDifference {Y : Type*} {t n : ℕ} {f : Y → Cube t n}
    {L : Set (Slot t)} {Z : Set (Slots t n)} (q : TorusLocus f L Z) : Fin n → L :=
  fun j => ⟨(f q.val.1).val j - q.val.2.val j, q.property j⟩

lemma isClosed_torusLocus {Y : Type*} [TopologicalSpace Y] {t n : ℕ}
    {f : Y → Cube t n} {L : Set (Slot t)} {Z : Set (Slots t n)}
    (hf : Continuous f) (hL : IsClosed L) : IsClosed (torusLocus f L Z) := by
  unfold torusLocus
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro j
  apply hL.preimage
  have hc₁ : Continuous (fun q : Y × Z => (f q.1).val j) :=
    (continuous_apply j).comp (hf.subtype_val.comp continuous_fst)
  have hc₂ : Continuous (fun q : Y × Z => q.2.val j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
  exact hc₁.sub hc₂

lemma isCompact_sparse_torusLocus {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    {t n : ℕ} {f : Y → Cube t n} {L : Set (Slot t)}
    (hf : Continuous f) (hL : IsClosed L) (s : ℝ) :
    IsCompact (torusLocus f L (sparseParameters t n s)) := by
  let : CompactSpace (sparseParameters t n s) :=
    isCompact_iff_compactSpace.mp (isCompact_sparseParameters t n s)
  exact (isClosed_torusLocus hf hL).isCompact

lemma continuous_locusDifference {Y : Type*} [TopologicalSpace Y] {t n : ℕ}
    {f : Y → Cube t n} {L : Set (Slot t)} {Z : Set (Slots t n)}
    (hf : Continuous f) : Continuous (locusDifference (f := f) (L := L) (Z := Z)) := by
  apply continuous_pi
  intro j
  apply Continuous.subtype_mk
  have hc₁ : Continuous (fun q : TorusLocus f L Z => (f q.val.1).val j) :=
    (continuous_apply j).comp
      (hf.subtype_val.comp (continuous_fst.comp continuous_subtype_val))
  have hc₂ : Continuous (fun q : TorusLocus f L Z => q.val.2.val j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp
      (continuous_snd.comp continuous_subtype_val))
  exact hc₁.sub hc₂

def slotBundleFiber {Y : Type*} {t n r : ℕ} {f : Y → Cube t n}
    {L : Set (Slot t)} {Z : Set (Slots t n)}
    (H : L → Submodule ℂ (Fin r → ℂ)) (q : TorusLocus f L Z) :
    Submodule ℂ (Fin n → Fin r → ℂ) :=
  Submodule.pi univ (fun j => H (locusDifference q j))

@[simp] lemma mem_slotBundleFiber {Y : Type*} {t n r : ℕ} {f : Y → Cube t n}
    {L : Set (Slot t)} {Z : Set (Slots t n)} (H : L → Submodule ℂ (Fin r → ℂ))
    (q : TorusLocus f L Z) (v : Fin n → Fin r → ℂ) :
    v ∈ slotBundleFiber H q ↔ ∀ j, v j ∈ H (locusDifference q j) := by
  simp [slotBundleFiber, Submodule.mem_pi]

def EmbeddedTotal {B V : Type*} [AddCommGroup V] [Module ℂ V]
    (E : B → Submodule ℂ V) := {q : B × V // q.2 ∈ E q.1}

instance {B V : Type*} [TopologicalSpace B] [TopologicalSpace V]
    [AddCommGroup V] [Module ℂ V] (E : B → Submodule ℂ V) :
    TopologicalSpace (EmbeddedTotal E) := inferInstanceAs (TopologicalSpace {q : B × V // q.2 ∈ E q.1})

structure BundleMono {B V : Type*} [TopologicalSpace B] [TopologicalSpace V]
    [AddCommGroup V] [Module ℂ V] (E : B → Submodule ℂ V) (K : ℕ) where
  map : ∀ b, E b →ₗ[ℂ] (Fin K → ℂ)
  injective : ∀ b, Function.Injective (map b)
  continuous_total : Continuous (fun q : EmbeddedTotal E => map q.val.1 ⟨q.val.2, q.property⟩)

def slotBundleFiberEquiv {Y : Type*} {t n r : ℕ} {f : Y → Cube t n}
    {L : Set (Slot t)} {Z : Set (Slots t n)}
    (H : L → Submodule ℂ (Fin r → ℂ)) (q : TorusLocus f L Z) :
    slotBundleFiber H q ≃ₗ[ℂ] ((j : Fin n) → H (locusDifference q j)) where
  toFun v j := ⟨v.val j, (mem_slotBundleFiber H q v.val).mp v.property j⟩
  invFun v := ⟨fun j => (v j).val,
    (mem_slotBundleFiber H q _).mpr (fun j => (v j).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma finrank_slotBundleFiber {Y : Type*} {t n r p : ℕ} {f : Y → Cube t n}
    {L : Set (Slot t)} {Z : Set (Slots t n)}
    (H : L → Submodule ℂ (Fin r → ℂ)) (hH : ∀ l, Module.finrank ℂ (H l) = p)
    (q : TorusLocus f L Z) : Module.finrank ℂ (slotBundleFiber H q) = p * n := by
  rw [(slotBundleFiberEquiv H q).finrank_eq, Module.finrank_pi_fintype]
  simp [hH, Nat.mul_comm]

lemma BundleMono.finrank_le {B V : Type*} [TopologicalSpace B] [TopologicalSpace V]
    [AddCommGroup V] [Module ℂ V] {E : B → Submodule ℂ V} {K : ℕ}
    (M : BundleMono E K) (b : B) : Module.finrank ℂ (E b) ≤ K := by
  have h := LinearMap.finrank_le_finrank_of_injective (M.injective b)
  simpa using h

theorem rank_le_target_of_nonempty_locus {Y : Type*} [TopologicalSpace Y]
    {t n r p K : ℕ} {f : Y → Cube t n}
    {L : Set (Slot t)} {Z : Set (Slots t n)}
    (H : L → Submodule ℂ (Fin r → ℂ)) (hH : ∀ l, Module.finrank ℂ (H l) = p)
    (M : BundleMono (slotBundleFiber H (f := f) (Z := Z)) K)
    (hq : (torusLocus f L Z).Nonempty) : p * n ≤ K := by
  obtain ⟨q, hq⟩ := hq
  simpa [finrank_slotBundleFiber H hH] using M.finrank_le (⟨q, hq⟩ : TorusLocus f L Z)

def slotIndex {u n : ℕ} (b : Fin u) (j : Fin n) : Fin (u * n) :=
  finProdFinEquiv (b, j)

@[simp] lemma slotIndex_val {u n : ℕ} (b : Fin u) (j : Fin n) :
    (slotIndex b j).val = b.val * n + j.val := by
  simp [slotIndex, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

def powerMap {X Y : Type*} (q : X → Y) (u : ℕ) (x : Fin u → X) : Fin u → Y :=
  fun b => q (x b)

lemma continuous_powerMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {q : X → Y} (hq : Continuous q) (u : ℕ) : Continuous (powerMap q u) := by
  exact continuous_pi fun b => hq.comp (continuous_apply b)

def concatenate {X : Type*} {t n : ℕ} (f : X → Cube t n) (u : ℕ)
    (x : Fin u → X) : Cube t (u * n) :=
  ⟨fun k => (f (x (finProdFinEquiv.symm k).1)).val (finProdFinEquiv.symm k).2,
   fun k => (f (x (finProdFinEquiv.symm k).1)).property (finProdFinEquiv.symm k).2⟩

@[simp] lemma concatenate_slot {X : Type*} {t n : ℕ} (f : X → Cube t n)
    (u : ℕ) (x : Fin u → X) (b : Fin u) (j : Fin n) :
    (concatenate f u x).val (slotIndex b j) = (f (x b)).val j := by
  simp only [concatenate, slotIndex, Equiv.symm_apply_apply]

lemma boundarySlots_concatenate_sum {X : Type*} {t n : ℕ}
    (f : X → Cube t n) (u : ℕ) (x : Fin u → X) :
    (boundarySlots (concatenate f u x).val).card =
      ∑ b : Fin u, (boundarySlots (f (x b)).val).card := by
  simp only [boundarySlots, Finset.card_filter]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  rw [show finProdFinEquiv (b, j) = slotIndex b j from rfl, concatenate_slot]

lemma continuous_concatenate {X : Type*} [TopologicalSpace X] {t n : ℕ}
    {f : X → Cube t n} (hf : Continuous f) (u : ℕ) : Continuous (concatenate f u) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  exact (continuous_apply (finProdFinEquiv.symm k).2).comp
    (hf.subtype_val.comp (continuous_apply (finProdFinEquiv.symm k).1))

def IsCompression {X : Type*} [TopologicalSpace X] {t n : ℕ}
    (f : X → Cube t n) (a : ℝ) (u : ℕ) (G : (Fin u → X) → Cube t (u * n)) : Prop :=
  Continuous G ∧
  (∀ x, (a / 8) * (u : ℝ) * (n : ℝ) ≤ ((boundarySlots (G x).val).card : ℝ)) ∧
  (∀ x b j, OnBoundary ((f (x b)).val j) →
    (G x).val (slotIndex b j) = (f (x b)).val j)

def ArbitrarilyCompresses {X : Type*} [TopologicalSpace X] {t n : ℕ}
    (f : X → Cube t n) (a : ℝ) : Prop :=
  ∀ U : ℕ, 1 ≤ U → ∃ u : ℕ, U ≤ u ∧
    ∃ G : (Fin u → X) → Cube t (u * n), IsCompression f a u G

theorem compression_pullback {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
    {t n u : ℕ} {a : ℝ} {f : X → Cube t n} {fP : P → Cube t n}
    (q : X → P) (hq : Continuous q) (hfactor : f = fP ∘ q)
    {G : (Fin u → P) → Cube t (u * n)} (hG : IsCompression fP a u G) :
    IsCompression f a u (G ∘ powerMap q u) := by
  refine ⟨hG.1.comp (continuous_powerMap hq u), ?_, ?_⟩
  · intro x
    exact hG.2.1 (powerMap q u x)
  · intro x b j hx
    rw [hfactor] at hx ⊢
    exact hG.2.2 (powerMap q u x) b j hx

theorem arbitrarily_compresses_pullback {X P : Type*}
    [TopologicalSpace X] [TopologicalSpace P]
    {t n : ℕ} {a : ℝ} {f : X → Cube t n} {fP : P → Cube t n}
    (q : X → P) (hq : Continuous q) (hfactor : f = fP ∘ q)
    (hP : ArbitrarilyCompresses fP a) : ArbitrarilyCompresses f a := by
  intro U hU
  obtain ⟨u, hUu, G, hG⟩ := hP U hU
  exact ⟨u, hUu, G ∘ powerMap q u, compression_pullback q hq hfactor hG⟩

theorem arbitrarily_compresses_of_isEmpty {X : Type*} [TopologicalSpace X] [IsEmpty X]
    {t n : ℕ} (f : X → Cube t n) (a : ℝ) : ArbitrarilyCompresses f a := by
  intro U hU
  let G : (Fin U → X) → Cube t (U * n) := fun _ => ⟨0, by simp [cubeSet]⟩
  refine ⟨U, le_rfl, G, continuous_const, ?_, ?_⟩
  · intro x
    exact isEmptyElim (x ⟨0, by omega⟩)
  · intro x
    exact isEmptyElim (x ⟨0, by omega⟩)

lemma repeated_compression {X : Type*} [TopologicalSpace X] {t n : ℕ}
    {f F : X → Cube t n} {a : ℝ} (hF : Continuous F)
    (hcount : ∀ x, (a / 8) * (n : ℝ) ≤ ((boundarySlots (F x).val).card : ℝ))
    (hfix : ∀ x j, OnBoundary ((f x).val j) → (F x).val j = (f x).val j)
    (u : ℕ) : IsCompression f a u (concatenate F u) := by
  refine ⟨continuous_concatenate hF u, ?_, ?_⟩
  · intro x
    rw [boundarySlots_concatenate_sum, Nat.cast_sum]
    calc
      a / 8 * (u : ℝ) * (n : ℝ) = ∑ _b : Fin u, (a / 8) * (n : ℝ) := by
        simp [Finset.sum_const, mul_comm, mul_left_comm]
      _ ≤ ∑ b : Fin u, ((boundarySlots (F (x b)).val).card : ℝ) :=
        Finset.sum_le_sum (fun b _ => hcount (x b))
  · intro x b j hj
    rw [concatenate_slot]
    exact hfix (x b) j hj

theorem arbitrarily_compresses_of_empty_locus {X : Type*} [TopologicalSpace X]
    {t n : ℕ} {f : X → Cube t n} {L : Set (Slot t)} {a : ℝ}
    (hf : Continuous f) (ha : 0 ≤ a) (l : Slot t) (hlL : l ∈ L) (hl : ‖l‖ < 1 / 2)
    (hempty : torusLocus f L (sparseParameters t n (a * (n : ℝ))) = ∅) :
    ArbitrarilyCompresses f a := by
  let s := ⌊a * (n : ℝ)⌋₊
  let g : X → Slots t n := fun x j => (f x).val j - l
  have hg : Continuous g := hf.subtype_val.sub continuous_const
  have hclose : ∀ x, ‖g x - (f x).val‖ < 1 / 2 := by
    intro x
    have heq : g x - (f x).val = fun _ : Fin n => -l := by
      funext j
      dsimp [g]
      abel
    rw [heq]
    have hbound : ‖(fun _ : Fin n => -l)‖ ≤ ‖l‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg l)]
      intro j
      simp
    exact hbound.trans_lt hl
  have havoid : ∀ x, g x ∉ sparseParameters t n (s : ℝ) := by
    intro x hx
    have hz : g x ∈ sparseParameters t n (a * (n : ℝ)) :=
      ⟨hx.1, hx.2.trans (Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n)))⟩
    have hq : (x, ⟨g x, hz⟩) ∈ torusLocus f L (sparseParameters t n (a * (n : ℝ))) := by
      intro j
      change (f x).val j - ((f x).val j - l) ∈ L
      simpa only [sub_sub_cancel] using hlL
    rw [hempty] at hq
    exact hq
  obtain ⟨F, hF, hcount, hfix⟩ :=
    boundary_restoration_of_sparseParameters f g hf hg havoid hclose
  have hreal : (a / 8) * (n : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
    have h0 : 0 ≤ a * (n : ℝ) := mul_nonneg ha (Nat.cast_nonneg n)
    have hfloor := Nat.lt_floor_add_one (a * (n : ℝ))
    dsimp [s]
    push_cast
    linarith
  intro U _hU
  refine ⟨U, le_rfl, concatenate F U, repeated_compression hF ?_ hfix U⟩
  intro x
  exact hreal.trans (Nat.cast_le.mpr (hcount x))

lemma floor_batch_lower_bound {a : ℝ} {b : ℕ} (hab : 16 ≤ a * (b : ℝ)) :
    3 * a * (b : ℝ) / 16 ≤ (⌊a * (b : ℝ) / 4⌋₊ : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (a * (b : ℝ) / 4)
  linarith

theorem padding_boundary_fraction {a : ℝ} {b B j : ℕ}
    (ha : 0 ≤ a) (hab : 16 ≤ a * (b : ℝ)) (hj : 2 * B ≤ j) :
    (a / 8) * ((b * (B + j) : ℕ) : ℝ) ≤
      ((j * ⌊a * (b : ℝ) / 4⌋₊ : ℕ) : ℝ) := by
  have hfloor := floor_batch_lower_bound hab
  have hBj : 2 * (B : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hcount := mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg j : 0 ≤ (j : ℝ))
  have hscale := mul_le_mul_of_nonneg_left hBj
    (mul_nonneg ha (Nat.cast_nonneg b : 0 ≤ (b : ℝ)))
  push_cast
  nlinarith

end TorusCompression

end

end OAI
