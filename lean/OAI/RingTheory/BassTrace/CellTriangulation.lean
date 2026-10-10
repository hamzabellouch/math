import OAI.RingTheory.BassTrace.FiniteCells

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section CellVertices

open Filter

open scoped Topology

variable {I : Type*} [Fintype I]

noncomputable def activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) : Finset I :=
  Finset.univ.filter fun i => a i x = b i

lemma mem_activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) (i : I) :
    i ∈ activeConstraints a b x ↔ a i x = b i := by
  classical
  simp [activeConstraints]

lemma exists_extrapolate_mem
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {x y : E}
    (hx : x ∈ cell a b)
    (hactive : activeConstraints a b x = activeConstraints a b y) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - y) ∈ cell a b := by
  have hi (i : I) : ∀ᶠ t : ℝ in 𝓝 0, a i (x + t • (x - y)) ≤ b i := by
    by_cases h : a i x = b i
    · have hyi : a i y = b i := by
        rw [← mem_activeConstraints, ← hactive, mem_activeConstraints]
        exact h
      filter_upwards [] with t
      simp only [map_add, map_smul, map_sub, smul_eq_mul, h, hyi, sub_self,
        mul_zero, add_zero, le_refl]
    · have hlt : a i x < b i := lt_of_le_of_ne (hx i) h
      have hc : Continuous (fun t : ℝ => a i x + t * (a i x - a i y)) := by fun_prop
      have he : ∀ᶠ t : ℝ in 𝓝 0, a i x + t * (a i x - a i y) < b i :=
        hc.continuousAt.eventually (gt_mem_nhds (by simpa using hlt))
      filter_upwards [he] with t ht
      simpa only [map_add, map_smul, map_sub, smul_eq_mul] using ht.le
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, a i (x + t • (x - y)) ≤ b i :=
    Filter.eventually_all.mpr hi
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨δ / 2, by positivity, hball ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos (by positivity : 0 < δ / 2)]
  linarith

lemma activeConstraints_injOn_extremePoints
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    Set.InjOn (activeConstraints a b) ((cell a b).extremePoints ℝ) := by
  intro x hx y hy hactive
  obtain ⟨t, ht, hz⟩ := exists_extrapolate_mem a b hx.1 hactive
  have hsum : t + 1 ≠ 0 := by positivity
  have hseg : x ∈ openSegment ℝ y (x + t • (x - y)) := by
    apply mem_openSegment_iff_div.mpr
    refine ⟨t, 1, ht, by norm_num, ?_⟩
    simp only [smul_add, smul_sub, smul_smul]
    rw [show 1 / (t + 1) * t = t / (t + 1) by ring]
    calc
      _ = (1 / (t + 1) + t / (t + 1)) • x := by module
      _ = x := by rw [← add_div, add_comm 1 t, div_self hsum, one_smul]
  exact (hx.2 hy.1 hz hseg).symm

lemma finite_extremePoints_cell
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ((cell a b).extremePoints ℝ).Finite := by
  classical
  exact Set.Finite.of_injOn (t := Set.univ) (Set.mapsTo_univ _ _)
    (activeConstraints_injOn_extremePoints a b) Set.finite_univ

noncomputable def polyhedronVertices (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Finset E :=
  (finite_extremePoints_cell a b).toFinset

@[simp] lemma mem_polyhedronVertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) :
    x ∈ polyhedronVertices a b ↔ x ∈ (cell a b).extremePoints ℝ :=
  Set.Finite.mem_toFinset _

variable [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

lemma exists_extreme_maximizer {s : Set E} (hs : IsCompact s) (hne : s.Nonempty)
    (f : E →L[ℝ] ℝ) :
    ∃ x ∈ s.extremePoints ℝ, ∀ y ∈ s, f y ≤ f x := by
  obtain ⟨x, hx, hxmax⟩ := hs.exists_isMaxOn hne f.continuous.continuousOn
  have hex : IsExposed ℝ s {x ∈ s | ∀ y ∈ s, f y ≤ f x} := fun _ => ⟨f, rfl⟩
  obtain ⟨z, hz⟩ := (hex.isCompact hs).extremePoints_nonempty ⟨x, hx, hxmax⟩
  exact ⟨z, hex.isExtreme.extremePoints_subset_extremePoints hz, hz.1.2⟩

lemma exists_vertex_maximizer (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hc : IsCompact (cell a b))
    (hne : (cell a b).Nonempty) (f : E →L[ℝ] ℝ) :
    ∃ x ∈ polyhedronVertices a b, ∀ y ∈ cell a b, f y ≤ f x := by
  simpa only [mem_polyhedronVertices] using exists_extreme_maximizer hc hne f

lemma cell_eq_convexHull_vertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hc : IsCompact (cell a b)) :
    cell a b = convexHull ℝ (polyhedronVertices a b : Set E) := by
  have hv : Convex ℝ (cell a b) := by
    intro x hx y hy r s hr hs hrs i
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      r * a i x + s * a i y ≤ r * b i + s * b i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
          (mul_le_mul_of_nonneg_left (hy i) hs)
      _ = b i := by rw [← add_mul, hrs, one_mul]
  have he : (polyhedronVertices a b : Set E) =
      (cell a b).extremePoints ℝ := by
    ext x
    exact mem_polyhedronVertices a b x
  have h := closure_convexHull_extremePoints hc hv
  rw [← he, ((polyhedronVertices a b).finite_toSet.isClosed_convexHull (𝕜 := ℝ)).closure_eq] at h
  exact h.symm

end CellVertices

section Arrangements

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I] [Fintype J]

omit [Fintype I] in
lemma isClosed_cell (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) : IsClosed (cell a b) := by
  have he : cell a b = ⋂ i, {x | a i x ≤ b i} := by ext x; simp [cell]
  rw [he]
  exact isClosed_iInter fun i => isClosed_le (a i).continuous_of_finiteDimensional continuous_const

lemma cell_eq_convexHull_of_bounded (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hb : Bornology.IsBounded (cell a b)) :
    cell a b = convexHull ℝ (polyhedronVertices a b : Set V) :=
  cell_eq_convexHull_vertices a b (Metric.isCompact_of_isClosed_isBounded (isClosed_cell a b) hb)

noncomputable def CellData.ofBounded (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hb : Bornology.IsBounded (cell a b)) (hne : (cell a b).Nonempty) :
    CellData (cell a b) := by
  have he := cell_eq_convexHull_of_bounded a b hb
  have hvn : (polyhedronVertices a b).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp (he ▸ hne))
  exact CellData.ofPresentation _ a b rfl hb (vertexMean (polyhedronVertices a b))
    (he ▸ vertexMean_mem_convexHull hvn) (fun f d hf hc x hx =>
      vertexMean_supports hvn f d (he ▸ hf) hc x (he ▸ hx))

def signedForm (a : J → V →ₗ[ℝ] ℝ) (s : J → Bool) (j : J) : V →ₗ[ℝ] ℝ :=
  if s j then a j else -a j

def signedBound (b : J → ℝ) (s : J → Bool) (j : J) : ℝ :=
  if s j then b j else -b j

def cutCell (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (s : J → Bool) : Set V := P ∩ cell (signedForm a s) (signedBound b s)

lemma cutCell_nonempty_data {P : Set V} (p : CellData P)
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) (s : J → Bool)
    (hne : (cutCell P a b s).Nonempty) :
    Nonempty (CellData (cutCell P a b s)) ∧
    ∃ v : Finset V, cutCell P a b s = convexHull ℝ (v : Set V) := by
  let a' : Fin p.n ⊕ J → V →ₗ[ℝ] ℝ := Sum.elim p.a (signedForm a s)
  let b' : Fin p.n ⊕ J → ℝ := Sum.elim p.b (signedBound b s)
  have he : cutCell P a b s = cell a' b' := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩ i
      cases i with
      | inl i => exact (p.eq_cell ▸ hx) i
      | inr j => exact hy j
    · intro hx
      exact ⟨p.eq_cell.symm ▸ (show x ∈ cell p.a p.b from fun i => hx (Sum.inl i)),
        fun j => hx (Sum.inr j)⟩
  have hb : Bornology.IsBounded (cell a' b') :=
    he ▸ p.bounded.subset Set.inter_subset_left
  exact ⟨⟨he ▸ CellData.ofBounded a' b' hb (he ▸ hne)⟩,
    polyhedronVertices a' b', he.trans (cell_eq_convexHull_of_bounded a' b' hb)⟩

omit [FiniteDimensional ℝ V] in
lemma cutCell_inter_supporting (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (s t : J → Bool) : SupportingFace (cutCell P a b s ∩ cutCell P a b t)
      (cutCell P a b s) := by
  classical
  let T : Finset J := Finset.univ.filter fun j => s j ≠ t j
  let f : V →ₗ[ℝ] ℝ := ∑ j ∈ T, signedForm a s j
  let d : ℝ := ∑ j ∈ T, signedBound b s j
  have hle {x : V} (hx : x ∈ cutCell P a b s) : f x ≤ d := by
    simp only [f, LinearMap.sum_apply]
    exact Finset.sum_le_sum fun j _ => hx.2 j
  have heq {x : V} (hx : x ∈ cutCell P a b s) :
      f x = d ↔ ∀ j ∈ T, signedForm a s j x = signedBound b s j := by
    simp only [f, d, LinearMap.sum_apply]
    exact Finset.sum_eq_sum_iff_of_le (fun j _ => hx.2 j)
  refine ⟨f, d, fun _ hx => hle hx, ?_⟩
  ext x
  constructor
  · rintro ⟨hxs, hxt⟩
    refine ⟨hxs, (heq hxs).mpr ?_⟩
    intro j hj
    have hst : s j ≠ t j := (Finset.mem_filter.mp hj).2
    have hs := hxs.2 j
    have ht := hxt.2 j
    cases hs' : s j <;> cases ht' : t j <;>
      simp only [hs', ht', signedForm, signedBound, Bool.false_eq_true, ↓reduceIte,
        LinearMap.neg_apply, ne_eq, not_true_eq_false] at hst hs ht ⊢ <;> linarith
  · rintro ⟨hxs, hfx⟩
    refine ⟨hxs, hxs.1, ?_⟩
    intro j
    by_cases hst : s j = t j
    · simpa only [signedForm, signedBound, ← hst] using hxs.2 j
    · have hjeq := (heq hxs).mp hfx j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hst⟩)
      cases hs' : s j <;> cases ht' : t j <;>
        simp only [hs', ht', signedForm, signedBound, Bool.false_eq_true, ↓reduceIte,
          LinearMap.neg_apply, not_true_eq_false] at hst hjeq ⊢ <;> linarith

omit [Fintype J] [FiniteDimensional ℝ V] in
lemma cutCell_cover (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    P = ⋃ s : J → Bool, cutCell P a b s := by
  classical
  ext x
  constructor
  · intro hx
    apply Set.mem_iUnion.mpr
    refine ⟨fun j => decide (a j x ≤ b j), hx, ?_⟩
    intro j
    by_cases h : a j x ≤ b j
    · simp [signedForm, signedBound, h]
    · simp only [signedForm, signedBound, h, decide_false, Bool.false_eq_true,
        ↓reduceIte, LinearMap.neg_apply]
      linarith
  · intro hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    exact hs.1

end Arrangements

section ArrangementTriangulation

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype J]

omit [FiniteDimensional ℝ V] in
lemma SupportingFace.inter_restrict {P Q S : Set V}
    (h : SupportingFace (P ∩ Q) P) (hSP : S ⊆ P) : SupportingFace (S ∩ Q) S := by
  have hh := h.restrict hSP
  convert hh using 1
  ext x
  exact ⟨fun hx => ⟨hx.1, hSP hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩

omit [FiniteDimensional ℝ V] in
lemma cutCell_inter_parents_supporting {P Q : Set V}
    (hPQ : SupportingFace (P ∩ Q) P) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (s t : J → Bool) : SupportingFace
      (cutCell P a b s ∩ cutCell Q a b t) (cutCell P a b s) := by
  have hQ := hPQ.inter_restrict (show cutCell P a b s ⊆ P from Set.inter_subset_left)
  have hT := cutCell_inter_supporting P a b s t
  have hh := hQ.supporting_inter hT
  convert hh using 1
  ext x
  simp only [cutCell, Set.mem_inter_iff]
  tauto

noncomputable def cutParents (A : Finset (Set V))
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) : Finset (Set V) := by
  classical
  exact ((A ×ˢ Finset.univ).image (fun ps : Set V × (J → Bool) => cutCell ps.1 a b ps.2)).filter
    Set.Nonempty

omit [FiniteDimensional ℝ V] in
lemma mem_cutParents (A : Finset (Set V)) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (Q : Set V) : Q ∈ cutParents A a b ↔
      ∃ P ∈ A, ∃ s : J → Bool, Q = cutCell P a b s ∧ Q.Nonempty := by
  classical
  simp only [cutParents, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
    Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨⟨P, s, hP, he⟩, hne⟩
    exact ⟨P, hP, s, he.symm, hne⟩
  · rintro ⟨P, hP, s, he, hne⟩
    exact ⟨⟨P, s, hP, he.symm⟩, hne⟩

theorem exists_cutTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation A,
      ∀ P ∈ A, ∀ s : J → Bool, RespectsSet B.complex (cutCell P a b s) := by
  classical
  let C := cutParents A a b
  have hCdata : ∀ Q ∈ C, Nonempty (CellData Q) := by
    intro Q hQ
    obtain ⟨P, hP, s, rfl, hne⟩ := (mem_cutParents A a b Q).mp hQ
    obtain ⟨p⟩ := hdata P hP
    exact (cutCell_nonempty_data p a b s hne).1
  have hCvertices : ∀ Q ∈ C, ∃ v : Finset V, Q = convexHull ℝ (v : Set V) := by
    intro Q hQ
    obtain ⟨P, hP, s, rfl, hne⟩ := (mem_cutParents A a b Q).mp hQ
    obtain ⟨p⟩ := hdata P hP
    exact (cutCell_nonempty_data p a b s hne).2
  have hCinter : ∀ Q ∈ C, ∀ R ∈ C, SupportingFace (Q ∩ R) Q := by
    intro Q hQ R hR
    obtain ⟨P, hP, s, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
    obtain ⟨P', hP', t, rfl, _⟩ := (mem_cutParents A a b R).mp hR
    exact cutCell_inter_parents_supporting (hinter P hP P' hP') a b s t
  obtain ⟨B⟩ := exists_cellTriangulation_parents C hCdata hCvertices hCinter
  have hspace : familySpace C = familySpace A := by
    ext x
    constructor
    · rintro ⟨Q, hQ, hxQ⟩
      obtain ⟨P, hP, s, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
      exact ⟨P, hP, hxQ.1⟩
    · rintro ⟨P, hP, hxP⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ((cutCell_cover P a b).subset hxP)
      exact ⟨cutCell P a b s, (mem_cutParents A a b _).mpr ⟨P, hP, s, rfl, x, hs⟩, hs⟩
  have htrace : ∀ P ∈ A, RespectsSet B.complex P := by
    intro P hP
    apply B.respects_of_carrier
    intro Q hQ
    obtain ⟨P', hP', s, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
    exact (hinter P' hP' P hP).inter_restrict Set.inter_subset_left
  have hcarrier : ∀ s ∈ B.complex.faces,
      ∃ P ∈ A, convexHull ℝ (s : Set V) ⊆ P := by
    intro s hs
    obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
    obtain ⟨P, hP, t, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
    exact ⟨P, hP, hsQ.trans Set.inter_subset_left⟩
  refine ⟨⟨B.complex, B.finite, B.space.trans hspace, htrace, hcarrier⟩, ?_⟩
  intro P hP s
  by_cases hne : (cutCell P a b s).Nonempty
  · exact B.trace _ ((mem_cutParents A a b _).mpr ⟨P, hP, s, rfl, hne⟩)
  · have he : cutCell P a b s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    intro t ht
    simp [he]

end ArrangementTriangulation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
lemma affine_decomp_apply (f : V →ᵃ[ℝ] ℝ) (x : V) : f x = f.linear x + f 0 := by
  exact congrFun f.decomp x

theorem simplex_has_cellData (s : Finset V) (hs : s.Nonempty)
    (hi : AffineIndependent ℝ ((↑) : s → V)) :
    Nonempty (CellData (convexHull ℝ (s : Set V))) := by
  classical
  obtain ⟨t, hst, htind, httop⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top hi
  let B : AffineBasis t ℝ V := ⟨Subtype.val, htind, by simpa using httop⟩
  let : Finite t := B.finite
  let : Fintype t := Fintype.ofFinite t
  let v : Finset V := (B.setFinite).toFinset
  have hv : (v : Set V) = t := Set.Finite.coe_toFinset _
  have hBrange : Set.range B = t := Subtype.range_coe
  let a : t → V →ₗ[ℝ] ℝ := fun i => -(B.coord i).linear
  let b : t → ℝ := fun i => B.coord i 0
  have hfull : convexHull ℝ (v : Set V) = cell a b := by
    have he : convexHull ℝ (v : Set V) = convexHull ℝ (Set.range B) :=
      congrArg (convexHull ℝ) (hv.trans hBrange.symm)
    rw [he, B.convexHull_eq_nonneg_coord]
    ext x
    constructor
    · intro hx i
      have hd := affine_decomp_apply (B.coord i) x
      have hc := hx i
      change -(B.coord i).linear x ≤ B.coord i 0
      linarith
    · intro hx i
      have hd := affine_decomp_apply (B.coord i) x
      have hc : -(B.coord i).linear x ≤ B.coord i 0 := hx i
      linarith
  have hfull_ne : (cell a b).Nonempty := by
    apply hfull ▸ ((convexHull_nonempty_iff).mpr ?_)
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, by rw [hv]; exact hst hx⟩
  have hbounded : Bornology.IsBounded (cell a b) := by
    rw [← hfull]
    exact (v.finite_toSet.isCompact_convexHull ℝ).isBounded
  let p : CellData (convexHull ℝ (v : Set V)) :=
    hfull ▸ CellData.ofBounded a b hbounded hfull_ne
  let S : Finset t := Finset.univ.filter fun i => (i : V) ∈ s
  let f : V →ᵃ[ℝ] ℝ := ∑ i ∈ S, B.coord i
  have hf_basis (i : t) : f (B i) = if (i : V) ∈ s then 1 else 0 := by
    have hsum (T : Finset t) : (∑ j ∈ T, B.coord j) (B i) =
        ∑ j ∈ T, B.coord j (B i) := by
      induction T using Finset.induction_on with
      | empty => simp
      | @insert j T hj ih => simp [Finset.sum_insert hj, ih]
    rw [hsum]
    simp only [B.coord_apply]
    simp [S]
  have hle : ∀ x ∈ (v : Set V), f.linear x ≤ 1-f 0 := by
    intro x hx
    have hxt : x ∈ t := hv ▸ hx
    have hh := hf_basis ⟨x, hxt⟩
    have hd := affine_decomp_apply f x
    change f x = if x ∈ s then 1 else 0 at hh
    split_ifs at hh <;> linarith
  have he : (v : Set V) ∩ {x | f.linear x = 1-f 0} = (s : Set V) := by
    ext x
    constructor
    · rintro ⟨hx, he⟩
      have hxt : x ∈ t := hv ▸ hx
      have hh := hf_basis ⟨x, hxt⟩
      have hd := affine_decomp_apply f x
      change f x = if x ∈ s then 1 else 0 at hh
      by_contra hxs
      change x ∉ s at hxs
      rw [ite_eq_right hxs] at hh
      change f.linear x = 1-f 0 at he
      linarith
    · intro hx
      have hxt := hst hx
      refine ⟨by rw [hv]; exact hxt, ?_⟩
      have hh := hf_basis ⟨x, hxt⟩
      have hd := affine_decomp_apply f x
      change f x = if x ∈ s then 1 else 0 at hh
      change x ∈ s at hx
      rw [ite_eq_left hx] at hh
      change f.linear x = 1-f 0
      linarith
  have hface : SupportingFace (convexHull ℝ (s : Set V))
      (convexHull ℝ (v : Set V)) := by
    refine ⟨f.linear, 1-f 0, linear_le_on_convexHull _ _ _ hle, ?_⟩
    rw [convexHull_inter_supporting _ f.linear (1-f 0) hle, he]
  exact ⟨p.supportingFace v rfl hface (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs))⟩

omit [FiniteDimensional ℝ V] in

lemma simplex_affine_indicator (s t : Finset V)
    (hi : AffineIndependent ℝ ((↑) : s → V)) :
    ∃ f : V →ᵃ[ℝ] ℝ, ∀ x ∈ s, f x = if x ∈ t then 1 else 0 := by
  classical
  obtain ⟨u, hsu, huind, hutop⟩ := exists_subset_affineIndependent_affineSpan_eq_top hi
  let B : AffineBasis u ℝ V := ⟨Subtype.val, huind, by simpa using hutop⟩
  let T : Finset u := t.preimage Subtype.val Subtype.val_injective.injOn
  refine ⟨∑ i ∈ T, B.coord i, ?_⟩
  intro x hx
  let i : u := ⟨x, hsu hx⟩
  have hsum (R : Finset u) : (∑ j ∈ R, B.coord j) (B i) =
      ∑ j ∈ R, B.coord j (B i) := by
    induction R using Finset.induction_on with
    | empty => simp
    | @insert j R hj ih => simp [Finset.sum_insert hj, ih]
  change (∑ j ∈ T, B.coord j) (B i) = _
  rw [hsum]
  simp [T, B.coord_apply, i]

omit [FiniteDimensional ℝ V] in

lemma simplex_face_supporting (s t : Finset V)
    (hi : AffineIndependent ℝ ((↑) : s → V)) (ht : t ⊆ s) :
    SupportingFace (convexHull ℝ (t : Set V)) (convexHull ℝ (s : Set V)) := by
  classical
  obtain ⟨f, hf⟩ := simplex_affine_indicator s t hi
  have hle : ∀ x ∈ (s : Set V), f.linear x ≤ 1-f 0 := by
    intro x hx
    have hh := hf x hx
    have hd := affine_decomp_apply f x
    split_ifs at hh <;> linarith
  refine ⟨f.linear, 1-f 0, linear_le_on_convexHull _ _ _ hle, ?_⟩
  rw [convexHull_inter_supporting _ f.linear (1-f 0) hle]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨ht hx, ?_⟩
    have hh := hf x (ht hx)
    have hd := affine_decomp_apply f x
    change x ∈ t at hx
    rw [ite_eq_left hx] at hh
    change f.linear x = 1-f 0
    linarith
  · rintro ⟨hx, he⟩
    have hh := hf x hx
    have hd := affine_decomp_apply f x
    change f.linear x = 1-f 0 at he
    by_contra hxt
    change x ∉ t at hxt
    rw [ite_eq_right hxt] at hh
    linarith

theorem exists_simplicialCutTriangulation (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) {J : Type*} [Fintype J]
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation (hK.toFinset.image fun (s : Finset V) => convexHull ℝ (s : Set V)),
      ∀ s ∈ K.faces, ∀ e : J → Bool,
        RespectsSet B.complex (cutCell (convexHull ℝ (s : Set V)) a b e) := by
  classical
  let A := hK.toFinset.image fun (s : Finset V) => convexHull ℝ (s : Set V)
  have hdata : ∀ P ∈ A, Nonempty (CellData P) := by
    intro P hP
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hP
    have htK : t ∈ K.faces := by simpa using ht
    exact simplex_has_cellData t (K.nonempty_of_mem_faces htK) (K.indep htK)
  have hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P := by
    intro P hP Q hQ
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hQ
    have hsK : s ∈ K.faces := by simpa using hs
    have htK : t ∈ K.faces := by simpa using ht
    rw [K.convexHull_inter_convexHull hsK htK, ← Finset.coe_inter]
    exact simplex_face_supporting s (s ∩ t) (K.indep hsK) Finset.inter_subset_left
  obtain ⟨B, hB⟩ := exists_cutTriangulation A hdata hinter a b
  exact ⟨B, fun s hs e => hB _ (Finset.mem_image.mpr
    ⟨s, by simpa using hs, rfl⟩) e⟩

end BassTrace.Sparse.Cuts

end OAI
