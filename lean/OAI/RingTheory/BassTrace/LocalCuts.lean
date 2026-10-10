import OAI.RingTheory.BassTrace.DirectedCuts

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section LocallyFiniteCuts

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma faceClosure_mono {A B : Finset (Set V)} (h : A ⊆ B) :
    faceClosure A ⊆ faceClosure B := by
  classical
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := Finset.mem_biUnion.mp hP
  exact Finset.mem_biUnion.mpr ⟨Q, h hQ, hPQ⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_mono {A B : Finset (Set V)} {c : Set V → V} (h : A ⊆ B) :
    chainFaces A c ⊆ chainFaces B c := by
  rintro s ⟨t, hn, ht, hc, he⟩
  exact ⟨t, hn, ht.trans h, hc, he⟩

lemma cutCell_extend_irrelevant (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    {I L : Finset J} (hIL : I ⊆ L) (s : I → Bool)
    (hz : ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 ≤ b j) :
    ∃ t : L → Bool, cutCell P (fun j : I => a j) (fun j : I => b j) s =
      cutCell P (fun j : L => a j) (fun j : L => b j) t := by
  classical
  let t : L → Bool := fun j => if h : j.val ∈ I then s ⟨j.val, h⟩ else true
  refine ⟨t, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨hx, ?_⟩
    intro j
    by_cases hj : j.val ∈ I
    · simpa only [signedForm, signedBound, t, dite_eq_left hj] using hs ⟨j.val, hj⟩
    · simp only [signedForm, signedBound, t, dite_eq_right hj, ↓reduceIte]
      rw [hz j.val j.property hj x hx]
      exact hb j.val j.property
  · rintro ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    intro j
    simpa only [signedForm, signedBound, t, dite_eq_left j.property] using
      ht ⟨j.val, hIL j.property⟩

lemma cutParents_mono_irrelevant {A B : Finset (Set V)} (hAB : A ⊆ B)
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) {I L : Finset J} (hIL : I ⊆ L)
    (hz : ∀ P ∈ A, ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 ≤ b j) :
    cutParents A (fun j : I => a j) (fun j : I => b j) ⊆
      cutParents B (fun j : L => a j) (fun j : L => b j) := by
  intro Q hQ
  obtain ⟨P, hP, s, rfl, hn⟩ := (mem_cutParents _ _ _ _).mp hQ
  obtain ⟨t, ht⟩ := cutCell_extend_irrelevant P a b hIL s (hz P hP) hb
  exact (mem_cutParents _ _ _ _).mpr ⟨P, hAB hP, t, ht, hn⟩

lemma complexParents_mono {K L : Geometry.SimplicialComplex ℝ V}
    (hK : K.faces.Finite) (hL : L.faces.Finite) (hKL : K ≤ L) :
    complexParents K hK ⊆ complexParents L hL := by
  intro P hP
  obtain ⟨s, hs, rfl⟩ := (mem_complexParents K hK P).mp hP
  exact (mem_complexParents L hL _).mpr ⟨s, hKL hs, rfl⟩

lemma finiteComplex_space_finiteHull (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) (hc : Convex ℝ K.space) :
    ∃ s : Finset V, K.space = convexHull ℝ (s : Set V) := by
  classical
  let s : Finset V := hK.toFinset.biUnion id
  refine ⟨s, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨t, ht, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    apply convexHull_mono (t := (s : Set V)) ?_ hx
    intro y hy
    exact Finset.mem_biUnion.mpr ⟨t, by simpa using ht, hy⟩
  · apply convexHull_min ?_ hc
    intro x hx
    obtain ⟨t, ht, hx⟩ := Finset.mem_biUnion.mp hx
    exact K.subset_space (by simpa using ht) hx

lemma finiteHull_of_respects (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (P : Set V) (hc : Convex ℝ P) (hP : P ⊆ K.space) (htr : RespectsSet K P) :
    ∃ s : Finset V, P = convexHull ℝ (s : Set V) := by
  have he : (restrictComplex K P).space = P := by
    rw [restrictComplex_space_of_respects K P htr]
    exact Set.inter_eq_right.mpr hP
  obtain ⟨s, hs⟩ := finiteComplex_space_finiteHull (restrictComplex K P)
    (restrictComplex_finite K P hK) (he.symm ▸ hc)
  exact ⟨s, he.symm.trans hs⟩

lemma cutParents_finiteHull_simplicial (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ∀ P ∈ cutParents (complexParents K hK) a b,
      ∃ s : Finset V, P = convexHull ℝ (s : Set V) := by
  obtain ⟨B, _, htr⟩ := exists_canonical_simplicialCuts K hK a b
  intro P hP
  obtain ⟨Q, hQ, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hP
  obtain ⟨t, ht, rfl⟩ := (mem_complexParents K hK Q).mp hQ
  apply finiteHull_of_respects B.complex B.finite _
    ((convex_convexHull ℝ _).inter (convex_cell _ _)) ?_ (htr t ht e)
  rw [B.space, complexParents_space]
  exact Set.inter_subset_left.trans (K.convexHull_subset_space ht)

lemma canonicalCenter_supporting_iff {P Q : Set V}
    (hn : Q.Nonempty) (hv : ∃ s : Finset V, Q = convexHull ℝ (s : Set V))
    (hface : SupportingFace (Q ∩ P) Q) : canonicalCenter Q ∈ P ↔ Q ⊆ P := by
  obtain ⟨s, rfl⟩ := hv
  have hs : s.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hn)
  have hmem := canonicalCenter_mem_finiteHull hs
  constructor
  · intro hc
    obtain ⟨f, b, hf, he⟩ := hface
    have hcb : f (canonicalCenter (convexHull ℝ (s : Set V))) = b :=
      (he.subset ⟨hmem, hc⟩).2
    intro x hx
    exact (he.symm.subset ⟨hx, canonicalCenter_supports_finiteHull hs f b hf hcb x hx⟩).2
  · exact fun h => h hmem

lemma simplicialParents_inter_supporting (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) {P Q : Set V} (hP : P ∈ complexParents K hK)
    (hQ : Q ∈ complexParents K hK) : SupportingFace (P ∩ Q) P := by
  obtain ⟨s, hs, rfl⟩ := (mem_complexParents _ _ _).mp hP
  obtain ⟨t, ht, rfl⟩ := (mem_complexParents _ _ _).mp hQ
  rw [K.convexHull_inter_convexHull hs ht, ← Finset.coe_inter]
  exact simplex_face_supporting s (s ∩ t) (K.indep hs) Finset.inter_subset_left

lemma cutParents_mono {I : Type*} [Fintype I] {A B : Finset (Set V)}
    (hAB : A ⊆ B) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    cutParents A a b ⊆ cutParents B a b := by
  intro P hP
  obtain ⟨Q, hQ, e, he, hn⟩ := (mem_cutParents _ _ _ _).mp hP
  exact (mem_cutParents _ _ _ _).mpr ⟨Q, hAB hQ, e, he, hn⟩

lemma faceClosure_cutParents_filter {I : Type*} [Fintype I]
    (A : Finset (Set V)) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hv : ∀ Q ∈ cutParents A a b, ∃ s : Finset V, Q = convexHull ℝ (s : Set V))
    (hi : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    {P : Set V} (hP : P ∈ A) :
    (faceClosure (cutParents A a b)).filter (fun Q => Q ⊆ P) =
      faceClosure (cutParents {P} a b) := by
  classical
  have hsub : cutParents {P} a b ⊆ cutParents A a b :=
    cutParents_mono (Finset.singleton_subset_iff.mpr hP) a b
  have hvP := fun Q hQ => hv Q (hsub hQ)
  apply Finset.ext
  intro Q
  rw [Finset.mem_filter, mem_faceClosure _ hv, mem_faceClosure _ hvP]
  constructor
  · rintro ⟨⟨R, hR, hn, hQR⟩, hQP⟩
    obtain ⟨S, hS, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hR
    let X := cutCell P a b e
    have hQX : Q ⊆ X := fun x hx => ⟨hQP hx, (hQR.subset hx).2⟩
    have hX : X ∈ cutParents {P} a b :=
      (mem_cutParents _ _ _ _).mpr ⟨P, Finset.mem_singleton_self _, e, rfl, hn.mono hQX⟩
    obtain ⟨s, hs⟩ := hvP X hX
    have hface := (supportingFace_self X).inter_of_parent_inter hQR
      (cutCell_inter_parents_supporting (hi P hP S hS) a b e e) hs
    rw [Set.inter_eq_right.mpr hQX] at hface
    exact ⟨X, hX, hn, hface⟩
  · rintro ⟨R, hR, hn, hQR⟩
    refine ⟨⟨R, hsub hR, hn, hQR⟩, ?_⟩
    obtain ⟨S, hS, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hR
    have hSP : S = P := Finset.mem_singleton.mp hS
    subst S
    exact hQR.subset.trans Set.inter_subset_left

lemma canonical_chainFaces_restrict_parent {I : Type*} [Fintype I]
    (A : Finset (Set V)) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hv : ∀ Q ∈ cutParents A a b, ∃ s : Finset V, Q = convexHull ℝ (s : Set V))
    (hi : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    {P : Set V} (hP : P ∈ A) (s : Finset V) :
    s ∈ chainFaces (faceClosure (cutParents A a b)) canonicalCenter ∧ (s : Set V) ⊆ P ↔
      s ∈ chainFaces (faceClosure (cutParents {P} a b)) canonicalCenter := by
  have hc : ∀ Q ∈ faceClosure (cutParents A a b), canonicalCenter Q ∈ P ↔ Q ⊆ P := by
    intro Q hQ
    obtain ⟨R, hR, hn, hQR⟩ := (mem_faceClosure _ hv Q).mp hQ
    obtain ⟨v, hvR⟩ := hv R hR
    have hvQ : ∃ u : Finset V, Q = convexHull ℝ (u : Set V) := by
      rw [hvR] at hQR
      obtain ⟨u, _, hu⟩ := hQR.eq_convexHull_subset
      exact ⟨u, hu⟩
    obtain ⟨S, hS, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hR
    exact canonicalCenter_supporting_iff hn hvQ
      ((hi S hS P hP).inter_restrict (hQR.subset.trans Set.inter_subset_left))
  rw [chainFaces_restrict _ _ P hc s, faceClosure_cutParents_filter A a b hv hi hP]

lemma cutCell_restrict_irrelevant (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    {I L : Finset J} (hIL : I ⊆ L) (t : L → Bool)
    (hz : ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 < b j)
    (hn : (cutCell P (fun j : L => a j) (fun j : L => b j) t).Nonempty) :
    cutCell P (fun j : L => a j) (fun j : L => b j) t =
      cutCell P (fun j : I => a j) (fun j : I => b j)
        (fun j => t ⟨j.val, hIL j.property⟩) := by
  classical
  obtain ⟨z, hzP, hzt⟩ := hn
  have ht {j : L} (hj : j.val ∉ I) : t j = true := by
    have hh := hzt j
    have hzero := hz j.val j.property hj z hzP
    cases he : t j
    · simp only [signedForm, signedBound, he, Bool.false_eq_true, ↓reduceIte,
        LinearMap.neg_apply, hzero, neg_zero] at hh
      linarith [hb j.val j.property]
    · rfl
  ext x
  constructor
  · rintro ⟨hx, hxL⟩
    exact ⟨hx, fun j => hxL ⟨j.val, hIL j.property⟩⟩
  · rintro ⟨hx, hxI⟩
    refine ⟨hx, ?_⟩
    intro j
    by_cases hj : j.val ∈ I
    · exact hxI ⟨j.val, hj⟩
    · simp only [signedForm, signedBound, ht hj, ↓reduceIte, hz j.val j.property hj x hx]
      exact (hb j.val j.property).le

lemma cutParents_eq_irrelevant (A : Finset (Set V))
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) {I L : Finset J} (hIL : I ⊆ L)
    (hz : ∀ P ∈ A, ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 < b j) :
    cutParents A (fun j : I => a j) (fun j : I => b j) =
      cutParents A (fun j : L => a j) (fun j : L => b j) := by
  apply Finset.Subset.antisymm
  · exact cutParents_mono_irrelevant (Finset.Subset.refl _) a b hIL hz
      (fun j hj => (hb j hj).le)
  · intro Q hQ
    obtain ⟨P, hP, e, rfl, hn⟩ := (mem_cutParents _ _ _ _).mp hQ
    exact (mem_cutParents _ _ _ _).mpr ⟨P, hP, _,
      cutCell_restrict_irrelevant P a b hIL e (hz P hP) hb hn, hn⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_finite (F : Finset (Set V)) (c : Set V → V) : (chainFaces F c).Finite := by
  classical
  apply (F.powerset.image (fun t : Finset (Set V) => t.image c)).finite_toSet.subset
  rintro s ⟨t, _, ht, _, rfl⟩
  exact Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr ht)

structure LocalCutData (K : Geometry.SimplicialComplex ℝ V) (J : Type*) where
  form : J → V →ₗ[ℝ] ℝ
  level : J → ℝ
  positive : ∀ j, 0 < level j
  relevant : Finset V → Finset J
  vanish : ∀ s ∈ K.faces, ∀ j, j ∉ relevant s →
    ∀ x ∈ convexHull ℝ (s : Set V), form j x = 0

abbrev CutPatch (K : Geometry.SimplicialComplex ℝ V) :=
  {A : Finset (Finset V) // ∀ s ∈ A, s ∈ K.faces}

lemma finitePatch_le (K : Geometry.SimplicialComplex ℝ V) (p : CutPatch K) :
    finitePatch K p.val p.property ≤ K := by
  rintro s ⟨hs, t, ht, hst⟩
  exact K.down_closed (p.property t ht) hst hs

namespace LocalCutData

variable {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)

noncomputable def patchIndices (p : CutPatch K) : Finset J := p.val.biUnion d.relevant

lemma patchIndices_mono {p q : CutPatch K} (hpq : p.val ⊆ q.val) :
    d.patchIndices p ⊆ d.patchIndices q := by
  classical
  intro j hj
  obtain ⟨s, hs, hj⟩ := Finset.mem_biUnion.mp hj
  exact Finset.mem_biUnion.mpr ⟨s, hpq hs, hj⟩

lemma patch_vanish (p : CutPatch K) (P : Set V)
    (hP : P ∈ complexParents (finitePatch K p.val p.property)
      (finitePatch_finite K p.val p.property)) (j : J) (hj : j ∉ d.patchIndices p) :
    ∀ x ∈ P, d.form j x = 0 := by
  classical
  obtain ⟨s, ⟨_, t, ht, hst⟩, rfl⟩ := (mem_complexParents _ _ P).mp hP
  have hjt : j ∉ d.relevant t := fun h =>
    hj (Finset.mem_biUnion.mpr ⟨t, ht, h⟩)
  exact fun x hx => d.vanish t (p.property t ht) j hjt x (convexHull_mono hst hx)

noncomputable def patchTriangulation (p : CutPatch K) :
    CellTriangulation (complexParents (finitePatch K p.val p.property)
      (finitePatch_finite K p.val p.property)) :=
  Classical.choose (exists_canonical_simplicialCuts (finitePatch K p.val p.property)
    (finitePatch_finite K p.val p.property)
    (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j))

lemma patchTriangulation_faces (p : CutPatch K) :
    (d.patchTriangulation p).complex.faces = chainFaces
      (faceClosure (cutParents (complexParents (finitePatch K p.val p.property)
        (finitePatch_finite K p.val p.property))
        (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j)))
      canonicalCenter :=
  (Classical.choose_spec (exists_canonical_simplicialCuts (finitePatch K p.val p.property)
    (finitePatch_finite K p.val p.property)
    (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j))).1

lemma patchTriangulation_trace (p : CutPatch K) (s : Finset V)
    (hs : s ∈ (finitePatch K p.val p.property).faces) (e : d.patchIndices p → Bool) :
    RespectsSet (d.patchTriangulation p).complex
      (cutCell (convexHull ℝ (s : Set V))
        (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j) e) :=
  (Classical.choose_spec (exists_canonical_simplicialCuts (finitePatch K p.val p.property)
    (finitePatch_finite K p.val p.property)
    (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j))).2 s hs e

lemma patchTriangulation_mono {p q : CutPatch K} (hpq : p.val ⊆ q.val) :
    (d.patchTriangulation p).complex ≤ (d.patchTriangulation q).complex := by
  intro s hs
  change s ∈ (d.patchTriangulation p).complex.faces at hs
  change s ∈ (d.patchTriangulation q).complex.faces
  rw [d.patchTriangulation_faces] at hs ⊢
  refine chainFaces_mono (faceClosure_mono (cutParents_mono_irrelevant ?_
    d.form d.level (d.patchIndices_mono hpq) ?_ ?_)) hs
  · exact complexParents_mono _ _ (finitePatch_mono K p.property q.property hpq)
  · intro P hP j _ hj
    exact d.patch_vanish p P hP j hj
  · exact fun j _ => (d.positive j).le

lemma patchTriangulation_directed : Directed (· ≤ ·) (fun p : CutPatch K =>
    (d.patchTriangulation p).complex) := by
  classical
  intro p q
  let u : CutPatch K := ⟨p.val ∪ q.val, fun s hs => (Finset.mem_union.mp hs).elim
    (p.property s) (q.property s)⟩
  exact ⟨u, d.patchTriangulation_mono Finset.subset_union_left,
    d.patchTriangulation_mono Finset.subset_union_right⟩

noncomputable def globalComplex : Geometry.SimplicialComplex ℝ V :=
  directedUnionComplex (fun p : CutPatch K => (d.patchTriangulation p).complex)
    d.patchTriangulation_directed

lemma globalComplex_space : d.globalComplex.space = K.space := by
  change (directedUnionComplex _ d.patchTriangulation_directed).space = _
  rw [directedUnionComplex_space]
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    rw [(d.patchTriangulation p).space, complexParents_space] at hp
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, finitePatch_le K p hs, hx⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    let p : CutPatch K := ⟨{s}, by simpa using hs⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p, ?_⟩
    rw [(d.patchTriangulation p).space, complexParents_space]
    exact Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨s, mem_finitePatch K p.val p.property (Finset.mem_singleton_self s), hx⟩

lemma globalComplex_carrier {s : Finset V} (hs : s ∈ d.globalComplex.faces) :
    ∃ t ∈ K.faces, convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨P, hP, hsP⟩ := (d.patchTriangulation p).carrier s hp
  obtain ⟨t, ht, rfl⟩ := (mem_complexParents _ _ P).mp hP
  exact ⟨t, finitePatch_le K p ht, hsP⟩

lemma globalComplex_trace (s : Finset V) (hs : s ∈ K.faces) :
    RespectsSet d.globalComplex (convexHull ℝ (s : Set V)) := by
  classical
  rintro t ⟨p, hp⟩
  let q : CutPatch K := ⟨insert s p.val, by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hs
    · exact p.property u hu⟩
  have hpq : p.val ⊆ q.val := Finset.subset_insert _ _
  have hsq : s ∈ (finitePatch K q.val q.property).faces :=
    mem_finitePatch K q.val q.property (Finset.mem_insert_self _ _)
  exact (d.patchTriangulation q).trace _ ((mem_complexParents _ _ _).mpr ⟨s, hsq, rfl⟩)
    t (d.patchTriangulation_mono hpq hp)

lemma globalComplex_cut_trace (s : Finset V) (hs : s ∈ K.faces)
    (e : d.relevant s → Bool) : RespectsSet d.globalComplex
      (cutCell (convexHull ℝ (s : Set V)) (fun j : d.relevant s => d.form j)
        (fun j : d.relevant s => d.level j) e) := by
  classical
  rintro t ⟨p, hp⟩
  let q : CutPatch K := ⟨insert s p.val, by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hs
    · exact p.property u hu⟩
  have hsq : s ∈ (finitePatch K q.val q.property).faces :=
    mem_finitePatch K q.val q.property (Finset.mem_insert_self _ _)
  have hi : d.relevant s ⊆ d.patchIndices q := fun j hj =>
    Finset.mem_biUnion.mpr ⟨s, Finset.mem_insert_self _ _, hj⟩
  obtain ⟨e', he⟩ := cutCell_extend_irrelevant (convexHull ℝ (s : Set V))
    d.form d.level hi e (fun j _ hj => d.vanish s hs j hj) (fun j _ => (d.positive j).le)
  rw [he]
  exact d.patchTriangulation_trace q s hsq e' t
    (d.patchTriangulation_mono (Finset.subset_insert _ _) hp)

lemma patchTriangulation_restrict_faces (p : CutPatch K) (s : Finset V)
    (hs : s ∈ p.val) :
    (restrictComplex (d.patchTriangulation p).complex
      (convexHull ℝ (s : Set V))).faces =
      chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)}
        (fun j : d.relevant s => d.form j) (fun j : d.relevant s => d.level j)))
        canonicalCenter := by
  classical
  let L := finitePatch K p.val p.property
  have hsL : s ∈ L.faces := mem_finitePatch K p.val p.property hs
  have hsub : d.relevant s ⊆ d.patchIndices p := fun j hj =>
    Finset.mem_biUnion.mpr ⟨s, hs, hj⟩
  have he := cutParents_eq_irrelevant {convexHull ℝ (s : Set V)}
    d.form d.level hsub (by
      intro P hP j _ hj x hx
      have hP' : P = convexHull ℝ (s : Set V) := Finset.mem_singleton.mp hP
      subst P
      exact d.vanish s (p.property s hs) j hj x hx)
    (fun j _ => d.positive j)
  ext t
  change t ∈ (d.patchTriangulation p).complex.faces ∧
    (t : Set V) ⊆ convexHull ℝ (s : Set V) ↔ _
  rw [d.patchTriangulation_faces]
  rw [canonical_chainFaces_restrict_parent _ _ _
    (cutParents_finiteHull_simplicial L (finitePatch_finite K p.val p.property) _ _)
    (fun P hP Q hQ => simplicialParents_inter_supporting L _ hP hQ)
    ((mem_complexParents L _ _).mpr ⟨s, hsL, rfl⟩)]
  rw [← he]

lemma globalComplex_restrict_faces (s : Finset V) (hs : s ∈ K.faces) :
    (restrictComplex d.globalComplex (convexHull ℝ (s : Set V))).faces =
      chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)}
        (fun j : d.relevant s => d.form j) (fun j : d.relevant s => d.level j)))
        canonicalCenter := by
  classical
  ext t
  constructor
  · rintro ⟨⟨p, hp⟩, ht⟩
    let q : CutPatch K := ⟨insert s p.val, by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hs
      · exact p.property u hu⟩
    have hq : t ∈ (restrictComplex (d.patchTriangulation q).complex
        (convexHull ℝ (s : Set V))).faces :=
      ⟨d.patchTriangulation_mono (Finset.subset_insert _ _) hp, ht⟩
    rwa [d.patchTriangulation_restrict_faces q s (Finset.mem_insert_self _ _)] at hq
  · intro ht
    let p : CutPatch K := ⟨{s}, by simpa using hs⟩
    rw [← d.patchTriangulation_restrict_faces p s (Finset.mem_singleton_self _)] at ht
    exact ⟨⟨p, ht.1⟩, ht.2⟩

lemma globalComplex_restrict_finite (s : Finset V) (hs : s ∈ K.faces) :
    (restrictComplex d.globalComplex (convexHull ℝ (s : Set V))).faces.Finite := by
  rw [d.globalComplex_restrict_faces s hs]
  exact chainFaces_finite _ _

lemma globalComplex_restrict_space (s : Finset V) (hs : s ∈ K.faces) :
    (restrictComplex d.globalComplex (convexHull ℝ (s : Set V))).space =
      convexHull ℝ (s : Set V) := by
  rw [restrictComplex_space_of_respects _ _ (d.globalComplex_trace s hs),
    d.globalComplex_space]
  exact Set.inter_eq_right.mpr (K.convexHull_subset_space hs)

end LocalCutData

end LocallyFiniteCuts

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
lemma cutCell_reindex (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (e : I ≃ J) (s : J → Bool) :
    cutCell P (a ∘ e) (b ∘ e) (s ∘ e) = cutCell P a b s := by
  ext x
  have h (i : I) :
      signedForm (a ∘ e) (s ∘ e) i x ≤ signedBound (b ∘ e) (s ∘ e) i ↔
      signedForm a s (e i) x ≤ signedBound b s (e i) := Iff.rfl
  change (x ∈ P ∧ ∀ i, signedForm (a ∘ e) (s ∘ e) i x ≤
    signedBound (b ∘ e) (s ∘ e) i) ↔
    (x ∈ P ∧ ∀ j, signedForm a s j x ≤ signedBound b s j)
  simp only [h]
  constructor
  · rintro ⟨hx, hle⟩
    exact ⟨hx, fun j => by simpa using hle (e.symm j)⟩
  · rintro ⟨hx, hle⟩
    exact ⟨hx, fun i => hle (e i)⟩

lemma cutParents_reindex (A : Finset (Set V)) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (e : I ≃ J) : cutParents A (a ∘ e) (b ∘ e) = cutParents A a b := by
  classical
  apply Finset.ext
  intro Q
  rw [mem_cutParents, mem_cutParents]
  constructor
  · rintro ⟨P, hP, s, rfl, hn⟩
    let t : J → Bool := s ∘ e.symm
    have he : t ∘ e = s := by funext i; simp [t]
    rw [← he, cutCell_reindex] at hn ⊢
    exact ⟨P, hP, t, rfl, hn⟩
  · rintro ⟨P, hP, s, rfl, hn⟩
    refine ⟨P, hP, s ∘ e, ?_, hn⟩
    exact (cutCell_reindex P a b e s).symm

end BassTrace.Sparse.Cuts

end OAI
