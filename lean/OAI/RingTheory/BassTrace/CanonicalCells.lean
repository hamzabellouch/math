import OAI.RingTheory.BassTrace.CellTriangulation

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section CanonicalCenters

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def canonicalVertices (P : Set V) : Finset V :=
  if h : (P.extremePoints ℝ).Finite then h.toFinset else ∅

noncomputable def canonicalCenter (P : Set V) : V := vertexMean (canonicalVertices P)

lemma coe_canonicalVertices {P : Set V} (hP : (P.extremePoints ℝ).Finite) :
    (canonicalVertices P : Set V) = P.extremePoints ℝ := by
  simp [canonicalVertices, hP]

lemma finite_extremePoints_finiteHull (s : Finset V) :
    ((convexHull ℝ (s : Set V)).extremePoints ℝ).Finite :=
  s.finite_toSet.subset extremePoints_convexHull_subset

lemma finiteHull_eq_canonicalVertices (s : Finset V) :
    convexHull ℝ (s : Set V) =
      convexHull ℝ (canonicalVertices (convexHull ℝ (s : Set V)) : Set V) := by
  have hfin := finite_extremePoints_finiteHull s
  rw [coe_canonicalVertices hfin]
  have hk := closure_convexHull_extremePoints (s.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (s : Set V))
  rw [(hfin.isClosed_convexHull ℝ).closure_eq] at hk
  exact hk.symm

lemma canonicalCenter_mem_finiteHull {s : Finset V} (hs : s.Nonempty) :
    canonicalCenter (convexHull ℝ (s : Set V)) ∈ convexHull ℝ (s : Set V) := by
  have hne : (canonicalVertices (convexHull ℝ (s : Set V))).Nonempty := by
    apply Finset.coe_nonempty.mp
    have hh : (convexHull ℝ (s : Set V)).Nonempty :=
      convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
    exact convexHull_nonempty_iff.mp ((finiteHull_eq_canonicalVertices s) ▸ hh)
  exact (finiteHull_eq_canonicalVertices s).symm.subset (vertexMean_mem_convexHull hne)

lemma canonicalCenter_supports_finiteHull {s : Finset V} (hs : s.Nonempty)
    (f : V →ₗ[ℝ] ℝ) (d : ℝ)
    (hf : ∀ x ∈ convexHull ℝ (s : Set V), f x ≤ d)
    (he : f (canonicalCenter (convexHull ℝ (s : Set V))) = d) :
    ∀ x ∈ convexHull ℝ (s : Set V), f x = d := by
  have hne : (canonicalVertices (convexHull ℝ (s : Set V))).Nonempty := by
    apply Finset.coe_nonempty.mp
    have hh : (convexHull ℝ (s : Set V)).Nonempty :=
      convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
    exact convexHull_nonempty_iff.mp ((finiteHull_eq_canonicalVertices s) ▸ hh)
  intro x hx
  exact vertexMean_supports hne f d ((finiteHull_eq_canonicalVertices s) ▸ hf)
    he x ((finiteHull_eq_canonicalVertices s) ▸ hx)

lemma affine_image_extremePoints (e : V ≃ᵃ[ℝ] W) (P : Set V) :
    e '' P.extremePoints ℝ = (e '' P).extremePoints ℝ := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  have hseg (a b : V) : e '' openSegment ℝ a b = openSegment ℝ (e a) (e b) :=
    image_openSegment _ e.toAffineMap a b
  simp only [mem_extremePoints, e.surjective.forall, e.injective.mem_set_image,
    e.injective.eq_iff, ← hseg]

lemma canonicalVertices_map (e : V ≃ᵃ[ℝ] W) (P : Set V)
    (hP : (P.extremePoints ℝ).Finite) :
    canonicalVertices (e '' P) = (canonicalVertices P).map e.toEquiv.toEmbedding := by
  have himg : ((e '' P).extremePoints ℝ).Finite :=
    (affine_image_extremePoints e P) ▸ hP.image e
  apply Finset.coe_injective
  rw [coe_canonicalVertices himg, Finset.coe_map, coe_canonicalVertices hP]
  exact (affine_image_extremePoints e P).symm

lemma canonicalCenter_map (e : V ≃ᵃ[ℝ] W) (P : Set V)
    (hP : (P.extremePoints ℝ).Finite) (hne : (P.extremePoints ℝ).Nonempty) :
    canonicalCenter (e '' P) = e (canonicalCenter P) := by
  unfold canonicalCenter
  rw [canonicalVertices_map e P hP]
  apply vertexMean_map e
  apply Finset.coe_nonempty.mp
  rwa [coe_canonicalVertices hP]

variable [FiniteDimensional ℝ V]

noncomputable def CellData.canonical {P : Set V} (p : CellData P) : CellData P := by
  let v := polyhedronVertices p.a p.b
  have he : P = convexHull ℝ (v : Set V) := p.eq_cell.trans
    (cell_eq_convexHull_of_bounded p.a p.b (p.eq_cell ▸ p.bounded))
  have hv : v.Nonempty := Finset.coe_nonempty.mp
    (convexHull_nonempty_iff.mp (he ▸ (show P.Nonempty from ⟨p.center, p.center_mem⟩)))
  exact { p with
    center := canonicalCenter P
    center_mem := by rw [he]; exact canonicalCenter_mem_finiteHull hv
    center_support := by
      rw [he]
      exact fun f d hf he => canonicalCenter_supports_finiteHull hv f d hf he }

lemma CellData.canonical_center {P : Set V} (p : CellData P) :
    p.canonical.center = canonicalCenter P := rfl

theorem exists_canonical_cellTriangulation (F : Finset (Set V))
    (hF : FiniteCellFamily F) :
    ∃ B : CellTriangulation F, B.complex.faces = chainFaces F canonicalCenter := by
  apply exists_cellTriangulation_chains F hF canonicalCenter
  intro P hP
  obtain ⟨p⟩ := hF.data P hP
  exact ⟨p.canonical, rfl⟩

omit [FiniteDimensional ℝ V] in
lemma chainFaces_affine_map (F : Finset (Set V)) (c : Set V → V)
    (d : Set W → W) (e : V ≃ᵃ[ℝ] W)
    (hcd : ∀ P ∈ F, d (e '' P) = e (c P))
    {s : Finset V} (hs : s ∈ chainFaces F c) :
    s.map e.toEquiv.toEmbedding ∈ chainFaces (F.image fun P => e '' P) d := by
  classical
  obtain ⟨t, hne, ht, hchain, rfl⟩ := hs
  refine ⟨t.image (fun P => e '' P), hne.image _, ?_, ?_, ?_⟩
  · exact Finset.image_subset_image ht
  · intro P hP Q hQ hne
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
    have he : P' ≠ Q' := fun h => hne (h ▸ rfl)
    rcases hchain hP' hQ' he with h | h
    · exact Or.inl (Set.image_mono h)
    · exact Or.inr (Set.image_mono h)
  · rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro P hP
    exact (hcd P (ht hP)).symm

omit [FiniteDimensional ℝ V] [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_restrict (F : Finset (Set V)) (c : Set V → V) (P : Set V)
    (hc : ∀ Q ∈ F, c Q ∈ P ↔ Q ⊆ P) (s : Finset V) :
    s ∈ chainFaces F c ∧ (s : Set V) ⊆ P ↔
      s ∈ chainFaces (F.filter fun Q => Q ⊆ P) c := by
  classical
  constructor
  · rintro ⟨⟨t, hne, hsub, hchain, rfl⟩, hP⟩
    refine ⟨t, hne, ?_, hchain, rfl⟩
    intro Q hQ
    exact Finset.mem_filter.mpr ⟨hsub hQ,
      (hc Q (hsub hQ)).mp (hP (Finset.mem_image_of_mem c hQ))⟩
  · rintro ⟨t, hne, hsub, hchain, rfl⟩
    refine ⟨⟨t, hne, hsub.trans (Finset.filter_subset _ _), hchain, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
    have hh := Finset.mem_filter.mp (hsub hQ)
    exact (hc Q hh.1).mpr hh.2

omit [FiniteDimensional ℝ V] in

lemma canonical_chainFaces_affine_map (F : Finset (Set V)) (e : V ≃ᵃ[ℝ] W)
    (hvertices : ∀ P ∈ F, ∃ t : Finset V, t.Nonempty ∧ P = convexHull ℝ (t : Set V))
    {s : Finset V} (hs : s ∈ chainFaces F canonicalCenter) :
    s.map e.toEquiv.toEmbedding ∈
      chainFaces (F.image fun P => e '' P) canonicalCenter := by
  apply chainFaces_affine_map F canonicalCenter canonicalCenter e ?_ hs
  intro P hP
  obtain ⟨t, ht, rfl⟩ := hvertices P hP
  apply canonicalCenter_map e _ (finite_extremePoints_finiteHull t)
  exact (t.finite_toSet.isCompact_convexHull ℝ).extremePoints_nonempty
    (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr ht))

end CanonicalCenters

section CanonicalFaceFamilies

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def cellFaces (P : Set V) : Finset (Set V) :=
  if h : {Q : Set V | Q.Nonempty ∧ SupportingFace Q P}.Finite then h.toFinset else ∅

noncomputable def faceClosure (A : Finset (Set V)) : Finset (Set V) :=
  A.biUnion cellFaces

lemma mem_cellFaces {P Q : Set V} (hP : ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    Q ∈ cellFaces P ↔ Q.Nonempty ∧ SupportingFace Q P := by
  obtain ⟨s, rfl⟩ := hP
  simp [cellFaces, finite_supportingFaces s]

lemma mem_faceClosure (A : Finset (Set V))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V)) (Q : Set V) :
    Q ∈ faceClosure A ↔ ∃ P ∈ A, Q.Nonempty ∧ SupportingFace Q P := by
  simp only [faceClosure, Finset.mem_biUnion]
  constructor
  · rintro ⟨P, hP, hQ⟩
    exact ⟨P, hP, (mem_cellFaces (hvertices P hP)).mp hQ⟩
  · rintro ⟨P, hP, hQ⟩
    exact ⟨P, hP, (mem_cellFaces (hvertices P hP)).mpr hQ⟩

lemma SupportingFace.affine_image {P Q : Set V} (h : SupportingFace Q P)
    (e : V ≃ᵃ[ℝ] W) : SupportingFace (e '' Q) (e '' P) := by
  obtain ⟨f, d, hf, he⟩ := h
  let f' : W →ᵃ[ℝ] ℝ := f.toAffineMap.comp e.symm.toAffineMap
  have hh (x : V) : f'.linear (e x) = f x - f' 0 := by
    have := affine_decomp_apply f' (e x)
    have heval : f' (e x) = f x := by simp [f']
    rw [heval] at this
    linarith
  refine ⟨f'.linear, d - f' 0, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [hh]
    exact sub_le_sub_right (hf x hx) _
  · ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [e.injective.mem_set_image, Set.mem_inter_iff, Set.mem_ofPred_eq, hh]
    rw [he]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, sub_left_inj]

lemma cellFaces_affine_map (e : V ≃ᵃ[ℝ] W) {P : Set V}
    (hP : ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    cellFaces (e '' P) = (cellFaces P).image (fun Q => e '' Q) := by
  have himg : ∃ s : Finset W, e '' P = convexHull ℝ (s : Set W) := by
    obtain ⟨s, rfl⟩ := hP
    refine ⟨s.map e.toEquiv.toEmbedding, ?_⟩
    rw [Finset.coe_map]
    exact e.toAffineMap.image_convexHull (s : Set V)
  ext Q
  rw [mem_cellFaces himg, Finset.mem_image]
  constructor
  · rintro ⟨hne, hface⟩
    refine ⟨e.symm '' Q, (mem_cellFaces hP).mpr ⟨hne.image _, ?_⟩, ?_⟩
    · have h := hface.affine_image e.symm
      simpa only [Set.image_image, e.symm_apply_apply, Set.image_id'] using h
    · simp only [Set.image_image, e.apply_symm_apply, Set.image_id']
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨hne, hface⟩ := (mem_cellFaces hP).mp hR
    exact ⟨hne.image _, hface.affine_image e⟩

lemma faceClosure_affine_map (e : V ≃ᵃ[ℝ] W) (A : Finset (Set V))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    faceClosure (A.image fun P => e '' P) =
      (faceClosure A).image (fun P => e '' P) := by
  unfold faceClosure
  rw [Finset.biUnion_image, Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro P hP
  exact cellFaces_affine_map e (hvertices P hP)

theorem faceClosure_isCellFamily (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P) :
    FiniteCellFamily (faceClosure A) := by
  have hmem := mem_faceClosure A hvertices
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨P, hP, hne, hQP⟩ := (hmem Q).mp hQ
    obtain ⟨p⟩ := hdata P hP
    obtain ⟨s, hs⟩ := hvertices P hP
    exact ⟨p.supportingFace s hs hQP hne⟩
  · intro Q hQ R hRQ hne
    obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
    obtain ⟨s, hs⟩ := hvertices P hP
    apply (hmem R).mpr
    refine ⟨P, hP, hne, ?_⟩
    rw [hs] at hQP ⊢
    exact hQP.trans_finite_hull hRQ
  · intro Q hQ R hR
    obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
    obtain ⟨S, hS, _, hRS⟩ := (hmem R).mp hR
    obtain ⟨s, hs⟩ := hvertices P hP
    obtain ⟨t, _, ht⟩ := (hs ▸ hQP).eq_convexHull_subset
    exact hQP.inter_of_parent_inter hRS (hinter P hP S hS) ht

variable [FiniteDimensional ℝ V]

theorem exists_canonical_parentTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P) :
    ∃ B : CellTriangulation A,
      B.complex.faces = chainFaces (faceClosure A) canonicalCenter := by
  have hmem := mem_faceClosure A hvertices
  have hsubset : A ⊆ faceClosure A := by
    intro P hP
    apply (hmem P).mpr
    obtain ⟨p⟩ := hdata P hP
    exact ⟨P, hP, ⟨p.center, p.center_mem⟩, supportingFace_self P⟩
  obtain ⟨B, hB⟩ := exists_canonical_cellTriangulation (faceClosure A)
    (faceClosure_isCellFamily A hdata hvertices hinter)
  let C : CellTriangulation A := {
    complex := B.complex
    finite := B.finite
    space := by
      rw [B.space]
      ext x
      constructor
      · rintro ⟨Q, hQ, hxQ⟩
        obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
        exact ⟨P, hP, hQP.subset hxQ⟩
      · rintro ⟨P, hP, hxP⟩
        exact ⟨P, hsubset hP, hxP⟩
    trace := fun P hP => B.trace P (hsubset hP)
    carrier := by
      intro s hs
      obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
      obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
      exact ⟨P, hP, hsQ.trans hQP.subset⟩ }
  exact ⟨C, hB⟩

end CanonicalFaceFamilies

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma affineIndependent_map_finset (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) :
    AffineIndependent ℝ ((↑) : s.map ⟨f, hf⟩ → F) := by
  have h := hs.map' f hf
  have he : f ∘ ((↑) : s → E) =
      ((↑) : s.map ⟨f, hf⟩ → F) ∘ (s.equivMap ⟨f, hf⟩) := rfl
  rw [he, affineIndependent_equiv] at h
  exact h

noncomputable def affineImageComplex (K : Geometry.SimplicialComplex ℝ E)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) : Geometry.SimplicialComplex ℝ F where
  faces := (fun s : Finset E => s.map ⟨f, hf⟩) '' K.faces
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    refine ⟨(K.nonempty_of_mem_faces ht).map, ?_⟩
    intro u hut hu
    let t' := t.filter (fun x => f x ∈ u)
    have he : t'.map ⟨f, hf⟩ = u := by
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, t']
      constructor
      · rintro ⟨x, ⟨_, hu⟩, rfl⟩; exact hu
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp (hut hy)
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    refine ⟨t', K.down_closed ht (Finset.filter_subset _ _) ?_, he⟩
    exact Finset.map_nonempty.mp (he.symm ▸ hu)
  indep := by
    rintro s ⟨t, ht, rfl⟩
    exact affineIndependent_map_finset f hf (K.indep ht)
  inter_subset_convexHull := by
    rintro s t ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ x hx
    have hconv (a : Finset E) :
        convexHull ℝ (a.map ⟨f, hf⟩ : Set F) = f '' convexHull ℝ (a : Set E) := by
      rw [Finset.coe_map]
      exact (f.image_convexHull (a : Set E)).symm
    rw [hconv, hconv, ← Set.image_inter hf] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hh := K.inter_subset_convexHull hu hv hy
    have hab : ((u.map ⟨f, hf⟩ ∩ v.map ⟨f, hf⟩ : Finset F) : Set F) =
        ((u ∩ v).map ⟨f, hf⟩ : Set F) := by rw [Finset.map_inter]
    rw [← Finset.coe_inter, hab, hconv]
    exact ⟨y, by simpa only [Finset.coe_inter] using hh, rfl⟩

lemma affineImageComplex_finite (K : Geometry.SimplicialComplex ℝ E)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (hK : K.faces.Finite) :
    (affineImageComplex K f hf).faces.Finite := hK.image _

lemma affineImageComplex_space (K : Geometry.SimplicialComplex ℝ E)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) :
    (affineImageComplex K f hf).space = f '' K.space := by
  ext y
  simp only [Geometry.SimplicialComplex.mem_space_iff, affineImageComplex, Set.mem_image]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, hy⟩
    rw [Finset.coe_map] at hy
    change y ∈ convexHull ℝ (f '' (t : Set E)) at hy
    rw [← f.image_convexHull] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨t, ht, hx⟩, rfl⟩
  · rintro ⟨x, ⟨t, ht, hx⟩, rfl⟩
    refine ⟨t.map ⟨f, hf⟩, ⟨t, ht, rfl⟩, ?_⟩
    rw [Finset.coe_map]
    change f x ∈ convexHull ℝ (f '' (t : Set E))
    rw [← f.image_convexHull]
    exact ⟨x, hx, rfl⟩

lemma affine_image_extremePoints_injective (f : E →ᵃ[ℝ] F)
    (hf : Function.Injective f) (P : Set E) :
    f '' P.extremePoints ℝ = (f '' P).extremePoints ℝ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxP, hxe⟩ := mem_extremePoints_iff_left.mp hx
    apply mem_extremePoints_iff_left.mpr
    refine ⟨⟨x, hxP, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [← image_openSegment ℝ f a b, hf.mem_set_image] at hab
    exact congrArg f (hxe a ha b hb hab)
  · intro hy
    obtain ⟨hyP, hye⟩ := mem_extremePoints_iff_left.mp hy
    obtain ⟨x, hx, rfl⟩ := hyP
    refine ⟨x, mem_extremePoints_iff_left.mpr ⟨hx, ?_⟩, rfl⟩
    intro a ha b hb hab
    apply hf
    apply hye _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← image_openSegment ℝ f a b]
    exact ⟨x, hab, rfl⟩

noncomputable def affinePreimageComplex (K : Geometry.SimplicialComplex ℝ F)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) : Geometry.SimplicialComplex ℝ E where
  faces := (fun s : Finset E => s.map ⟨f, hf⟩) ⁻¹' K.faces
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨Finset.map_nonempty.mp (K.nonempty_of_mem_faces hs), ?_⟩
    intro t hts ht
    exact K.down_closed hs (Finset.map_subset_map.mpr hts) ht.map
  indep := by
    intro s hs
    apply AffineIndependent.of_comp f
    have h := (affineIndependent_equiv (s.equivMap ⟨f,hf⟩)).mpr (K.indep hs)
    exact h
  inter_subset_convexHull := by
    intro s t hs ht x hx
    have hconv (a : Finset E) :
        convexHull ℝ (a.map ⟨f, hf⟩ : Set F) = f '' convexHull ℝ (a : Set E) := by
      rw [Finset.coe_map]
      exact (f.image_convexHull (a : Set E)).symm
    have hx' : f x ∈ convexHull ℝ (s.map ⟨f,hf⟩ : Set F) ∩
        convexHull ℝ (t.map ⟨f,hf⟩ : Set F) := by
      rw [hconv, hconv]
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
    have hh := K.inter_subset_convexHull hs ht hx'
    rw [← Finset.coe_inter, ← Finset.map_inter, hconv, hf.mem_set_image] at hh
    simpa only [Finset.coe_inter] using hh

lemma affinePreimageComplex_finite (K : Geometry.SimplicialComplex ℝ F)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (hK : K.faces.Finite) :
    (affinePreimageComplex K f hf).faces.Finite := by
  exact hK.preimage (Finset.map_injective ⟨f, hf⟩).injOn

lemma affineImage_preimage_complex (K : Geometry.SimplicialComplex ℝ F)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (hK : ∀ s ∈ K.faces, (s : Set F) ⊆ Set.range f) :
    affineImageComplex (affinePreimageComplex K f hf) f hf = K := by
  apply Geometry.SimplicialComplex.ext
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hs
    let t := s.preimage f hf.injOn
    have ht : t.map ⟨f,hf⟩ = s := by
      ext y
      simp only [Finset.mem_map, t, Finset.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hy
        obtain ⟨x, rfl⟩ := hK s hs hy
        exact ⟨x, hy, rfl⟩
    exact ⟨t, show t.map ⟨f,hf⟩ ∈ K.faces by rwa [ht], ht⟩

end BassTrace.Sparse.Cuts

end OAI
