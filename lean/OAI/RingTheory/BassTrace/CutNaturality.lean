import OAI.RingTheory.BassTrace.CanonicalCells

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section EmbeddingNaturality

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma vertexMean_affine_map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {s : Finset V} (hs : s.Nonempty) :
    vertexMean (s.map ⟨f, hf⟩) = f (vertexMean s) := by
  rw [vertexMean_eq_centroid hs, vertexMean_eq_centroid hs.map, Finset.centroid_map]
  simp only [Finset.centroid_def]
  convert (s.map_affineCombination id (s.centroidWeights ℝ)
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) f).symm using 1
  rfl

lemma canonicalVertices_affine_map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (P : Set V) (hP : (P.extremePoints ℝ).Finite) :
    canonicalVertices (f '' P) = (canonicalVertices P).map ⟨f, hf⟩ := by
  have himg : ((f '' P).extremePoints ℝ).Finite :=
    (affine_image_extremePoints_injective f hf P) ▸ hP.image f
  apply Finset.coe_injective
  rw [coe_canonicalVertices himg, Finset.coe_map, coe_canonicalVertices hP]
  exact (affine_image_extremePoints_injective f hf P).symm

lemma canonicalCenter_affine_map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (P : Set V) (hP : (P.extremePoints ℝ).Finite) (hne : (P.extremePoints ℝ).Nonempty) :
    canonicalCenter (f '' P) = f (canonicalCenter P) := by
  unfold canonicalCenter
  rw [canonicalVertices_affine_map f hf P hP]
  apply vertexMean_affine_map f hf
  apply Finset.coe_nonempty.mp
  rwa [coe_canonicalVertices hP]

lemma SupportingFace.affine_image_injective {P Q : Set V} (h : SupportingFace Q P)
    (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    SupportingFace (f '' Q) (f '' P) := by
  obtain ⟨a, d, ha, he⟩ := h
  obtain ⟨g, hg⟩ := f.linear.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (f.linear_injective_iff.mpr hf))
  let a' : W →ₗ[ℝ] ℝ := a.comp g
  have hh (x : V) : a' (f x) = a x + a' (f 0) := by
    have hd := affine_decomp_apply (a'.toAffineMap.comp f) x
    have hgx := LinearMap.congr_fun hg x
    change g (f.linear x) = x at hgx
    simpa [a', hgx] using hd
  refine ⟨a', d + a' (f 0), ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [hh]
    linarith [ha x hx]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [he] at hx
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      change a' (f x) = d + a' (f 0)
      rw [hh x]
      exact congrArg (fun z => z + a' (f 0)) hx.2
    · rintro ⟨⟨x, hx, rfl⟩, hax⟩
      refine ⟨x, ?_, rfl⟩
      rw [he]
      change a' (f x) = d + a' (f 0) at hax
      rw [hh x] at hax
      exact ⟨hx, add_right_cancel hax⟩

lemma SupportingFace.affine_preimage {P Q : Set W} (h : SupportingFace Q P)
    (f : V →ᵃ[ℝ] W) : SupportingFace (f ⁻¹' Q) (f ⁻¹' P) := by
  obtain ⟨a, d, ha, he⟩ := h
  let a' : V →ₗ[ℝ] ℝ := a.comp f.linear
  have hh (x : V) : a (f x) = a' x + a (f 0) :=
    affine_decomp_apply (a.toAffineMap.comp f) x
  refine ⟨a', d - a (f 0), ?_, ?_⟩
  · intro x hx
    have ht := ha (f x) hx
    rw [hh] at ht
    linarith
  · ext x
    simp only [Set.mem_preimage, he, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [hh x]
    exact and_congr_right (fun _ => eq_sub_iff_add_eq.symm)

lemma cellFaces_affine_map_injective (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (hP : ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    cellFaces (f '' P) = (cellFaces P).image (fun Q => f '' Q) := by
  have himg : ∃ s : Finset W, f '' P = convexHull ℝ (s : Set W) := by
    obtain ⟨s, rfl⟩ := hP
    refine ⟨s.map ⟨f, hf⟩, ?_⟩
    rw [Finset.coe_map]
    exact f.image_convexHull (s : Set V)
  ext Q
  rw [mem_cellFaces himg, Finset.mem_image]
  constructor
  · rintro ⟨hne, hface⟩
    have hsub := hface.subset
    have he : f '' (f ⁻¹' Q) = Q := Set.image_preimage_eq_of_subset (hsub.trans (Set.image_subset_range f P))
    refine ⟨f ⁻¹' Q, (mem_cellFaces hP).mpr ⟨?_, ?_⟩, he⟩
    · obtain ⟨y, hy⟩ := hne
      obtain ⟨x, _, rfl⟩ := hsub hy
      exact ⟨x, hy⟩
    · have hh := hface.affine_preimage f
      simpa only [hf.preimage_image] using hh
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨hne, hface⟩ := (mem_cellFaces hP).mp hR
    exact ⟨hne.image _, hface.affine_image_injective f hf⟩

lemma RespectsSet.affine_image {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (h : RespectsSet K P) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    RespectsSet (affineImageComplex K f hf) (f '' P) := by
  rintro s ⟨t, ht, rfl⟩
  rw [Finset.coe_map]
  change convexHull ℝ (f '' (t : Set V)) ∩ f '' P =
    convexHull ℝ ((f '' (t : Set V)) ∩ f '' P)
  rw [← f.image_convexHull, ← Set.image_inter hf, h t ht,
    f.image_convexHull, Set.image_inter hf]

noncomputable def CellTriangulation.affineImage {A : Finset (Set V)}
    (B : CellTriangulation A) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    CellTriangulation (A.image fun P => f '' P) where
  complex := affineImageComplex B.complex f hf
  finite := affineImageComplex_finite B.complex f hf B.finite
  space := by
    rw [affineImageComplex_space, B.space]
    ext y
    constructor
    · rintro ⟨x, ⟨P, hP, hx⟩, rfl⟩
      exact ⟨f '' P, Finset.mem_image_of_mem _ hP, x, hx, rfl⟩
    · rintro ⟨Q, hQ, hy⟩
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, ⟨P, hP, hx⟩, rfl⟩
  trace := by
    rintro Q hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    exact (B.trace P hP).affine_image f hf
  carrier := by
    rintro s ⟨t, ht, rfl⟩
    obtain ⟨P, hP, htP⟩ := B.carrier t ht
    refine ⟨f '' P, Finset.mem_image_of_mem _ hP, ?_⟩
    rw [Finset.coe_map]
    change convexHull ℝ (f '' (t : Set V)) ⊆ f '' P
    rw [← f.image_convexHull]
    exact Set.image_mono htP

lemma faceClosure_affine_map_injective (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (A : Finset (Set V))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    faceClosure (A.image fun P => f '' P) =
      (faceClosure A).image (fun P => f '' P) := by
  unfold faceClosure
  rw [Finset.biUnion_image, Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro P hP
  exact cellFaces_affine_map_injective f hf (hvertices P hP)

end EmbeddingNaturality

section CanonicalCuts

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {J : Type*} [Fintype J]

theorem exists_canonical_cutTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation A,
      B.complex.faces = chainFaces (faceClosure (cutParents A a b)) canonicalCenter ∧
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
  obtain ⟨B, hB⟩ := exists_canonical_parentTriangulation C hCdata hCvertices hCinter
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
  refine ⟨⟨B.complex, B.finite, B.space.trans hspace, htrace, hcarrier⟩, hB, ?_⟩
  intro P hP s
  by_cases hne : (cutCell P a b s).Nonempty
  · exact B.trace _ ((mem_cutParents A a b _).mpr ⟨P, hP, s, rfl, hne⟩)
  · have he : cutCell P a b s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    intro t ht
    simp [he]

end CanonicalCuts

section GeneralChains

variable {V W : Type*}

lemma chainFaces_map_injective (A : Finset (Set V)) (c : Set V → V)
    (d : Set W → W) (f : V → W) (hf : Function.Injective f)
    (hcd : ∀ P ∈ A, d (f '' P) = f (c P)) :
    chainFaces (A.image fun P => f '' P) d =
      (fun s : Finset V => s.map ⟨f, hf⟩) '' chainFaces A c := by
  have hfi : Function.Injective (fun P : Set V => f '' P) := Set.image_injective.mpr hf
  ext s
  constructor
  · rintro ⟨t, hne, ht, hchain, rfl⟩
    let u := t.preimage (fun P : Set V => f '' P) hfi.injOn
    have hu : u ⊆ A := by
      intro P hP
      have htP := ht (Finset.mem_preimage.mp hP)
      obtain ⟨Q, hQ, he⟩ := Finset.mem_image.mp htP
      exact hfi he ▸ hQ
    have hut : u.image (fun P => f '' P) = t := by
      ext Q
      simp only [Finset.mem_image, u, Finset.mem_preimage]
      constructor
      · rintro ⟨P, hP, rfl⟩; exact hP
      · intro hQ
        obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp (ht hQ)
        exact ⟨P, hQ, rfl⟩
    have hune : u.Nonempty := by
      obtain ⟨Q, hQ⟩ := hne
      rw [← hut] at hQ
      obtain ⟨P, hP, _⟩ := Finset.mem_image.mp hQ
      exact ⟨P, hP⟩
    have huchain : (u : Set (Set V)).Pairwise (fun P Q => P ⊆ Q ∨ Q ⊆ P) := by
      intro P hP Q hQ hpq
      have himgne : f '' P ≠ f '' Q := fun h => hpq (hfi h)
      rcases hchain (Finset.mem_preimage.mp hP) (Finset.mem_preimage.mp hQ) himgne with h | h
      · exact Or.inl ((Set.image_subset_image_iff hf).mp h)
      · exact Or.inr ((Set.image_subset_image_iff hf).mp h)
    refine ⟨u.image c, ⟨u, hune, hu, huchain, rfl⟩, ?_⟩
    change (u.image c).map ⟨f, hf⟩ = t.image d
    rw [← hut, Finset.image_image, Finset.map_eq_image, Finset.image_image]
    apply Finset.image_congr
    intro P hP
    exact (hcd P (hu hP)).symm
  · rintro ⟨s, ⟨t, hne, ht, hchain, rfl⟩, rfl⟩
    refine ⟨t.image (fun P => f '' P), hne.image _, Finset.image_subset_image ht, ?_, ?_⟩
    · intro P hP Q hQ hpq
      obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have hne' : P' ≠ Q' := fun h => hpq (h ▸ rfl)
      rcases hchain hP' hQ' hne' with h | h
      · exact Or.inl (Set.image_mono h)
      · exact Or.inr (Set.image_mono h)
    · change (t.image c).map ⟨f, hf⟩ = (t.image fun P => f '' P).image d
      rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro P hP
      exact (hcd P (ht hP)).symm

end GeneralChains

section LinearCutNaturality

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {J : Type*} [Fintype J]

omit [Fintype J] in
lemma cutCell_linear_image (f : V →ₗ[ℝ] W) (P : Set V)
    (a : J → W →ₗ[ℝ] ℝ) (b : J → ℝ) (s : J → Bool) :
    f '' cutCell P (fun j => (a j).comp f) b s = cutCell (f '' P) a b s := by
  have hh (x : V) (j : J) :
      signedForm (fun j => (a j).comp f) s j x = signedForm a s j (f x) := by
    cases h : s j <;> simp [signedForm, h]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxa⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, fun j => (hh x j) ▸ hxa j⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxa⟩
    exact ⟨x, ⟨hx, fun j => (hh x j).symm ▸ hxa j⟩, rfl⟩

lemma cutParents_linear_image (f : V →ₗ[ℝ] W) (A : Finset (Set V))
    (a : J → W →ₗ[ℝ] ℝ) (b : J → ℝ) :
    cutParents (A.image fun P => f '' P) a b =
      (cutParents A (fun j => (a j).comp f) b).image (fun P => f '' P) := by
  ext Q
  rw [mem_cutParents, Finset.mem_image]
  constructor
  · rintro ⟨P, hP, s, rfl, hne⟩
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hP
    rw [← cutCell_linear_image] at hne ⊢
    exact ⟨_, (mem_cutParents A _ b _).mpr
      ⟨R, hR, s, rfl, Set.image_nonempty.mp hne⟩, rfl⟩
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨P, hP, s, rfl, hne⟩ := (mem_cutParents A _ b R).mp hR
    refine ⟨f '' P, Finset.mem_image_of_mem _ hP, s, ?_, ?_⟩
    · exact cutCell_linear_image f P a b s
    · exact hne.image _

lemma canonical_chainFaces_map_injective (F : Finset (Set V))
    (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (hF : ∀ P ∈ F, ∃ s : Finset V, s.Nonempty ∧ P = convexHull ℝ (s : Set V)) :
    chainFaces (F.image fun P => f '' P) canonicalCenter =
      (fun s : Finset V => s.map ⟨f, hf⟩) '' chainFaces F canonicalCenter := by
  apply chainFaces_map_injective F canonicalCenter canonicalCenter f hf
  intro P hP
  obtain ⟨s, hs, rfl⟩ := hF P hP
  apply canonicalCenter_affine_map f hf _ (finite_extremePoints_finiteHull s)
  have hne : (canonicalVertices (convexHull ℝ (s : Set V))).Nonempty := by
    apply Finset.coe_nonempty.mp
    apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
    rw [← finiteHull_eq_canonicalVertices]
    exact convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
  have := Finset.coe_nonempty.mpr hne
  rwa [coe_canonicalVertices (finite_extremePoints_finiteHull s)] at this

end LinearCutNaturality

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma faceClosure_finiteHull (A : Finset (Set V))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    ∀ P ∈ faceClosure A, ∃ s : Finset V, s.Nonempty ∧ P = convexHull ℝ (s : Set V) := by
  intro Q hQ
  obtain ⟨P, hP, hne, hface⟩ := (mem_faceClosure A hvertices Q).mp hQ
  obtain ⟨t, rfl⟩ := hvertices P hP
  obtain ⟨s, _, rfl⟩ := hface.eq_convexHull_subset
  exact ⟨s, Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hne), rfl⟩

variable [FiniteDimensional ℝ V] {J : Type*} [Fintype J]

theorem exists_embedded_canonical_cutTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    (a : J → W →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation (A.image fun P => f '' P),
      B.complex.faces = chainFaces
        (faceClosure (cutParents (A.image fun P => f '' P) a b)) canonicalCenter ∧
      ∀ P ∈ A, ∀ s : J → Bool,
        RespectsSet B.complex (cutCell (f '' P) a b s) := by
  let a' : J → V →ₗ[ℝ] ℝ := fun j => (a j).comp f
  obtain ⟨B, hB, htr⟩ := exists_canonical_cutTriangulation A hdata hinter a' b
  have hv : ∀ P ∈ cutParents A a' b, ∃ s : Finset V, P = convexHull ℝ (s : Set V) := by
    intro P hP
    obtain ⟨Q, hQ, s, rfl, hne⟩ := (mem_cutParents A a' b P).mp hP
    obtain ⟨q⟩ := hdata Q hQ
    exact (cutCell_nonempty_data q a' b s hne).2
  refine ⟨B.affineImage f.toAffineMap hf, ?_, ?_⟩
  · change (fun s : Finset V => s.map ⟨f, hf⟩) '' B.complex.faces = _
    rw [hB, cutParents_linear_image]
    change (fun s : Finset V => s.map ⟨f.toAffineMap, hf⟩) ''
      chainFaces (faceClosure (cutParents A a' b)) canonicalCenter =
      chainFaces (faceClosure ((cutParents A a' b).image
        fun P => f.toAffineMap '' P)) canonicalCenter
    rw [faceClosure_affine_map_injective f.toAffineMap hf _ hv]
    exact (canonical_chainFaces_map_injective _ f.toAffineMap hf
      (faceClosure_finiteHull _ hv)).symm
  · intro P hP s
    have hh := (htr P hP s).affine_image f.toAffineMap hf
    change RespectsSet (B.affineImage f.toAffineMap hf).complex (f '' cutCell P a' b s) at hh
    rwa [cutCell_linear_image] at hh

end BassTrace.Sparse.Cuts

end OAI
