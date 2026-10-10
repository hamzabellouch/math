import OAI.RingTheory.BassTrace.CutNaturality

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section ArbitraryAmbientComplex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_finite_coordinate_patch (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) :
    ∃ U : Submodule ℝ V, FiniteDimensional ℝ U ∧
      ∀ s ∈ K.faces, (s : Set V) ⊆ Set.range U.subtype := by
  let S : Finset V := hK.toFinset.biUnion id
  let U : Submodule ℝ V := Submodule.span ℝ (S : Set V)
  refine ⟨U, FiniteDimensional.span_of_finite ℝ S.finite_toSet, ?_⟩
  intro s hs x hx
  have hxS : x ∈ S := Finset.mem_biUnion.mpr ⟨s, by simpa using hs, hx⟩
  exact ⟨⟨x, Submodule.subset_span hxS⟩, rfl⟩

end ArbitraryAmbientComplex

section FiniteComplexPatches

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def complexParents (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite) :
    Finset (Set V) := hK.toFinset.image fun (s : Finset V) => convexHull ℝ (s : Set V)

lemma mem_complexParents (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (P : Set V) : P ∈ complexParents K hK ↔
      ∃ s ∈ K.faces, P = convexHull ℝ (s : Set V) := by
  simp only [complexParents, Finset.mem_image, Set.Finite.mem_toFinset, eq_comm]

lemma complexParents_affineImage (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    complexParents (affineImageComplex K f hf) (affineImageComplex_finite K f hf hK) =
      (complexParents K hK).image (fun P => f '' P) := by
  apply Finset.ext
  intro P
  rw [mem_complexParents, Finset.mem_image]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨convexHull ℝ (t : Set V), (mem_complexParents K hK _).mpr ⟨t, ht, rfl⟩, ?_⟩
    rw [Finset.coe_map]
    exact f.image_convexHull (t : Set V)
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_complexParents K hK Q).mp hQ
    refine ⟨t.map ⟨f,hf⟩, ⟨t, ht, rfl⟩, ?_⟩
    rw [Finset.coe_map]
    exact f.image_convexHull (t : Set V)

lemma complexParents_space (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite) :
    familySpace (complexParents K hK) = K.space := by
  ext x
  constructor
  · rintro ⟨P, hP, hx⟩
    obtain ⟨s, hs, rfl⟩ := (mem_complexParents K hK P).mp hP
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, hs, hx⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact ⟨_, (mem_complexParents K hK _).mpr ⟨s, hs, rfl⟩, hx⟩

theorem exists_canonical_simplicialCuts (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) {J : Type*} [Fintype J]
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation (complexParents K hK),
      B.complex.faces = chainFaces
        (faceClosure (cutParents (complexParents K hK) a b)) canonicalCenter ∧
      ∀ s ∈ K.faces, ∀ e : J → Bool,
        RespectsSet B.complex (cutCell (convexHull ℝ (s : Set V)) a b e) := by
  obtain ⟨U, hdim, hU⟩ := exists_finite_coordinate_patch K hK
  let : FiniteDimensional ℝ U := hdim
  let f := U.subtype
  have hf : Function.Injective f := U.subtype_injective
  let L := affinePreimageComplex K f.toAffineMap hf
  have hL : L.faces.Finite := affinePreimageComplex_finite K f.toAffineMap hf hK
  have hLK : affineImageComplex L f.toAffineMap hf = K :=
    affineImage_preimage_complex K f.toAffineMap hf hU
  have hA : (complexParents L hL).image (fun P => f '' P) = complexParents K hK := by
    have hh := complexParents_affineImage L hL f.toAffineMap hf
    change (complexParents L hL).image (fun P => f.toAffineMap '' P) = _
    simpa only [hLK] using hh.symm
  have hdata : ∀ P ∈ complexParents L hL, Nonempty (CellData P) := by
    intro P hP
    obtain ⟨t, ht, rfl⟩ := (mem_complexParents L hL P).mp hP
    exact simplex_has_cellData t (L.nonempty_of_mem_faces ht) (L.indep ht)
  have hinter : ∀ P ∈ complexParents L hL, ∀ Q ∈ complexParents L hL,
      SupportingFace (P ∩ Q) P := by
    intro P hP Q hQ
    obtain ⟨s, hs, rfl⟩ := (mem_complexParents L hL P).mp hP
    obtain ⟨t, ht, rfl⟩ := (mem_complexParents L hL Q).mp hQ
    rw [L.convexHull_inter_convexHull hs ht, ← Finset.coe_inter]
    exact simplex_face_supporting s (s ∩ t) (L.indep hs) Finset.inter_subset_left
  obtain ⟨B, hB, htr⟩ := exists_embedded_canonical_cutTriangulation
    (complexParents L hL) hdata hinter f hf a b
  have htr' : ∀ P ∈ (complexParents L hL).image (fun P => f '' P), ∀ e : J → Bool,
      RespectsSet B.complex (cutCell P a b e) := by
    intro P hP e
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact htr Q hQ e
  have hres : ∃ C : CellTriangulation ((complexParents L hL).image (fun P => f '' P)),
      C.complex.faces = chainFaces
        (faceClosure (cutParents ((complexParents L hL).image (fun P => f '' P)) a b)) canonicalCenter ∧
      ∀ P ∈ (complexParents L hL).image (fun P => f '' P), ∀ e : J → Bool,
        RespectsSet C.complex (cutCell P a b e) := ⟨B, hB, htr'⟩
  rw [hA] at hres
  obtain ⟨C, hC, hCt⟩ := hres
  exact ⟨C, hC, fun s hs e => hCt _ ((mem_complexParents K hK _).mpr ⟨s, hs, rfl⟩) e⟩

end FiniteComplexPatches

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def directedUnionComplex {I : Type*} (K : I → Geometry.SimplicialComplex ℝ V)
    (hK : Directed (· ≤ ·) K) : Geometry.SimplicialComplex ℝ V where
  faces := {s | ∃ i, s ∈ (K i).faces}
  indep := by
    rintro s ⟨i, hi⟩
    exact (K i).indep hi
  isRelLowerSet_faces := by
    rintro s ⟨i, hi⟩
    exact ⟨(K i).nonempty_of_mem_faces hi, fun t hts ht =>
      ⟨i, (K i).down_closed hi hts ht⟩⟩
  inter_subset_convexHull := by
    rintro s t ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := hK i j
    exact (K k).inter_subset_convexHull (hik hi) (hjk hj)

lemma directedUnionComplex_space {I : Type*} (K : I → Geometry.SimplicialComplex ℝ V)
    (hK : Directed (· ≤ ·) K) : (directedUnionComplex K hK).space = ⋃ i, (K i).space := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, Set.mem_iUnion]
  exact ⟨fun ⟨s, ⟨i, hs⟩, hx⟩ => ⟨i, s, hs, hx⟩,
    fun ⟨i, s, hs, hx⟩ => ⟨s, ⟨i, hs⟩, hx⟩⟩

def finitePatch (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) : Geometry.SimplicialComplex ℝ V where
  faces := {s | s.Nonempty ∧ ∃ t ∈ A, s ⊆ t}
  indep := by
    rintro s ⟨hs, t, ht, hst⟩
    exact K.indep (K.down_closed (hA t ht) hst hs)
  isRelLowerSet_faces := by
    rintro s ⟨hs, t, ht, hst⟩
    exact ⟨hs, fun u hus hu => ⟨hu, t, ht, hus.trans hst⟩⟩
  inter_subset_convexHull := by
    rintro s t ⟨hs, u, hu, hsu⟩ ⟨ht, v, hv, htv⟩
    exact K.inter_subset_convexHull (K.down_closed (hA u hu) hsu hs)
      (K.down_closed (hA v hv) htv ht)

lemma finitePatch_finite (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) :
    (finitePatch K A hA).faces.Finite := by
  classical
  apply (A.biUnion Finset.powerset).finite_toSet.subset
  rintro s ⟨_, t, ht, hst⟩
  exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_powerset.mpr hst⟩

lemma finitePatch_mono (K : Geometry.SimplicialComplex ℝ V)
    {A B : Finset (Finset V)} (hA : ∀ s ∈ A, s ∈ K.faces) (hB : ∀ s ∈ B, s ∈ K.faces)
    (hAB : A ⊆ B) : finitePatch K A hA ≤ finitePatch K B hB := by
  rintro s ⟨hs, t, ht, hst⟩
  exact ⟨hs, t, hAB ht, hst⟩

lemma mem_finitePatch (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) {s : Finset V} (hs : s ∈ A) :
    s ∈ (finitePatch K A hA).faces :=
  ⟨K.nonempty_of_mem_faces (hA s hs), s, hs, Finset.Subset.refl s⟩

end BassTrace.Sparse.Cuts

end OAI
