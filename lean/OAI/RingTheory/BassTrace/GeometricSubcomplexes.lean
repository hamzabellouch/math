import OAI.RingTheory.BassTrace.LocalCuts

namespace OAI

noncomputable section

namespace BassTrace

/-! Local finiteness passes to a simplexwise finite subdivision. -/

namespace Sparse

open Set

open scoped Topology

lemma locallyFinite_refinement {I J X : Type*} [TopologicalSpace X]
    {f : I → Set X} {g : J → Set X} (hf : LocallyFinite f)
    (c : J → I) (hc : ∀ j, g j ⊆ f (c j))
    (hfin : ∀ i, (c ⁻¹' {i}).Finite) : LocallyFinite g := by
  intro x
  obtain ⟨U, hU, hUf⟩ := hf x
  refine ⟨U, hU, ?_⟩
  have hb := hUf.biUnion (fun i _ => hfin i)
  apply hb.subset
  rintro j ⟨y, hy, hyU⟩
  exact Set.mem_iUnion₂.mpr ⟨c j, ⟨y, hc j hy, hyU⟩, rfl⟩

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

lemma simplicial_refinement_locallyFinite
    (K L : Geometry.SimplicialComplex ℝ V)
    (hK : LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set V)))
    (hcarrier : ∀ s ∈ L.faces, ∃ t ∈ K.faces,
      convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V))
    (hfin : ∀ t ∈ K.faces,
      {s ∈ L.faces | (s : Set V) ⊆ convexHull ℝ (t : Set V)}.Finite) :
    LocallyFinite (fun s : L.faces => convexHull ℝ (s.val : Set V)) := by
  classical
  choose c hcK hcs using hcarrier
  let carrier : L.faces → K.faces := fun s => ⟨c s.val s.property, hcK s.val s.property⟩
  apply locallyFinite_refinement hK carrier (fun s => hcs s.val s.property)
  intro t
  have ht := (hfin t.val t.property).preimage_embedding (Function.Embedding.subtype (fun s => s ∈ L.faces))
  apply ht.subset
  intro s hs
  have he : carrier s = t := hs
  refine ⟨s.property, ?_⟩
  have h := (subset_convexHull ℝ (s.val : Set V)).trans (hcs s.val s.property)
  change (s.val : Set V) ⊆ convexHull ℝ (t.val : Set V)
  rw [← congrArg Subtype.val he]
  exact h

end Sparse

namespace Sparse.Cuts

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {J : Type*}

lemma LocalCutData.globalComplex_locallyFinite {K : Geometry.SimplicialComplex ℝ V}
    (d : LocalCutData K J)
    (hK : LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set V))) :
    LocallyFinite (fun s : d.globalComplex.faces => convexHull ℝ (s.val : Set V)) := by
  apply simplicial_refinement_locallyFinite K d.globalComplex hK (fun _ => d.globalComplex_carrier)
  intro t ht
  exact d.globalComplex_restrict_finite t ht

end

/-! Geometric subcomplexes used by the compatible-cut lemma. A marked subset
is a union of closed simplices, not necessarily the full complex induced by
its old vertices. Keeping this distinction is essential for unions of levels. -/

section

open Set Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def geometricRestriction (K : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

def IsMarked (K : Geometry.SimplicialComplex ℝ E) (P : Set E) : Prop :=
  ∀ x ∈ P, ∃ s ∈ K.faces, x ∈ convexHull ℝ (s : Set E) ∧
    convexHull ℝ (s : Set E) ⊆ P

lemma geometricRestriction_le (K : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    geometricRestriction K P ≤ K := fun _ hs => hs.1

lemma IsMarked.subset_space {K : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P) : P ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hxs, _⟩ := hP x hx
  exact K.convexHull_subset_space hs hxs

lemma IsMarked.restriction_space {K : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P) : (geometricRestriction K P).space = P := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact hs.2 hxs
  · intro hx
    obtain ⟨s, hs, hxs, hsub⟩ := hP x hx
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, ⟨hs, hsub⟩, hxs⟩

lemma isMarked_empty (K : Geometry.SimplicialComplex ℝ E) : IsMarked K ∅ := by
  intro x hx
  exact hx.elim

lemma isMarked_space (K : Geometry.SimplicialComplex ℝ E) : IsMarked K K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  exact ⟨s, hs, hxs, K.convexHull_subset_space hs⟩

lemma isMarked_simplex (K : Geometry.SimplicialComplex ℝ E) {s : Finset E}
    (hs : s ∈ K.faces) : IsMarked K (convexHull ℝ (s : Set E)) :=
  fun _ hx => ⟨s, hs, hx, subset_rfl⟩

lemma IsMarked.sUnion {K : Geometry.SimplicialComplex ℝ E} {A : Set (Set E)}
    (hA : ∀ P ∈ A, IsMarked K P) : IsMarked K (⋃₀ A) := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := Set.mem_sUnion.mp hx
  obtain ⟨s, hs, hxs, hsub⟩ := hA P hP x hxP
  exact ⟨s, hs, hxs, hsub.trans (Set.subset_sUnion_of_mem hP)⟩

lemma IsMarked.iUnion {K : Geometry.SimplicialComplex ℝ E} {I : Sort*}
    {P : I → Set E} (hP : ∀ i, IsMarked K (P i)) : IsMarked K (⋃ i, P i) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨s, hs, hxs, hsub⟩ := hP i x hxi
  exact ⟨s, hs, hxs, hsub.trans (Set.subset_iUnion P i)⟩

lemma IsMarked.union {K : Geometry.SimplicialComplex ℝ E} {P Q : Set E}
    (hP : IsMarked K P) (hQ : IsMarked K Q) : IsMarked K (P ∪ Q) := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨s, hs, hxs, hsub⟩ := hP x hx
    exact ⟨s, hs, hxs, hsub.trans Set.subset_union_left⟩
  · obtain ⟨s, hs, hxs, hsub⟩ := hQ x hx
    exact ⟨s, hs, hxs, hsub.trans Set.subset_union_right⟩

lemma IsMarked.inter {K : Geometry.SimplicialComplex ℝ E} {P Q : Set E}
    (hP : IsMarked K P) (hQ : IsMarked K Q) : IsMarked K (P ∩ Q) := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs, hsP⟩ := hP x hx.1
  obtain ⟨t, ht, hxt, htQ⟩ := hQ x hx.2
  have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨hxs, hxt⟩
  have hne : (s ∩ t).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxst⟩)
  refine ⟨s ∩ t, K.down_closed hs Finset.inter_subset_left hne, hxst, ?_⟩
  exact subset_inter ((convexHull_mono Finset.inter_subset_left).trans hsP)
    ((convexHull_mono Finset.inter_subset_right).trans htQ)

lemma IsMarked.refinement {K L : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P)
    (hcover : ∀ s ∈ K.faces, IsMarked L (convexHull ℝ (s : Set E))) :
    IsMarked L P := by
  intro x hx
  obtain ⟨s, hs, hxs, hsP⟩ := hP x hx
  obtain ⟨t, ht, hxt, hts⟩ := hcover s hs x hxs
  exact ⟨t, ht, hxt, hts.trans hsP⟩

lemma card_lt_of_generic_hyperplane {s t : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (heq : ∀ x ∈ t, f x = b) (hne : ∃ x ∈ s, f x ≠ b) :
    t.card < s.card := by
  apply ht.card_lt_card_of_affineSpan_lt_affineSpan
  have hle : affineSpan ℝ (t : Set E) ≤ affineSpan ℝ (s : Set E) := by
    apply affineSpan_le.mpr
    exact hst.trans (convexHull_subset_affineSpan (s : Set E))
  apply lt_of_le_of_ne hle
  intro h
  have he : (t : Set E).EqOn f.toAffineMap (AffineMap.const ℝ E b) := heq
  have he' := AffineMap.eqOn_affineSpan he
  obtain ⟨x, hx, hnx⟩ := hne
  apply hnx
  exact he' (by rw [h]; exact subset_affineSpan ℝ (s : Set E) hx)

lemma exists_branch_eq_on_simplex {I : Type*} (a : I → E →ₗ[ℝ] ℝ)
    (b : ℝ) {t : Finset E} (ht : t.Nonempty)
    (hle : ∀ x ∈ convexHull ℝ (t : Set E), ∀ i, a i x ≤ b)
    (heq : ∀ x ∈ convexHull ℝ (t : Set E), ∃ i, a i x = b) :
    ∃ i, ∀ x ∈ t, a i x = b := by
  obtain ⟨i, hi⟩ := heq (vertexMean t) (vertexMean_mem_convexHull ht)
  refine ⟨i, (linear_vertexMean_eq_iff (a i) ht ?_).mp hi⟩
  intro x hx
  exact hle x (subset_convexHull ℝ (t : Set E) hx) i

lemma card_lt_of_generic_max_level {I : Type*} (a : I → E →ₗ[ℝ] ℝ)
    (b : ℝ) {s t : Finset E} (ht : t.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E))
    (hgeneric : ∀ i, ∃ x ∈ s, a i x ≠ b)
    (hle : ∀ x ∈ convexHull ℝ (t : Set E), ∀ i, a i x ≤ b)
    (heq : ∀ x ∈ convexHull ℝ (t : Set E), ∃ i, a i x = b) :
    t.card < s.card := by
  obtain ⟨i, hi⟩ := exists_branch_eq_on_simplex a b ht hle heq
  exact card_lt_of_generic_hyperplane hind hst (a i) b hi (hgeneric i)

end

section

open Set

lemma exists_generic_level {T I E : Type*} [Countable T] [Countable I]
    (s : T → Finset E) (a : I → E → ℝ) {r R : ℝ} (h : r < R) :
    ∃ b ∈ Set.Ioo r R, ∀ t i x, x ∈ s t → a i x ≠ b := by
  let bad : Set ℝ := ⋃ t, ⋃ i, a i '' (s t : Set E)
  have hbad : bad.Countable := by
    apply Set.countable_iUnion
    intro t
    apply Set.countable_iUnion
    intro i
    exact (s t).countable_toSet.image (a i)
  obtain ⟨b, hbnot, hb⟩ := hbad.dense_compl ℝ |>.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr h)
  refine ⟨b, hb, ?_⟩
  intro t i x hx he
  apply hbnot
  exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨i, x, hx, he⟩⟩

end

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma RespectsSet.isMarked {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (h : RespectsSet K P) : IsMarked K (K.space ∩ P) := by
  intro x hx
  have hx' : x ∈ (restrictComplex K P).space := by
    rw [restrictComplex_space_of_respects K P h]
    exact hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx'
  refine ⟨s, hs.1, hxs, fun y hy => ⟨K.convexHull_subset_space hs.1 hy, ?_⟩⟩
  have he : (s : Set V) ∩ P = s := Set.inter_eq_left.mpr hs.2
  have hy' : y ∈ convexHull ℝ (s : Set V) ∩ P := by
    rw [h s hs.1, he]
    exact hy
  exact hy'.2

lemma LocalCutData.globalComplex_isMarked_simplex {J : Type*}
    {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)
    (s : Finset V) (hs : s ∈ K.faces) :
    IsMarked d.globalComplex (convexHull ℝ (s : Set V)) := by
  have h := (d.globalComplex_trace s hs).isMarked
  rwa [d.globalComplex_space, Set.inter_eq_right.mpr (K.convexHull_subset_space hs)] at h

lemma LocalCutData.globalComplex_preserves_marked {J : Type*}
    {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)
    {P : Set V} (hP : IsMarked K P) : IsMarked d.globalComplex P :=
  hP.refinement d.globalComplex_isMarked_simplex

end

section

open Set Finset

section

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma cutParents_singleton_finiteHull (K : Geometry.SimplicialComplex ℝ V)
    (s : Finset V) (hs : s ∈ K.faces) {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ∀ P ∈ cutParents {convexHull ℝ (s : Set V)} a b,
      ∃ t : Finset V, P = convexHull ℝ (t : Set V) := by
  classical
  let p : CutPatch K := ⟨{s},by simpa using hs⟩
  let L := finitePatch K p.val p.property
  have hsub : {convexHull ℝ (s : Set V)} ⊆
      complexParents L (finitePatch_finite K p.val p.property) := by
    intro P hP
    have hP' := Finset.mem_singleton.mp hP
    subst P
    exact (mem_complexParents _ _ _).mpr
      ⟨s,mem_finitePatch K p.val p.property (Finset.mem_singleton_self _),rfl⟩
  intro P hP
  exact cutParents_finiteHull_simplicial L (finitePatch_finite K p.val p.property) a b P
    (cutParents_mono hsub a b hP)

lemma canonicalCuts_linear_map (K : Geometry.SimplicialComplex ℝ V)
    (s : Finset V) (hs : s ∈ K.faces) (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (a' : J → W →ₗ[ℝ] ℝ) (b' : J → ℝ)
    (ha : ∀ i, (a' (e i)).comp f = a i) (hb : ∀ i, b' (e i) = b i) :
    chainFaces (faceClosure (cutParents {convexHull ℝ ((s.map ⟨f,hf⟩) : Set W)} a' b'))
      canonicalCenter =
      (fun t : Finset V => t.map ⟨f,hf⟩) ''
        chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)} a b)) canonicalCenter := by
  have hp : cutParents {convexHull ℝ ((s.map ⟨f,hf⟩) : Set W)} a' b' =
      (cutParents {convexHull ℝ (s : Set V)} a b).image (fun P => f '' P) := by
    rw [← cutParents_reindex _ a' b' e]
    have hcoe : convexHull ℝ ((s.map ⟨f,hf⟩) : Set W) = f '' convexHull ℝ (s : Set V) := by
      rw [Finset.coe_map]
      exact (f.toAffineMap.image_convexHull _).symm
    rw [hcoe,← Finset.image_singleton,cutParents_linear_image]
    congr 1
    · congr 1
      · exact funext ha
      · exact funext hb
  rw [hp]
  have hfinite := cutParents_singleton_finiteHull K s hs a b
  have hfaces := faceClosure_affine_map_injective f.toAffineMap hf _ hfinite
  change faceClosure ((cutParents {convexHull ℝ (s : Set V)} a b).image
    (fun P => f '' P)) = (faceClosure (cutParents {convexHull ℝ (s : Set V)} a b)).image
    (fun P => f '' P) at hfaces
  rw [hfaces]
  exact canonical_chainFaces_map_injective _ f.toAffineMap hf
    (faceClosure_finiteHull _ hfinite)

namespace LocalCutData

variable {K : Geometry.SimplicialComplex ℝ V} {K' : Geometry.SimplicialComplex ℝ W}
  {I J : Type*} (d : LocalCutData K I) (d' : LocalCutData K' J)

lemma globalComplex_map (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    (hk : ∀ s ∈ K.faces, s.map ⟨f,hf⟩ ∈ K'.faces)
    (e : ∀ s, s ∈ K.faces → d.relevant s ≃ d'.relevant (s.map ⟨f,hf⟩))
    (ha : ∀ s hs i, (d'.form (e s hs i)).comp f = d.form i)
    (hb : ∀ s hs i, d'.level (e s hs i) = d.level i)
    {u : Finset V} (hu : u ∈ d.globalComplex.faces) :
    u.map ⟨f,hf⟩ ∈ d'.globalComplex.faces := by
  obtain ⟨s,hs,hus⟩ := d.globalComplex_carrier hu
  have hlocal : u ∈ (restrictComplex d.globalComplex (convexHull ℝ (s : Set V))).faces :=
    ⟨hu,Subset.trans (subset_convexHull ℝ _) hus⟩
  rw [d.globalComplex_restrict_faces s hs] at hlocal
  have hlocal' := Set.mem_image_of_mem (fun t : Finset V => t.map ⟨f,hf⟩) hlocal
  rw [← canonicalCuts_linear_map K s hs f hf (e s hs)
    (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i)
    (fun j : d'.relevant (s.map ⟨f,hf⟩) => d'.form j)
    (fun j : d'.relevant (s.map ⟨f,hf⟩) => d'.level j) (ha s hs) (hb s hs),
    ← d'.globalComplex_restrict_faces _ (hk s hs)] at hlocal'
  exact hlocal'.1

end LocalCutData

end

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma exists_smallest_carrier (K : Geometry.SimplicialComplex ℝ V) {x : V}
    (hx : x ∈ K.space) :
    ∃ s ∈ K.faces, x ∈ convexHull ℝ (s : Set V) ∧
      ∀ t ∈ K.faces, x ∈ convexHull ℝ (t : Set V) → s ⊆ t := by
  classical
  let P : ℕ → Prop := fun n => ∃ s ∈ K.faces,
    x ∈ convexHull ℝ (s : Set V) ∧ s.card = n
  have hex : ∃ n, P n := by
    obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact ⟨s.card,s,hs,hxs,rfl⟩
  obtain ⟨s,hs,hxs,hcard⟩ := Nat.find_spec hex
  refine ⟨s,hs,hxs,fun t ht hxt => ?_⟩
  have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset V) : Set V) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨hxs,hxt⟩
  have hne : (s ∩ t).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x,hxst⟩)
  have hst := K.down_closed hs Finset.inter_subset_left hne
  have hmin : s.card ≤ (s ∩ t).card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨s ∩ t,hst,hxst,rfl⟩
  have he : s ∩ t = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hmin
  exact he ▸ Finset.inter_subset_right

lemma IsMarked.iInter_space {K : Geometry.SimplicialComplex ℝ V} {I : Sort*}
    {P : I → Set V} (hP : ∀ i, IsMarked K (P i)) :
    IsMarked K (K.space ∩ ⋂ i, P i) := by
  intro x hx
  obtain ⟨s,hs,hxs,hmin⟩ := exists_smallest_carrier K hx.1
  refine ⟨s,hs,hxs,fun y hy => ⟨K.convexHull_subset_space hs hy,?_⟩⟩
  apply Set.mem_iInter.mpr
  intro i
  obtain ⟨t,ht,hxt,htP⟩ := hP i x (Set.mem_iInter.mp hx.2 i)
  exact htP (convexHull_mono (hmin t ht hxt) hy)

namespace LocalCutData

variable {J : Type*} {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)

lemma globalComplex_marked_le (j : J) :
    IsMarked d.globalComplex (K.space ∩ {x | d.form j x ≤ d.level j}) := by
  classical
  intro x hx
  have hxj : d.form j x ≤ d.level j := hx.2
  obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.1
  let e : d.relevant s → Bool := fun i => decide (d.form i x ≤ d.level i)
  have hxc : x ∈ cutCell (convexHull ℝ (s : Set V))
      (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i) e := by
    refine ⟨hxs,fun i => ?_⟩
    simp only [signedForm,signedBound,e,decide_eq_true_eq]
    split_ifs with h
    · exact h
    · exact neg_le_neg (le_of_not_ge h)
  have hm := (d.globalComplex_cut_trace s hs e).isMarked
  obtain ⟨t,ht,hxt,htc⟩ := hm x ⟨d.globalComplex_space.symm ▸ hx.1,hxc⟩
  refine ⟨t,ht,hxt,fun y hy => ⟨d.globalComplex_space ▸
    d.globalComplex.convexHull_subset_space ht hy,?_⟩⟩
  change d.form j y ≤ d.level j
  by_cases hj : j ∈ d.relevant s
  · have he : e ⟨j,hj⟩ = true := by simpa only [e,decide_eq_true_eq] using hxj
    have hh := (htc hy).2.2 ⟨j,hj⟩
    simpa only [signedForm,signedBound,he,ite_true] using hh
  · rw [d.vanish s hs j hj y (htc hy).2.1]
    exact (d.positive j).le

lemma globalComplex_marked_ge (j : J) :
    IsMarked d.globalComplex (K.space ∩ {x | d.level j ≤ d.form j x}) := by
  classical
  intro x hx
  have hxj : d.level j ≤ d.form j x := hx.2
  obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.1
  have hj : j ∈ d.relevant s := by
    by_contra hn
    have hh := d.vanish s hs j hn x hxs
    have := d.positive j
    linarith
  let e : d.relevant s → Bool := fun i => decide (d.form i x < d.level i)
  have hxc : x ∈ cutCell (convexHull ℝ (s : Set V))
      (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i) e := by
    refine ⟨hxs,fun i => ?_⟩
    simp only [signedForm,signedBound,e,decide_eq_true_eq]
    split_ifs with h
    · exact h.le
    · exact neg_le_neg (le_of_not_gt h)
  have hm := (d.globalComplex_cut_trace s hs e).isMarked
  obtain ⟨t,ht,hxt,htc⟩ := hm x ⟨d.globalComplex_space.symm ▸ hx.1,hxc⟩
  refine ⟨t,ht,hxt,fun y hy => ⟨d.globalComplex_space ▸
    d.globalComplex.convexHull_subset_space ht hy,?_⟩⟩
  change d.level j ≤ d.form j y
  have he : e ⟨j,hj⟩ = false := by simp only [e,decide_eq_false_iff_not,not_lt]; exact hxj
  have hh := (htc hy).2.2 ⟨j,hj⟩
  simpa only [signedForm,signedBound,he,Bool.false_eq_true,ite_false,
    LinearMap.neg_apply,neg_le_neg_iff] using hh

lemma globalComplex_marked_eq (j : J) :
    IsMarked d.globalComplex (K.space ∩ {x | d.form j x = d.level j}) := by
  have hh := (d.globalComplex_marked_le j).inter (d.globalComplex_marked_ge j)
  convert hh using 1
  ext x
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨⟨h.1,h.2.le⟩,h.1,h.2.ge⟩,
    fun h => ⟨h.1.1,le_antisymm h.1.2 h.2.2⟩⟩

end LocalCutData

end

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

open scoped Classical

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma coe_filter_mem (s : Finset V) (P : Set V) :
    ((s.filter (· ∈ P) : Finset V) : Set V) = (s : Set V) ∩ P := by
  ext x
  simp

lemma respectsSet_face {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : RespectsSet K P) {s : Finset V} (hs : s ∈ K.faces)
    (hne : (convexHull ℝ (s : Set V) ∩ P).Nonempty) :
    s.filter (· ∈ P) ∈ K.faces := by
  classical
  apply K.down_closed hs (Finset.filter_subset _ _)
  have hh := hP s hs
  rw [hh] at hne
  rw [← coe_filter_mem s P] at hne
  exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hne)

namespace LocalCutData

variable {J : Type*} {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)

lemma globalComplex_carrier_in {P : Set V} (hP : RespectsSet K P)
    {s : Finset V} (hs : s ∈ d.globalComplex.faces) (hsP : (s : Set V) ⊆ P) :
    ∃ t ∈ K.faces, (t : Set V) ⊆ P ∧
      convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
  classical
  obtain ⟨t,ht,hst⟩ := d.globalComplex_carrier hs
  have hv : (s : Set V) ⊆ convexHull ℝ (t : Set V) ∩ P :=
    subset_inter ((subset_convexHull ℝ _).trans hst) hsP
  have hne : (convexHull ℝ (t : Set V) ∩ P).Nonempty :=
    (d.globalComplex.nonempty_of_mem_faces hs).to_set.mono hv
  refine ⟨t.filter (· ∈ P),respectsSet_face hP ht hne,?_,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · apply convexHull_min
    · simpa only [coe_filter_mem] using (hP t ht ▸ hv)
    · exact convex_convexHull ℝ _

lemma globalComplex_preserves_respects {P : Set V} (hP : RespectsSet K P) :
    RespectsSet d.globalComplex P := by
  classical
  intro s hs
  obtain ⟨t,ht,hst⟩ := d.globalComplex_carrier hs
  by_cases hh : (convexHull ℝ (t : Set V) ∩ P).Nonempty
  · let u := t.filter (· ∈ P)
    have hu : u ∈ K.faces := respectsSet_face hP ht hh
    have huet : convexHull ℝ (u : Set V) = convexHull ℝ (t : Set V) ∩ P := by
      simpa only [u,coe_filter_mem] using (hP t ht).symm
    have htrace := d.globalComplex_trace u hu s hs
    have hleft : convexHull ℝ (s : Set V) ∩ convexHull ℝ (u : Set V) =
        convexHull ℝ (s : Set V) ∩ P := by
      rw [huet]
      rw [← Set.inter_assoc,Set.inter_eq_left.mpr hst]
    have hv : (s : Set V) ∩ convexHull ℝ (u : Set V) = (s : Set V) ∩ P := by
      rw [huet]
      have hsub := (subset_convexHull ℝ (s : Set V)).trans hst
      rw [← Set.inter_assoc,Set.inter_eq_left.mpr hsub]
    simpa only [hleft,hv] using htrace
  · have he : convexHull ℝ (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hh ⟨y,hst hy.1,hy.2⟩)
    have hv : (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hh ⟨y,
        hst (subset_convexHull ℝ _ hy.1),hy.2⟩)
    rw [he,hv,convexHull_empty]

end LocalCutData

structure UniversalCuts (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (J : Type*) where
  form : J → V →ₗ[ℝ] ℝ
  level : J → ℝ
  positive : ∀ j, 0 < level j
  relevant : Finset V → Finset J
  vanish : ∀ s j, j ∉ relevant s →
    ∀ x ∈ convexHull ℝ (s : Set V), form j x = 0

namespace UniversalCuts

variable {J : Type*} (d : UniversalCuts V J)

def onComplex (K : Geometry.SimplicialComplex ℝ V) : LocalCutData K J :=
  ⟨d.form,d.level,d.positive,d.relevant,fun s _ => d.vanish s⟩

def localFaces (s : Finset V) : Set (Finset V) :=
  chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)}
    (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i))) canonicalCenter

lemma mem_global_iff {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : RespectsSet K P) (s : Finset V) :
    s ∈ (restrictComplex (d.onComplex K).globalComplex P).faces ↔
      ∃ t ∈ (restrictComplex K P).faces, s ∈ d.localFaces t := by
  constructor
  · intro hs
    obtain ⟨t,ht,htP,hst⟩ := (d.onComplex K).globalComplex_carrier_in hP hs.1 hs.2
    refine ⟨t,⟨ht,htP⟩,?_⟩
    have hh : s ∈ (restrictComplex (d.onComplex K).globalComplex
        (convexHull ℝ (t : Set V))).faces :=
      ⟨hs.1,(subset_convexHull ℝ _).trans hst⟩
    rwa [(d.onComplex K).globalComplex_restrict_faces t ht] at hh
  · rintro ⟨t,⟨ht,htP⟩,hst⟩
    have hh : s ∈ (restrictComplex (d.onComplex K).globalComplex
        (convexHull ℝ (t : Set V))).faces := by
      rw [(d.onComplex K).globalComplex_restrict_faces t ht]
      exact hst
    have htrace := hP t ht
    have htconv : convexHull ℝ (t : Set V) ⊆ P := by
      have he : (t : Set V) ∩ P = t := Set.inter_eq_left.mpr htP
      rw [he] at htrace
      exact Set.inter_eq_left.mp htrace
    exact ⟨hh.1,hh.2.trans htconv⟩

lemma restrict_eq_of_restrict_eq (K L : Geometry.SimplicialComplex ℝ V) (P : Set V)
    (hKP : RespectsSet K P) (hLP : RespectsSet L P)
    (h : (restrictComplex K P).faces = (restrictComplex L P).faces) :
    (restrictComplex (d.onComplex K).globalComplex P).faces =
      (restrictComplex (d.onComplex L).globalComplex P).faces := by
  ext s
  rw [d.mem_global_iff hKP,d.mem_global_iff hLP,h]

end UniversalCuts

end Sparse.Cuts

end BassTrace

end

end OAI
