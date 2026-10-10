import OAI.RingTheory.BassTrace.GeometricSubcomplexes

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

open Set Finset

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

structure Subdivision (K : Geometry.SimplicialComplex ℝ V) where
  complex : Geometry.SimplicialComplex ℝ V
  space_eq : complex.space = K.space
  carrier : ∀ s ∈ complex.faces, ∃ t ∈ K.faces,
    convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V)
  respects : ∀ s ∈ K.faces, RespectsSet complex (convexHull ℝ (s : Set V))
  finite : ∀ s ∈ K.faces,
    (restrictComplex complex (convexHull ℝ (s : Set V))).faces.Finite

lemma complex_respects_simplex (K : Geometry.SimplicialComplex ℝ V)
    {t : Finset V} (ht : t ∈ K.faces) : RespectsSet K (convexHull ℝ (t : Set V)) := by
  intro s hs
  have hv : (s : Set V) ∩ convexHull ℝ (t : Set V) = (s : Set V) ∩ t := by
    ext x
    constructor
    · rintro ⟨hx,hxt⟩
      have hxv : x ∈ K.vertices := K.down_closed hs (Finset.singleton_subset_iff.mpr hx)
        (Finset.singleton_nonempty _)
      exact ⟨hx,(K.vertex_mem_convexHull_iff hxv ht).mp hxt⟩
    · rintro ⟨hx,hxt⟩
      exact ⟨hx,subset_convexHull ℝ _ hxt⟩
  rw [hv,K.convexHull_inter_convexHull hs ht]

lemma complex_restrict_finite (K : Geometry.SimplicialComplex ℝ V)
    {t : Finset V} (ht : t ∈ K.faces) :
    (restrictComplex K (convexHull ℝ (t : Set V))).faces.Finite := by
  classical
  apply (t.powerset.finite_toSet).subset
  intro s hs
  apply Finset.mem_powerset.mpr
  apply (K.face_subset_face_iff hs.1 ht).mp
  exact convexHull_min hs.2 (convex_convexHull ℝ _)

namespace Subdivision

variable {K : Geometry.SimplicialComplex ℝ V}

def original (K : Geometry.SimplicialComplex ℝ V) : Subdivision K where
  complex := K
  space_eq := rfl
  carrier := fun s hs => ⟨s,hs,subset_rfl⟩
  respects := fun _ hs => complex_respects_simplex K hs
  finite := fun _ hs => complex_restrict_finite K hs

lemma marked (T : Subdivision K) {s : Finset V} (hs : s ∈ K.faces) :
    IsMarked T.complex (convexHull ℝ (s : Set V)) := by
  classical
  intro x hx
  have hxsp : x ∈ T.complex.space := T.space_eq.symm ▸ K.convexHull_subset_space hs hx
  obtain ⟨t,ht,hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hxsp
  have he := T.respects s hs t ht
  have hxs : x ∈ convexHull ℝ ((t : Set V) ∩ convexHull ℝ (s : Set V)) := by
    rw [← he]
    exact ⟨hxt,hx⟩
  let u := t.filter (· ∈ convexHull ℝ (s : Set V))
  have hu : u ∈ T.complex.faces := respectsSet_face (T.respects s hs) ht ⟨x,hxt,hx⟩
  refine ⟨u,hu,?_,?_⟩
  · simpa only [u,coe_filter_mem] using hxs
  · apply convexHull_min
    · intro y hy
      exact (Finset.mem_filter.mp hy).2
    · exact convex_convexHull ℝ _

end Subdivision

namespace UniversalCuts

variable {J : Type*} (d : UniversalCuts V J)

lemma localFaces_finite (s : Finset V) : (d.localFaces s).Finite :=
  chainFaces_finite _ _

lemma restrict_finite {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : RespectsSet K P) (hf : (restrictComplex K P).faces.Finite) :
    (restrictComplex (d.onComplex K).globalComplex P).faces.Finite := by
  have he : (restrictComplex (d.onComplex K).globalComplex P).faces =
      ⋃ t ∈ (restrictComplex K P).faces, d.localFaces t := by
    ext s
    simp only [d.mem_global_iff hP,Set.mem_iUnion,exists_prop]
  rw [he]
  exact hf.biUnion (fun t _ => d.localFaces_finite t)

def refine {K : Geometry.SimplicialComplex ℝ V} (T : Subdivision K) : Subdivision K where
  complex := (d.onComplex T.complex).globalComplex
  space_eq := (d.onComplex T.complex).globalComplex_space.trans T.space_eq
  carrier := by
    intro s hs
    obtain ⟨t,ht,hst⟩ := (d.onComplex T.complex).globalComplex_carrier hs
    obtain ⟨u,hu,htu⟩ := T.carrier t ht
    exact ⟨u,hu,hst.trans htu⟩
  respects := fun s hs => (d.onComplex T.complex).globalComplex_preserves_respects (T.respects s hs)
  finite := fun s hs => d.restrict_finite (T.respects s hs) (T.finite s hs)

lemma refine_preserves_marked {K : Geometry.SimplicialComplex ℝ V} (T : Subdivision K)
    {P : Set V} (hP : IsMarked T.complex P) : IsMarked (d.refine T).complex P :=
  (d.onComplex T.complex).globalComplex_preserves_marked hP

end UniversalCuts

structure SubdivisionFamily (X : Type*) [TopologicalSpace X]
    (K : Geometry.SimplicialComplex ℝ V) where
  val : X → Subdivision K
  localConstancy : ∀ s ∈ K.faces, IsLocallyConstant
    (fun x => (restrictComplex (val x).complex (convexHull ℝ (s : Set V))).faces)

namespace UniversalCuts

variable {J X : Type*} [TopologicalSpace X] (d : UniversalCuts V J)

def refineFamily {K : Geometry.SimplicialComplex ℝ V} (T : SubdivisionFamily X K) :
    SubdivisionFamily X K where
  val := fun x => d.refine (T.val x)
  localConstancy := by
    intro s hs
    let F : Set (Finset V) → Set (Finset V) := fun A => ⋃ t ∈ A, d.localFaces t
    have he (x : X) : (restrictComplex (d.refine (T.val x)).complex
        (convexHull ℝ (s : Set V))).faces = F
        ((restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces) := by
      ext u
      simp only [refine,mem_global_iff d ((T.val x).respects s hs),F,Set.mem_iUnion,exists_prop]
    simp_rw [he]
    exact (T.localConstancy s hs).comp F

end UniversalCuts

end

section

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] [CompactSpace X]

variable {K : Geometry.SimplicialComplex ℝ V}

namespace SubdivisionFamily

lemma finite_faces_on (T : SubdivisionFamily X K) (s : Finset V) (hs : s ∈ K.faces) :
    (⋃ x, (restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces).Finite := by
  let f := fun x => (restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces
  have hf : (Set.range f).Finite := (T.localConstancy s hs).range_finite
  have hh : (⋃ F ∈ Set.range f, F).Finite := hf.biUnion (by
    rintro F ⟨x,rfl⟩
    exact (T.val x).finite s hs)
  apply hh.subset
  intro u hu
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hu
  exact Set.mem_iUnion₂.mpr ⟨f x,⟨x,rfl⟩,hx⟩

lemma countable_faces (T : SubdivisionFamily X K) (hK : K.faces.Countable) :
    (⋃ x, (T.val x).complex.faces).Countable := by
  have hh : (⋃ s ∈ K.faces, ⋃ x,
      (restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces).Countable :=
    hK.biUnion (fun s hs => (T.finite_faces_on s hs).countable)
  apply hh.mono
  intro u hu
  obtain ⟨x,hxu⟩ := Set.mem_iUnion.mp hu
  obtain ⟨s,hs,hus⟩ := (T.val x).carrier u hxu
  exact Set.mem_iUnion₂.mpr ⟨s,hs,Set.mem_iUnion.mpr
    ⟨x,hxu,(subset_convexHull ℝ _).trans hus⟩⟩

lemma countable_vertices (T : SubdivisionFamily X K) (hK : K.faces.Countable) :
    (⋃ x, (T.val x).complex.vertices).Countable := by
  have hh : (⋃ s ∈ (⋃ x, (T.val x).complex.faces), (s : Set V)).Countable :=
    (T.countable_faces hK).biUnion (fun s _ => s.countable_toSet)
  apply hh.mono
  intro y hy
  obtain ⟨x,hxy⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion₂.mpr ⟨{y},Set.mem_iUnion.mpr ⟨x,hxy⟩,by simp⟩

lemma exists_generic_level (T : SubdivisionFamily X K) (hK : K.faces.Countable)
    {J : Type*} [Countable J] (a : J → V → ℝ) {r R : ℝ} (hr : r < R) :
    ∃ t ∈ Set.Ioo r R, ∀ x s, s ∈ (T.val x).complex.faces →
      ∀ j y, y ∈ s → a j y ≠ t := by
  let bad : Set ℝ := ⋃ j, a j '' (⋃ x, (T.val x).complex.vertices)
  have hb : bad.Countable := Set.countable_iUnion fun j => (T.countable_vertices hK).image (a j)
  obtain ⟨t,hnt,ht⟩ := hb.dense_compl ℝ |>.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hr)
  refine ⟨t,ht,?_⟩
  intro x s hs j y hy he
  apply hnt
  apply Set.mem_iUnion.mpr
  refine ⟨j,y,Set.mem_iUnion.mpr ⟨x,?_⟩,he⟩
  exact (T.val x).complex.down_closed hs (Finset.singleton_subset_iff.mpr hy)
    (Finset.singleton_nonempty _)

end SubdivisionFamily

end

section

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X]

variable {K : Geometry.SimplicialComplex ℝ V}

def Refines (L K : Geometry.SimplicialComplex ℝ V) : Prop :=
  ∃ S : Subdivision K, S.complex = L

lemma refines_self (K : Geometry.SimplicialComplex ℝ V) : Refines K K :=
  ⟨Subdivision.original K,rfl⟩

lemma UniversalCuts.refine_refines {J : Type*} (d : UniversalCuts V J)
    (T : Subdivision K) : Refines (d.refine T).complex T.complex := by
  exact ⟨d.refine (Subdivision.original T.complex),rfl⟩

structure MarkedFamily (T : SubdivisionFamily X K) where
  val : X → Set V
  marked : ∀ x, IsMarked (T.val x).complex (val x)
  localConstancy : ∀ s ∈ K.faces, IsLocallyConstant (fun x =>
    (restrictComplex (geometricRestriction (T.val x).complex (val x))
      (convexHull ℝ (s : Set V))).faces)

def ComponentDiameter (ρ : V → V → ℝ) (P : Set V) (R : ℝ) : Prop :=
  ∀ C : Set V, IsPreconnected C → C ⊆ P →
    ∀ p ∈ C, ∀ q ∈ C, ρ p q ≤ R

def DimensionDrop (T S : Geometry.SimplicialComplex ℝ V) (P Z : Set V) : Prop :=
  ∀ F ∈ T.faces, convexHull ℝ (F : Set V) ⊆ P →
    ∀ E ∈ S.faces, convexHull ℝ (E : Set V) ⊆ convexHull ℝ (F : Set V) ∩ Z →
      E.card < F.card

structure AdmissibleStep (ρ : V → V → ℝ) (R : ℝ)
    (T : SubdivisionFamily X K) (P : MarkedFamily T) where
  next : SubdivisionFamily X K
  finer : ∀ x, Refines (next.val x).complex (T.val x).complex
  oldMarked : ∀ x, IsMarked (next.val x).complex (P.val x)
  zero : MarkedFamily next
  subset : ∀ x, zero.val x ⊆ P.val x
  dimensionDrop : ∀ x, DimensionDrop (T.val x).complex (next.val x).complex (P.val x) (zero.val x)
  diameter : ∀ x, ComponentDiameter ρ (P.val x \ zero.val x) (2*R)

lemma DimensionDrop.avoids_vertices {T S : Geometry.SimplicialComplex ℝ V}
    {P Z : Set V} (h : DimensionDrop T S P Z) (hR : Refines S T)
    {v : V} (hvT : v ∈ T.vertices) (hvP : v ∈ P) : v ∉ Z := by
  classical
  intro hvZ
  obtain ⟨W,rfl⟩ := hR
  have hm := W.marked hvT
  have hvh : v ∈ convexHull ℝ (({v} : Finset V) : Set V) := by simp
  obtain ⟨E,hE,_,hEv⟩ := hm v hvh
  have hsingle : convexHull ℝ (({v} : Finset V) : Set V) = {v} := by simp
  have hb := h {v} hvT (by simpa only [hsingle,Set.singleton_subset_iff] using hvP)
    E hE (Set.subset_inter hEv (hEv.trans (by
      simpa only [hsingle,Set.singleton_subset_iff] using hvZ)))
  have hp := W.complex.nonempty_of_mem_faces hE |>.card_pos
  simp only [Finset.card_singleton] at hb
  omega

end

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Subdivision

variable {K : Geometry.SimplicialComplex ℝ V} (S : Subdivision K)

lemma preserves_marked {P : Set V} (hP : IsMarked K P) : IsMarked S.complex P :=
  hP.refinement (fun _ hs => S.marked hs)

lemma carrier_in {P : Set V} (hP : RespectsSet K P) {s : Finset V}
    (hs : s ∈ S.complex.faces) (hsp : (s : Set V) ⊆ P) :
    ∃ t ∈ K.faces, (t : Set V) ⊆ P ∧ convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
  classical
  obtain ⟨t,ht,hst⟩ := S.carrier s hs
  have hv := Set.subset_inter ((subset_convexHull ℝ _).trans hst) hsp
  have hne := (S.complex.nonempty_of_mem_faces hs).to_set.mono hv
  refine ⟨t.filter (· ∈ P),respectsSet_face hP ht hne,?_,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · apply convexHull_min _ (convex_convexHull ℝ _)
    simpa only [coe_filter_mem] using (hP t ht ▸ hv)

lemma preserves_respects {P : Set V} (hP : RespectsSet K P) : RespectsSet S.complex P := by
  classical
  intro s hs
  obtain ⟨t,ht,hst⟩ := S.carrier s hs
  by_cases hh : (convexHull ℝ (t : Set V) ∩ P).Nonempty
  · let u := t.filter (· ∈ P)
    have hu : u ∈ K.faces := respectsSet_face hP ht hh
    have he : convexHull ℝ (u : Set V) = convexHull ℝ (t : Set V) ∩ P := by
      simpa only [u,coe_filter_mem] using (hP t ht).symm
    have htrace := S.respects u hu s hs
    have hc : convexHull ℝ (s : Set V) ∩ convexHull ℝ (u : Set V) =
        convexHull ℝ (s : Set V) ∩ P := by
      rw [he,← Set.inter_assoc,Set.inter_eq_left.mpr hst]
    have hv : (s : Set V) ∩ convexHull ℝ (u : Set V) = (s : Set V) ∩ P := by
      rw [he,← Set.inter_assoc,Set.inter_eq_left.mpr ((subset_convexHull ℝ _).trans hst)]
    simpa only [hc,hv] using htrace
  · have hc : convexHull ℝ (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hh ⟨x,hst hx.1,hx.2⟩)
    have hv : (s : Set V) ∩ P = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun x hx => hh ⟨x,hst (subset_convexHull ℝ _ hx.1),hx.2⟩)
    rw [hc,hv,convexHull_empty]

lemma finite_on_respected {P : Set V} (hP : RespectsSet K P)
    (hf : (restrictComplex K P).faces.Finite) : (restrictComplex S.complex P).faces.Finite := by
  have hh : (⋃ t ∈ (restrictComplex K P).faces,
      (restrictComplex S.complex (convexHull ℝ (t : Set V))).faces).Finite :=
    hf.biUnion (fun t ht => S.finite t ht.1)
  apply hh.subset
  intro s hs
  obtain ⟨t,ht,htP,hst⟩ := S.carrier_in hP hs.1 hs.2
  exact Set.mem_iUnion₂.mpr ⟨t,⟨ht,htP⟩,hs.1,(subset_convexHull ℝ _).trans hst⟩

def trans {L : Geometry.SimplicialComplex ℝ V} (T : Subdivision L)
    (h : T.complex = K) : Subdivision L where
  complex := S.complex
  space_eq := S.space_eq.trans (h ▸ T.space_eq)
  carrier := by
    intro s hs
    obtain ⟨t,ht,hst⟩ := S.carrier s hs
    obtain ⟨u,hu,htu⟩ := T.carrier t (h.symm ▸ ht)
    exact ⟨u,hu,hst.trans htu⟩
  respects := fun s hs => S.preserves_respects (h ▸ T.respects s hs)
  finite := fun s hs => S.finite_on_respected (h ▸ T.respects s hs) (h ▸ T.finite s hs)

end Subdivision

lemma Refines.trans {K L M : Geometry.SimplicialComplex ℝ V}
    (hML : Refines M L) (hLK : Refines L K) : Refines M K := by
  obtain ⟨S,rfl⟩ := hML
  obtain ⟨T,hT⟩ := hLK
  exact ⟨S.trans T hT,rfl⟩

lemma Refines.preserves_marked {K L : Geometry.SimplicialComplex ℝ V}
    (h : Refines L K) {P : Set V} (hP : IsMarked K P) : IsMarked L P := by
  obtain ⟨S,rfl⟩ := h
  exact S.preserves_marked hP

end BassTrace.Sparse.Cuts

end

end OAI
