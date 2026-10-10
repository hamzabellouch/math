import OAI.RingTheory.BassTrace.SimplexCoordinates

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

namespace Sparse

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma measurable_intrinsicInterior_finite_hull [MeasurableSpace V] [BorelSpace V]
    (s : Finset V) : MeasurableSet (intrinsicInterior ℝ (convexHull ℝ (s : Set V))) := by
  have hA : IsClosed ((affineSpan ℝ (convexHull ℝ (s : Set V))) : Set V) := by
    rw [affineSpan_convexHull]
    let := finiteDimensional_direction_affineSpan_of_finite ℝ s.finite_toSet
    exact (affineSpan ℝ (s : Set V)).closed_of_finiteDimensional
  exact (hA.isClosedEmbedding_subtypeVal.measurableEmbedding.measurableSet_image).mpr
    isOpen_interior.measurableSet

end

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

lemma support_of_mem_original_hull (s : Finset Y) {p : Y →₀ ℝ}
    (hp : p∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) : p.support⊆s := by
  have hprob : p∈probabilitySet s := by
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hp
  exact hprob.2.2

lemma simplexCoordinates_full {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Y →₀ ℝ} (hp : p∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    simplexCoordinates s hs p∈fullBarycentricSimplex n := by
  have hprob : p∈probabilitySet s := by
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hp
  exact ⟨fun i => hprob.1 _,simplexCoordinates_sum s hs hp⟩

lemma marked_chart_pieces (Q : OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (d : ℕ) (x : X)
    (hd : ∀ t∈(Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) :
    ∃ (I : Type) (_ : Fintype I) (s : I → Finset (Fin (n+1) → ℝ))
      (A : I → Set (Fin (n+1) → ℝ)),
      (∀ i,(s i).card≤d+1) ∧
      (∀ i p,p∈s i → ∑ v,p v=1) ∧
      (∀ i,MeasurableSet (A i)) ∧
      (∀ i,A i⊆convexHull ℝ (s i : Set (Fin (n+1) → ℝ))) ∧
      (∀ i,A i⊆fullBarycentricSimplex n) ∧
      (⋃ i,A i)=simplexCoordinates σ.val σ.property.2 '' (Q.P.val x∩sourceInterior σ.val) := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  let η := simplexCoordinates σ.val σ.property.2
  let e := simplexEmbed σ.val σ.property.2
  let L := Cuts.restrictComplex (Cuts.geometricRestriction (Q.T.val x).complex (Q.P.val x))
    (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))
  have hf : L.faces.Finite := ((Q.T.val x).finite (simplexVertices σ.val)
    ⟨σ.val,σ.property.1,rfl⟩).subset (fun _ h => ⟨h.1.1,h.2⟩)
  let F := hf.toFinset
  let I := Fin F.card
  let α : I ≃ {t // t∈L.faces} :=
    (F.equivFin).symm.trans (Set.equivOfEq (by ext t; exact hf.mem_toFinset))
  let s (i : I) := (α i).val.image η
  let A (i : I) := convexHull ℝ (s i : Set (Fin (n+1) → ℝ)) ∩ e ⁻¹' sourceInterior σ.val
  have hsource (i : I) : convexHull ℝ ((α i).val : Set (Y →₀ ℝ)) ⊆
      convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)) :=
    convexHull_min (α i).property.2 (convex_convexHull ℝ _)
  have himage (i : I) : convexHull ℝ (s i : Set (Fin (n+1) → ℝ)) =
      η '' convexHull ℝ ((α i).val : Set (Y →₀ ℝ)) := by
    change convexHull ℝ (((α i).val.image η : Finset (Fin (n+1) → ℝ)) : Set (Fin (n+1) → ℝ)) = _
    rw [Finset.coe_image,← η.image_convexHull]
  have hin (i : I) {p : Fin (n+1) → ℝ}
      (hp : p∈convexHull ℝ (s i : Set (Fin (n+1) → ℝ))) :
      e p∈convexHull ℝ ((α i).val : Set (Y →₀ ℝ)) := by
    rw [himage i] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    change simplexEmbed σ.val σ.property.2 (simplexCoordinates σ.val σ.property.2 q)∈_
    rw [simplexEmbed_coordinates _ _ (support_of_mem_original_hull _ (hsource i hq))]
    exact hq
  refine ⟨I,inferInstance,s,A,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact Finset.card_image_le.trans (hd _ (α i).property.1.1 (α i).property.1.2)
  · intro i p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact simplexCoordinates_sum _ _ ((α i).property.2 hq)
  · intro i
    exact ((s i).finite_toSet.isCompact_convexHull ℝ).isClosed.measurableSet.inter
      ((measurable_intrinsicInterior_finite_hull (simplexVertices σ.val)).preimage
        e.continuous_of_finiteDimensional.measurable)
  · exact fun _ => Set.inter_subset_left
  · intro i p hp
    have hp' := hp.1
    rw [himage i] at hp'
    obtain ⟨q,hq,rfl⟩ := hp'
    exact simplexCoordinates_full _ _ (hsource i hq)
  · apply Set.Subset.antisymm
    · intro p hp
      obtain ⟨i,hp⟩ := Set.mem_iUnion.mp hp
      refine ⟨e p,⟨(α i).property.1.2 (hin i hp.1),hp.2⟩,?_⟩
      exact simplexCoordinates_embed _ _ p
    · rintro _ ⟨p,hp,rfl⟩
      have hpL : p∈L.space := by
        change p∈(Cuts.restrictComplex (Cuts.geometricRestriction (Q.T.val x).complex (Q.P.val x))
          (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).space
        rw [Q.P.trace_space (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩ x]
        exact ⟨hp.1,intrinsicInterior_subset hp.2⟩
      obtain ⟨t,ht,hpt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hpL
      obtain ⟨i,hi⟩ := α.surjective ⟨t,ht⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i,?_,?_⟩
      · rw [himage i,hi]
        exact ⟨p,hpt,rfl⟩
      · change simplexEmbed σ.val σ.property.2 (simplexCoordinates σ.val σ.property.2 p)∈sourceInterior σ.val
        rw [simplexEmbed_coordinates _ _ (support_of_mem_sourceInterior _ hp.2)]
        exact hp.2

end

open Set MeasureTheory

open scoped ENNReal

lemma IsLocallyConstant.measurable_uncurry {X A Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] {f : X → A} (hf : IsLocallyConstant f)
    (F : A → Y → ℝ≥0∞) (hF : ∀ a∈Set.range f,Measurable (F a)) :
    Measurable (fun p : X×Y => F (f p.1) p.2) := by
  classical
  let S := hf.range_finite.toFinset
  have he : (fun p : X×Y => F (f p.1) p.2) =
      fun p => ∑ a∈S, ({q : X×Y | f q.1=a}.indicator (fun q=>F a q.2)) p := by
    funext p
    rw [Finset.sum_eq_single (f p.1)]
    · simp
    · intro a _ ha
      exact Set.indicator_of_notMem (by exact Ne.symm ha) _
    · intro h
      exact (h (hf.range_finite.mem_toFinset.mpr (Set.mem_range_self _))).elim
  rw [he]
  apply Finset.measurable_sum
  intro a ha
  apply ((hF a (hf.range_finite.mem_toFinset.mp ha)).comp measurable_snd).indicator
  exact ((hf.isClopen_fiber a).isOpen.measurableSet.preimage measurable_fst)

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

omit [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X] in
lemma chartDistance_coordinates (σ : SourceTop K n) (c : FinProbability Y)
    {p : Y →₀ ℝ} (hp : p∈sourceInterior σ.val) :
    letI := graphMetric Γ hΓ
    chartDistance σ.val σ.property.2 c (simplexCoordinates σ.val σ.property.2 p) =
      centerDistance Γ hΓ K n c p := by
  let := graphMetric Γ hΓ
  have hpK : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨simplexVertices σ.val,⟨σ.val,σ.property.1,rfl⟩,intrinsicInterior_subset hp⟩
  rw [chartDistance_apply _ _ _ _ (simplexCoordinates_full _ _ (intrinsicInterior_subset hp))]
  simp only [centerDistance,dite_eq_left hpK]
  congr 1
  apply FinProbability.ext_coeff
  change simplexEmbed σ.val σ.property.2 (simplexCoordinates σ.val σ.property.2 p) = _
  rw [simplexEmbed_coordinates _ _ (support_of_mem_sourceInterior _ hp),pointProbability_coeff]

omit [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X] in
lemma coordinates_radius_inter (σ : SourceTop K n) (c : FinProbability Y)
    (A : Set (Y →₀ ℝ)) (hA : A⊆sourceInterior σ.val) (R : Set ℝ) :
    letI := graphMetric Γ hΓ
    simplexCoordinates σ.val σ.property.2 '' (A∩(centerDistance Γ hΓ K n c ⁻¹' R)) =
    (simplexCoordinates σ.val σ.property.2 '' A) ∩
      (chartDistance σ.val σ.property.2 c ⁻¹' R) := by
  let := graphMetric Γ hΓ
  ext p
  constructor
  · rintro ⟨q,⟨hq,hqR⟩,rfl⟩
    refine ⟨⟨q,hq,rfl⟩,?_⟩
    simpa only [Set.mem_preimage,chartDistance_coordinates Γ hΓ σ c (hA hq)] using hqR
  · rintro ⟨⟨q,hq,rfl⟩,hpR⟩
    refine ⟨q,⟨hq,?_⟩,rfl⟩
    simpa only [Set.mem_preimage,chartDistance_coordinates Γ hΓ σ c (hA hq)] using hpR

theorem marked_ball_coarea (hn : 0<n)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (c : FinProbability Y) (d : ℕ) (hdn : d≤n) (x : X)
    (hd : ∀ t∈(Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) (r b : ℝ) :
    (∫⁻ t in Ioo r b,localOriginalArea Γ Q σ (d-1)
      {v | centerDistance Γ hΓ K n c v=t} x) ≤
      localOriginalArea Γ Q σ d {v | centerDistance Γ hΓ K n c v≤b} x := by
  let := graphMetric Γ hΓ
  obtain ⟨I,hI,s,A,hs,hplane,hA,hAs,hfull,he⟩ := marked_chart_pieces Q σ d x hd
  let : Fintype I := hI
  have hgraph (u v : Fin (n+1)) (huv : (simplexGraph Γ σ.val σ.property.2).Adj u v) :
      dist (simplexEnumeration σ.val σ.property.2 u).val
        (simplexEnumeration σ.val σ.property.2 v).val≤1 := by
    change (Γ.dist _ _ : ℝ)≤1
    exact_mod_cast (SimpleGraph.dist_eq_one_iff_adj.mpr (show Γ.Adj _ _ from huv)).le
  have hc := graphBall_coarea hn σ.val σ.property.2 c
    (simplexGraph Γ σ.val σ.property.2) hgraph s d hs hdn hplane A hA hAs hfull r b
  rw [he] at hc
  convert hc using 1
  · congr 1
    funext t
    unfold localOriginalArea
    congr 1
    simpa only [Set.inter_assoc, Set.preimage, Set.mem_singleton_iff] using
      coordinates_radius_inter Γ hΓ σ c (Q.P.val x∩sourceInterior σ.val)
        Set.inter_subset_right {t}
  · unfold localOriginalArea
    congr 1
    simpa only [Set.inter_assoc, Set.preimage, Set.mem_Iic] using
      coordinates_radius_inter Γ hΓ σ c (Q.P.val x∩sourceInterior σ.val)
        Set.inter_subset_right (Iic b)

lemma measurable_marked_ball_slices
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (c : FinProbability Y) (d : ℕ) (hdn : d≤n) (x : X)
    (hd : ∀ t∈(Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) :
    Measurable (fun t => localOriginalArea Γ Q σ (d-1)
      {v | centerDistance Γ hΓ K n c v=t} x) := by
  let := graphMetric Γ hΓ
  obtain ⟨I,hI,s,A,hs,hplane,hA,hAs,hfull,he⟩ := marked_chart_pieces Q σ d x hd
  let : Fintype I := hI
  have hc := measurable_graphBall_slices σ.val σ.property.2 c
    (simplexGraph Γ σ.val σ.property.2) s d hs hdn hplane A hA hAs hfull
  rw [he] at hc
  convert hc using 1
  funext t
  unfold localOriginalArea
  congr 1
  simpa only [Set.inter_assoc, Set.preimage, Set.mem_singleton_iff] using
    coordinates_radius_inter Γ hΓ σ c (Q.P.val x∩sourceInterior σ.val)
      Set.inter_subset_right {t}

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

lemma measurable_marked_ball_slices_joint
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (c : FinProbability Y) (d : ℕ) (hdn : d≤n)
    (hd : ∀ x t,t∈(Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) :
    Measurable (fun p : X×ℝ => localOriginalArea Γ Q σ (d-1)
      {v | centerDistance Γ hΓ K n c v=p.2} p.1) := by
  let f (x : X) := Q.P.val x∩sourceInterior σ.val
  have hf : IsLocallyConstant f := Q.P.localConstancy_inter (simplexVertices σ.val)
    ⟨σ.val,σ.property.1,rfl⟩ _ intrinsicInterior_subset
  let F (A : Set (Y →₀ ℝ)) (t : ℝ) := simplexArea (simplexGraph Γ σ.val σ.property.2)
    (d-1) (simplexCoordinates σ.val σ.property.2 ''
      (A ∩ {v | centerDistance Γ hΓ K n c v=t}))
  have hF : ∀ A∈Set.range f,Measurable (F A) := by
    rintro A ⟨x,rfl⟩
    simpa only [F,f,Set.inter_assoc,localOriginalArea] using
      measurable_marked_ball_slices Γ hΓ Q σ c d hdn x (hd x)
  simpa only [F,f,Set.inter_assoc,localOriginalArea] using BassTrace.Sparse.IsLocallyConstant.measurable_uncurry hf F hF

theorem integrated_marked_ball_coarea [Countable Y]
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) [SFinite μ] (B : Set X) (c : FinProbability Y)
    (hn : 0<n) (d : ℕ) (hdn : d≤n)
    (hd : ∀ x t,t∈(Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) (r b : ℝ) :
    (∫⁻ t in Ioo r b, ∫⁻ x in B, ∑' σ : SourceTop K n,
      localOriginalArea Γ Q σ (d-1) {v | centerDistance Γ hΓ K n c v=t} x ∂μ) ≤
      ∫⁻ x in B, ∑' σ : SourceTop K n,
        localOriginalArea Γ Q σ d {v | centerDistance Γ hΓ K n c v≤b} x ∂μ := by
  let : Countable (SourceTop K n) :=
    inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
  have hm (σ : SourceTop K n) := measurable_marked_ball_slices_joint Γ hΓ Q σ c d hdn hd
  rw [← lintegral_lintegral_swap ((Measurable.tsum hm).aemeasurable)]
  apply lintegral_mono
  intro x
  dsimp only
  rw [lintegral_tsum (fun σ => (measurable_marked_ball_slices Γ hΓ Q σ c d hdn x (hd x)).aemeasurable)]
  exact ENNReal.tsum_le_tsum (fun σ => marked_ball_coarea Γ hΓ hn Q σ c d hdn x (hd x) r b)

end Sparse.GraphGeometry

end BassTrace

end

end OAI
