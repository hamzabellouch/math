import OAI.RingTheory.BassTrace.BarycentricBounds

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

lemma sparseChainFamily_bound (x : X) (v : Fin (n+1) → Y)
    (hs : Finset.univ.image v∈K.faces) (hv : Function.Injective v)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (M : ℝ) (hM0 : 0≤M)
    (hM : ∀w : Fin (n+1) → Y,(∀i,w i∈GraphGeometry.labelWindow Γ n R (Finset.univ.image v))→
      ‖ψ (wedge (n+1) w)‖≤M) :
    ‖ψ (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (n+1) (wedge (n+1) v))‖≤
      M*(2^n : ℕ)*(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)))).toReal := by
  let s := Finset.univ.image v
  let L := localTriangulation ((Q.pair 0).T.val x) s
  have hfin : L.faces.Finite := localTriangulation_finite ((Q.pair 0).T.val x) s hs
  have hLT : L.faces⊆((Q.point x).T 0).faces := fun _ h=>h.1
  have hd : ∀s∈K.faces,s.card≤n+1 := by
    intro s hs
    obtain ⟨t,_,hst,hc,_⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hc
  have hdim : ∀s∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces,s.card≤n+1 := by
    rintro _ ⟨s,hs,rfl⟩
    exact Finset.card_image_le.trans (hd s hs)
  have hLspace := localTriangulation_space ((Q.pair 0).T.val x) s hs
  have hsc : s.card=n+1 := by rw [Finset.card_image_of_injective _ hv,Finset.card_univ,Fintype.card_fin]
  have hzero := zero_inter_simplex_finite Q hd ⟨s,hs,hsc⟩ x
  have hbound := labeled_chain_bound (Q.point x) hdim L hfin hLT
    (faceWeight Γ hΓ Q hK hn hR y₀ x) (fun s hs t ht hts he=>by
      rw [ActualFlags.level_face (Q.point x) t (hLT ht),
        ActualFlags.level_face (Q.point x) s (hLT hs)] at he
      exact faceWeight_nested_equal_level Γ hΓ Q hK hn hR y₀ x
        ⟨t,hLT ht⟩ ⟨s,hLT hs⟩ hts he)
    (GraphGeometry.labelWindow Γ n R s) (fun F hF=>by
      refine ⟨componentVertices Γ hΓ Q hK hn hR x ⟨F,hLT hF⟩,
        componentVertices_nonempty Γ hΓ Q hK hn hR x _,?_,?_⟩
      · intro y hy
        exact componentSupport_subset Γ hΓ Q hK hn hR x ⟨F,hLT hF⟩ s
          ((convexHull_min hF.2 (convex_convexHull ℝ _))
            (Cuts.vertexMean_mem_convexHull (L.nonempty_of_mem_faces hF)))
          ((mem_componentVertices Γ hΓ Q hK hn hR x _ y).mp hy)
      · exact faceWeight_face Γ hΓ Q hK hn hR y₀ x ⟨F,hLT hF⟩)
    (chart v) ψ M hM0 hM
  change ‖ψ (labelMap _ (n+1) (subdivision _ (n+1) (wedge (n+1) v)))‖≤_
  rw [subdivision_wedge_succ,tupleSubdivision,dite_eq_left hs]
  apply hbound.trans
  rw [Nat.cast_mul,←mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (ActualFlags.zeroFaces_real_le_count (Q.point x) L hfin hLT _ hLspace.subset hzero)
    (mul_nonneg hM0 (Nat.cast_nonneg _))

end

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

variable (μ : Measure X) [IsProbabilityMeasure μ]

local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

lemma averagedSparseChain_bound (v : Fin (n+1) → Y)
    (hs : Finset.univ.image v∈K.faces) (hv : Function.Injective v)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (M : ℝ) (hM0 : 0≤M)
    (hM : ∀w : Fin (n+1) → Y,(∀i,w i∈GraphGeometry.labelWindow Γ n R (Finset.univ.image v))→
      ‖ψ (wedge (n+1) w)‖≤M) :
    ‖ψ (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (n+1) (wedge (n+1) v))‖≤
      M*(2^n : ℕ)*(∫x,(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)))).toReal ∂μ) := by
  unfold averagedSparseChain
  rw [FiniteAverage.locallyConstantLinearMap_post]
  apply (FiniteAverage.norm_average_le_integral_norm μ _).trans
  have hZ : IsLocallyConstant (fun x=>(Measure.count ((Q.pair 0).P.val x∩
      convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)))).toReal) :=
    ((Q.pair 0).P.localConstancy_inter (simplexVertices (Finset.univ.image v))
      ⟨_,hs,rfl⟩ _ subset_rfl).comp (fun A=>(Measure.count A).toReal)
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono
  · exact SimpleFunc.integrable_of_isFiniteMeasure _ |>.norm
  · exact (FiniteAverage.ofLocallyConstant _ hZ).integrable_of_isFiniteMeasure.const_mul _
  · intro x
    exact sparseChainFamily_bound Γ hΓ Q hK hn hR y₀ x v hs hv ψ M hM0 hM

end BassTrace.Sparse

namespace BassTrace.BarycentricChains

open Set Finset

open scoped Classical

open Oriented ChainHomotopy

lemma finite_norm_bound {I : Type*} [Finite I] (f : I → ℂ) :
    ∃M : ℝ,0≤M ∧ ∀i,‖f i‖≤M := by
  let _ := Fintype.ofFinite I
  refine ⟨∑i,‖f i‖,Finset.sum_nonneg (fun _ _=>norm_nonneg _),?_⟩
  intro i
  exact Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ i)

lemma exists_finite_wedge_bound {Y : Type*} (k : ℕ) (W : Finset Y)
    (ψ : Degree Y k →ₗ[ℂ] ℂ) :
    ∃M : ℝ,0≤M ∧ ∀v : Fin k → Y,(∀i,v i∈W)→‖ψ (wedge k v)‖≤M := by
  let f : (Fin k → {y // y∈W}) → ℂ := fun v=>ψ (wedge k (fun i=>(v i).val))
  obtain ⟨M,hM,h⟩ := finite_norm_bound f
  refine ⟨M,hM,?_⟩
  intro v hv
  exact h (fun i=>⟨v i,hv i⟩)

end BassTrace.BarycentricChains

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains GraphGeometry

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

variable (μ : Measure X) [IsProbabilityMeasure μ]

local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩

lemma exists_chain_bound (C : SourceTop K n → ℝ) (hC : ∀σ,0≤C σ)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (c : Degree Y (n+1))
    (hc : c∈(augmentedComplex K).chains (n+1)) :
    ∃B : ℝ,0≤B ∧ ∀ε : ℝ,0<ε →
      ∀Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) R n,
      (∀σ : SourceTop K n,(∫x,(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε) →
      ‖ψ (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (n+1) c)‖≤B*ε := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,hv,rfl⟩ := hc
    by_cases hinj : Function.Injective v
    · have hs : Finset.univ.image v∈K.faces := by
        rcases hv with hv|hv
        · exact False.elim ((Finset.image_nonempty.mpr Finset.univ_nonempty).ne_empty hv)
        · exact hv
      have hsc : (Finset.univ.image v).card=n+1 := by
        rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
      let σ : SourceTop K n := ⟨Finset.univ.image v,hs,hsc⟩
      obtain ⟨M,hM0,hM⟩ := exists_finite_wedge_bound (n+1) (labelWindow Γ n R σ.val) ψ
      refine ⟨M*(2^n : ℕ)*C σ,mul_nonneg (mul_nonneg hM0 (Nat.cast_nonneg _)) (hC σ),?_⟩
      intro ε _ Q hQ
      apply (averagedSparseChain_bound Γ hΓ Q hK hn hR y₀ μ v hs hinj ψ M hM0 hM).trans
      calc
        _ ≤ M*(2^n : ℕ)*(C σ*ε) := mul_le_mul_of_nonneg_left (hQ σ)
          (mul_nonneg hM0 (Nat.cast_nonneg _))
        _ = _ := by ring
    · refine ⟨0,le_rfl,?_⟩
      intro ε _ Q _
      rw [wedge_eq_zero_of_not_injective _ hinj,map_zero,map_zero,norm_zero,zero_mul]
  | zero =>
    refine ⟨0,le_rfl,?_⟩
    intro ε _ Q _
    simp only [map_zero,norm_zero,zero_mul,le_refl]
  | add a b _ _ ha hb =>
    obtain ⟨A,hA,hA'⟩ := ha
    obtain ⟨B,hB,hB'⟩ := hb
    refine ⟨A+B,add_nonneg hA hB,?_⟩
    intro ε hε Q hQ
    rw [map_add,map_add,add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hA' ε hε Q hQ) (hB' ε hε Q hQ))
  | smul r a _ ha =>
    obtain ⟨A,hA,hA'⟩ := ha
    refine ⟨‖r‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
    intro ε hε Q hQ
    rw [map_smul,map_smul,norm_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA' ε hε Q hQ) (norm_nonneg _)

include hK hn hR y₀ in
lemma vanishing_of_zero_strata
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (hμ : ∀h : H,MeasurePreserving (fun x : X=>h • x) μ μ)
    (C : SourceTop K n → ℝ) (hC : ∀σ,0≤C σ)
    (hzero : ∀ε : ℝ,0<ε → ∃Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n,
      ∀σ : SourceTop K n,(∫x,(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀(h : H) c,ψ (relabel (n+1) (fun y=>h • y) c)=ψ c)
    (hψd : ∀c,ψ (d (n+1) c)=0)
    (c : (augmentedComplex K).chains (n+1))
    (hc : (⟨d n c,(augmentedComplex K).d_mem n c.property⟩ :
      (augmentedComplex K).chains n)∈(augmentedComplex K).relations hInv n) : ψ c=0 := by
  obtain ⟨B,hB,hbound⟩ := exists_chain_bound (H := H) Γ hΓ hK hn hR y₀ μ C hC ψ c c.property
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  by_contra hh
  have hp : 0<‖ψ c‖ := lt_of_not_ge hh
  let ε := ‖ψ c‖/(2*(B+1))
  have hε : 0<ε := div_pos hp (by positivity)
  obtain ⟨Q,hQ⟩ := hzero ε hε
  have hb := hbound ε hε Q hQ
  rw [averagedSparseChain_comparison Γ hΓ Q hK hn hR y₀ μ hInv hμ n ψ hψ hψd c hc] at hb
  have he : ε*(2*(B+1))=‖ψ c‖ := div_mul_cancel₀ _ (by positivity)
  nlinarith

end BassTrace.Sparse

namespace BassTrace.Sparse.GraphGeometry

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

open Oriented ChainHomotopy

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [Countable Y] [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})

local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ

variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

omit [LinearOrder (Y →₀ ℝ)] [Countable Y] [Countable H] [IsCancelSMul H Y] in
lemma augmentedComplex_invariant : (augmentedComplex K).IsInvariant (H := H) := by
  intro h s hs
  rcases hs with rfl|hs
  · exact Set.mem_insert_iff.mpr (Or.inl (by simp))
  · apply Set.mem_insert_of_mem
    have hh := hact.out h s hs
    rw [Finset.map_eq_image] at hh
    exact hh

include hi hn hK hΓaut in

theorem sparse_vanishing (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hlarge : volumeThreshold D≤n)
    (F : Finset (Finset Y)) (hF : ∀ s∈F,s∈K.faces)
    (hrep : ∀ s∈K.faces,∃ h : H,∃ τ∈F,s=τ.map (MulAction.toPerm h).toEmbedding)
    (y₀ : Y) (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀(h : H) c,ψ (relabel (n+1) (fun y=>h • y) c)=ψ c)
    (hψd : ∀c,ψ (d (n+1) c)=0)
    (c : (augmentedComplex K).chains (n+1))
    (hc : (⟨d n c,(augmentedComplex K).d_mem n c.property⟩ :
      (augmentedComplex K).chains n)∈(augmentedComplex K).relations (augmentedComplex_invariant (H := H)) n) :
    ψ c=0 := by
  obtain ⟨C,hC,hzero⟩ := exists_sparse_zero_strata Γ hΓ hΓaut hi hn hK μ hμ D hD hdeg hlarge F hF hrep
  exact vanishing_of_zero_strata Γ hΓ hK hn (by positivity) y₀ μ
    (augmentedComplex_invariant (H := H)) hμ C hC hzero ψ hψ hψd c hc

end

open scoped Classical

lemma graphMetric_action_isometry {H Y : Type*} [Group H] [MulAction H Y]
    (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
    (hAut : ∀(h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v) (h : H) :
    @Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
      (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y) := by
  let _ := graphMetric Γ hΓ
  have hle (h : H) (u v : Y) : Γ.dist (h•u) (h•v)≤Γ.dist u v := by
    let f : Γ →g Γ := ⟨fun y=>h•y,fun ha=>(hAut h _ _).mpr ha⟩
    obtain ⟨p,hp⟩ := hΓ.exists_walk_length_eq_dist u v
    calc _ ≤ (p.map f).length := SimpleGraph.dist_le _
         _ = _ := by rw [SimpleGraph.Walk.length_map,hp]
  apply Isometry.of_dist_eq
  intro u v
  change (Γ.dist (h•u) (h•v) : ℝ)=(Γ.dist u v : ℝ)
  congr 1
  apply le_antisymm (hle h u v)
  simpa only [inv_smul_smul] using hle h⁻¹ (h•u) (h•v)

end BassTrace.Sparse.GraphGeometry

end

end OAI
