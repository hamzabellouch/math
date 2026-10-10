import OAI.RingTheory.BassTrace.SparseChains

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.SubdivisionChains

open Set Finset

open scoped BassTrace.Sparse Classical

open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence Sparse.OrbitForms

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y}

variable (P : MarkedPair (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))

omit [LinearOrder (Y →₀ ℝ)] in
lemma originalHull_push (h : H) (s : Finset Y) :
    convexHull ℝ (simplexVertices (s.map (MulAction.toPerm h).toEmbedding) : Set (Y →₀ ℝ))=
      push h '' convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) := by
  rw [simplexVertices_relabel]
  exact ((push h).toLinearMap.image_convexHull _).symm

omit [LinearOrder (Y →₀ ℝ)] in
lemma localFace_push (h : H) (x : X) (s : Finset Y) (F : Finset (Y →₀ ℝ))
    (hF : F∈(localTriangulation (P.T.val x) s).faces) :
    F.map (push h).toEmbedding∈
      (localTriangulation (P.T.val (h • x)) (s.map (MulAction.toPerm h).toEmbedding)).faces := by
  refine ⟨P.equivariant h x F hF.1,?_⟩
  rw [originalHull_push]
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  exact ⟨q,hF.2 hq,rfl⟩

omit [LinearOrder Y] [LinearOrder (Y →₀ ℝ)] in
lemma map_push_inverse (h : H) (F : Finset (Y →₀ ℝ)) :
    (F.map (push h).toEmbedding).map (push h⁻¹).toEmbedding=F := by
  rw [Finset.map_map]
  have he : (push h).toEmbedding.trans (push h⁻¹).toEmbedding=Function.Embedding.refl (Y →₀ ℝ) :=
    Function.Embedding.ext (push_inv_push (Y := Y) h)
  rw [he,Finset.map_refl]

omit [LinearOrder Y] [LinearOrder (Y →₀ ℝ)] in
lemma map_action_inverse (h : H) (s : Finset Y) :
    (s.map (MulAction.toPerm h).toEmbedding).map (MulAction.toPerm h⁻¹).toEmbedding=s := by
  rw [Finset.map_map]
  have he : (MulAction.toPerm h).toEmbedding.trans (MulAction.toPerm h⁻¹).toEmbedding=
      Function.Embedding.refl Y := Function.Embedding.ext (fun y : Y => inv_smul_smul h y)
  rw [he,Finset.map_refl]

omit [LinearOrder (Y →₀ ℝ)] in
lemma local_faces_natural (h : H) (x : X) (s : Finset Y) (hs : s∈K.faces)
    (ht : s.map (MulAction.toPerm h).toEmbedding∈K.faces) (k : ℕ) :
    (faces (localTriangulation (P.T.val x) s) (localTriangulation_finite _ _ hs) k).map
      (simplexMap (push h).toEmbedding k)=
    faces (localTriangulation (P.T.val (h • x)) (s.map (MulAction.toPerm h).toEmbedding))
      (localTriangulation_finite _ _ ht) k := by
  ext F
  rw [Finset.mem_map,mem_faces]
  constructor
  · rintro ⟨E,hE,rfl⟩
    exact localFace_push P h x s E.val ((mem_faces _ _ _ E).mp hE)
  · intro hF
    refine ⟨⟨F.val.map (push h⁻¹).toEmbedding,by simp⟩,?_,?_⟩
    · rw [mem_faces]
      have hh := localFace_push P h⁻¹ (h • x) (s.map (MulAction.toPerm h).toEmbedding)
        F.val hF
      simpa only [map_action_inverse,inv_smul_smul] using hh
    · apply Subtype.ext
      change (F.val.map (push h⁻¹).toEmbedding).map (push h).toEmbedding=F.val
      simpa only [inv_inv] using map_push_inverse (Y := Y) h⁻¹ F.val

lemma subdivision_natural_face (h : H) (x : X) (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces)
    (ht : (Finset.univ.image v).map (MulAction.toPerm h).toEmbedding∈K.faces) :
    relabel (k+1) (push h) (subdivision (P.T.val x) (k+1) (wedge (k+1) v))=
      subdivision (P.T.val (h • x)) (k+1) (wedge (k+1) (fun i=>h • v i)) := by
  have himage : Finset.univ.image (fun i=>h • v i)=
      (Finset.univ.image v).map (MulAction.toPerm h).toEmbedding := by
    simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def,
      Equiv.coe_toEmbedding,MulAction.toPerm_apply]
  have htv : Finset.univ.image (fun i=>h • v i)∈K.faces := himage.symm ▸ ht
  rw [subdivision_wedge_face _ _ _ hs,subdivision_wedge_face _ _ _ htv]
  calc
    _ = chain ((faces (localTriangulation (P.T.val x) (Finset.univ.image v))
        (localTriangulation_finite _ _ hs) (k+1)).map (simplexMap (push h).toEmbedding (k+1)))
        (chart (fun i=>h • v i)) := by
      exact chain_relabel _ _ (chart (fun i=>h • v i)) (push h).toEmbedding (by
        intro p
        ext i
        change (push h p) (h • v i) = p (v i)
        rw [push_apply,inv_smul_smul])
    _ = _ := by
      congr 1
      simpa only [himage] using local_faces_natural P h x (Finset.univ.image v) hs ht (k+1)

end BassTrace.SubdivisionChains

namespace BassTrace.Sparse

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

omit [LinearOrder (Y →₀ ℝ)] [LinearOrder Y] in
lemma vertexMap_perm (h : H) (b : Y →₀ ℂ) :
    vertexMap (fun y=>h • y) b=Finsupp.domLCongr (R := ℂ) (MulAction.toPerm h) b := by
  ext y
  change Finsupp.mapDomain (MulAction.toPerm h) b y = _
  rw [Finsupp.mapDomain_equiv_apply]
  rfl

lemma sparseChainFamily_natural_face (h : H) (x : X) (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces)
    (ht : (Finset.univ.image v).map (MulAction.toPerm h).toEmbedding∈K.faces) :
    relabel (k+1) (fun y=>h • y)
        (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v))=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ (h • x) (k+1)
        (wedge (k+1) (fun i=>h • v i)) := by
  unfold sparseChainFamily
  simp only [LinearMap.comp_apply]
  rw [←subdivision_natural_face (Q.pair 0) h x k v hs ht,subdivision_wedge_face _ _ _ hs]
  simp only [chain,map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  simp only [map_smul,basis_eq_wedge,relabel_wedge]
  congr 1
  apply labelMap_natural_local _ _ _ _ F.val
  · intro t htF htn
    have htf : t∈((Q.pair 0).T.val x).complex.faces :=
      ((Q.pair 0).T.val x).complex.down_closed
        ((mem_faces _ _ _ F).mp hF).1 htF htn
    rw [vertexMap_perm]
    calc
      _ = faceWeight Γ hΓ Q hK hn hR y₀ (h • x)
          (t.map (OrbitForms.push h).toEmbedding) := by
        apply congrArg (faceWeight Γ hΓ Q hK hn hR y₀ (h • x))
        ext p
        simp only [Finset.mem_image,Finset.mem_map]
        rfl
      _ = _ := faceWeight_nat Γ hΓ Q hK hn hR y₀ h x ⟨t,htf⟩
  · exact fun i=>OrientedIncidence.vertices_mem F i

lemma sparseChainFamily_natural
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (h : H) (x : X) (k : ℕ) (c : Degree Y k)
    (hc : c∈(augmentedComplex K).chains k) :
    relabel k (fun y=>h • y) (sparseChainFamily Γ hΓ Q hK hn hR y₀ x k c)=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ (h • x) k (relabel k (fun y=>h • y) c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,hv,rfl⟩:=hc
    cases k with
    | zero => rw [sparseChainFamily_zero,sparseChainFamily_zero]; rfl
    | succ k =>
      have hs : Finset.univ.image v∈K.faces := by
        rcases hv with hv | hv
        · exact False.elim ((Finset.image_nonempty.mpr Finset.univ_nonempty).ne_empty hv)
        · exact hv
      rw [relabel_wedge]
      apply sparseChainFamily_natural_face Γ hΓ Q hK hn hR y₀ h x k v hs
      have ht := hInv h (Finset.univ.image v) (Set.mem_insert_of_mem ∅ hs)
      rcases ht with ht | ht
      · exact False.elim ((Finset.image_nonempty.mpr (Finset.image_nonempty.mpr
          Finset.univ_nonempty)).ne_empty ht)
      · convert ht using 1
        ext y
        simp only [Finset.mem_image,Finset.mem_map]
        rfl
  | zero => simp
  | add c d _ _ hc hd => simp only [map_add,hc,hd]
  | smul a c _ hc => simp only [map_smul,hc]

end BassTrace.Sparse

namespace BassTrace.FiniteAverage

open Set Finset MeasureTheory

open scoped Classical

variable {X V W Z : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Z] [Module ℂ Z]

variable (μ : Measure X) [IsFiniteMeasure μ]

def locallyConstantLinearMap (F : X → V →ₗ[ℂ] W)
    (hF : ∀v,IsLocallyConstant (fun x=>F x v)) : V →ₗ[ℂ] W where
  toFun v := average μ (ofLocallyConstant _ (hF v))
  map_add' a b := by
    have he : ofLocallyConstant (fun x=>F x (a+b)) (hF (a+b)) =
        ofLocallyConstant (fun x=>F x a) (hF a)+ofLocallyConstant (fun x=>F x b) (hF b) := by
      ext x
      exact map_add (F x) a b
    rw [he,average_add]
  map_smul' r v := by
    let L : W →ₗ[ℝ] W := (r • (LinearMap.id : W →ₗ[ℂ] W)).restrictScalars ℝ
    have he : ofLocallyConstant (fun x=>F x (r • v)) (hF (r • v)) =
        (ofLocallyConstant (fun x=>F x v) (hF v)).map L := by
      ext x
      exact map_smul (F x) r v
    rw [he,average_map]
    rfl

lemma locallyConstantLinearMap_post (F : X → V →ₗ[ℂ] W)
    (hF : ∀v,IsLocallyConstant (fun x=>F x v)) (L : W →ₗ[ℂ] Z) (v : V) :
    L (locallyConstantLinearMap μ F hF v)=
      average μ ((ofLocallyConstant (fun x=>F x v) (hF v)).map L) :=
  (average_map μ (L.restrictScalars ℝ) _).symm

lemma locallyConstantLinearMap_const [IsProbabilityMeasure μ] (F : V →ₗ[ℂ] W) (v : V) :
    locallyConstantLinearMap μ (fun _=>F) (fun v=>IsLocallyConstant.const (F v)) v=F v := by
  change average μ (ofLocallyConstant _ _)=F v
  have he : ofLocallyConstant (fun _ : X=>F v) (IsLocallyConstant.const (F v)) =
      SimpleFunc.const X (F v) := by ext; rfl
  rw [he,average_const]

end BassTrace.FiniteAverage

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains FiniteAverage

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

def averagedSparseChain (k : ℕ) : Degree Y k →ₗ[ℂ] Degree Y k :=
  locallyConstantLinearMap μ (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x k)
    (sparseChainFamily_local Γ hΓ Q hK hn hR y₀ k)

lemma averagedSparseChain_zero (c : Degree Y 0) :
    averagedSparseChain Γ hΓ Q hK hn hR y₀ μ 0 c=c := by
  unfold averagedSparseChain
  simp_rw [sparseChainFamily_zero]
  exact locallyConstantLinearMap_const μ LinearMap.id c

lemma averagedSparseChain_chain (k : ℕ) (c : Degree Y (k+1))
    (hc : c∈(augmentedComplex K).chains (k+1)) :
    d k (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (k+1) c)=
      averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k (d k c) := by
  unfold averagedSparseChain
  rw [locallyConstantLinearMap_post]
  apply congrArg (FiniteAverage.average μ)
  apply SimpleFunc.ext
  intro x
  exact sparseChainFamily_chain Γ hΓ Q hK hn hR y₀ x k c hc

lemma averagedSparseChain_natural
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (hμ : ∀h : H,MeasurePreserving (fun x : X=>h • x) μ μ)
    (h : H) (k : ℕ) (c : Degree Y k) (hc : c∈(augmentedComplex K).chains k) :
    relabel k (fun y=>h • y) (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k c)=
      averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k (relabel k (fun y=>h • y) c) := by
  unfold averagedSparseChain
  rw [locallyConstantLinearMap_post]
  let f := ofLocallyConstant
    (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x k (relabel k (fun y=>h • y) c))
    (sparseChainFamily_local Γ hΓ Q hK hn hR y₀ k _)
  change FiniteAverage.average μ _=FiniteAverage.average μ f
  rw [←average_precomp μ μ (fun x : X=>h • x) (hμ h)
    (MulAction.bijective h).surjective f]
  apply congrArg (FiniteAverage.average μ)
  apply SimpleFunc.ext
  intro x
  exact sparseChainFamily_natural Γ hΓ Q hK hn hR y₀ hInv h x k c hc

lemma averagedSparseChain_comparison
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (hμ : ∀h : H,MeasurePreserving (fun x : X=>h • x) μ μ)
    (k : ℕ) (ψ : Degree Y (k+1) →ₗ[ℂ] ℂ)
    (hψ : ∀(h : H) c,ψ (relabel (k+1) (fun y=>h • y) c)=ψ c)
    (hψd : ∀c,ψ (d (k+1) c)=0)
    (c : (augmentedComplex K).chains (k+1))
    (hc : (⟨d k c,(augmentedComplex K).d_mem k c.property⟩ :
      (augmentedComplex K).chains k)∈(augmentedComplex K).relations hInv k) :
    ψ (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (k+1) c)=ψ c := by
  refine source_coinvariant_comparison (augmentedComplex K) hInv
    (fun k=>(averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k).comp
      ((augmentedComplex K).chains k).subtype)
    (fun c=>averagedSparseChain_zero Γ hΓ Q hK hn hR y₀ μ c)
    (fun k c=>averagedSparseChain_chain Γ hΓ Q hK hn hR y₀ μ k c c.property)
    (fun k h c=>averagedSparseChain_natural Γ hΓ Q hK hn hR y₀ μ hInv hμ h k c c.property)
    k ψ hψ hψd c hc

end BassTrace.Sparse

end

end OAI
