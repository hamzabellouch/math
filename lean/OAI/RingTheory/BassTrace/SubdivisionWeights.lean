import OAI.RingTheory.BassTrace.FiniteGenerators

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

section

open Set Finset

open scoped Classical Pointwise

variable {H Y : Type*} [Group H] [MulAction H Y]

def generatedComplex (T : Finset (Finset Y)) : PreAbstractSimplicialComplex Y where
  faces := {s | s.Nonempty ∧ ∃h : H,∃t∈T,s⊆h • t}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    obtain ⟨h,u,hu,hsu⟩ := hs.2
    exact ⟨ht,h,u,hu,hts.trans hsu⟩

lemma generatedComplex_invariant (T : Finset (Finset Y)) (h : H) s
    (hs : s∈(generatedComplex (H := H) T).faces) :
    s.map (MulAction.toPerm h).toEmbedding∈(generatedComplex (H := H) T).faces := by
  rw [←smul_finset_eq_map]
  obtain ⟨hne,k,t,ht,hst⟩ := hs
  refine ⟨Finset.smul_finset_nonempty.mpr hne,h*k,t,ht,?_⟩
  rw [mul_smul]
  exact Finset.smul_finset_subset_smul_finset hst

lemma generatedComplex_top_mem (T : Finset (Finset Y)) {t : Finset Y}
    (ht : t∈T) (hne : t.Nonempty) : t∈(generatedComplex (H := H) T).faces :=
  ⟨hne,1,t,ht,by simp only [one_smul,Finset.Subset.refl]⟩

lemma connected_smul (Γ : SimpleGraph Y)
    (ha : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
    (h : H) (t : Finset Y) (hc : (Γ.induce (t : Set Y)).Connected) :
    (Γ.induce (↑(h • t) : Set Y)).Connected := by
  let f : Γ.induce (t : Set Y) →g Γ.induce (↑(h • t) : Set Y) := {
    toFun := fun y=>⟨h•y.val,Finset.smul_mem_smul_finset (a := h) y.property⟩
    map_rel' := fun hy=>(ha h _ _).mpr hy }
  apply hc.map f
  intro y
  obtain ⟨z,hz,he⟩ := Finset.mem_smul_finset.mp y.property
  exact ⟨⟨z,hz⟩,Subtype.ext he⟩

lemma generatedComplex_pure (T : Finset (Finset Y)) (n : ℕ) (Γ : SimpleGraph Y)
    (ha : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
    (hT : ∀t∈T,t.card=n+1 ∧ (Γ.induce (t : Set Y)).Connected) :
    ∀s∈(generatedComplex (H := H) T).faces,∃σ∈(generatedComplex (H := H) T).faces,
      s⊆σ ∧ σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected := by
  intro s hs
  obtain ⟨hne,h,t,ht,hst⟩ := hs
  refine ⟨h•t,⟨hne.mono hst,h,t,ht,subset_rfl⟩,hst,?_,connected_smul Γ ha h t (hT t ht).2⟩
  simpa only [Finset.card_smul_finset] using (hT t ht).1

def generatedReps (T : Finset (Finset Y)) : Finset (Finset Y) :=
  (T.biUnion Finset.powerset).filter (·.Nonempty)

lemma generatedReps_mem (T : Finset (Finset Y)) {s : Finset Y}
    (hs : s∈generatedReps T) : s∈(generatedComplex (H := H) T).faces := by
  obtain ⟨hs,hne⟩ := Finset.mem_filter.mp hs
  obtain ⟨t,ht,hst⟩ := Finset.mem_biUnion.mp hs
  exact ⟨hne,1,t,ht,by simpa only [one_smul] using Finset.mem_powerset.mp hst⟩

lemma generatedReps_complete (T : Finset (Finset Y)) {s : Finset Y}
    (hs : s∈(generatedComplex (H := H) T).faces) :
    ∃h : H,∃t∈generatedReps T,s=t.map (MulAction.toPerm h).toEmbedding := by
  obtain ⟨hne,h,t,ht,hst⟩ := hs
  refine ⟨h,h⁻¹•s,?_,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_powerset.mpr ?_⟩,
      Finset.smul_finset_nonempty.mpr hne⟩
    have hh := Finset.smul_finset_subset_smul_finset (a := h⁻¹) hst
    simpa only [inv_smul_smul] using hh
  · rw [←smul_finset_eq_map,smul_inv_smul]

lemma generatedTop_finite (T : Finset (Finset Y)) (n : ℕ)
    (hT : ∀t∈T,t.card=n+1) :
    letI := sourceTopAction (generatedComplex (H := H) T) n (generatedComplex_invariant T)
    Finite (MulAction.orbitRel.Quotient H (SourceTop (generatedComplex (H := H) T) n)) := by
  let := sourceTopAction (generatedComplex (H := H) T) n (generatedComplex_invariant T)
  let f : T → MulAction.orbitRel.Quotient H (SourceTop (generatedComplex (H := H) T) n) :=
    fun t=>Quotient.mk _ ⟨t.val,generatedComplex_top_mem T t.property
      (Finset.card_pos.mp (by rw [hT t t.property]; omega)),hT t t.property⟩
  apply Finite.of_surjective f
  intro q
  induction q using Quotient.inductionOn with | _ σ =>
    obtain ⟨hne,h,t,ht,hst⟩ := σ.property.1
    have he : σ.val=h•t := Finset.eq_of_subset_of_card_le hst (by
      rw [Finset.card_smul_finset,hT t ht,σ.property.2])
    refine ⟨⟨t,ht⟩,Quotient.sound ?_⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨h⁻¹,Subtype.ext ?_⟩
    change h⁻¹ • σ.val=t
    rw [he,inv_smul_smul]

end

section

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*}

def uniformVector (s : Finset Y) : Y →₀ ℂ :=
  ∑y∈s,Finsupp.single y (s.card : ℂ)⁻¹

lemma uniformVector_apply (s : Finset Y) (y : Y) :
    uniformVector s y=if y∈s then (s.card : ℂ)⁻¹ else 0 := by
  classical
  simp [uniformVector,Finsupp.finsetSum_apply,Finsupp.single_apply,eq_comm]

lemma uniformVector_sum (s : Finset Y) (hs : s.Nonempty) :
    (uniformVector s).sum (fun _ c=>c)=1 := by
  have hh : (Finsupp.linearCombination ℂ (fun _ : Y=>(1:ℂ))) (uniformVector s)=1 := by
    simp [uniformVector,Nat.ne_of_gt hs.card_pos]
  simpa only [Finsupp.linearCombination_apply,smul_eq_mul,mul_one] using hh

lemma uniformVector_nat (s : Finset Y) {Z : Type*} (e : Y ≃ Z) :
    uniformVector (s.map e.toEmbedding)=Finsupp.domLCongr (R := ℂ) e (uniformVector s) := by
  simp only [uniformVector,Finset.sum_map,Finset.card_map,map_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact (Finsupp.domLCongr_single (R := ℂ) e y _).symm

lemma supportVertices_push {H : Type*} [Group H] [MulAction H Y]
    (h : H) (U : Set (Y →₀ ℝ)) :
    supportVertices (OrbitForms.push h '' U)= (fun y=>h • y) '' supportVertices U := by
  ext y
  constructor
  · rintro ⟨p,⟨q,hq,rfl⟩,hy⟩
    refine ⟨h⁻¹ • y,⟨q,hq,?_⟩,smul_inv_smul h y⟩
    simpa only [Finsupp.mem_support_iff,OrbitForms.push_apply] using hy
  · rintro ⟨z,⟨p,hp,hz⟩,rfl⟩
    refine ⟨OrbitForms.push h p,⟨p,hp,rfl⟩,?_⟩
    simpa only [Finsupp.mem_support_iff,OrbitForms.push_apply,inv_smul_smul] using hz

variable {H X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R)

def componentVertices (x : X) (F : (Q.point x).FinalFace) : Finset Y :=
  (componentSupport_finite Γ hΓ Q hK hn hR x F).toFinset

@[simp] lemma mem_componentVertices (x : X) (F : (Q.point x).FinalFace) (y : Y) :
    y∈componentVertices Γ hΓ Q hK hn hR x F ↔
      y∈supportVertices ((Q.point x).faceComponent F) := Set.Finite.mem_toFinset _

lemma componentVertices_nonempty (x : X) (F : (Q.point x).FinalFace) :
    (componentVertices Γ hΓ Q hK hn hR x F).Nonempty := by
  obtain ⟨y,hy⟩ := componentSupport_nonempty Γ hΓ Q x F
  exact ⟨y,(mem_componentVertices Γ hΓ Q hK hn hR x F y).mpr hy⟩

lemma componentVertices_nat (h : H) (x : X) (F : (Q.point x).FinalFace) :
    componentVertices Γ hΓ Q hK hn hR (h • x) (Q.translateFace h x F)=
      (componentVertices Γ hΓ Q hK hn hR x F).map (MulAction.toPerm h).toEmbedding := by
  ext y
  simp only [mem_componentVertices,Finset.mem_map,Equiv.coe_toEmbedding,MulAction.toPerm_apply]
  rw [Q.translateFace_component,supportVertices_push]
  rfl

def componentWeight (x : X) (F : (Q.point x).FinalFace) : Y →₀ ℂ :=
  uniformVector (componentVertices Γ hΓ Q hK hn hR x F)

lemma componentWeight_sum (x : X) (F : (Q.point x).FinalFace) :
    (componentWeight Γ hΓ Q hK hn hR x F).sum (fun _ c=>c)=1 :=
  uniformVector_sum _ (componentVertices_nonempty Γ hΓ Q hK hn hR x F)

lemma componentWeight_nat (h : H) (x : X) (F : (Q.point x).FinalFace) :
    componentWeight Γ hΓ Q hK hn hR (h • x) (Q.translateFace h x F)=
      Finsupp.domLCongr (R := ℂ) (MulAction.toPerm h) (componentWeight Γ hΓ Q hK hn hR x F) := by
  unfold componentWeight
  rw [componentVertices_nat,uniformVector_nat]

lemma componentWeight_eq_of_component (x y : X)
    (F : (Q.point x).FinalFace) (G : (Q.point y).FinalFace)
    (h : (Q.point x).faceComponent F=(Q.point y).faceComponent G) :
    componentWeight Γ hΓ Q hK hn hR x F=componentWeight Γ hΓ Q hK hn hR y G := by
  unfold componentWeight
  congr 1
  ext z
  simp only [mem_componentVertices,h]

lemma componentWeight_support (x : X) (F : (Q.point x).FinalFace) (s : Finset Y)
    (hFs : Cuts.vertexMean F.val∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    (componentWeight Γ hΓ Q hK hn hR x F).support ⊆ GraphGeometry.labelWindow Γ n R s := by
  intro y hy
  rw [Finsupp.mem_support_iff,componentWeight,uniformVector_apply] at hy
  have hy' : y∈componentVertices Γ hΓ Q hK hn hR x F := by
    by_contra hh
    simp [hh] at hy
  exact componentSupport_subset Γ hΓ Q hK hn hR x F s hFs
    ((mem_componentVertices Γ hΓ Q hK hn hR x F y).mp hy')

end

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

def faceWeight (x : X) (F : Finset (Y →₀ ℝ)) : Y →₀ ℂ :=
  if hF : F∈((Q.pair 0).T.val x).complex.faces then
    componentWeight Γ hΓ Q hK hn hR x ⟨F,hF⟩
  else Finsupp.single y₀ 1

lemma faceWeight_sum (x : X) (F : Finset (Y →₀ ℝ)) :
    (faceWeight Γ hΓ Q hK hn hR y₀ x F).sum (fun _ c=>c)=1 := by
  unfold faceWeight
  split_ifs
  · exact componentWeight_sum Γ hΓ Q hK hn hR x _
  · simp

lemma faceWeight_face (x : X) (F : (Q.point x).FinalFace) :
    faceWeight Γ hΓ Q hK hn hR y₀ x F.val=componentWeight Γ hΓ Q hK hn hR x F := by
  unfold faceWeight
  have hf : F.val∈((Q.pair 0).T.val x).complex.faces := F.property
  rw [dite_eq_left hf]
  rfl

lemma faceWeight_nat (h : H) (x : X) (F : (Q.point x).FinalFace) :
    faceWeight Γ hΓ Q hK hn hR y₀ (h • x) (F.val.map (OrbitForms.push h).toEmbedding)=
      Finsupp.domLCongr (R := ℂ) (MulAction.toPerm h)
        (faceWeight Γ hΓ Q hK hn hR y₀ x F.val) := by
  change faceWeight Γ hΓ Q hK hn hR y₀ (h • x) (Q.translateFace h x F).val=_
  rw [faceWeight_face,faceWeight_face,componentWeight_nat]

lemma faceWeight_nested_equal_level (x : X) (F G : (Q.point x).FinalFace)
    (hFG : F.val⊆G.val) (hlevel : (Q.point x).faceLevel F=(Q.point x).faceLevel G) :
    faceWeight Γ hΓ Q hK hn hR y₀ x F.val=faceWeight Γ hΓ Q hK hn hR y₀ x G.val := by
  rw [faceWeight_face,faceWeight_face]
  exact componentWeight_eq_of_component Γ hΓ Q hK hn hR x x F G
    ((Q.point x).faceComponent_eq_of_level_eq F G hFG hlevel)

lemma faceWeight_local (s : Finset Y) (hs : s∈K.faces) (x : X) : ∀ᶠ y in nhds x,
    (Cuts.restrictComplex ((Q.pair 0).T.val y).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces=
    (Cuts.restrictComplex ((Q.pair 0).T.val x).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces ∧
    ∀ F∈(Cuts.restrictComplex ((Q.pair 0).T.val x).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces,
      faceWeight Γ hΓ Q hK hn hR y₀ y F=faceWeight Γ hΓ Q hK hn hR y₀ x F := by
  filter_upwards [GraphGeometry.faceComponents_eq_local Γ hΓ Q hK hn hR s hs x] with y hy
  refine ⟨hy.1,?_⟩
  intro F hF
  have hF' : F∈(Cuts.restrictComplex ((Q.pair 0).T.val y).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces := hy.1.symm ▸ hF
  change F∈((Q.pair 0).T.val x).complex.faces ∧ _ at hF
  change F∈((Q.pair 0).T.val y).complex.faces ∧ _ at hF'
  rw [faceWeight,faceWeight,dite_eq_left hF.1,dite_eq_left hF'.1]
  exact componentWeight_eq_of_component Γ hΓ Q hK hn hR y x ⟨F,hF'.1⟩ ⟨F,hF.1⟩
    (hy.2 F hF.1 hF'.1 (convexHull_min hF.2 (convex_convexHull ℝ _)))

end BassTrace.Sparse

namespace BassTrace.SubdivisionChains

section

open Set Finset

open scoped BassTrace.Sparse Classical

open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence

variable {Y : Type*} [LinearOrder Y] [LinearOrder (Y →₀ ℝ)]

variable {K : PreAbstractSimplicialComplex Y}

variable (T : Cuts.Subdivision (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))

def chart {k : ℕ} (v : Fin k → Y) : (Y →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  LinearMap.pi (fun i=>Finsupp.lapply (v i))

omit [LinearOrder Y] [LinearOrder (Y →₀ ℝ)] in
@[simp] lemma chart_apply {k : ℕ} (v : Fin k → Y) (p : Y →₀ ℝ) (i : Fin k) :
    chart v p i=p (v i) := rfl

omit [LinearOrder (Y →₀ ℝ)] in
lemma chart_vertex {k : ℕ} (v : Fin k → Y) (hv : Function.Injective v) (j : Fin k) :
    chart v (Finsupp.single (v j) 1)=Pi.single j 1 := by
  ext i
  simp [chart_apply,Finsupp.single_apply,Pi.single_apply,hv.eq_iff,eq_comm]

def localTriangulation (s : Finset Y) :=
  Cuts.restrictComplex T.complex (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))

omit [LinearOrder (Y →₀ ℝ)] in
lemma localTriangulation_finite (s : Finset Y) (hs : s∈K.faces) :
    (localTriangulation T s).faces.Finite := T.finite (simplexVertices s) ⟨s,hs,rfl⟩

omit [LinearOrder (Y →₀ ℝ)] in
lemma localTriangulation_space (s : Finset Y) (hs : s∈K.faces) :
    (localTriangulation T s).space=convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) := by
  rw [localTriangulation,Cuts.restrictComplex_space_of_respects _ _
    (T.respects (simplexVertices s) ⟨s,hs,rfl⟩),T.space_eq]
  exact Set.inter_eq_right.mpr
    ((Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space ⟨s,hs,rfl⟩)

def tupleSubdivision (k : ℕ) (v : Fin (k+1) → Y) : Degree (Y →₀ ℝ) (k+1) :=
  if hs : Finset.univ.image v∈K.faces then
    chain (faces (localTriangulation T (Finset.univ.image v))
      (localTriangulation_finite T _ hs) (k+1)) (chart v)
  else 0

omit [LinearOrder Y] in
lemma chain_chart_perm {k : ℕ} (A : Finset (Set.powersetCard (Y →₀ ℝ) (k+1)))
    (v : Fin (k+1) → Y) (σ : Equiv.Perm (Fin (k+1))) :
    chain A (chart (v ∘ σ))=(Equiv.Perm.sign σ) • chain A (chart v) := by
  unfold chain
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have he : Matrix.det (fun i=>chart (v ∘ σ) (vertices s i))=
      (Equiv.Perm.sign σ : ℝ)*Matrix.det (fun i=>chart v (vertices s i)) :=
    by exact Matrix.det_permute' σ (fun i j=>vertices s i (v j))
  rw [he]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simp only [h,Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul,
      Real.sign_neg,Complex.ofReal_neg,Units.neg_smul,one_smul]
    exact _root_.neg_smul (Real.sign (Matrix.det (fun i=>chart v (vertices s i))) : ℂ)
      (basis (k+1) s)

lemma tupleSubdivision_perm (k : ℕ) (v : Fin (k+1) → Y)
    (σ : Equiv.Perm (Fin (k+1))) :
    tupleSubdivision T k (v ∘ σ)=(Equiv.Perm.sign σ) • tupleSubdivision T k v := by
  unfold tupleSubdivision
  simp only [tuple_image_perm]
  split_ifs with hs
  · exact chain_chart_perm _ v σ
  · simp

lemma tupleSubdivision_zero (k : ℕ) (v : Fin (k+1) → Y)
    (hv : ¬Function.Injective v) : tupleSubdivision T k v=0 := by
  unfold tupleSubdivision
  split_ifs with hs
  · unfold chain
    apply Finset.sum_eq_zero
    intro s _
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hv
    have hd : Matrix.det (fun a=>chart v (vertices s a))=0 :=
      Matrix.det_zero_of_column_eq hne (fun a=>congrArg (vertices s a) hij)
    rw [hd,Real.sign_zero,Complex.ofReal_zero,zero_smul]
  · rfl

def subdivisionValues (k : ℕ) : AltFunction Y (k+1) (Degree (Y →₀ ℝ) (k+1)) where
  toFun := tupleSubdivision T k
  perm := tupleSubdivision_perm T k
  zero := tupleSubdivision_zero T k

def subdivision : ∀ k, Degree Y k →ₗ[ℂ] Degree (Y →₀ ℝ) k
  | 0 => relabel 0 (fun y=>Finsupp.single y (1:ℝ))
  | k+1 => (subdivisionValues T k).lift

@[simp] lemma subdivision_wedge_succ (k : ℕ) (v : Fin (k+1) → Y) :
    subdivision T (k+1) (wedge (k+1) v)=tupleSubdivision T k v :=
  (subdivisionValues T k).lift_wedge v

lemma subdivision_wedge_face (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) :
    subdivision T (k+1) (wedge (k+1) v)=
      chain (faces (localTriangulation T (Finset.univ.image v))
        (localTriangulation_finite T _ hs) (k+1)) (chart v) := by
  rw [subdivision_wedge_succ,tupleSubdivision,dite_eq_left hs]

end

open Set Finset

open scoped BassTrace.Sparse Classical

open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence

variable {Y : Type*} [LinearOrder Y] [LinearOrder (Y →₀ ℝ)]

variable {K : PreAbstractSimplicialComplex Y}

variable (T : Cuts.Subdivision (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))

omit [LinearOrder (Y →₀ ℝ)] in
lemma simplexVertices_image {k : ℕ} (v : Fin k → Y) :
    (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ))=
      Set.range (fun i=>Finsupp.single (v i) (1:ℝ)) := by
  ext p
  simp only [simplexVertices,Finset.coe_image,Finset.coe_univ,Set.image_univ,Set.mem_image,
    Set.mem_range]
  constructor
  · rintro ⟨y,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨v i,⟨i,rfl⟩,rfl⟩

omit [LinearOrder (Y →₀ ℝ)] in
lemma localTriangulation_face {k : ℕ} (v : Fin (k+1) → Y)
    (hv : Function.Injective v) (i : Fin (k+1)) :
    Sparse.restrictComplex (localTriangulation T (Finset.univ.image v))
      {p | chart v p i=0}=
    localTriangulation T (Finset.univ.image (fun j=>v (i.succAbove j))) := by
  apply Geometry.SimplicialComplex.ext
  ext s
  change (s∈T.complex.faces ∧ (s : Set (Y →₀ ℝ))⊆
      convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ))) ∧
      (s : Set (Y →₀ ℝ))⊆{p | chart v p i=0} ↔ s∈T.complex.faces ∧
      (s : Set (Y →₀ ℝ))⊆convexHull ℝ
        (simplexVertices (Finset.univ.image (fun j=>v (i.succAbove j))) : Set (Y →₀ ℝ))
  rw [simplexVertices_image,simplexVertices_image]
  rw [← parent_face_chart (fun j=>Finsupp.single (v j) (1:ℝ)) (chart v)
    (chart_vertex v hv) i,Set.subset_inter_iff]
  tauto

lemma subdivision_chain_wedge (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) :
    d k (subdivision T (k+1) (wedge (k+1) v))=
      subdivision T k (d k (wedge (k+1) v)) := by
  by_cases hv : Function.Injective v
  swap
  · rw [wedge_eq_zero_of_not_injective _ hv,map_zero,map_zero,map_zero,map_zero]
  cases k with
  | zero =>
    rw [subdivision_wedge_face T 0 v hs]
    have hsp : (localTriangulation T (Finset.univ.image v)).space=
        {Finsupp.single (v 0) (1:ℝ)} := by
      rw [localTriangulation_space T _ hs,simplexVertices_image]
      have he : Set.range (fun i : Fin 1=>Finsupp.single (v i) (1:ℝ))=
          {Finsupp.single (v 0) (1:ℝ)} := by simp
      rw [he,convexHull_singleton]
    rw [augmentation_chain _ _ _ hsp _ (by
      simpa only [Pi.single_eq_same] using congrFun (chart_vertex v hv 0) 0)]
    change wedge 0 (Fin.elim0 : Fin 0 → (Y →₀ ℝ))=
      relabel 0 (fun y : Y=>Finsupp.single y (1:ℝ)) (d 0 (wedge 1 v))
    rw [d_wedge]
    change _=relabel 0 _ (∑i : Fin 1,(-1:ℂ)^i.val •
      wedge 0 (fun j=>v (i.succAbove j)))
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero,pow_zero,one_smul,relabel_wedge]
    congr 1
    exact Subsingleton.elim _ _
  | succ k =>
    rw [subdivision_wedge_face T (k+1) v hs]
    let w : Fin (k+2) ↪ (Y →₀ ℝ) := ⟨fun i=>Finsupp.single (v i) 1,
      (Finsupp.single_left_injective (by norm_num : (1:ℝ)≠0)).comp hv⟩
    have hw : Set.range w=(simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)) :=
      (simplexVertices_image v).symm
    rw [boundary_chain_restrictions _ _ _ w hw (localTriangulation_space T _ hs)
      (chart v) (chart_vertex v hv),d_wedge,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    congr 1
    have hsub : Finset.univ.image (fun j=>v (i.succAbove j))⊆Finset.univ.image v := by
      intro y hy
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨i.succAbove j,Finset.mem_univ _,rfl⟩
    have hface := (K.isRelLowerSet_faces hs).2 hsub
      (Finset.image_nonempty.mpr Finset.univ_nonempty)
    rw [subdivision_wedge_face T k _ hface]
    congr 2
    exact localTriangulation_face T v hv i

end BassTrace.SubdivisionChains

end

end OAI
