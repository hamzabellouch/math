import OAI.RingTheory.BassTrace.ZeroStrata

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.Cuts

open Set Finset

open scoped Classical

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma vertexMean_weight_sum {F : Finset E} (hF : F.Nonempty) :
    ∑ _x ∈ F, (F.card : ℝ)⁻¹ = 1 := by
  simp [ne_of_gt (Nat.cast_pos.mpr hF.card_pos : (0:ℝ)<F.card)]

lemma vertexMean_eq_sum (F : Finset E) :
    vertexMean F = ∑ x ∈ F, (F.card : ℝ)⁻¹ • x := by
  simp only [vertexMean,Finset.smul_sum]

lemma vertexMean_mem_marked_iff (K : Geometry.SimplicialComplex ℝ E)
    {Z : Set E} (hZ : IsMarked K Z) {F : Finset E} (hF : F ∈ K.faces) :
    vertexMean F ∈ Z ↔ convexHull ℝ (F : Set E) ⊆ Z := by
  constructor
  · intro hm
    obtain ⟨T,hT,hmt,hTZ⟩ := hZ _ hm
    rw [vertexMean_eq_sum] at hmt
    have hFT := simplex_contains_positivePoint K hF hT (fun _ => (F.card : ℝ)⁻¹)
      (fun _ _ => inv_pos.mpr (Nat.cast_pos.mpr (K.nonempty_of_mem_faces hF).card_pos))
      (vertexMean_weight_sum (K.nonempty_of_mem_faces hF)) hmt
    exact (convexHull_mono hFT).trans hTZ
  · exact fun hh => hh (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hF))

lemma segment_vertexMean_avoids (K : Geometry.SimplicialComplex ℝ E)
    {Z : Set E} (hZ : IsMarked K Z) {F G : Finset E}
    (hF : F ∈ K.faces) (hG : G ∈ K.faces) (hFG : F ⊆ G)
    (hmF : vertexMean F ∉ Z) (hmG : vertexMean G ∉ Z) :
    Disjoint (segment ℝ (vertexMean F) (vertexMean G)) Z := by
  apply Set.disjoint_left.mpr
  rintro q ⟨a,b,ha,hb,hab,rfl⟩ hq
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    simp only [ha1,hb0,one_smul,zero_smul,add_zero] at hq
    exact hmF hq
  have hbpos : 0<b := lt_of_le_of_ne hb (Ne.symm hb0)
  let u : E → ℝ := fun x => if x ∈ F then (F.card : ℝ)⁻¹ else 0
  let w : E → ℝ := fun x => a*u x + b*(G.card : ℝ)⁻¹
  have hu : ∑ x ∈ G, u x = 1 := by
    calc
      _ = ∑ x ∈ F, u x := (Finset.sum_subset hFG (fun x _ hx => by simp [u,hx])).symm
      _ = ∑ _x ∈ F, (F.card : ℝ)⁻¹ := Finset.sum_congr rfl (fun x hx => by simp [u,hx])
      _ = 1 := vertexMean_weight_sum (K.nonempty_of_mem_faces hF)
  have hvec : ∑ x ∈ G, u x • x = vertexMean F := by
    calc
      _ = ∑ x ∈ F, u x • x :=
        (Finset.sum_subset hFG (fun x _ hx => by simp [u,hx])).symm
      _ = ∑ x ∈ F, (F.card : ℝ)⁻¹ • x :=
        Finset.sum_congr rfl (fun x hx => by simp [u,hx])
      _ = _ := (vertexMean_eq_sum F).symm
  have hw : ∀ x ∈ G, 0 < w x := by
    intro x _
    have hux : 0 ≤ u x := by dsimp [u]; split_ifs <;> positivity
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha hux)
      (mul_pos hbpos (inv_pos.mpr (Nat.cast_pos.mpr (K.nonempty_of_mem_faces hG).card_pos)))
  have hws : ∑ x ∈ G, w x = 1 := by
    simp only [w,Finset.sum_add_distrib,← Finset.mul_sum,hu,
      vertexMean_weight_sum (K.nonempty_of_mem_faces hG),mul_one]
    exact hab
  have heq : ∑ x ∈ G, w x • x = a • vertexMean F + b • vertexMean G := by
    simp only [w,add_smul,mul_smul,Finset.sum_add_distrib,← Finset.smul_sum,hvec,
      ← vertexMean_eq_sum]
  obtain ⟨T,hT,hqT,hTZ⟩ := hZ _ hq
  rw [← heq] at hqT
  have hGT := simplex_contains_positivePoint K hG hT w hw hws hqT
  exact hmG (hTZ (convexHull_mono hGT (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hG))))

lemma vertexMean_components_eq (K : Geometry.SimplicialComplex ℝ E)
    {P Z : Set E} (hZ : IsMarked K Z) {F G : Finset E}
    (hF : F ∈ K.faces) (hG : G ∈ K.faces) (hFG : F ⊆ G)
    (hGP : convexHull ℝ (G : Set E) ⊆ P)
    (hmF : vertexMean F ∉ Z) (hmG : vertexMean G ∉ Z) :
    connectedComponentIn (P \ Z) (vertexMean F) =
      connectedComponentIn (P \ Z) (vertexMean G) := by
  have hsub : segment ℝ (vertexMean F) (vertexMean G) ⊆ P \ Z := by
    intro q hq
    refine ⟨?_,fun hqZ => Set.disjoint_left.mp (segment_vertexMean_avoids K hZ hF hG hFG hmF hmG) hq hqZ⟩
    exact hGP ((convex_convexHull ℝ (G : Set E)).segment_subset
      (convexHull_mono hFG (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hF)))
      (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hG)) hq)
  have hh := (convex_segment (vertexMean F) (vertexMean G)).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ _ _) hsub (right_mem_segment ℝ _ _)
  exact connectedComponentIn_eq hh

end

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

namespace PointFiltration

variable (Q : PointFiltration K n)

def FinalFace := {F : Finset V // F∈(Q.T 0).faces}

lemma final_marked (i : ℕ) (hi : i≤n) : IsMarked (Q.T 0) (Q.Z i) :=
  (Q.refines (Nat.zero_le i) hi).preserves_marked (Q.marked i hi)

lemma final_mean_in_top (F : Q.FinalFace) : vertexMean F.val∈Q.Z n := by
  rw [Q.top_space]
  obtain ⟨S,hS⟩ := Q.refines (Nat.zero_le n) le_rfl
  have hF : F.val∈S.complex.faces := hS.symm ▸ F.property
  have hh := S.complex.convexHull_subset_space hF
    (vertexMean_mem_convexHull (S.complex.nonempty_of_mem_faces hF))
  rw [S.space_eq,Q.top] at hh
  exact hh

lemma exists_face_level (F : Q.FinalFace) : ∃ i,i≤n ∧ vertexMean F.val∈Q.Z i :=
  ⟨n,le_rfl,Q.final_mean_in_top F⟩

def faceLevel (F : Q.FinalFace) : ℕ := Nat.find (Q.exists_face_level F)

lemma faceLevel_le (F : Q.FinalFace) : Q.faceLevel F≤n :=
  (Nat.find_spec (Q.exists_face_level F)).1

lemma mean_mem_faceLevel (F : Q.FinalFace) : vertexMean F.val∈Q.Z (Q.faceLevel F) :=
  (Nat.find_spec (Q.exists_face_level F)).2

lemma mean_notMem_below_level (F : Q.FinalFace) {i : ℕ} (hi : i<Q.faceLevel F) :
    vertexMean F.val∉Q.Z i := by
  intro h
  exact Nat.not_lt_of_ge (Nat.find_min' (Q.exists_face_level F)
    ⟨hi.le.trans (Q.faceLevel_le F),h⟩) hi

lemma mean_mem_iff_level_le (F : Q.FinalFace) {i : ℕ} (hi : i≤n) :
    vertexMean F.val∈Q.Z i ↔ Q.faceLevel F ≤ i := by
  constructor
  · exact fun h=>Nat.find_min' (Q.exists_face_level F) ⟨hi,h⟩
  · exact fun h=>Q.subset h hi (Q.mean_mem_faceLevel F)

lemma hull_mem_iff_level_le (F : Q.FinalFace) {i : ℕ} (hi : i≤n) :
    convexHull ℝ (F.val : Set V)⊆Q.Z i ↔ Q.faceLevel F ≤ i := by
  rw [← vertexMean_mem_marked_iff (Q.T 0) (Q.final_marked i hi) F.property]
  exact Q.mean_mem_iff_level_le F hi

lemma faceLevel_mono (F G : Q.FinalFace) (hFG : F.val⊆G.val) :
    Q.faceLevel F≤Q.faceLevel G := by
  apply (Q.hull_mem_iff_level_le F (Q.faceLevel_le G)).mp
  exact (convexHull_mono hFG).trans
    ((Q.hull_mem_iff_level_le G (Q.faceLevel_le G)).mpr le_rfl)

def below (i : ℕ) : Set V := if i=0 then ∅ else Q.Z (i-1)

def stratum (i : ℕ) : Set V := Q.Z i \ Q.below i

def faceComponent (F : Q.FinalFace) : Set V :=
  connectedComponentIn (Q.stratum (Q.faceLevel F)) (vertexMean F.val)

lemma mean_mem_stratum (F : Q.FinalFace) :
    vertexMean F.val∈Q.stratum (Q.faceLevel F) := by
  refine ⟨Q.mean_mem_faceLevel F,?_⟩
  unfold below
  split_ifs with h
  · simp
  · exact Q.mean_notMem_below_level F (by omega)

lemma mean_mem_component (F : Q.FinalFace) : vertexMean F.val∈Q.faceComponent F :=
  mem_connectedComponentIn (Q.mean_mem_stratum F)

lemma faceComponent_subset (F : Q.FinalFace) : Q.faceComponent F⊆Q.stratum (Q.faceLevel F) :=
  connectedComponentIn_subset _ _

lemma faceComponent_eq_of_level_eq (F G : Q.FinalFace) (hFG : F.val⊆G.val)
    (hlevel : Q.faceLevel F=Q.faceLevel G) : Q.faceComponent F=Q.faceComponent G := by
  have hi := Q.faceLevel_le G
  have hz : IsMarked (Q.T 0) (Q.below (Q.faceLevel G)) := by
    unfold below
    split_ifs
    · exact isMarked_empty _
    · exact Q.final_marked _ (by omega)
  have hP : convexHull ℝ (G.val : Set V)⊆Q.Z (Q.faceLevel G) :=
    (Q.hull_mem_iff_level_le G hi).mpr le_rfl
  have hFZ : vertexMean F.val∉Q.below (Q.faceLevel G) :=
    hlevel ▸ (Q.mean_mem_stratum F).2
  exact (by
    unfold faceComponent
    rw [hlevel]
    exact vertexMean_components_eq (Q.T 0) hz F.property G.property hFG hP hFZ
      (Q.mean_mem_stratum G).2)

lemma final_face_card_le_level (hK : ∀ F∈K.faces,F.card≤n+1) (F : Q.FinalFace) :
    F.val.card≤Q.faceLevel F+1 := by
  obtain ⟨S,hS⟩ := Q.refines (Nat.zero_le (Q.faceLevel F)) (Q.faceLevel_le F)
  obtain ⟨T,hT,hTZ,hFT⟩ := S.carrier_marked (Q.marked _ (Q.faceLevel_le F))
    (hS.symm ▸ F.property)
    ((Q.hull_mem_iff_level_le F (Q.faceLevel_le F)).mpr le_rfl)
  have hc := (Q.T 0).indep F.property |>.card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (hFT.trans (convexHull_subset_affineSpan _)))
  exact hc.trans (Q.dimension_bound hK (Q.faceLevel_le F) hT hTZ)

end PointFiltration

end Sparse.Cuts

namespace Sparse

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)

variable (hK : ∀ s∈K.faces,s.card≤n+1)

include hK in
lemma zero_support_top (x : X) {v : Y →₀ ℝ}
    (hv : v∈(Q.pair 0).P.val x) : v.support∈K.faces ∧ v.support.card=n+1 := by
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    ((Q.pair 0).T.val x).space_eq ▸ ((Q.pair 0).P.marked x).subset_space hv
  let p := GraphGeometry.pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := GraphGeometry.pointProbability_coeff K _
  have hs : v.support∈K.faces := hp ▸ GraphGeometry.pointProbability_face K ⟨v,hvK⟩
  have hf : simplexVertices v.support∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces := ⟨_,hs,rfl⟩
  have hmem : v∈convexHull ℝ (simplexVertices v.support : Set (Y →₀ ℝ)) := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex]
  have hl := (Q.point x).card_lower_of_mem_zero (i := n) le_rfl hv
    (show simplexVertices v.support∈((Q.point x).T n).faces by
      change _∈((Q.pair n).T.val x).complex.faces
      rw [Q.top]; exact hf)
    (show convexHull ℝ (simplexVertices v.support : Set (Y →₀ ℝ))⊆(Q.point x).Z n by
      change _⊆(Q.pair n).P.val x
      rw [Q.top_space]
      exact (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space hf) hmem
  exact ⟨hs,le_antisymm (hK _ hs) (hl.trans Finset.card_image_le)⟩

include hK in
lemma zero_isDiscrete (x : X) : IsDiscrete ((Q.pair 0).P.val x) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro p hp
  let σ : SourceTop K n := ⟨p.support,zero_support_top Q hK x hp⟩
  let U : Set (Y →₀ ℝ) := ⋂ y : p.support,{q | q y.val≠0}
  have hU : IsOpen U := isOpen_iInter_of_finite fun y=>isOpen_ne.preimage
    (coordinateCLM y.val).continuous
  have hpU : p∈U := Set.mem_iInter.mpr fun y=>Finsupp.mem_support_iff.mp y.property
  let A := (Q.pair 0).P.val x∩convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))
  have hA : A.Finite := zero_inter_simplex_finite Q hK σ x
  have hsub : U∩(Q.pair 0).P.val x⊆A := by
    rintro q ⟨hqU,hq⟩
    have hs : p.support⊆q.support := fun y hy=>Finsupp.mem_support_iff.mpr
      (Set.mem_iInter.mp hqU ⟨y,hy⟩)
    have he : p.support=q.support := Finset.eq_of_subset_of_card_le hs (by
      rw [(zero_support_top Q hK x hp).2,(zero_support_top Q hK x hq).2])
    have hqK : q∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
      ((Q.pair 0).T.val x).space_eq ▸ ((Q.pair 0).P.marked x).subset_space hq
    let r := GraphGeometry.pointProbability K ⟨q,hqK⟩
    refine ⟨hq,?_⟩
    change q∈convexHull ℝ (simplexVertices p.support : Set (Y →₀ ℝ))
    rw [show q=r.coeff from (GraphGeometry.pointProbability_coeff K ⟨q,hqK⟩).symm,
      simplexVertices,Finset.coe_image,r.mem_geometric_simplex]
    rw [GraphGeometry.pointProbability_coeff K ⟨q,hqK⟩]
    exact he.symm.subset
  refine ⟨U\(A\{p}),hU.sdiff (hA.sdiff.isClosed),?_⟩
  ext q
  constructor
  · rintro ⟨⟨hqu,hqa⟩,hq⟩
    by_contra hne
    exact hqa ⟨hsub ⟨hqu,hq⟩,hne⟩
  · intro hq
    have he : q=p := hq
    subst q
    exact ⟨⟨hpU,fun h=>h.2 rfl⟩,hp⟩

include hK in
lemma zero_component_subsingleton (x : X) (p : Y →₀ ℝ) :
    (connectedComponentIn ((Q.pair 0).P.val x) p).Subsingleton :=
  (isPreconnected_connectedComponentIn).isDiscrete_iff_subsingleton.mp
    ((zero_isDiscrete Q hK x).mono (connectedComponentIn_subset _ _))

end Sparse

namespace Sparse.GraphGeometry

open Set Finset

open Cuts.PointFiltration

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) (realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

omit [DecidableEq Y] [Γ.LocallyFinite] in
include hK in
lemma original_card_bound : ∀ s∈K.faces,s.card≤n+1 := by
  intro s hs
  obtain ⟨σ,_,hst,hc,_⟩ := hK s hs
  exact (Finset.card_le_card hst).trans_eq hc

omit [Γ.LocallyFinite] in
lemma faceComponent_mem_space (x : X) (F : (Q.point x).FinalFace)
    {p : Y →₀ ℝ} (hp : p∈(Q.point x).faceComponent F) :
    p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  have hh := ((Q.point x).faceComponent_subset F hp).1
  have htop := (Q.point x).subset ((Q.point x).faceLevel_le F) le_rfl hh
  exact (Q.top_space x) ▸ htop

omit [Γ.LocallyFinite] in
include hK in
lemma faceComponent_distance (hR : 0≤R) (x : X) (F : (Q.point x).FinalFace)
    {p q : Y →₀ ℝ} (hp : p∈(Q.point x).faceComponent F)
    (hq : q∈(Q.point x).faceComponent F) :
    realizationDistance Γ hΓ K n p q≤2*R := by
  by_cases hz : (Q.point x).faceLevel F=0
  · have he : (Q.point x).faceComponent F=
        connectedComponentIn ((Q.pair 0).P.val x) (Cuts.vertexMean F.val) := by
      simp only [faceComponent,hz,stratum,below,ite_true,Set.sdiff_empty]
      rfl
    have heq : p=q := (zero_component_subsingleton Q (original_card_bound Γ hK) x _) (he ▸ hp) (he ▸ hq)
    subst q
    have hr : realizationDistance Γ hΓ K n p p=0 := by
      simp [realizationDistance,FinProbability.rho,FinProbability.transport_self]
    rw [hr]
    positivity
  · have hi : (Q.point x).faceLevel F-1<n := by
      have := (Q.point x).faceLevel_le F
      omega
    apply Q.diameter _ hi x ((Q.point x).faceComponent F)
      (isPreconnected_connectedComponentIn) ?_ p hp q hq
    have he : (Q.point x).stratum ((Q.point x).faceLevel F)=
        (Q.pair ((Q.point x).faceLevel F-1+1)).P.val x\
          (Q.pair ((Q.point x).faceLevel F-1)).P.val x := by
      have hi' : (Q.point x).faceLevel F-1+1=(Q.point x).faceLevel F := by omega
      rw [hi']
      simp only [stratum,below,ite_eq_right hz]
      rfl
    exact he ▸ (Q.point x).faceComponent_subset F

def labelWindow (n : ℕ) (R : ℝ) (s : Finset Y) : Finset Y :=
  s.biUnion (neighborhood Γ (⌊(2*R)*Real.sqrt (n : ℝ)⌋₊+n))

include hK in
lemma component_support_subset (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) (s : Finset Y)
    (hFs : Cuts.vertexMean F.val∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))
    {v : Y →₀ ℝ} (hv : v∈(Q.point x).faceComponent F) :
    v.support⊆labelWindow Γ n R s := by
  let p := pointProbability K ⟨Cuts.vertexMean F.val,
    faceComponent_mem_space Γ hΓ Q x F ((Q.point x).mean_mem_component F)⟩
  let q := pointProbability K ⟨v,faceComponent_mem_space Γ hΓ Q x F hv⟩
  have hp : p.coeff=Cuts.vertexMean F.val := pointProbability_coeff K _
  have hq : q.coeff=v := pointProbability_coeff K _
  obtain ⟨τ,hτ,hqτ,hcard,hconn⟩ := hK q.coeff.support (pointProbability_face K _)
  have hdist : @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n p q≤2*R := by
    rw [← realizationDistance_apply Γ hΓ K n p q (pointProbability_face K _) (pointProbability_face K _),hp,hq]
    exact faceComponent_distance Γ hΓ Q hK hR x F ((Q.point x).mean_mem_component F) hv
  have hmem := meeting_simplex_vertices Γ hΓ hn p q τ hcard hconn hqτ (2*R)
    (by positivity) hdist
  have hps : p.coeff.support⊆s := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex] at hFs
    exact hFs
  rw [← hq]
  exact hqτ.trans (hmem.trans (Finset.biUnion_subset_biUnion_of_subset_left _ hps))

end Sparse.GraphGeometry

namespace Sparse

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*}

def supportVertices (U : Set (Y →₀ ℝ)) : Set Y :=
  {y | ∃p∈U,y∈p.support}

lemma supportVertices_mono {U V : Set (Y →₀ ℝ)} (h : U⊆V) :
    supportVertices U⊆supportVertices V := by
  rintro y ⟨p,hp,hy⟩
  exact ⟨p,h hp,hy⟩

variable {H X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hK in
lemma componentSupport_subset (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) (s : Finset Y)
    (hFs : Cuts.vertexMean F.val∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    supportVertices ((Q.point x).faceComponent F)⊆
      (GraphGeometry.labelWindow Γ n R s : Set Y) := by
  rintro y ⟨p,hp,hy⟩
  exact GraphGeometry.component_support_subset Γ hΓ Q hK hn hR x F s hFs hp hy

include hK in
lemma componentSupport_finite (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) :
    (supportVertices ((Q.point x).faceComponent F)).Finite := by
  have hmK := GraphGeometry.faceComponent_mem_space Γ hΓ Q x F ((Q.point x).mean_mem_component F)
  let p := GraphGeometry.pointProbability K ⟨Cuts.vertexMean F.val,hmK⟩
  have hp : p.coeff=Cuts.vertexMean F.val := GraphGeometry.pointProbability_coeff K _
  have hms : Cuts.vertexMean F.val∈convexHull ℝ
      (simplexVertices p.coeff.support : Set (Y →₀ ℝ)) := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex]
  exact (Finset.finite_toSet (GraphGeometry.labelWindow Γ n R p.coeff.support)).subset
    (componentSupport_subset Γ hΓ Q hK hn hR x F p.coeff.support hms)

omit [Γ.LocallyFinite] in
lemma componentSupport_nonempty (x : X) (F : (Q.point x).FinalFace) :
    (supportVertices ((Q.point x).faceComponent F)).Nonempty := by
  let p := GraphGeometry.pointProbability K ⟨Cuts.vertexMean F.val,
    GraphGeometry.faceComponent_mem_space Γ hΓ Q x F ((Q.point x).mean_mem_component F)⟩
  have hp := p.coeff_support_nonempty
  obtain ⟨y,hy⟩ := hp
  refine ⟨y,Cuts.vertexMean F.val,(Q.point x).mean_mem_component F,?_⟩
  have he : p.coeff=Cuts.vertexMean F.val := GraphGeometry.pointProbability_coeff K _
  exact he ▸ hy

end Sparse

end BassTrace

end

end OAI
