import OAI.RingTheory.BassTrace.BallReplacement

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open MeasureTheory Set Finset

open scoped ENNReal

def treeAreaMeasure {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) : Measure (Fin (n+1) → ℝ) :=
  Measure.map (treeParam T hT) μHE[j]

lemma treeAreaMeasure_apply {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) (Q : Set (Fin (n+1) → ℝ)) :
    treeAreaMeasure T hT j Q = treeArea T hT j Q :=
  ((continuous_treeParam T hT).measurableEmbedding (treeParam_injective T hT)).map_apply _ _

def simplexAreaMeasure {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (j : ℕ) :
    Measure (Fin (n+1) → ℝ) :=
  (Fintype.card (SpanningTree Γ) : ℝ≥0∞)⁻¹ •
    ∑ T : SpanningTree Γ, treeAreaMeasure T.val T.property.2 j

lemma simplexAreaMeasure_apply {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (j : ℕ)
    (Q : Set (Fin (n+1) → ℝ)) : simplexAreaMeasure Γ j Q = simplexArea Γ j Q := by
  simp only [simplexAreaMeasure,Measure.smul_apply,Measure.finsetSum_apply,
    treeAreaMeasure_apply,smul_eq_mul,simplexArea,div_eq_mul_inv,mul_comm]

lemma simplexArea_union {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (j : ℕ)
    {Q W : Set (Fin (n+1) → ℝ)} (hW : MeasurableSet W) (hdisj : Disjoint Q W) :
    simplexArea Γ j (Q ∪ W) = simplexArea Γ j Q + simplexArea Γ j W := by
  simp_rw [← simplexAreaMeasure_apply]
  exact measure_union hdisj hW

lemma measure_surgery_gain {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (P Z U S : Set E) (hU : MeasurableSet U) :
    μ ((Z \ U) ∪ (P ∩ S)) + μ (Z ∩ U) ≤ μ Z + μ (P ∩ S) := by
  calc
    _ ≤ (μ (Z \ U) + μ (P ∩ S)) + μ (Z ∩ U) :=
      add_le_add_left (measure_union_le _ _) _
    _ = (μ (Z \ U) + μ (Z ∩ U)) + μ (P ∩ S) := by ac_rfl
    _ = _ := by rw [measure_sdiff_add_inter Z hU]

lemma simplexArea_surgery_gain {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (j : ℕ)
    (P Z U S : Set (Fin (n+1) → ℝ)) (hU : MeasurableSet U) :
    simplexArea Γ j ((Z \ U) ∪ (P ∩ S)) + simplexArea Γ j (Z ∩ U) ≤
      simplexArea Γ j Z + simplexArea Γ j (P ∩ S) := by
  simp_rw [← simplexAreaMeasure_apply]
  exact measure_surgery_gain _ _ _ _ _ hU

end

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

section

variable {Y : Type*} [DecidableEq Y]

def simplexEmbed {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] (Y →₀ ℝ) :=
  (Finsupp.lmapDomain ℝ ℝ (fun i => (simplexEnumeration s hs i).val)).comp
    (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).symm.toLinearMap

omit [DecidableEq Y] in
lemma simplexCoordinates_embed {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : simplexCoordinates s hs (simplexEmbed s hs p) = p := by
  ext i
  change (Finsupp.mapDomain (fun i => (simplexEnumeration s hs i).val)
    ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).symm p))
    (simplexEnumeration s hs i).val = p i
  have hi : Function.Injective (fun i => (simplexEnumeration s hs i).val) :=
    Subtype.val_injective.comp (simplexEnumeration s hs).injective
  rw [Finsupp.mapDomain_apply_of_injective hi]
  exact congrFun ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).apply_symm_apply p) i

omit [DecidableEq Y] in
lemma simplexEmbed_support {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : (simplexEmbed s hs p).support ⊆ s := by
  let f : Fin (n+1) ↪ Y := ⟨fun i => (simplexEnumeration s hs i).val,
    Subtype.val_injective.comp (simplexEnumeration s hs).injective⟩
  change (Finsupp.mapDomain f _).support ⊆ s
  rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain]
  intro y hy
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
  exact (simplexEnumeration s hs i).property

lemma simplexEmbed_coordinates {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Y →₀ ℝ} (hp : p.support ⊆ s) :
    simplexEmbed s hs (simplexCoordinates s hs p) = p := by
  let q := simplexEmbed s hs (simplexCoordinates s hs p)
  have hq := simplexEmbed_support s hs (simplexCoordinates s hs p)
  ext y
  by_cases hy : y∈s
  · obtain ⟨i,hi⟩ := (simplexEnumeration s hs).surjective ⟨y,hy⟩
    have h := congrFun (simplexCoordinates_embed s hs (simplexCoordinates s hs p)) i
    change q (simplexEnumeration s hs i).val = p (simplexEnumeration s hs i).val at h
    simpa only [hi] using h
  · exact (Finsupp.notMem_support_iff.mp (fun h => hy (hq h))).trans
      (Finsupp.notMem_support_iff.mp (fun h => hy (hp h))).symm

omit [DecidableEq Y] in
lemma simplexEmbed_injective {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    Function.Injective (simplexEmbed s hs) :=
  Function.HasLeftInverse.injective ⟨simplexCoordinates s hs,simplexCoordinates_embed s hs⟩

lemma simplexEmbed_preimage {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (Q : Set (Y →₀ ℝ)) (hQ : ∀ p∈Q,p.support⊆s) :
    simplexEmbed s hs ⁻¹' Q = simplexCoordinates s hs '' Q := by
  ext p
  constructor
  · intro hp
    exact ⟨simplexEmbed s hs p,hp,simplexCoordinates_embed s hs p⟩
  · rintro ⟨q,hq,rfl⟩
    change simplexEmbed s hs (simplexCoordinates s hs q)∈Q
    rw [simplexEmbed_coordinates s hs (hQ q hq)]
    exact hq

def originalAreaMeasure {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (s : Finset Y) (hs : s.card=n+1) (j : ℕ) :
    @Measure (Y →₀ ℝ) (borel (Y →₀ ℝ)) :=
  @Measure.map _ _ _ (borel (Y →₀ ℝ)) (simplexEmbed s hs) (simplexAreaMeasure Γ j)

lemma originalAreaMeasure_apply {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (s : Finset Y) (hs : s.card=n+1) (j : ℕ)
    (Q : Set (Y →₀ ℝ)) (hQ : ∀ p∈Q,p.support⊆s) :
    originalAreaMeasure Γ s hs j Q = simplexArea Γ j (simplexCoordinates s hs '' Q) := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  unfold originalAreaMeasure
  have he : MeasurableEmbedding (simplexEmbed s hs) :=
    (simplexEmbed s hs).continuous_of_finiteDimensional.measurableEmbedding
      (simplexEmbed_injective s hs)
  rw [he.map_apply, simplexEmbed_preimage s hs Q hQ,simplexAreaMeasure_apply]

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

lemma support_of_mem_sourceInterior (s : Finset Y) {p : Y →₀ ℝ}
    (hp : p∈sourceInterior s) : p.support⊆s := by
  have hh := intrinsicInterior_subset hp
  rw [show (simplexVertices s : Set (Y →₀ ℝ)) =
    (fun y => Finsupp.single y (1 : ℝ)) '' (s : Set Y) from Finset.coe_image] at hh
  rw [convexHull_single_eq_probabilitySet s] at hh
  exact hh.2.2

lemma originalArea_eq_measure {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (x : X) :
    originalArea Γ Q σ j x =
      originalAreaMeasure (simplexGraph Γ σ.val σ.property.2) σ.val σ.property.2 j
      (Q.P.val x ∩ sourceInterior σ.val) := by
  symm
  exact originalAreaMeasure_apply _ _ _ _ _
    (fun p hp => support_of_mem_sourceInterior σ.val hp.2)

end

section

open Finset Set MeasureTheory

variable {n : ℕ}

def relabelCoefficients (e : Equiv.Perm (Fin (n+1))) :
    (Fin (n+1) → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) where
  toFun p := p ∘ e.symm
  invFun p := p ∘ e
  left_inv p := by ext i; simp
  right_inv p := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma sum_relabelCoefficients (e : Equiv.Perm (Fin (n+1))) (p : Fin (n+1) → ℝ) :
    ∑ i, relabelCoefficients e p i = ∑ i,p i := e.symm.sum_comp p

lemma relabelCoefficients_single (e : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
    relabelCoefficients e (Pi.single i 1) = Pi.single (e i) 1 := by
  ext j
  change (Pi.single i 1 : Fin (n+1) → ℝ) (e.symm j) = (Pi.single (e i) 1 : Fin (n+1) → ℝ) j
  simp only [Pi.single_apply]
  by_cases h : e.symm j = i
  · have he : j=e i := by simpa using congrArg e h
    simp [he]
  · have he : j≠e i := fun k => h (by simp [k])
    simp [h,he]

def edgeVector (u v : Fin (n+1)) : Fin (n+1) → ℝ := Pi.single u 1 - Pi.single v 1

lemma sum_edgeVector (u v : Fin (n+1)) : ∑ i, edgeVector u v i = 0 := by
  simp [edgeVector,Pi.sub_apply,Finset.sum_sub_distrib]

lemma relabel_edgeVector (e : Equiv.Perm (Fin (n+1))) (u v : Fin (n+1)) :
    relabelCoefficients e (edgeVector u v) = edgeVector (e u) (e v) := by
  simp only [edgeVector,map_sub,relabelCoefficients_single]

lemma coefficient_ext_total {p q : Fin (n+1) → ℝ}
    (hs : ∑ i,p i = ∑ i,q i) (he : ∀ i : Fin n,p i.succ=q i.succ) : p=q := by
  ext i
  induction i using Fin.cases with
  | zero =>
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ] at hs
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (by rfl : (Finset.univ : Finset (Fin n))=Finset.univ)
      (fun i _ => he i)
    linarith
  | succ i => exact he i

lemma treeParam_difference (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x y : EuclideanSpace ℝ (Fin n)) :
    treeParam T hT x - treeParam T hT y =
      ∑ j, (x.ofLp j-y.ofLp j) • edgeVector
        ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2) := by
  apply coefficient_ext_total
  · simp only [Pi.sub_apply,Finset.sum_sub_distrib]
    rw [show (∑ i,treeParam T hT x i)=1 from sum_barycentricParam _,
      show (∑ i,treeParam T hT y i)=1 from sum_barycentricParam _]
    simp only [sub_self,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,sum_edgeVector,mul_zero,Finset.sum_const_zero]
  · intro i
    simp only [treeParam,barycentricParam,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    change (∑ j, realTreeIncidence T hT i j * x.ofLp j) -
      (∑ j, realTreeIncidence T hT i j * y.ofLp j) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hc : realTreeIncidence T hT i j = edgeVector
        ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2) i.succ := by
      simp [realTreeIncidence,treeIncidence,rootCoordinate,edgeVector,Pi.single_apply]
    rw [hc]
    ring

lemma treeCoordinates_edgeVector (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (j : Fin n) :
    treeCoordinates T hT (edgeVector ((treeEdgeEquiv T hT j).val.out.1)
      ((treeEdgeEquiv T hT j).val.out.2)) = WithLp.toLp 2 (Pi.single j 1) := by
  have hh := treeParam_difference T hT (WithLp.toLp 2 (Pi.single j 1)) 0
  have hh' : treeParam T hT (WithLp.toLp 2 (Pi.single j 1)) - treeParam T hT 0 =
      edgeVector ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2) := by
    simpa only [WithLp.ofLp_zero,Pi.zero_apply,sub_zero,Pi.single_apply,
      ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh
  rw [← hh',map_sub,treeCoordinates_treeParam,treeCoordinates_treeParam,sub_zero]

def treeEdgePermutation (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) : Equiv.Perm (Fin n) :=
  (treeEdgeEquiv T hT).trans (e.mapEdgeSet.trans (treeEdgeEquiv U hU).symm)

lemma mapped_treeEdge_out (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) (j : Fin n) :
    (e ((treeEdgeEquiv T hT j).val.out.1) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1 ∧
     e ((treeEdgeEquiv T hT j).val.out.2) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) ∨
    (e ((treeEdgeEquiv T hT j).val.out.1) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2 ∧
     e ((treeEdgeEquiv T hT j).val.out.2) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1) := by
  apply Sym2.eq_iff.mp
  have ho : s((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1,
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val :=
    (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out_eq
  rw [ho]
  have h : treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j) =
      e.mapEdgeSet (treeEdgeEquiv T hT j) := by simp [treeEdgePermutation]
  rw [h]
  change s(e ((treeEdgeEquiv T hT j).val.out.1),e ((treeEdgeEquiv T hT j).val.out.2)) =
    Sym2.map e ((treeEdgeEquiv T hT j).val)
  have ho' : s((treeEdgeEquiv T hT j).val.out.1,(treeEdgeEquiv T hT j).val.out.2) =
      (treeEdgeEquiv T hT j).val := (treeEdgeEquiv T hT j).val.out_eq
  exact congrArg (Sym2.map e) ho'

lemma exists_treeEdge_signs (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) : ∃ ε : Fin n → ℝ, (∀ j, ε j ^ 2 = 1) ∧ ∀ j,
      relabelCoefficients e.toEquiv (edgeVector ((treeEdgeEquiv T hT j).val.out.1)
        ((treeEdgeEquiv T hT j).val.out.2)) = ε j •
      edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) := by
  classical
  have hh : ∀ j : Fin n, ∃ a : ℝ, a^2=1 ∧
      relabelCoefficients e.toEquiv (edgeVector ((treeEdgeEquiv T hT j).val.out.1)
        ((treeEdgeEquiv T hT j).val.out.2)) = a •
      edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) := by
    intro j
    rw [relabel_edgeVector]
    change ∃ a : ℝ, a^2=1 ∧ edgeVector (e ((treeEdgeEquiv T hT j).val.out.1))
        (e ((treeEdgeEquiv T hT j).val.out.2)) = a •
      edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2)
    rcases mapped_treeEdge_out T U hT hU e j with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · refine ⟨1,by norm_num,?_⟩
      simpa only [one_smul] using congrArg₂ edgeVector h₁ h₂
    · refine ⟨-1,by norm_num,?_⟩
      rw [h₁,h₂]
      simp [edgeVector]
  choose ε hε he using hh
  exact ⟨ε,hε,he⟩

def signedEdgeMap (π : Equiv.Perm (Fin n)) (ε : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun j => ε (π.symm j) * x.ofLp (π.symm j))
  map_add' x y := by ext j; simp [mul_add]
  map_smul' a x := by ext j; simp [mul_left_comm]

lemma signedEdgeMap_isometry (π : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (hε : ∀ j, ε j ^ 2 = 1) : Isometry (signedEdgeMap π ε) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  have hsq : ‖signedEdgeMap π ε x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    change (∑ j, (ε (π.symm j) * x.ofLp (π.symm j)) ^ 2) = ∑ j,x.ofLp j ^ 2
    simp_rw [mul_pow,hε,one_mul]
    exact π.symm.sum_comp (fun j : Fin n => x.ofLp j ^ 2)
  nlinarith [norm_nonneg (signedEdgeMap π ε x),norm_nonneg x]

lemma signedEdgeMap_sum (π : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : signedEdgeMap π ε x =
      ∑ j, (x.ofLp j * ε j) • WithLp.toLp 2 (Pi.single (π j) 1) := by
  ext k
  change ε (π.symm k) * x.ofLp (π.symm k) =
    (∑ j, (x.ofLp j * ε j) • (WithLp.toLp 2 (Pi.single (π j) 1) : EuclideanSpace ℝ (Fin n))).ofLp k
  simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,
    Pi.single_apply]
  rw [Finset.sum_eq_single (π.symm k)]
  · simp [mul_comm]
  · intro j _ hj
    have hne : k ≠ π j := fun he => hj (by simpa using congrArg π.symm he.symm)
    simp [hne]
  · simp

lemma treeTransition_sub (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) (ε : Fin n → ℝ)
    (he : ∀ j, relabelCoefficients e.toEquiv
      (edgeVector ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2)) =
      ε j • edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2))
    (x y : EuclideanSpace ℝ (Fin n)) :
    treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT x)) -
      treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT y)) =
        signedEdgeMap (treeEdgePermutation T U hT hU e) ε (x-y) := by
  rw [← map_sub,← map_sub,treeParam_difference]
  simp_rw [map_sum,map_smul,he,map_smul,treeCoordinates_edgeVector,smul_smul]
  rw [signedEdgeMap_sum]
  rfl

lemma treeTransition_isometry (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) : Isometry (fun x =>
      treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT x))) := by
  obtain ⟨ε,hε,he⟩ := exists_treeEdge_signs T U hT hU e
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm,treeTransition_sub T U hT hU e ε he,map_sub,← dist_eq_norm]
  exact (signedEdgeMap_isometry _ ε hε).dist_eq x y

lemma treeArea_relabel (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) (j : ℕ) (Q : Set (Fin (n+1) → ℝ))
    (hQ : Q ⊆ {p | ∑ i,p i=1}) :
    treeArea U hU j (relabelCoefficients e.toEquiv '' Q) = treeArea T hT j Q := by
  have hQ' : relabelCoefficients e.toEquiv '' Q ⊆ {p | ∑ i,p i=1} := by
    rintro _ ⟨p,hp,rfl⟩
    simpa only [Set.mem_ofPred_eq,sum_relabelCoefficients] using hQ hp
  unfold treeArea
  rw [treeParam_preimage_eq_image U hU _ hQ']
  have hset : treeCoordinates U hU '' (relabelCoefficients e.toEquiv '' Q) =
      (fun x => treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT x))) ''
        (treeParam T hT ⁻¹' Q) := by
    ext z
    constructor
    · rintro ⟨_,⟨p,hp,rfl⟩,rfl⟩
      refine ⟨treeCoordinates T hT p,?_,?_⟩
      · simpa only [Set.mem_preimage,treeParam_treeCoordinates T hT p (hQ hp)] using hp
      · change treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT (treeCoordinates T hT p))) = _
        rw [treeParam_treeCoordinates T hT p (hQ hp)]
    · rintro ⟨x,hx,rfl⟩
      exact ⟨_,⟨treeParam T hT x,hx,rfl⟩,rfl⟩
  rw [hset]
  exact (treeTransition_isometry T U hT hU e).euclideanHausdorffMeasure_image _

end

open MeasureTheory Set Finset

open scoped ENNReal

variable {n : ℕ}

def spanningTreeRelabel (Γ : SimpleGraph (Fin (n+1))) (e : Equiv.Perm (Fin (n+1))) :
    SpanningTree Γ ≃ SpanningTree (e.simpleGraph Γ) :=
  Equiv.subtypeEquiv e.simpleGraph (fun T => by
    constructor
    · rintro ⟨hle,ht⟩
      exact ⟨fun _ _ h => hle h, ((SimpleGraph.Iso.comap e.symm T).isTree_iff).mpr ht⟩
    · rintro ⟨hle,ht⟩
      refine ⟨?_,((SimpleGraph.Iso.comap e.symm T).isTree_iff).mp ht⟩
      intro v w hvw
      have h := hle (show (e.simpleGraph T).Adj (e v) (e w) by simpa using hvw)
      simpa using h)

lemma simplexArea_relabel (Γ : SimpleGraph (Fin (n+1)))
    (e : Equiv.Perm (Fin (n+1))) (j : ℕ) (Q : Set (Fin (n+1) → ℝ))
    (hQ : Q ⊆ {p | ∑ i,p i=1}) :
    simplexArea (e.simpleGraph Γ) j (relabelCoefficients e '' Q) = simplexArea Γ j Q := by
  unfold simplexArea
  rw [← Fintype.card_congr (spanningTreeRelabel Γ e)]
  congr 1
  rw [← (spanningTreeRelabel Γ e).sum_comp]
  apply Finset.sum_congr rfl
  intro T _
  exact treeArea_relabel T.val (e.simpleGraph T.val) T.property.2
    (spanningTreeRelabel Γ e T).property.2 (SimpleGraph.Iso.comap e.symm T.val).symm j Q hQ

end BassTrace.Sparse

end

end OAI
