import OAI.RingTheory.BassTrace.VolumeBounds

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

def ballIntegrand
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (c : FinProbability Y) (t : ℝ) (x : X) : ℝ≥0∞ :=
  ∑' σ : SourceTop K n,localOriginalArea Γ Q σ j
    {v | centerDistance Γ hΓ K n c v≤t} x

omit [Γ.LocallyFinite] in
lemma localOriginalArea_eq_zero_of_not_mem_localTops
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (c : FinProbability Y) (b : ℝ) (σ : SourceTop K n)
    (hσ : σ∉localTops (K := K) (n := n) Γ hΓ c b) (x : X) :
    localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x=0 := by
  rw [localOriginalArea_eq_measure]
  have he : (Q.P.val x∩sourceInterior σ.val)∩{v | centerDistance Γ hΓ K n c v≤b}=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro v ⟨⟨_,hv⟩,hr⟩
    exact hσ ⟨v,hv,hr⟩
  rw [he,measure_empty]

include hn hK in
lemma ballIntegrand_locallyConstant
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (c : FinProbability Y) (b : ℝ) (hb : 0≤b) :
    IsLocallyConstant (ballIntegrand (n := n) Γ hΓ Q j c b) := by
  let F := (localTops_finite Γ hΓ hn hK c b hb).toFinset
  have he (x : X) : ballIntegrand (n := n) Γ hΓ Q j c b x =
      ∑ σ∈F,localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x := by
    apply tsum_eq_sum
    intro σ hσ
    exact localOriginalArea_eq_zero_of_not_mem_localTops Γ hΓ Q j c b σ
      (fun h=>hσ ((localTops_finite Γ hΓ hn hK c b hb).mem_toFinset.mpr h)) x
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hall : ∀ᶠ y in nhds x,∀ σ∈F,
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} y=
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x :=
    F.eventually_all.mpr fun σ _=>(localOriginalArea_locallyConstant Γ Q σ j _).eventually_eq x
  filter_upwards [hall] with y hy
  rw [he,he]
  exact Finset.sum_congr rfl hy

omit [Γ.LocallyFinite] in
include hK in
lemma localOriginalArea_zero_eq_count
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (W : Set (Y →₀ ℝ)) (x : X) :
    localOriginalArea Γ Q σ 0 W x = Measure.count
      (simplexCoordinates σ.val σ.property.2 '' (Q.P.val x∩(sourceInterior σ.val∩W))) := by
  apply simplexArea_zero _ (simplexGraph_connected Γ σ.val σ.property.2 (sourceTop_connected Γ hK σ))
  rintro _ ⟨v,⟨_,hv,_⟩,rfl⟩
  exact simplexCoordinates_sum _ _ (intrinsicInterior_subset hv)

omit [Γ.LocallyFinite] in
include hK in
lemma one_le_ballIntegrand_of_ne_zero
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (c : FinProbability Y) (b : ℝ) (x : X)
    (hx : ballIntegrand (n := n) Γ hΓ Q 0 c b x≠0) :
    1≤ballIntegrand (n := n) Γ hΓ Q 0 c b x := by
  have hex : ∃ σ : SourceTop K n,
      localOriginalArea Γ Q σ 0 {v | centerDistance Γ hΓ K n c v≤b} x≠0 := by
    by_contra! h
    exact hx (by simp only [ballIntegrand,h,tsum_zero])
  obtain ⟨σ,hσ⟩ := hex
  rw [localOriginalArea_zero_eq_count Γ hK] at hσ
  obtain ⟨v,hv⟩ := Measure.count_ne_zero_iff.mp hσ
  calc
    _ = Measure.count ({v} : Set (Fin (n+1) → ℝ)) := (Measure.count_singleton v).symm
    _ ≤ _ := measure_mono (singleton_subset_iff.mpr hv)
    _ = localOriginalArea Γ Q σ 0 {v | centerDistance Γ hΓ K n c v≤b} x :=
      (localOriginalArea_zero_eq_count Γ hK Q σ _ x).symm
    _ ≤ _ := ENNReal.le_tsum (f := fun τ : SourceTop K n =>
      localOriginalArea Γ Q τ 0 {v | centerDistance Γ hΓ K n c v≤b} x) σ

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
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

include hi hn hK hΓaut in

theorem zero_ball_mass_bound (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    (c : FinProbability Y) (hc : c.coeff.support.card≤n+1) (A : Set X) (hA : IsClopen A)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow A (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow A (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)))
    (r : ℝ) (hr : 0≤r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hmargin : ballVolumeBound D n R<dividedPower n (R-r)) :
    (ballMass (n := n) Γ hΓ (Q.pair 0) μ A 0 c r).toReal ≤
      slicingError n (R-r)/(dividedPower n (R-r)-ballVolumeBound D n R)*ε := by
  let f := ballIntegrand (n := n) Γ hΓ (Q.pair 0) 0 c r
  let S : Set X := {x | f x≠0}
  have hS : IsClopen S :=
    (ballIntegrand_locallyConstant Γ hΓ hn hK (Q.pair 0) 0 c r hr).isClopen_fiber 0 |>.compl
  let B := A∩S
  have hB : IsClopen B := hA.inter hS
  have hwin (h : H) (x : X) : activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x ⊆
      activeWindow A (ballWindow K Γ hΓ (n := n) c (Iic R)) h x := by
    unfold activeWindow
    split_ifs with hb ha
    · exact subset_rfl
    · exact False.elim (ha hb.1)
    · exact empty_subset _
    · exact subset_rfl
  have hdisjB x : Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)) :=
    fun h k hk=>(hdisj x hk).mono (hwin h x) (hwin k x)
  have he : ballMass (n := n) Γ hΓ (Q.pair 0) μ B 0 c r =
      ballMass (n := n) Γ hΓ (Q.pair 0) μ A 0 c r := by
    have hh := setLIntegral_eq_of_support_subset (μ := μ.restrict A) (s := S) (f := f)
      (show Function.support f⊆S from subset_rfl)
    rw [Measure.restrict_restrict hS.isClosed.measurableSet,inter_comm] at hh
    exact hh
  have hμle : μ B≤ballMass (n := n) Γ hΓ (Q.pair 0) μ B 0 c r := by
    calc
      _ = ∫⁻ _x in B,(1 : ℝ≥0∞) ∂μ := by simp
      _ ≤ _ := setLIntegral_mono' hB.isClosed.measurableSet fun x hx=>
        one_le_ballIntegrand_of_ne_zero Γ hΓ hK (Q.pair 0) c r x hx.2
  have hdim x t (ht : t∈((Q.pair 0).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair 0).P.val x) : t.card≤0+1 := by
    apply (Q.point x).dimension_bound _ (Nat.zero_le n) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hf := ballMass_lt_top Γ hΓ hn hK (Q.pair 0) μ B 0 hdim c r hr
  have hμle' := ENNReal.toReal_mono hf.ne hμle
  have hv := iterated_ball_volume Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin c hc
    B hB hdisjB r hr hrR D hD hdeg
  rw [he] at hμle' hv
  exact absorb_nonempty_probability _ _ _ _ _ _ hmargin
    (by unfold ballVolumeBound; positivity) hμle' hv

end Sparse.GraphGeometry

/-! Finite clopen partitions and disjoint translates. -/

namespace Sparse

section

open Set TopologicalSpace

open scoped Pointwise Function

variable {H X : Type*} [Group H] [TopologicalSpace X] [MulAction H X]

lemma exists_clopen_disjoint_translate
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (x : X) (g : H) (hg : g ≠ 1) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ Disjoint U (g • U) := by
  have hne : x ≠ g • x := by
    intro h
    exact hg (IsCancelSMul.eq_one_of_smul h.symm)
  obtain ⟨V, hV, hx, hgx⟩ := exists_isClopen_of_totally_separated hne
  refine ⟨V ∩ (fun y : X => g • y) ⁻¹' Vᶜ,
    hV.inter (hV.compl.preimage (continuous_const_smul g)), ⟨hx, hgx⟩, ?_⟩
  apply Set.disjoint_left.mpr
  intro y hy hgy
  obtain ⟨z, hz, rfl⟩ := hgy
  exact hz.2 hy.1

lemma exists_clopen_disjoint_translates
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (x : X) (s : Finset H) (hs : 1 ∉ s) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ ∀ g ∈ s, Disjoint U (g • U) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Set.univ, isClopen_univ, Set.mem_univ _, by simp⟩
  | @insert g s hgs ih =>
      have hgone : g ≠ 1 := by
        intro hg
        exact hs (by simp [hg])
      obtain ⟨U, hU, hxU, hUD⟩ := ih (fun h => hs (Finset.mem_insert_of_mem h))
      obtain ⟨V, hV, hxV, hVD⟩ := exists_clopen_disjoint_translate x g hgone
      refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hVD.mono Set.inter_subset_right (Set.smul_set_mono Set.inter_subset_right)
      · exact (hUD k hk).mono Set.inter_subset_left
          (Set.smul_set_mono Set.inter_subset_left)

theorem exists_separated_clopen_partition
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (s : Finset H) (hs : 1 ∉ s) :
    ∃ (n : ℕ) (W : Fin n → Clopens X),
      (Set.univ : Set X) ⊆ ⋃ j, (W j : Set X) ∧
      Pairwise (Disjoint on W) ∧
      ∀ j g, g ∈ s → Disjoint (W j : Set X) (g • (W j : Set X)) := by
  classical
  choose U hU hx hD using fun x : X => exists_clopen_disjoint_translates x s hs
  let V : X → Opens X := fun x => ⟨U x, (hU x).isOpen⟩
  have hcover : IsOpenCover V := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨n, W, hWsub, hWcover, hWdisj⟩ :=
    hcover.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, W, hWcover, hWdisj, ?_⟩
  intro j g hg
  obtain ⟨x, hjx⟩ := (hWsub j).2
  exact (hD x g hg).mono hjx (Set.smul_set_mono hjx)

omit [TopologicalSpace X] in

theorem pairwise_disjoint_product_translates {Y : Type*} [MulAction H Y]
    (A : Set X) (U : Set Y) (s : Set H)
    (hcollision : ∀ g, g ≠ 1 → ¬ Disjoint U (g • U) → g ∈ s)
    (hsep : ∀ g ∈ s, Disjoint A (g • A)) :
    Pairwise (fun h k : H => Disjoint ((h • A) ×ˢ (h • U))
      ((k • A) ×ˢ (k • U))) := by
  intro h k hne
  have hdiff : h⁻¹ * k ≠ 1 := by
    intro hc
    exact hne (inv_mul_eq_one.mp hc)
  by_cases hc : Disjoint U ((h⁻¹ * k) • U)
  · have hd : Disjoint (h • U) (k • U) := by
      rw [Set.disjoint_smul_set_left, ← mul_smul]
      exact hc
    exact hd.set_prod_right _ _
  · have hd : Disjoint (h • A) (k • A) := by
      rw [Set.disjoint_smul_set_left, ← mul_smul]
      exact hsep _ (hcollision _ hdiff hc)
    exact hd.set_prod_left _ _

end

open Set Finset

open scoped Pointwise Classical

variable {H Y : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]

lemma finite_push_collisions (W : Finset Y) (U : Set (Y →₀ ℝ))
    (hU : ∀ p∈U,p≠0 ∧ p.support⊆W) :
    {h : H | ¬Disjoint U (OrbitForms.push h '' U)}.Finite := by
  have hf : (⋃ w∈(W : Set Y),{h : H | h•w∈W}).Finite := by
    apply W.finite_toSet.biUnion
    intro w _
    exact Set.Finite.preimage (fun h _ k _ he=>IsCancelSMul.right_cancel h k w he)
      W.finite_toSet
  apply hf.subset
  intro h hh
  obtain ⟨p,hp,q,hq,he⟩ := Set.not_disjoint_iff.mp hh
  obtain ⟨w,hw⟩ := Finsupp.support_nonempty_iff.mpr (hU q hq).1
  apply Set.mem_iUnion₂.mpr
  refine ⟨w,(hU q hq).2 hw,?_⟩
  apply (hU p hp).2
  rw [Finsupp.mem_support_iff,← he,OrbitForms.push_apply,inv_smul_smul]
  exact Finsupp.mem_support_iff.mp hw

variable {X : Type*} [TopologicalSpace X] [MulAction H X]

omit [IsCancelSMul H Y] [TopologicalSpace X] in
lemma activeWindows_disjoint (A : Set X) (U : Set (Y →₀ ℝ))
    (hA : ∀ g : H,g≠1 → ¬Disjoint U (OrbitForms.push g '' U) →
      Disjoint A (g•A)) :
    ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow A U h x) (activeWindow A U k x)) := by
  intro x h k hne
  by_cases hh : h⁻¹•x∈A
  · by_cases hk : k⁻¹•x∈A
    · simp only [activeWindow,hh,hk,ite_eq_left]
      apply Set.disjoint_left.mpr
      rintro p ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
      have hd : h⁻¹*k≠1 := fun he=>hne (inv_mul_eq_one.mp he)
      have hc : ¬Disjoint U (OrbitForms.push (h⁻¹*k) '' U) := by
        apply Set.not_disjoint_iff.mpr
        refine ⟨u,hu,v,hv,?_⟩
        rw [OrbitForms.push_mul,he,OrbitForms.push_inv_push]
      have ha := Set.disjoint_left.mp (hA _ hd hc) hh
      apply ha
      refine ⟨k⁻¹•x,hk,?_⟩
      simp [mul_smul]
    · simp [activeWindow,hk]
  · simp [activeWindow,hh]

-- no instance assumptions on properness of ambient action are needed

lemma exists_disjoint_active_partition
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (W : Finset Y) (U : Set (Y →₀ ℝ))
    (hU : ∀ p∈U,p≠0 ∧ p.support⊆W) :
    ∃ (m : ℕ) (A : Fin m → TopologicalSpace.Clopens X),
      (univ : Set X)⊆⋃ i,(A i : Set X) ∧
      Pairwise (fun i j=>Disjoint (A i : Set X) (A j : Set X)) ∧
      ∀ i x,Pairwise (fun h k : H=>Disjoint
        (activeWindow (A i : Set X) U h x) (activeWindow (A i : Set X) U k x)) := by
  let S := (show ({h : H | ¬Disjoint U (OrbitForms.push h '' U)} \ {1}).Finite from
    (finite_push_collisions W U hU).sdiff).toFinset
  have hS : 1∉S := by simp [S]
  obtain ⟨m,A,hcover,hdisj,hsep⟩ := exists_separated_clopen_partition (X := X) S hS
  refine ⟨m,A,hcover,?_,?_⟩
  · exact fun i j hij=>TopologicalSpace.Clopens.coe_disjoint.mpr (hdisj hij)
  · intro i
    apply activeWindows_disjoint
    intro g hg hc
    exact hsep i g (by simp [S,hg,hc])

end Sparse

namespace Sparse.GraphGeometry

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hn hK in
lemma exists_disjoint_ball_partition (c : FinProbability Y) {R : ℝ} (hR : 0≤R) :
    ∃ (m : ℕ) (A : Fin m → TopologicalSpace.Clopens X),
      (univ : Set X)⊆⋃ i,(A i : Set X) ∧
      Pairwise (fun i j=>Disjoint (A i : Set X) (A j : Set X)) ∧
      ∀ i x,Pairwise (fun h k : H=>Disjoint
        (activeWindow (A i : Set X) (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
        (activeWindow (A i : Set X) (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)) := by
  apply exists_disjoint_active_partition (ballSupport Γ c n R)
  rintro v ⟨hv,hball⟩
  let p := pointProbability K ⟨v,hv⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hpK := pointProbability_face K ⟨v,hv⟩
  change centerDistance Γ hΓ K n c v≤R at hball
  rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at hball
  rw [← hp]
  exact ⟨Finsupp.support_nonempty_iff.mp p.coeff_support_nonempty,
    ballSupport_contains Γ hΓ hn K hK c p hpK hR hball⟩

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
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

include hi hn hK hΓaut in

theorem global_zero_ball_mass_bound (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R : ℝ} (hR : 0<R) (c : FinProbability Y) (hc : c.coeff.support.card≤n+1)
    (r : ℝ) (hr : 0≤r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hmargin : ballVolumeBound D n R<dividedPower n (R-r)) :
    ∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) R n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) R
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c r).toReal≤C*ε := by
  obtain ⟨m,A,hcover,hdisj,hactive⟩ := exists_disjoint_ball_partition (H := H) (X := X) Γ hΓ hn hK c hR.le
  let C := slicingError n (R-r)/(dividedPower n (R-r)-ballVolumeBound D n R)
  have hC : 0≤C := by
    apply div_nonneg _ (sub_pos.mpr hmargin).le
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr hrR) _) (Nat.cast_nonneg _)
  refine ⟨m*C,mul_nonneg (Nat.cast_nonneg _) hC,?_⟩
  intro ε hε Q hmin
  have hdim x t (ht : t∈((Q.pair 0).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair 0).P.val x) : t.card≤0+1 := by
    apply (Q.point x).dimension_bound _ (Nat.zero_le n) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hu : (⋃ i,(A i : Set X))=univ := Set.eq_univ_iff_forall.mpr fun x=>hcover (Set.mem_univ x)
  have he : ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c r=
      ∑ i : Fin m,ballMass (n := n) Γ hΓ (Q.pair 0) μ (A i : Set X) 0 c r := by
    unfold ballMass
    rw [← hu,lintegral_iUnion (fun i=>(A i).isClosed.measurableSet) hdisj,tsum_fintype]
  rw [he,ENNReal.toReal_sum (fun i _=>(ballMass_lt_top Γ hΓ hn hK (Q.pair 0) μ
    (A i : Set X) 0 hdim c r hr).ne)]
  calc
    _ ≤ ∑ _i : Fin m,C*ε := Finset.sum_le_sum fun i _=>
      zero_ball_mass_bound Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin c hc
        (A i : Set X) (A i).isClopen (hactive i) r hr hrR D hD hdeg hmargin
    _ = (m*C)*ε := by simp [mul_assoc]

end

lemma ballVolume_strict_margin (D n : ℕ) (hD : 2≤D) (hn : volumeThreshold D≤n) :
    ballVolumeBound D n (4*(D : ℝ)^2)<
      dividedPower n (4*(D : ℝ)^2-2*(D : ℝ)^2) := by
  have he : 4*(D : ℝ)^2-2*(D : ℝ)^2=2*(D : ℝ)^2 := by ring
  simpa [ballVolumeBound,dividedPower,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,he] using
    strict_volume_margin D n hD hn

end Sparse.GraphGeometry

end BassTrace

end

end OAI
