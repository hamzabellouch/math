import OAI.RingTheory.BassTrace.BallComparison

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

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

theorem ballMass_recurrence (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    {j : ℕ} (hj : j<n) (c : FinProbability Y) (B : Set X) (hB : IsClopen B)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)))
    (r b : ℝ) (hr : 0≤r) (hb : b≤R) :
    (∫⁻ t in Ioo r b,ballMass (n := n) Γ hΓ (Q.pair j) μ B j c t) ≤
      ballMass (n := n) Γ hΓ (Q.pair (j+1)) μ B (j+1) c b +
        ENNReal.ofReal ε * ENNReal.ofReal (b-r) := by
  have hcomp := ae_open_ball_comparison Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin hj c B hB hdisj
  have heq := ae_local_ball_closed_eq_open Γ hΓ hn hK (Q.pair j) j c
  have hlocal : ∀ᵐ t ∂volume.restrict (Ioo r b),
      ballMass (n := n) Γ hΓ (Q.pair j) μ B j c t ≤
      (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ (Q.pair (j+1)) σ j
        {v | centerDistance Γ hΓ K n c v=t} x ∂μ)+ENNReal.ofReal ε := by
    filter_upwards [ae_restrict_of_ae hcomp,ae_restrict_of_ae heq,
      ae_restrict_mem measurableSet_Ioo] with t ht he htb
    have hc := ht (hr.trans_lt htb.1) (htb.2.le.trans hb)
    simpa only [ballMass,he] using hc
  have hdim : ∀ x t,t∈((Q.pair (j+1)).T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair (j+1)).P.val x → t.card≤j+1+1 := by
    intro x t ht htp
    apply (Q.point x).dimension_bound _ (by omega) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,hτ,hst,hcard,-⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hco := integrated_marked_ball_coarea Γ hΓ (Q.pair (j+1)) μ B c hn
    (j+1) (by omega) hdim r b
  simp only [Nat.add_sub_cancel] at hco
  calc
    _ ≤ ∫⁻ t in Ioo r b, (∫⁻ x in B,∑' σ : SourceTop K n,
          localOriginalArea Γ (Q.pair (j+1)) σ j
            {v | centerDistance Γ hΓ K n c v=t} x ∂μ)+ENNReal.ofReal ε :=
      lintegral_mono_ae hlocal
    _ = (∫⁻ t in Ioo r b, ∫⁻ x in B,∑' σ : SourceTop K n,
          localOriginalArea Γ (Q.pair (j+1)) σ j
            {v | centerDistance Γ hΓ K n c v=t} x ∂μ) +
        ENNReal.ofReal ε * ENNReal.ofReal (b-r) := by
      rw [lintegral_add_right _ measurable_const,lintegral_const,
        Measure.restrict_apply_univ,Real.volume_Ioo]
    _ ≤ _ := add_le_add hco le_rfl

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

def localTops (c : FinProbability Y) (b : ℝ) : Set (SourceTop K n) :=
  {σ | (sourceInterior σ.val∩{v | centerDistance Γ hΓ K n c v≤b}).Nonempty}

include hn hK in
lemma localTops_finite (c : FinProbability Y) (b : ℝ) (hb : 0≤b) :
    (localTops (K := K) (n := n) Γ hΓ c b).Finite := by
  have hconn (σ : Finset Y) (hs : σ∈K.faces ∧ σ.card=n+1) :
      (Γ.induce (σ : Set Y)).Connected := by
    obtain ⟨τ,hτ,hστ,hcard,hct⟩ := hK σ hs.1
    have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,hs.2])
    exact he.symm ▸ hct
  have hfin := finitely_many_meeting_top_simplices Γ hΓ hn
    {σ : Finset Y | σ∈K.faces ∧ σ.card=n+1} (fun σ hs=>⟨hs.2,hconn σ hs⟩) c b hb
  apply (hfin.preimage (show Function.Injective (fun σ : SourceTop K n=>σ.val) from Subtype.val_injective).injOn).subset
  rintro σ ⟨v,hv,hvb⟩
  refine ⟨σ.property,?_⟩
  have hvK := (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
    (show simplexVertices σ.val∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces from
      ⟨σ.val,σ.property.1,rfl⟩) (intrinsicInterior_subset hv)
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K ⟨v,hvK⟩
  refine ⟨p,?_,?_⟩
  · rw [hp]
    exact support_of_mem_sourceInterior σ.val hv
  · rw [← centerDistance_apply Γ hΓ K n c p (pointProbability_face K ⟨v,hvK⟩),hp]
    exact hvb

include hn hK in

lemma ballMass_lt_top
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) [IsFiniteMeasure μ] (B : Set X) (j : ℕ)
    (hd : ∀ x t,t∈(Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤j+1)
    (c : FinProbability Y) (b : ℝ) (hb : 0≤b) :
    ballMass (n := n) Γ hΓ Q μ B j c b<∞ := by
  let F := (localTops_finite Γ hΓ hn hK c b hb).toFinset
  have hzero (σ : SourceTop K n) (hσ : σ∉F) (x : X) :
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x=0 := by
    rw [localOriginalArea_eq_measure]
    have he : (Q.P.val x∩sourceInterior σ.val)∩{v | centerDistance Γ hΓ K n c v≤b}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨⟨_,hv⟩,hr⟩
      exact hσ ((localTops_finite Γ hΓ hn hK c b hb).mem_toFinset.mpr ⟨v,hv,hr⟩)
    rw [he,measure_empty]
  have hle (x : X) : (∑' σ : SourceTop K n,
        localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x) ≤
      ∑ σ∈F,originalArea Γ Q σ j x := by
    rw [tsum_eq_sum (s := F) (fun σ hσ=>hzero σ hσ x)]
    apply Finset.sum_le_sum
    intro σ _
    rw [localOriginalArea_eq_measure,originalArea_eq_measure]
    exact measure_mono Set.inter_subset_left
  apply lt_of_le_of_lt (lintegral_mono hle)
  rw [lintegral_finsetSum F (fun σ _=>(originalArea_locallyConstant Γ Q σ j).continuous.measurable)]
  apply ENNReal.sum_lt_top.mpr
  intro σ _
  apply IsLocallyConstant.lintegral_lt_top (originalArea_locallyConstant Γ Q σ j)
  intro x
  apply originalArea_lt_top Γ Q σ _ j x (hd x)
  obtain ⟨τ,hτ,hστ,hcard,hct⟩ := hK σ.val σ.property.1
  have he : σ.val=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,σ.property.2])
  exact he.symm ▸ hct

end Sparse.GraphGeometry

namespace Sparse.GraphCounting

open SimpleGraph

variable {Y : Type*} (Γ : SimpleGraph Y)

lemma extend_tour [DecidableEq Y] {v a b : Y} (p : Γ.Walk v v)
    (ha : a ∈ p.support) (hab : Γ.Adj a b) :
    ∃ q : Γ.Walk v v, q.length = p.length+2 ∧
      q.support.toFinset = insert b p.support.toFinset := by
  let q := (p.takeUntil a ha).append
    ((hab.toWalk.append hab.symm.toWalk).append (p.dropUntil a ha))
  refine ⟨q, ?_, ?_⟩
  · have hl := congrArg SimpleGraph.Walk.length (p.take_spec ha)
    simp only [Walk.length_append] at hl
    simp only [q, Walk.length_append, Adj.length_toWalk]
    omega
  · ext y
    have hm := congrArg (fun r : Γ.Walk v v => y ∈ r.support) (p.take_spec ha)
    simp only [Walk.mem_support_append_iff] at hm
    simp only [q, List.mem_toFinset, Finset.mem_insert, Walk.mem_support_append_iff,
      Adj.support_toWalk, List.mem_cons]
    have haa : a ∈ (p.takeUntil a ha).support := Walk.end_mem_support _
    have hh : y = a → y ∈ (p.takeUntil a ha).support := fun h => h ▸ haa
    tauto

lemma exists_tour_of_card [Fintype Y] [DecidableEq Y] (hΓ : Γ.Connected) (v : Y)
    (k : ℕ) (hk : k < Fintype.card Y) :
    ∃ p : Γ.Walk v v, p.length = 2*k ∧ p.support.toFinset.card = k+1 := by
  induction k with
  | zero => exact ⟨.nil, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨p,hp,hpc⟩ := ih (by omega)
    have hs : p.support.toFinset ≠ Finset.univ := by
      intro he
      have hcc := congrArg Finset.card he
      simp only [Finset.card_univ,hpc] at hcc
      omega
    have hex : ∃ b, b ∉ p.support.toFinset := by
      by_contra! ht
      exact hs (Finset.eq_univ_of_forall ht)
    obtain ⟨b,hb⟩ := hex
    obtain ⟨r⟩ := hΓ.preconnected v b
    obtain ⟨d,_,hd1,hd2⟩ := r.exists_boundary_dart
      (p.support.toFinset : Set Y) (by simp) hb
    obtain ⟨q,hq,hqs⟩ := extend_tour Γ p (by simpa using hd1) d.adj
    refine ⟨q, by omega, ?_⟩
    rw [hqs,Finset.card_insert_of_notMem hd2,hpc]

theorem exists_covering_tour [Fintype Y] [DecidableEq Y] (hΓ : Γ.Connected)
    (v : Y) : ∃ p : Γ.Walk v v,
      p.length = 2*(Fintype.card Y-1) ∧ p.support.toFinset = Finset.univ := by
  have hn : 0 < Fintype.card Y := Fintype.card_pos_iff.mpr ⟨v⟩
  obtain ⟨p,hp,hpc⟩ := exists_tour_of_card Γ hΓ v (Fintype.card Y-1) (by omega)
  refine ⟨p,hp,Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_⟩
  simp only [Finset.card_univ,hpc]
  omega

lemma connected_set_tour [DecidableEq Y] (s : Finset Y) (hc : (Γ.induce (s : Set Y)).Connected)
    (v : Y) (hv : v ∈ s) {n : ℕ} (hs : s.card=n+1) :
    ∃ p : Γ.Walk v v, p.length=2*n ∧ p.support.toFinset=s := by
  obtain ⟨p,hp,hps⟩ := exists_covering_tour (Γ.induce (s : Set Y)) hc ⟨v,hv⟩
  let f := (SimpleGraph.Embedding.induce (G := Γ) (s : Set Y)).toHom
  refine ⟨p.map f, ?_, ?_⟩
  · change (p.map f).length = 2*n
    rw [Walk.length_map,hp]
    have hcard : Fintype.card (s : Set Y) = s.card :=
      Fintype.card_of_subtype s (fun _ => Iff.rfl)
    rw [hcard,hs,Nat.add_sub_cancel]
  · change (p.map f).support.toFinset = s
    rw [Walk.support_map]
    ext y
    simp only [List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨a,_,rfl⟩
      exact a.property
    · intro hy
      refine ⟨⟨y,hy⟩,?_,rfl⟩
      have hm : (⟨y,hy⟩ : (s : Set Y)) ∈ p.support.toFinset := hps ▸ Finset.mem_univ _
      exact List.mem_toFinset.mp hm

abbrev BasedWalk (v : Y) (n : ℕ) := {p : (b : Y) × Γ.Walk v b // p.2.length = n}

lemma basedWalk_zero_subsingleton (v : Y) : Subsingleton (BasedWalk Γ v 0) := by
  refine ⟨?_⟩
  rintro ⟨⟨b,p⟩,hp⟩ ⟨⟨c,q⟩,hq⟩
  have hb := p.eq_of_length_eq_zero hp
  have hc := q.eq_of_length_eq_zero hq
  subst b
  subst c
  have he : p = .nil := Walk.eq_nil_iff_nil.mpr (Walk.length_eq_zero_iff.mp hp)
  have hf : q = .nil := Walk.eq_nil_iff_nil.mpr (Walk.length_eq_zero_iff.mp hq)
  subst p
  subst q
  rfl

def basedWalkSucc (v : Y) (n : ℕ) :
    BasedWalk Γ v (n+1) → (w : Γ.neighborSet v) × BasedWalk Γ w n
  | ⟨⟨_,.cons h p⟩,hl⟩ => ⟨⟨_,h⟩,⟨⟨_,p⟩,by simpa using hl⟩⟩

def basedWalkCons (v : Y) (n : ℕ) :
    ((w : Γ.neighborSet v) × BasedWalk Γ w n) → BasedWalk Γ v (n+1)
  | ⟨⟨w,h⟩,⟨⟨b,p⟩,hp⟩⟩ => ⟨⟨b,.cons h p⟩,by change p.length+1=n+1; change p.length=n at hp; omega⟩

lemma basedWalkSucc_injective (v : Y) (n : ℕ) :
    Function.Injective (basedWalkSucc Γ v n) := by
  apply Function.LeftInverse.injective (g := basedWalkCons Γ v n)
  rintro ⟨⟨b,p⟩,hp⟩
  cases p with
  | nil => simp at hp
  | cons h p => rfl

lemma basedWalk_finite [Γ.LocallyFinite] (v : Y) (n : ℕ) : Finite (BasedWalk Γ v n) := by
  induction n generalizing v with
  | zero =>
    let := basedWalk_zero_subsingleton Γ v
    infer_instance
  | succ n ih =>
    let : ∀ w : Γ.neighborSet v, Finite (BasedWalk Γ w n) := fun w => ih w
    exact Finite.of_injective _ (basedWalkSucc_injective Γ v n)

lemma basedWalk_card_le [Γ.LocallyFinite] (D : ℕ)
    (hD : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (v : Y) (n : ℕ) :
    Nat.card (BasedWalk Γ v n) ≤ D^n := by
  induction n generalizing v with
  | zero =>
    let := basedWalk_zero_subsingleton Γ v
    rw [Nat.card_of_subsingleton (⟨⟨v,.nil⟩,rfl⟩ : BasedWalk Γ v 0)]
    simp
  | succ n ih =>
    let : ∀ w : Γ.neighborSet v, Fintype (BasedWalk Γ w n) :=
      fun w => @Fintype.ofFinite _ (basedWalk_finite Γ w n)
    have hc := Nat.card_le_card_of_injective _ (basedWalkSucc_injective Γ v n)
    rw [Nat.card_eq_fintype_card (α := (w : Γ.neighborSet v) × BasedWalk Γ w n), Fintype.card_sigma] at hc
    calc Nat.card (BasedWalk Γ v (n+1)) ≤ _ := hc
         _ ≤ ∑ _w : Γ.neighborSet v, D^n := Finset.sum_le_sum fun w _ => by
           simpa only [Nat.card_eq_fintype_card] using ih w
         _ = Fintype.card (Γ.neighborSet v)*D^n := by simp
         _ ≤ D*D^n := Nat.mul_le_mul_right _ (hD v)
         _ = D^(n+1) := by rw [pow_succ, Nat.mul_comm]

abbrev ConnectedSets (v : Y) (n : ℕ) :=
  {s : Finset Y // v ∈ s ∧ s.card=n+1 ∧ (Γ.induce (s : Set Y)).Connected}

def connectedSetTour [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    Γ.Walk v v := (connected_set_tour Γ s.val s.property.2.2 v s.property.1
      s.property.2.1).choose

lemma connectedSetTour_length [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    (connectedSetTour Γ v n s).length=2*n :=
  (connected_set_tour Γ s.val s.property.2.2 v s.property.1 s.property.2.1).choose_spec.1

lemma connectedSetTour_support [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    (connectedSetTour Γ v n s).support.toFinset=s.val :=
  (connected_set_tour Γ s.val s.property.2.2 v s.property.1 s.property.2.1).choose_spec.2

def connectedSetEncoding [DecidableEq Y] (v : Y) (n : ℕ) :
    ConnectedSets Γ v n → BasedWalk Γ v (2*n) :=
  fun s => ⟨⟨v,connectedSetTour Γ v n s⟩,connectedSetTour_length Γ v n s⟩

lemma connectedSetEncoding_injective [DecidableEq Y] (v : Y) (n : ℕ) :
    Function.Injective (connectedSetEncoding Γ v n) := by
  intro s t he
  have hs := congrArg (fun w : BasedWalk Γ v (2*n) => w.val.2.support.toFinset) he
  change (connectedSetTour Γ v n s).support.toFinset =
    (connectedSetTour Γ v n t).support.toFinset at hs
  rw [connectedSetTour_support,connectedSetTour_support] at hs
  exact Subtype.ext hs

lemma connectedSets_finite [Γ.LocallyFinite] (v : Y) (n : ℕ) : Finite (ConnectedSets Γ v n) := by
  classical
  let := basedWalk_finite Γ v (2*n)
  exact Finite.of_injective _ (connectedSetEncoding_injective Γ v n)

theorem connectedSets_card_le [Γ.LocallyFinite] (D : ℕ)
    (hD : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (v : Y) (n : ℕ) :
    Nat.card (ConnectedSets Γ v n) ≤ D^(2*n) := by
  classical
  let := basedWalk_finite Γ v (2*n)
  exact (Nat.card_le_card_of_injective _ (connectedSetEncoding_injective Γ v n)).trans
    (basedWalk_card_le Γ D hD v (2*n))

end Sparse.GraphCounting

namespace Sparse.GraphGeometry

open Set Finset

variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]

lemma neighborhood_card_bound (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (k : ℕ) (v : Y) :
    (neighborhood Γ k v).card + 1 ≤ D^(k+1) := by
  induction k generalizing v with
  | zero => simpa [neighborhood] using hD
  | succ k ih =>
    have hi : ((Γ.neighborFinset v).biUnion (neighborhood Γ k)).card ≤
        ∑ w ∈ Γ.neighborFinset v, (neighborhood Γ k w).card := Finset.card_biUnion_le
    have hn : (Γ.neighborFinset v).card ≤ D := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact hdeg v
    have hp := Finset.card_insert_le v ((Γ.neighborFinset v).biUnion (neighborhood Γ k))
    have hexp : 1 ≤ D^(k+1) := Nat.one_le_pow _ _ (by omega)
    have hraw : (neighborhood Γ (k+1) v).card + 1 ≤
        2 + (Γ.neighborFinset v).card * (D^(k+1)-1) := by
      change (insert v ((Γ.neighborFinset v).biUnion (neighborhood Γ k))).card +1 ≤ _
      have hb : (∑ w ∈ Γ.neighborFinset v, (neighborhood Γ k w).card) ≤
          (Γ.neighborFinset v).card * (D^(k+1)-1) := by
        calc
          _ ≤ ∑ _w ∈ Γ.neighborFinset v, (D^(k+1)-1) :=
            Finset.sum_le_sum fun w _ => by have hh := ih w; omega
          _ = _ := by simp
      omega
    calc
      _ ≤ 2 + (Γ.neighborFinset v).card * (D^(k+1)-1) := hraw
      _ ≤ 2 + D * (D^(k+1)-1) := by gcongr
      _ ≤ D * D^(k+1) := by
        have heq : D^(k+1)-1+1 = D^(k+1) := Nat.sub_add_cancel hexp
        nlinarith
      _ = D^(k+1+1) := (pow_succ' D (k+1)).symm

lemma neighborhood_card_le (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (k : ℕ) (v : Y) :
    (neighborhood Γ k v).card ≤ D^(k+1) := by
  have h := neighborhood_card_bound Γ D hD hdeg k v
  omega

lemma supportNeighborhood_card_le (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (k : ℕ) (A : Finset Y) :
    (A.biUnion (neighborhood Γ k)).card ≤ A.card * D^(k+1) := by
  calc
    _ ≤ ∑ v ∈ A, (neighborhood Γ k v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ A, D^(k+1) := Finset.sum_le_sum fun v _ =>
      neighborhood_card_le Γ D hD hdeg k v
    _ = _ := by simp

end Sparse.GraphGeometry

namespace Sparse.GraphCounting

open Set Finset

variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]

abbrev ConnectedThrough (B : Finset Y) (n : ℕ) :=
  {s : Finset Y // s.card = n+1 ∧ (Γ.induce (s : Set Y)).Connected ∧
    ∃ v ∈ B, v ∈ s}

noncomputable def throughEncoding (B : Finset Y) (n : ℕ) :
    ConnectedThrough Γ B n → (v : B) × ConnectedSets Γ v n := fun s =>
  ⟨⟨s.property.2.2.choose,s.property.2.2.choose_spec.1⟩,
    ⟨s.val,s.property.2.2.choose_spec.2,s.property.1,s.property.2.1⟩⟩

omit [DecidableEq Y] [Γ.LocallyFinite] in
lemma throughEncoding_injective (B : Finset Y) (n : ℕ) :
    Function.Injective (throughEncoding Γ B n) := by
  intro s t h
  exact Subtype.ext (congrArg (fun p : (v : B) × ConnectedSets Γ v n => p.2.val) h)

omit [DecidableEq Y] in
lemma connectedThrough_finite (B : Finset Y) (n : ℕ) :
    Finite (ConnectedThrough Γ B n) := by
  let : ∀ v : B, Finite (ConnectedSets Γ v n) := fun v => connectedSets_finite Γ v n
  exact Finite.of_injective _ (throughEncoding_injective Γ B n)

omit [DecidableEq Y] in
theorem connectedThrough_card_le (D : ℕ)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (B : Finset Y) (n : ℕ) :
    Nat.card (ConnectedThrough Γ B n) ≤ B.card * D^(2*n) := by
  let : ∀ v : B, Fintype (ConnectedSets Γ v n) :=
    fun v => @Fintype.ofFinite _ (connectedSets_finite Γ v n)
  have hc := Nat.card_le_card_of_injective _ (throughEncoding_injective Γ B n)
  rw [Nat.card_eq_fintype_card (α := (v : B) × ConnectedSets Γ v n),Fintype.card_sigma] at hc
  calc
    _ ≤ _ := hc
    _ ≤ ∑ _v : B, D^(2*n) := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [Nat.card_eq_fintype_card] using connectedSets_card_le Γ D hdeg v n
    _ = _ := by simp

end Sparse.GraphCounting

namespace Sparse.GraphGeometry

open FinProbability

variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]

lemma meeting_simplex_contact (hΓ : Γ.Connected) {n : ℕ} (hn : 0<n)
    (c p : FinProbability Y) (σ : Finset Y) (hp : p.coeff.support ⊆ σ)
    (s : ℝ) (hs : 0 ≤ s)
    (hball : @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s) :
    ∃ v ∈ c.coeff.support.biUnion (neighborhood Γ ⌊s * Real.sqrt (n : ℝ)⌋₊), v ∈ σ := by
  let : MetricSpace Y := graphMetric Γ hΓ
  obtain ⟨a,ha,v,hv,hav⟩ := support_distance_rho hn c p
  have hle : (Γ.dist a v : ℝ) ≤ s * Real.sqrt (n : ℝ) := by
    change (Γ.dist a v : ℝ) ≤ Real.sqrt (n : ℝ) * rho n c p at hav
    calc _ ≤ Real.sqrt (n : ℝ) * rho n c p := hav
         _ ≤ Real.sqrt (n : ℝ) * s := mul_le_mul_of_nonneg_left hball (Real.sqrt_nonneg _)
         _ = _ := mul_comm _ _
  exact ⟨v,Finset.mem_biUnion.mpr ⟨a,ha,dist_le_mem_neighborhood Γ hΓ
    ((Nat.le_floor_iff (mul_nonneg hs (Real.sqrt_nonneg _))).mpr hle)⟩,hp hv⟩

abbrev MeetingTops (hΓ : Γ.Connected) (n : ℕ) (tops : Set (Finset Y))
    (c : FinProbability Y) (s : ℝ) :=
  {σ : Finset Y // σ ∈ tops ∧ ∃ p : FinProbability Y, p.coeff.support ⊆ σ ∧
    @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s}

theorem meetingTops_card_le (hΓ : Γ.Connected) (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) {n : ℕ} (hn : 0<n)
    (tops : Set (Finset Y))
    (htop : ∀ σ∈tops, σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (s : ℝ) (hs : 0 ≤ s) :
    Nat.card (MeetingTops Γ hΓ n tops c s) ≤
      c.coeff.support.card * D^(⌊s * Real.sqrt (n : ℝ)⌋₊+1) * D^(2*n) := by
  let B := c.coeff.support.biUnion (neighborhood Γ ⌊s * Real.sqrt (n : ℝ)⌋₊)
  let f : MeetingTops Γ hΓ n tops c s → GraphCounting.ConnectedThrough Γ B n := fun σ =>
    ⟨σ.val,(htop σ.val σ.property.1).1,(htop σ.val σ.property.1).2,by
      obtain ⟨p,hp,hball⟩ := σ.property.2
      exact meeting_simplex_contact Γ hΓ hn c p σ.val hp s hs hball⟩
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    exact congrArg (fun x : GraphCounting.ConnectedThrough Γ B n => x.val) h
  have : Finite (GraphCounting.ConnectedThrough Γ B n) :=
    GraphCounting.connectedThrough_finite Γ B n
  calc
    _ ≤ Nat.card (GraphCounting.ConnectedThrough Γ B n) := Nat.card_le_card_of_injective f hf
    _ ≤ B.card * D^(2*n) := GraphCounting.connectedThrough_card_le Γ D hdeg B n
    _ ≤ _ := Nat.mul_le_mul_right _ (supportNeighborhood_card_le Γ D hD hdeg _ _)

theorem meetingTops_card_le_uniform (hΓ : Γ.Connected) (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) {n : ℕ} (hn : 0<n)
    (tops : Set (Finset Y))
    (htop : ∀ σ∈tops, σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (hc : c.coeff.support.card ≤ n+1) (s : ℝ) (hs : 0 ≤ s) :
    Nat.card (MeetingTops Γ hΓ n tops c s) ≤
      (n+1) * D^(⌊s * Real.sqrt (n : ℝ)⌋₊+1) * D^(2*n) := by
  exact (meetingTops_card_le Γ hΓ D hD hdeg hn tops htop c s hs).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc))

end Sparse.GraphGeometry

end BassTrace

end

end OAI
