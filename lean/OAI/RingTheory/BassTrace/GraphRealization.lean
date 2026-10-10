import OAI.RingTheory.BassTrace.ProbabilityGeometry

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.GraphGeometry

section

open scoped BigOperators

open FinProbability

variable {Y : Type*} (Γ : SimpleGraph Y)

@[instance_reducible] def graphMetric (hΓ : Γ.Connected) : MetricSpace Y where
  dist a b := (Γ.dist a b : ℝ)
  dist_self a := by simp
  dist_comm a b := by rw [Γ.dist_comm]
  dist_triangle a b c := by
    exact_mod_cast (hΓ.preconnected a b).dist_triangle_left c
  eq_of_dist_eq_zero {a b} hab := by
    exact (hΓ.preconnected a b).dist_eq_zero_iff.mp (by exact_mod_cast hab)

lemma graphMetric_discrete (hΓ : Γ.Connected) (a b : Y) (hab : a ≠ b) :
    (1 : ℝ) ≤ (Γ.dist a b : ℝ) := by
  have hd : Γ.dist a b ≠ 0 := by
    intro he
    exact hab ((hΓ.preconnected a b).dist_eq_zero_iff.mp he)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd

variable [DecidableEq Y] [Γ.LocallyFinite]

def neighborhood : ℕ → Y → Finset Y
  | 0, a => {a}
  | k+1, a => insert a ((Γ.neighborFinset a).biUnion (neighborhood k))

lemma walk_end_mem_neighborhood {a b : Y} (p : Γ.Walk a b) (k : ℕ)
    (hp : p.length ≤ k) : b ∈ neighborhood Γ k a := by
  induction k generalizing a b with
  | zero =>
    have he : a=b := p.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero hp)
    simp [neighborhood,he]
  | succ k ih =>
    cases p with
    | nil => simp [neighborhood]
    | @cons a w b haw p =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      exact ⟨w,(Γ.mem_neighborFinset a w).mpr haw,ih p (by simpa using hp)⟩

lemma dist_le_mem_neighborhood (hΓ : Γ.Connected) {a b : Y} {k : ℕ}
    (hab : Γ.dist a b ≤ k) : b ∈ neighborhood Γ k a := by
  obtain ⟨p,_,hp⟩ := hΓ.exists_path_of_dist a b
  exact walk_end_mem_neighborhood Γ p k (hp ▸ hab)

omit [DecidableEq Y] [Γ.LocallyFinite] in

lemma connected_set_diameter (σ : Finset Y) {n : ℕ} (hcard : σ.card=n+1)
    (hc : (Γ.induce (σ : Set Y)).Connected) {a b : Y} (ha : a∈σ) (hb : b∈σ) :
    Γ.dist a b ≤ n := by
  obtain ⟨p,hp,_⟩ := hc.exists_path_of_dist ⟨a,ha⟩ ⟨b,hb⟩
  have hl := hp.length_lt
  have hl' : p.length < n+1 := by
    calc p.length < _ := hl
         _ = σ.card := Fintype.card_of_subtype σ (fun _ => Iff.rfl)
         _ = n+1 := hcard
  have hdist := SimpleGraph.dist_le (p.map (SimpleGraph.Embedding.induce (G := Γ) (σ : Set Y)).toHom)
  rw [SimpleGraph.Walk.length_map] at hdist
  exact hdist.trans (Nat.le_of_lt_succ hl')

lemma meeting_simplex_vertices (hΓ : Γ.Connected) {n : ℕ} (hn : 0<n)
    (c p : FinProbability Y) (σ : Finset Y) (hcard : σ.card=n+1)
    (hc : (Γ.induce (σ : Set Y)).Connected) (hp : p.coeff.support ⊆ σ)
    (s : ℝ) (hs : 0 ≤ s)
    (hball : @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s) :
    σ ⊆ c.coeff.support.biUnion
      (neighborhood Γ (⌊s * Real.sqrt (n : ℝ)⌋₊+n)) := by
  let : MetricSpace Y := graphMetric Γ hΓ
  obtain ⟨a,ha,v,hv,hav⟩ := support_distance_rho hn c p
  have hle : (Γ.dist a v : ℝ) ≤ s * Real.sqrt (n : ℝ) := by
    change (Γ.dist a v : ℝ) ≤ Real.sqrt (n : ℝ) * rho n c p at hav
    calc _ ≤ Real.sqrt (n : ℝ) * rho n c p := hav
         _ ≤ Real.sqrt (n : ℝ) * s := mul_le_mul_of_nonneg_left hball (Real.sqrt_nonneg _)
         _ = _ := mul_comm _ _
  have hnat : Γ.dist a v ≤ ⌊s * Real.sqrt (n : ℝ)⌋₊ :=
    (Nat.le_floor_iff (mul_nonneg hs (Real.sqrt_nonneg _))).mpr hle
  intro w hw
  apply Finset.mem_biUnion.mpr
  refine ⟨a,ha,dist_le_mem_neighborhood Γ hΓ ?_⟩
  exact (hΓ.preconnected a v).dist_triangle_left w |>.trans
    (Nat.add_le_add hnat (connected_set_diameter Γ σ hcard hc (hp hv) hw))

theorem finitely_many_meeting_top_simplices (hΓ : Γ.Connected) {n : ℕ} (hn : 0<n)
    (tops : Set (Finset Y))
    (htop : ∀ σ∈tops, σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (s : ℝ) (hs : 0 ≤ s) :
    {σ | σ∈tops ∧ ∃ p : FinProbability Y, p.coeff.support ⊆ σ ∧
      @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s}.Finite := by
  let W := c.coeff.support.biUnion (neighborhood Γ (⌊s * Real.sqrt (n : ℝ)⌋₊+n))
  apply W.powerset.finite_toSet.subset
  rintro σ ⟨hσ,p,hp,hball⟩
  exact Finset.mem_powerset.mpr
    (meeting_simplex_vertices Γ hΓ hn c p σ (htop σ hσ).1 (htop σ hσ).2 hp s hs hball)

end

open Set Finset

variable {Y : Type*} [DecidableEq Y] (Γ : SimpleGraph Y) [Γ.LocallyFinite]

def realization (tops : Set (Finset Y)) : Set (FinProbability Y) :=
  {p | ∃ σ ∈ tops, p.coeff.support ⊆ σ}

lemma locallyFinite_top_simplices (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    LocallyFinite (fun σ : tops => {p : FinProbability Y | p.coeff.support ⊆ σ.val}) := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  intro c
  refine ⟨Metric.ball c 1,Metric.ball_mem_nhds c zero_lt_one,?_⟩
  have hfin := finitely_many_meeting_top_simplices Γ hΓ hn tops htop c 1 zero_le_one
  apply (Set.Finite.preimage (f := fun σ : tops => σ.val) Subtype.val_injective.injOn hfin).subset
  intro σ hσ
  obtain ⟨p,hp,hpc⟩ := hσ
  refine ⟨σ.property,p,hp,?_⟩
  have hd : dist p c < 1 := hpc
  have heq : FinProbability.rho n c p = dist p c := FinProbability.rho_comm n c p
  exact heq ▸ hd.le

lemma isClosed_realization (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    IsClosed (realization tops) := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  have heq : realization tops = ⋃ σ : tops, {p : FinProbability Y | p.coeff.support ⊆ σ.val} := by
    ext p
    simp [realization]
  rw [heq]
  apply (locallyFinite_top_simplices Γ hΓ hn tops htop).isClosed_iUnion
  intro σ
  exact (isCompact_probability_simplex σ.val n hn (graphMetric_discrete Γ hΓ)).isClosed

lemma isCompact_realized_closedBall (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (s : ℝ) (hs : 0 ≤ s) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    IsCompact (realization tops ∩ Metric.closedBall c s) := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  let meeting := {σ | σ ∈ tops ∧ ∃ p : FinProbability Y, p.coeff.support ⊆ σ ∧
      FinProbability.rho n c p ≤ s}
  have hmfin : meeting.Finite := finitely_many_meeting_top_simplices Γ hΓ hn tops htop c s hs
  have hcompact : IsCompact (⋃ σ ∈ meeting, {p : FinProbability Y | p.coeff.support ⊆ σ}) := by
    exact hmfin.isCompact_biUnion fun σ _ =>
      isCompact_probability_simplex σ n hn (graphMetric_discrete Γ hΓ)
  apply hcompact.of_isClosed_subset
  · exact (isClosed_realization Γ hΓ hn tops htop).inter Metric.isClosed_closedBall
  · rintro p ⟨⟨σ,hσ,hp⟩,hpc⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨σ,⟨hσ,p,hp,?_⟩,hp⟩
    have hd : dist p c ≤ s := hpc
    simpa only [show dist p c = FinProbability.rho n p c from rfl,
      FinProbability.rho_comm n p c] using hd

end Sparse.GraphGeometry

namespace Sparse

open Set Finset

open scoped BassTrace.Sparse

variable {Y : Type*} [MetricSpace Y]

def simplexEquiv (S : Finset Y) : probabilitySet S ≃
    {p : FinProbability Y | p.coeff.support ⊆ S} where
  toFun v := ⟨simplexProbability S v,v.property.2.2⟩
  invFun p := ⟨p.val.coeff,p.val.nonneg,by simpa using p.val.total,p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def simplexHomeomorph (S : Finset Y) (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) :
    let := FinProbability.rhoMetric n hn hd
    probabilitySet S ≃ₜ {p : FinProbability Y | p.coeff.support ⊆ S} := by
  let := FinProbability.rhoMetric n hn hd
  let : CompactSpace (probabilitySet S) :=
    isCompact_iff_compactSpace.mp (geometric_simplex_compact S)
  have hc : Continuous (simplexEquiv S) :=
    (continuous_simplexProbability S n hn hd).subtype_mk _
  exact (simplexEquiv S).toHomeomorphOfContinuousClosed hc hc.isClosedMap

lemma continuousOn_coeff_simplex (S : Finset Y) (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) :
    let := FinProbability.rhoMetric n hn hd
    ContinuousOn FinProbability.coeff {p : FinProbability Y | p.coeff.support ⊆ S} := by
  let := FinProbability.rhoMetric n hn hd
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_subtype_val.comp (simplexHomeomorph S n hn hd).symm.continuous

end Sparse

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Topology

variable {Y : Type*} [DecidableEq Y] (Γ : SimpleGraph Y) [Γ.LocallyFinite]

lemma finitely_many_top_simplices_at (hΓ : Γ.Connected) {n : ℕ}
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) (v : Y) :
    {σ | σ ∈ tops ∧ v ∈ σ}.Finite := by
  apply (neighborhood Γ n v).powerset.finite_toSet.subset
  intro σ hσ
  apply Finset.mem_powerset.mpr
  intro w hw
  exact dist_le_mem_neighborhood Γ hΓ
    (connected_set_diameter Γ σ (htop σ hσ.1).1 (htop σ hσ.1).2 hσ.2 hw)

lemma continuousOn_coeff_realization (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    ContinuousOn FinProbability.coeff (realization tops) := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  have hc := (locallyFinite_top_simplices Γ hΓ hn tops htop).continuousOn_iUnion
    (fun σ => (isCompact_probability_simplex σ.val n hn (graphMetric_discrete Γ hΓ)).isClosed)
    (fun σ => continuousOn_coeff_simplex σ.val n hn (graphMetric_discrete Γ hΓ))
  convert hc using 1
  ext p
  simp [realization]

def affineRealization (tops : Set (Finset Y)) : Set (Y →₀ ℝ) :=
  ⋃ σ ∈ tops, probabilitySet σ

def affineProbability (tops : Set (Finset Y)) (v : affineRealization tops) : FinProbability Y where
  coeff := v.val
  nonneg := by
    obtain ⟨σ,_,hσ⟩ := Set.mem_iUnion₂.mp v.property
    exact hσ.1
  total := by
    obtain ⟨σ,_,hσ⟩ := Set.mem_iUnion₂.mp v.property
    simpa using hσ.2.1

omit [DecidableEq Y] in
@[simp] lemma affineProbability_coeff (tops : Set (Finset Y)) (v : affineRealization tops) :
    (affineProbability tops v).coeff = v.val := rfl

omit [DecidableEq Y] in
lemma affineProbability_mem (tops : Set (Finset Y)) (v : affineRealization tops) :
    affineProbability tops v ∈ realization tops := by
  obtain ⟨σ,hσ,hv⟩ := Set.mem_iUnion₂.mp v.property
  exact ⟨σ,hσ,hv.2.2⟩

lemma locallyFinite_affine_top_simplices (hΓ : Γ.Connected) {n : ℕ}
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) :
    LocallyFinite (fun σ : tops => {v : affineRealization tops | v.val ∈ probabilitySet σ.val}) := by
  intro p
  let q := affineProbability tops p
  obtain ⟨y,hy⟩ := q.coeff_support_nonempty
  have hpos : 0 < q.coeff y := lt_of_le_of_ne (q.nonneg y) (Finsupp.mem_support_iff.mp hy).symm
  let U : Set (affineRealization tops) := {v | 0 < v.val y}
  have hU : IsOpen U := isOpen_lt continuous_const
    ((coordinateCLM y).continuous.comp continuous_subtype_val)
  refine ⟨U,hU.mem_nhds hpos,?_⟩
  have hfin := finitely_many_top_simplices_at Γ hΓ tops htop y
  apply (hfin.preimage Subtype.val_injective.injOn).subset
  intro σ hσ
  obtain ⟨v,hv,hvU⟩ := hσ
  refine ⟨σ.property,hv.2.2 ?_⟩
  exact Finsupp.mem_support_iff.mpr (ne_of_gt hvU)

lemma continuous_affineProbability (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    Continuous (affineProbability tops) := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  apply (locallyFinite_affine_top_simplices Γ hΓ tops htop).continuous
  · ext v
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    obtain ⟨σ,hσ,hv⟩ := Set.mem_iUnion₂.mp v.property
    exact ⟨⟨σ,hσ⟩,hv⟩
  · intro σ
    exact (geometric_simplex_compact σ.val).isClosed.preimage continuous_subtype_val
  · intro σ
    apply continuousOn_iff_continuous_domRestrict.mpr
    let f : {v : affineRealization tops | v.val ∈ probabilitySet σ.val} → probabilitySet σ.val :=
      fun v => ⟨v.val.val,v.property⟩
    have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (continuous_simplexProbability σ.val n hn (graphMetric_discrete Γ hΓ)).comp hf

def realizationHomeomorph (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    realization tops ≃ₜ affineRealization tops := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  refine
    { toFun := fun p => ⟨p.val.coeff,?_⟩
      invFun := fun v => ⟨affineProbability tops v,affineProbability_mem tops v⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := ?_
      continuous_invFun := (continuous_affineProbability Γ hΓ hn tops htop).subtype_mk _ }
  · obtain ⟨σ,hσ,hp⟩ := p.property
    exact Set.mem_iUnion₂.mpr ⟨σ,hσ,p.val.nonneg,by simpa using p.val.total,hp⟩
  · exact ((continuousOn_iff_continuous_domRestrict.mp
      (continuousOn_coeff_realization Γ hΓ hn tops htop))).subtype_mk _

end Sparse.GraphGeometry

end BassTrace

end

end OAI
