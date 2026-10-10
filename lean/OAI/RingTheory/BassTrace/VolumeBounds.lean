import OAI.RingTheory.BassTrace.GraphCounting

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

/-! Scalar estimates for iterated volume growth and high-dimensional ball bounds. -/

open Finset MeasureTheory intervalIntegral

namespace Sparse

noncomputable def dividedPower (n : ℕ) (t : ℝ) : ℝ :=
  t ^ n / (n.factorial : ℝ)

noncomputable def slicingError (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, dividedPower (i + 1) t

lemma continuous_dividedPower (n : ℕ) : Continuous (dividedPower n) := by
  unfold dividedPower
  fun_prop

lemma continuous_slicingError (n : ℕ) : Continuous (slicingError n) := by
  unfold slicingError
  exact continuous_finsetSum _ fun _ _ => continuous_dividedPower _

@[simp] lemma dividedPower_zero (t : ℝ) : dividedPower 0 t = 1 := by
  simp [dividedPower]

@[simp] lemma slicingError_zero (t : ℝ) : slicingError 0 t = 0 := by
  simp [slicingError]

@[simp] lemma dividedPower_one (t : ℝ) : dividedPower 1 t = t := by
  simp [dividedPower]

lemma integral_dividedPower (n : ℕ) (b : ℝ) :
    (∫ t in 0..b, dividedPower n t) = dividedPower (n + 1) b := by
  unfold dividedPower
  rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero n),
    sub_zero, div_div, Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

lemma integral_slicingError (n : ℕ) (b : ℝ) :
    (∫ t in 0..b, slicingError n t) + b = slicingError (n + 1) b := by
  unfold slicingError
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_dividedPower (i + 1)).intervalIntegrable 0 b)]
  simp only [integral_dividedPower]
  rw [Finset.sum_range_succ']
  simp only [zero_add, dividedPower_one]

lemma integral_slicing_lower (n : ℕ) (b c ε : ℝ) :
    (∫ t in 0..b, c * dividedPower n t - ε * slicingError n t) - ε * b =
      c * dividedPower (n + 1) b - ε * slicingError (n + 1) b := by
  have hc : IntervalIntegrable (fun t => c * dividedPower n t) volume 0 b :=
    (continuous_const.mul (continuous_dividedPower n)).intervalIntegrable 0 b
  have he : IntervalIntegrable (fun t => ε * slicingError n t) volume 0 b :=
    (continuous_const.mul (continuous_slicingError n)).intervalIntegrable 0 b
  rw [intervalIntegral.integral_sub hc he,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_dividedPower]
  have h := integral_slicingError n b
  rw [← h]
  ring

theorem iterated_slicing_lower_bound
    (M : ℕ → ℝ → ℝ) (n : ℕ) (L ε : ℝ)
    (hmono : ∀ k, Monotone (M k))
    (hstep : ∀ k < n, ∀ b ∈ Set.Icc 0 L,
      (∫ t in 0..b, M k t) - ε * b ≤ M (k + 1) b) :
    ∀ k ≤ n, ∀ b ∈ Set.Icc 0 L,
      M 0 0 * dividedPower k b - ε * slicingError k b ≤ M k b := by
  intro k
  induction k with
  | zero =>
      intro _ b hb
      simpa using hmono 0 hb.1
  | succ k ih =>
      intro hk b hb
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hm :
          (∫ t in 0..b, M 0 0 * dividedPower k t - ε * slicingError k t) ≤
            ∫ t in 0..b, M k t := by
        apply intervalIntegral.integral_mono_on hb.1
          (((continuous_const.mul (continuous_dividedPower k)).sub
            (continuous_const.mul (continuous_slicingError k))).intervalIntegrable 0 b)
          (hmono k).intervalIntegrable
        intro t ht
        exact ih hk' t ⟨ht.1, ht.2.trans hb.2⟩
      have hs := hstep k (Nat.lt_of_succ_le hk) b hb
      rw [← integral_slicing_lower k b (M 0 0) ε]
      linarith

theorem absorb_nonempty_probability
    (A V μ M ε E : ℝ) (hVA : V < A) (hV : 0 ≤ V)
    (hμM : μ ≤ M) (hbound : A * M ≤ V * μ + ε * E) :
    M ≤ E / (A - V) * ε := by
  have hpos : 0 < A - V := sub_pos.mpr hVA
  have hmul : V * μ ≤ V * M := mul_le_mul_of_nonneg_left hμM hV
  have h : (A - V) * M ≤ ε * E := by nlinarith
  have h' : M ≤ (ε * E) / (A - V) := (le_div_iff₀ hpos).2 (by nlinarith)
  convert h' using 1
  ring

/-! A strict high-dimensional volume margin with radius 4 D² and half-radius 2 D². -/

def volumeThreshold (D : ℕ) : ℕ := (4 * D ^ 3 + D + 3) ^ 2

lemma square_succ_le_two_pow {t : ℕ} (ht : 6 ≤ t) : (t + 1) ^ 2 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      rw [pow_succ (2 : ℕ) t]
      have hsq : (t + 1 + 1) ^ 2 ≤ 2 * (t + 1) ^ 2 := by nlinarith
      omega

lemma real_sqrt_lt_nat_sqrt_succ (n : ℕ) :
    Real.sqrt (n : ℝ) < (Nat.sqrt n : ℝ) + 1 := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hn : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' n
  have ht : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

lemma floor_radius_sqrt_bound (D n : ℕ) :
    ⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ ≤
      4 * D ^ 2 * (Nat.sqrt n + 1) := by
  have hnonneg : 0 ≤ (4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ) := by positivity
  have hfloor := Nat.floor_le hnonneg
  have hroot := (real_sqrt_lt_nat_sqrt_succ n).le
  have hmul := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ 4 * (D : ℝ) ^ 2)
  have h : (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ : ℝ) ≤
      4 * (D : ℝ) ^ 2 * ((Nat.sqrt n : ℝ) + 1) := hfloor.trans hmul
  exact_mod_cast h

theorem exponential_volume_margin (D n : ℕ) (hD : 2 ≤ D)
    (hn : volumeThreshold D ≤ n) :
    (n + 1) * D ^ (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1) < 2 ^ n := by
  let t := Nat.sqrt n
  have ht : 4 * D ^ 3 + D + 3 ≤ t := Nat.le_sqrt'.mpr hn
  have htp : 6 ≤ t := by
    have hcube : 1 ≤ D ^ 3 := Nat.one_le_pow 3 D (by omega)
    omega
  have hnt : n + 1 ≤ 2 ^ t :=
    (Nat.succ_le_succ_sqrt' n).trans (square_succ_le_two_pow htp)
  have hfloor := floor_radius_sqrt_bound D n
  have hbase : D ≤ 2 ^ D := (Nat.lt_two_pow_self (n := D)).le
  have hexp : t + D * (4 * D ^ 2 * (t + 1) + 1) < t ^ 2 := by
    have h1 : (4 * D ^ 3 + D + 3) * t ≤ t * t := Nat.mul_le_mul_right t ht
    have h2 : 4 * D ^ 3 + D + 3 ≤ 3 * t := by omega
    nlinarith
  calc
    (n + 1) * D ^ (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1)
        ≤ 2 ^ t * (2 ^ D) ^ (4 * D ^ 2 * (t + 1) + 1) := by
          apply Nat.mul_le_mul hnt
          exact (Nat.pow_le_pow_left hbase _).trans
            (Nat.pow_le_pow_right (by positivity) (Nat.add_le_add_right hfloor 1))
    _ = 2 ^ (t + D * (4 * D ^ 2 * (t + 1) + 1)) := by
      rw [← pow_mul, ← pow_add]
    _ < 2 ^ (t ^ 2) := Nat.pow_lt_pow_right (by omega) hexp
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (Nat.sqrt_le' n)

theorem strict_volume_margin (D n : ℕ) (hD : 2 ≤ D)
    (hn : volumeThreshold D ≤ n) :
    ((n + 1 : ℕ) : ℝ) * (D : ℝ) ^
       (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1) *
       (D : ℝ) ^ (2 * n) / (n.factorial : ℝ) <
      (2 * (D : ℝ) ^ 2) ^ n / (n.factorial : ℝ) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply (div_lt_div_iff_of_pos_right hf).2
  have h := exponential_volume_margin D n hD hn
  have hc : ((n + 1 : ℕ) : ℝ) * (D : ℝ) ^
      (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1) < (2 : ℝ) ^ n := by
    exact_mod_cast h
  have hDp : (0 : ℝ) < (D : ℝ) ^ (2 * n) := by positivity
  have hm := mul_lt_mul_of_pos_right hc hDp
  simpa only [mul_pow, pow_mul] using hm

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

omit [DecidableEq Y] [Γ.LocallyFinite] in
include hK in
lemma sourceTop_connected (σ : SourceTop K n) : (Γ.induce (σ.val : Set Y)).Connected := by
  obtain ⟨τ,_,hστ,hcard,hct⟩ := hK σ.val σ.property.1
  have he : σ.val=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,σ.property.2])
  exact he.symm ▸ hct

omit [MeasurableSpace X] [Γ.LocallyFinite] in
include hK in
lemma localOriginalArea_top_le
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (W : Set (Y →₀ ℝ)) (x : X) :
    localOriginalArea Γ Q σ n W x ≤ ENNReal.ofReal (1/(n.factorial : ℝ)) := by
  rw [←simplexArea_top_simplex (simplexGraph Γ σ.val σ.property.2)
    (simplexGraph_connected Γ σ.val σ.property.2 (sourceTop_connected Γ hK σ))]
  apply simplexArea_mono
  rintro _ ⟨v,⟨_,hv,_⟩,rfl⟩
  exact simplexCoordinates_full _ _ (intrinsicInterior_subset hv)

include hn hK in
lemma localTops_card_le (D : ℕ) (hD : 2≤D)
    (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (c : FinProbability Y) (hc : c.coeff.support.card≤n+1) (b : ℝ) (hb : 0≤b) :
    Nat.card (localTops (K := K) (n := n) Γ hΓ c b) ≤
      (n+1)*D^(⌊b*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) := by
  let tops : Set (Finset Y) := {s | s∈K.faces ∧ s.card=n+1}
  let f : localTops (K := K) (n := n) Γ hΓ c b → MeetingTops Γ hΓ n tops c b := fun σ=>by
    refine ⟨σ.val.val,σ.val.property,?_⟩
    obtain ⟨v,hv,hvb⟩ := σ.property
    have hvK := (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
      (show simplexVertices σ.val.val∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces from
        ⟨σ.val.val,σ.val.property.1,rfl⟩) (intrinsicInterior_subset hv)
    let p := pointProbability K ⟨v,hvK⟩
    have hp : p.coeff=v := pointProbability_coeff K ⟨v,hvK⟩
    refine ⟨p,?_,?_⟩
    · rw [hp]; exact support_of_mem_sourceInterior _ hv
    · rw [←centerDistance_apply Γ hΓ K n c p (pointProbability_face K ⟨v,hvK⟩),hp]
      exact hvb
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun s : MeetingTops Γ hΓ n tops c b=>s.val) h
  have hfin := finitely_many_meeting_top_simplices Γ hΓ hn tops
    (fun s hs=>⟨hs.2,sourceTop_connected Γ hK ⟨s,hs⟩⟩) c b hb
  let : Finite (MeetingTops Γ hΓ n tops c b) := hfin.to_subtype
  exact (Nat.card_le_card_of_injective f hf).trans
    (meetingTops_card_le_uniform Γ hΓ D hD hdeg hn tops
      (fun s hs=>⟨hs.2,sourceTop_connected Γ hK ⟨s,hs⟩⟩) c hc b hb)

include hn hK in
lemma ballMass_top_bound
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (B : Set X) (c : FinProbability Y)
    (hc : c.coeff.support.card≤n+1) (b : ℝ) (hb : 0≤b)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D) :
    ballMass (n := n) Γ hΓ Q μ B n c b ≤
      ((n+1)*D^(⌊b*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) : ℕ) *
        ENNReal.ofReal (1/(n.factorial : ℝ)) * μ B := by
  let F := (localTops_finite Γ hΓ hn hK c b hb).toFinset
  have hzero (σ : SourceTop K n) (hσ : σ∉F) (x : X) :
      localOriginalArea Γ Q σ n {v | centerDistance Γ hΓ K n c v≤b} x=0 := by
    rw [localOriginalArea_eq_measure]
    have he : (Q.P.val x∩sourceInterior σ.val)∩{v | centerDistance Γ hΓ K n c v≤b}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨⟨_,hv⟩,hr⟩
      exact hσ ((localTops_finite Γ hΓ hn hK c b hb).mem_toFinset.mpr ⟨v,hv,hr⟩)
    rw [he,measure_empty]
  have hle (x : X) : (∑' σ : SourceTop K n,
        localOriginalArea Γ Q σ n {v | centerDistance Γ hΓ K n c v≤b} x) ≤
      (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(n.factorial : ℝ)) := by
    rw [tsum_eq_sum (s := F) (fun σ hσ=>hzero σ hσ x)]
    simpa using Finset.sum_le_sum (s := F) (fun σ _=>localOriginalArea_top_le Γ hK Q σ _ x)
  have hcard : F.card≤(n+1)*D^(⌊b*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) := by
    have h := localTops_card_le Γ hΓ hn hK D hD hdeg c hc b hb
    simpa only [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card _ (localTops_finite Γ hΓ hn hK c b hb),F] using h
  calc
    _ ≤ ∫⁻ _x in B, (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(n.factorial : ℝ)) ∂μ := lintegral_mono hle
    _ = (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(n.factorial : ℝ))*μ B := by simp
    _ ≤ _ := by gcongr

end Sparse.GraphGeometry

namespace Sparse

open Set MeasureTheory

open scoped ENNReal

lemma real_integral_of_mass_bound (F : ℝ → ℝ≥0∞) (hmono : Monotone F)
    (hfin : ∀ t,F t<∞) (r b ε : ℝ) (hrb : r≤b) (hε : 0≤ε)
    (C : ℝ≥0∞) (hC : C<∞)
    (h : (∫⁻ t in Ioo r b,F t)≤C+ENNReal.ofReal ε*ENNReal.ofReal (b-r)) :
    (∫ t in r..b,(F t).toReal)≤C.toReal+ε*(b-r) := by
  rw [intervalIntegral.integral_of_le hrb,integral_Ioc_eq_integral_Ioo,
    integral_toReal hmono.measurable.aemeasurable (Filter.Eventually.of_forall hfin)]
  have ht : C+ENNReal.ofReal ε*ENNReal.ofReal (b-r)≠∞ := by finiteness
  have hh := ENNReal.toReal_mono ht h
  rw [ENNReal.toReal_add hC.ne (by finiteness),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hε,ENNReal.toReal_ofReal (sub_nonneg.mpr hrb)] at hh
  exact hh

theorem iterated_mass_bound (M : ℕ → ℝ → ℝ≥0∞) (n : ℕ) (r R ε : ℝ)
    (hrR : r≤R) (hε : 0≤ε) (hmono : ∀ k,Monotone (M k))
    (hfin : ∀ k t,M k t<∞)
    (hstep : ∀ k<n,∀ b∈Icc r R,
      (∫⁻ t in Ioo r b,M k t)≤M (k+1) b+ENNReal.ofReal ε*ENNReal.ofReal (b-r)) :
    (M 0 r).toReal*dividedPower n (R-r)-ε*slicingError n (R-r)≤(M n R).toReal := by
  let F : ℕ → ℝ → ℝ := fun k t=>(M k (r+t)).toReal
  have hFm k : Monotone (F k) := fun a b hab=>
    ENNReal.toReal_mono (hfin k _).ne (hmono k (add_le_add le_rfl hab))
  have hFs k (hk : k<n) b (hb : b∈Icc 0 (R-r)) :
      (∫ t in 0..b,F k t)-ε*b≤F (k+1) b := by
    have hle := real_integral_of_mass_bound (M k) (hmono k) (hfin k) r (r+b) ε
      (by linarith [hb.1]) hε (M (k+1) (r+b)) (hfin _ _) (hstep k hk _ ⟨by linarith [hb.1],by linarith [hb.2]⟩)
    have he : (∫ t in 0..b,F k t) = ∫ t in r..r+b,(M k t).toReal := by
      simpa only [F,add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := b) (fun t=>(M k t).toReal) r
    rw [he]
    dsimp [F]
    linarith
  have hi := iterated_slicing_lower_bound F n (R-r) ε hFm hFs n le_rfl (R-r)
    ⟨sub_nonneg.mpr hrR,le_rfl⟩
  simpa only [F,add_zero,add_sub_cancel] using hi

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

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

def ballVolumeBound (D n : ℕ) (R : ℝ) : ℝ :=
  ((n+1)*D^(⌊R*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) : ℕ) / (n.factorial : ℝ)

include hi hn hK hΓaut in

theorem iterated_ball_volume (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    (c : FinProbability Y) (hc : c.coeff.support.card≤n+1) (B : Set X) (hB : IsClopen B)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)))
    (r : ℝ) (hr : 0≤r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D) :
    dividedPower n (R-r) * (ballMass (n := n) Γ hΓ (Q.pair 0) μ B 0 c r).toReal ≤
      ballVolumeBound D n R * (μ B).toReal + ε*slicingError n (R-r) := by
  have hdim j (hj : j≤n) x t (ht : t∈((Q.pair j).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair j).P.val x) : t.card≤j+1 := by
    apply (Q.point x).dimension_bound _ hj ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  let M : ℕ → ℝ → ℝ≥0∞ := fun j=>
    ballMass (n := n) Γ hΓ (Q.pair (min j n)) μ B (min j n) c
  have hmono j : Monotone (M j) := ballMass_mono Γ hΓ _ _ _ _ _
  have hfin j t : M j t<∞ := by
    apply lt_of_le_of_lt (hmono j (le_max_left t 0))
    exact ballMass_lt_top Γ hΓ hn hK _ μ B _ (hdim _ (min_le_right _ _)) c
      (max t 0) (le_max_right _ _)
  have hstep j (hj : j<n) b (hb : b∈Icc r R) :
      (∫⁻ t in Ioo r b,M j t)≤M (j+1) b+ENNReal.ofReal ε*ENNReal.ofReal (b-r) := by
    simpa only [M,min_eq_left hj.le,min_eq_left (Nat.succ_le_iff.mpr hj)] using
      ballMass_recurrence Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin hj c B hB hdisj r b hr hb.2
  have ht := iterated_mass_bound M n r R ε hrR hε hmono hfin hstep
  have htop := ballMass_top_bound Γ hΓ hn hK (Q.pair n) μ B c hc R hR.le D hD hdeg
  have htop' := ENNReal.toReal_mono (by finiteness) htop
  have hv : (ballMass (n := n) Γ hΓ (Q.pair n) μ B n c R).toReal ≤
      ballVolumeBound D n R * (μ B).toReal := by
    simpa [ballVolumeBound,ENNReal.toReal_mul,ENNReal.toReal_add,div_eq_mul_inv] using htop'
  simp only [M,min_self,zero_min] at ht
  nlinarith

end Sparse.GraphGeometry

end BassTrace

end

end OAI
