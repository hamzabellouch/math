import OAI.RingTheory.BassTrace.TransportMetric

namespace OAI

/-! Finite affine branch geometry for the exact transport metric and compatible cuts. -/

namespace BassTrace.Sparse

open Set Filter

open scoped Topology

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]

def halfspacePolyhedron (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}

noncomputable def activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) : Finset I :=
  Finset.univ.filter fun i => a i x = b i

lemma mem_activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) (i : I) :
    i ∈ activeConstraints a b x ↔ a i x = b i := by
  classical
  simp [activeConstraints]

lemma exists_extrapolate_mem
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {x y : E}
    (hx : x ∈ halfspacePolyhedron a b)
    (hactive : activeConstraints a b x = activeConstraints a b y) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - y) ∈ halfspacePolyhedron a b := by
  have hi (i : I) : ∀ᶠ t : ℝ in 𝓝 0, a i (x + t • (x - y)) ≤ b i := by
    by_cases h : a i x = b i
    · have hyi : a i y = b i := by
        rw [← mem_activeConstraints, ← hactive, mem_activeConstraints]
        exact h
      filter_upwards [] with t
      simp only [map_add, map_smul, map_sub, smul_eq_mul, h, hyi, sub_self,
        mul_zero, add_zero, le_refl]
    · have hlt : a i x < b i := lt_of_le_of_ne (hx i) h
      have hc : Continuous (fun t : ℝ => a i x + t * (a i x - a i y)) := by fun_prop
      have he : ∀ᶠ t : ℝ in 𝓝 0, a i x + t * (a i x - a i y) < b i :=
        hc.continuousAt.eventually (gt_mem_nhds (by simpa using hlt))
      filter_upwards [he] with t ht
      simpa only [map_add, map_smul, map_sub, smul_eq_mul] using ht.le
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, a i (x + t • (x - y)) ≤ b i :=
    Filter.eventually_all.mpr hi
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨δ / 2, by positivity, hball ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos (by positivity : 0 < δ / 2)]
  linarith

lemma activeConstraints_injOn_extremePoints
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    Set.InjOn (activeConstraints a b) ((halfspacePolyhedron a b).extremePoints ℝ) := by
  intro x hx y hy hactive
  obtain ⟨t, ht, hz⟩ := exists_extrapolate_mem a b hx.1 hactive
  have hsum : t + 1 ≠ 0 := by positivity
  have hseg : x ∈ openSegment ℝ y (x + t • (x - y)) := by
    apply mem_openSegment_iff_div.mpr
    refine ⟨t, 1, ht, by norm_num, ?_⟩
    simp only [smul_add, smul_sub, smul_smul]
    rw [show 1 / (t + 1) * t = t / (t + 1) by ring]
    calc
      _ = (1 / (t + 1) + t / (t + 1)) • x := by module
      _ = x := by rw [← add_div, add_comm 1 t, div_self hsum, one_smul]
  exact (hx.2 hy.1 hz hseg).symm

lemma finite_extremePoints_halfspacePolyhedron
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ((halfspacePolyhedron a b).extremePoints ℝ).Finite := by
  classical
  exact Set.Finite.of_injOn (t := Set.univ) (Set.mapsTo_univ _ _)
    (activeConstraints_injOn_extremePoints a b) Set.finite_univ

noncomputable def polyhedronVertices (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Finset E :=
  (finite_extremePoints_halfspacePolyhedron a b).toFinset

@[simp] lemma mem_polyhedronVertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) :
    x ∈ polyhedronVertices a b ↔ x ∈ (halfspacePolyhedron a b).extremePoints ℝ :=
  Set.Finite.mem_toFinset _

section Compact

variable [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

lemma exists_extreme_maximizer {s : Set E} (hs : IsCompact s) (hne : s.Nonempty)
    (f : E →L[ℝ] ℝ) :
    ∃ x ∈ s.extremePoints ℝ, ∀ y ∈ s, f y ≤ f x := by
  obtain ⟨x, hx, hxmax⟩ := hs.exists_isMaxOn hne f.continuous.continuousOn
  have hex : IsExposed ℝ s {x ∈ s | ∀ y ∈ s, f y ≤ f x} := fun _ => ⟨f, rfl⟩
  obtain ⟨z, hz⟩ := (hex.isCompact hs).extremePoints_nonempty ⟨x, hx, hxmax⟩
  exact ⟨z, hex.isExtreme.extremePoints_subset_extremePoints hz, hz.1.2⟩

lemma exists_vertex_maximizer (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hc : IsCompact (halfspacePolyhedron a b))
    (hne : (halfspacePolyhedron a b).Nonempty) (f : E →L[ℝ] ℝ) :
    ∃ x ∈ polyhedronVertices a b, ∀ y ∈ halfspacePolyhedron a b, f y ≤ f x := by
  simpa only [mem_polyhedronVertices] using exists_extreme_maximizer hc hne f

lemma halfspacePolyhedron_eq_convexHull_vertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hc : IsCompact (halfspacePolyhedron a b)) :
    halfspacePolyhedron a b = convexHull ℝ (polyhedronVertices a b : Set E) := by
  have hv : Convex ℝ (halfspacePolyhedron a b) := by
    intro x hx y hy r s hr hs hrs i
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      r * a i x + s * a i y ≤ r * b i + s * b i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
          (mul_le_mul_of_nonneg_left (hy i) hs)
      _ = b i := by rw [← add_mul, hrs, one_mul]
  have he : (polyhedronVertices a b : Set E) =
      (halfspacePolyhedron a b).extremePoints ℝ := by
    ext x
    exact mem_polyhedronVertices a b x
  have h := closure_convexHull_extremePoints hc hv
  rw [← he, ((polyhedronVertices a b).finite_toSet.isClosed_convexHull (𝕜 := ℝ)).closure_eq] at h
  exact h.symm

end Compact

section Potential

variable {V : Type*} [Fintype V] [MetricSpace V]

def potentialSet : Set (V → ℝ) :=
  {l | (∑ v, l v) = 0 ∧ ∀ v w, |l v - l w| ≤ dist v w}

noncomputable def potentialLinear : (V × V) ⊕ Bool → (V → ℝ) →ₗ[ℝ] ℝ
  | .inl (v,w) => LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) v - LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) w
  | .inr false => ∑ v : V, LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) v
  | .inr true => -∑ v : V, LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) v

def potentialBound : (V × V) ⊕ Bool → ℝ
  | .inl (v,w) => dist v w
  | .inr _ => 0

lemma potentialSet_eq_halfspacePolyhedron :
    (potentialSet : Set (V → ℝ)) = halfspacePolyhedron potentialLinear potentialBound := by
  classical
  ext l
  constructor
  · rintro ⟨hzero, hdist⟩ (⟨v,w⟩ | b)
    · exact le_trans (le_abs_self _) (hdist v w)
    · cases b <;> simp [potentialLinear, potentialBound, hzero]
  · intro h
    have hle : (∑ v, l v) ≤ 0 := by simpa [potentialLinear, potentialBound] using h (.inr false)
    have hge : 0 ≤ ∑ v, l v := by simpa [potentialLinear, potentialBound] using h (.inr true)
    refine ⟨le_antisymm hle hge, fun v w => abs_le.mpr ⟨?_, ?_⟩⟩
    · have h' : l w - l v ≤ dist v w := by
        simpa [potentialLinear, potentialBound, dist_comm] using h (.inl (w,v))
      linarith
    · exact h (.inl (v,w))

lemma zero_mem_potentialSet : (0 : V → ℝ) ∈ potentialSet := by
  simp [potentialSet, dist_nonneg]

lemma isClosed_potentialSet : IsClosed (potentialSet : Set (V → ℝ)) := by
  have heq : (potentialSet : Set (V → ℝ)) =
      {l | (∑ v, l v) = 0} ∩ ⋂ v, ⋂ w, {l | |l v - l w| ≤ dist v w} := by
    ext l
    simp [potentialSet]
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun v => isClosed_iInter fun w =>
      isClosed_le (by fun_prop) continuous_const

noncomputable def totalDistances : ℝ := ∑ v : V, ∑ w : V, dist v w

lemma totalDistances_nonneg : 0 ≤ totalDistances (V := V) :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg

lemma dist_le_totalDistances (v w : V) : dist v w ≤ totalDistances (V := V) := by
  classical
  apply (Finset.single_le_sum (f := fun w' : V => dist v w') (fun _ _ => dist_nonneg) (Finset.mem_univ w)).trans
  exact Finset.single_le_sum (f := fun v' : V => ∑ w' : V, dist v' w')
    (fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg) (Finset.mem_univ v)

lemma potential_coordinate_bound [Nonempty V] {l : V → ℝ} (hl : l ∈ potentialSet) (v : V) :
    |l v| ≤ totalDistances (V := V) := by
  classical
  have hmin : ∃ w, l w ≤ 0 := by
    by_contra! h
    have hp : 0 < ∑ w, l w := Finset.sum_pos (fun w _ => h w) Finset.univ_nonempty
    rw [hl.1] at hp
    exact lt_irrefl 0 hp
  have hmax : ∃ w, 0 ≤ l w := by
    by_contra! h
    have hp : ∑ w, l w < 0 := Finset.sum_neg (fun w _ => h w) Finset.univ_nonempty
    rw [hl.1] at hp
    exact lt_irrefl 0 hp
  obtain ⟨w, hw⟩ := hmin
  obtain ⟨z, hz⟩ := hmax
  have hvw := (hl.2 v w).trans (dist_le_totalDistances v w)
  have hvz := (hl.2 v z).trans (dist_le_totalDistances v z)
  rw [abs_le] at hvw hvz ⊢
  constructor <;> linarith

lemma isCompact_potentialSet [Nonempty V] : IsCompact (potentialSet : Set (V → ℝ)) := by
  apply IsCompact.of_isClosed_subset (s := Set.Icc (fun _ : V => -totalDistances (V := V))
    (fun _ : V => totalDistances (V := V))) isCompact_Icc isClosed_potentialSet
  intro l hl
  constructor <;> intro v
  · exact (abs_le.mp (potential_coordinate_bound hl v)).1
  · exact (abs_le.mp (potential_coordinate_bound hl v)).2

noncomputable def potentialVertices : Finset (V → ℝ) :=
  polyhedronVertices potentialLinear potentialBound

lemma mem_potentialVertices (l : V → ℝ) :
    l ∈ potentialVertices ↔ l ∈ (potentialSet : Set (V → ℝ)).extremePoints ℝ := by
  rw [potentialVertices, mem_polyhedronVertices, ← potentialSet_eq_halfspacePolyhedron]

lemma potentialVertices_subset (l : V → ℝ) (hl : l ∈ potentialVertices) : l ∈ potentialSet :=
  (mem_potentialVertices l).mp hl |>.1

lemma exists_potential_vertex_maximizer [Nonempty V] (f : (V → ℝ) →L[ℝ] ℝ) :
    ∃ l ∈ potentialVertices, ∀ k ∈ potentialSet, f k ≤ f l := by
  simpa only [mem_potentialVertices] using
    exists_extreme_maximizer isCompact_potentialSet ⟨0, zero_mem_potentialSet⟩ f

noncomputable def centerPotential (l : V → ℝ) (v : V) : ℝ :=
  l v - (∑ w, l w) / Fintype.card V

lemma centerPotential_mem [Nonempty V] {l : V → ℝ} (hl : LipschitzWith 1 l) :
    centerPotential l ∈ potentialSet := by
  classical
  have hc : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · simp only [centerPotential, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  · intro v w
    have h := hl.dist_le_mul v w
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    convert h using 1
    unfold centerPotential
    congr 1
    ring

noncomputable def potentialPairing (k : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ v : V, (k v) • ContinuousLinearMap.proj v

omit [MetricSpace V] in
lemma potentialPairing_apply (k l : V → ℝ) :
    potentialPairing k l = ∑ v, k v * l v := by
  classical
  simp [potentialPairing]

omit [MetricSpace V] in
lemma pairing_centerPotential (k l : V → ℝ) (hk : ∑ v, k v = 0) :
    potentialPairing k (centerPotential l) = potentialPairing k l := by
  classical
  simp only [potentialPairing_apply, centerPotential, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hk, zero_mul, sub_zero]

lemma lipschitz_potential {l : V → ℝ} (hl : l ∈ potentialSet) : LipschitzWith 1 l := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl.2 v w

end Potential

variable {Y : Type*} [MetricSpace Y] (S : Finset Y)

lemma exists_global_potential_extension {l : S → ℝ} (hl : l ∈ potentialSet) :
    ∃ f : Y → ℝ, LipschitzWith 1 f ∧ ∀ v : S, f v = l v := by
  classical
  let p : Y → ℝ := fun y => if h : y ∈ S then l ⟨y,h⟩ else 0
  have hp : LipschitzOnWith 1 p (S : Set Y) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro v hv w hw
    change v ∈ S at hv
    change w ∈ S at hw
    simpa only [p, dite_eq_left hv, dite_eq_left hw, Real.dist_eq, NNReal.coe_one, one_mul, Subtype.dist_eq]
      using hl.2 ⟨v,hv⟩ ⟨w,hw⟩
  obtain ⟨f, hf, hpf⟩ := hp.extend_real
  refine ⟨f, hf, fun v => ?_⟩
  have h := hpf v.2
  simpa [p, v.2, eq_comm] using h

lemma exists_global_vertex_maximizer (hne : S.Nonempty) (k : S → ℝ)
    (hk : ∑ v, k v = 0) :
    ∃ l ∈ (potentialVertices : Finset (S → ℝ)),
      (∃ f : Y → ℝ, LipschitzWith 1 f ∧ ∀ v : S, f v = l v) ∧
      ∀ f : Y → ℝ, LipschitzWith 1 f →
        (∑ v : S, k v * f v) ≤ ∑ v : S, k v * l v := by
  have : Nonempty S := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨⟨v,hv⟩⟩
  obtain ⟨l, hl, hmax⟩ := exists_potential_vertex_maximizer (potentialPairing k)
  refine ⟨l, hl, exists_global_potential_extension S (potentialVertices_subset l hl), ?_⟩
  intro f hf
  have hsub : LipschitzWith 1 (fun v : S => f v) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using hf.dist_le_mul v.val w.val
  have hm := hmax (centerPotential (fun v : S => f v)) (centerPotential_mem hsub)
  rw [pairing_centerPotential k _ hk] at hm
  simpa only [potentialPairing_apply] using hm

def globalPairingValues (k : S → ℝ) : Set ℝ :=
  {a | ∃ f : Y → ℝ, LipschitzWith 1 f ∧ a = ∑ v : S, k v * f v}

lemma global_dual_eq_finite_vertex_max (hne : S.Nonempty) (k : S → ℝ)
    (hk : ∑ v, k v = 0) :
    sSup (globalPairingValues S k) =
      sSup ((fun l : S → ℝ => ∑ v : S, k v * l v) ''
        ((potentialVertices : Finset (S → ℝ)) : Set (S → ℝ))) := by
  classical
  obtain ⟨l, hl, ⟨f, hf, hfl⟩, hmax⟩ := exists_global_vertex_maximizer S hne k hk
  let m := ∑ v : S, k v * l v
  have hgreat : IsGreatest (globalPairingValues S k) m := by
    constructor
    · refine ⟨f, hf, ?_⟩
      simp only [m, hfl]
    · rintro a ⟨g, hg, rfl⟩
      exact hmax g hg
  have hfinite : IsGreatest
      ((fun l : S → ℝ => ∑ v : S, k v * l v) ''
        ((potentialVertices : Finset (S → ℝ)) : Set (S → ℝ))) m := by
    constructor
    · exact ⟨l, hl, rfl⟩
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨g, hg, hgp⟩ := exists_global_potential_extension S
        (potentialVertices_subset p hp)
      simpa only [hgp] using hmax g hg
  exact hgreat.csSup_eq.trans hfinite.csSup_eq.symm

end BassTrace.Sparse

end OAI
