import OAI.RingTheory.BassTrace.BarycentricChains

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset

open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def vertexMean (s : Finset E) : E :=
  (s.card : ℝ)⁻¹ • ∑ x ∈ s, x

lemma vertexMean_mem_convexHull {s : Finset E} (hs : s.Nonempty) :
    vertexMean s ∈ convexHull ℝ (s : Set E) := by
  have h := s.centerMass_id_mem_convexHull (R := ℝ) (w := fun _ => 1)
    (fun _ _ => zero_le_one) (by simpa using (Nat.cast_pos.mpr hs.card_pos : (0 : ℝ) < s.card))
  simpa [Finset.centerMass, vertexMean] using h

lemma linear_vertexMean (f : E →ₗ[ℝ] ℝ) (s : Finset E) :
    f (vertexMean s) = (s.card : ℝ)⁻¹ * ∑ x ∈ s, f x := by
  simp [vertexMean]

lemma linear_vertexMean_le (f : E →ₗ[ℝ] ℝ) {s : Finset E} (hs : s.Nonempty)
    {b : ℝ} (hb : ∀ x ∈ s, f x ≤ b) : f (vertexMean s) ≤ b := by
  rw [linear_vertexMean]
  have hn : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  calc
    _ ≤ (s.card : ℝ)⁻¹ * ∑ _x ∈ s, b :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) (inv_nonneg.mpr hn.le)
    _ = b := by simp [ne_of_gt hn]

lemma linear_vertexMean_eq_iff (f : E →ₗ[ℝ] ℝ) {s : Finset E} (hs : s.Nonempty)
    {b : ℝ} (hb : ∀ x ∈ s, f x ≤ b) :
    f (vertexMean s) = b ↔ ∀ x ∈ s, f x = b := by
  have hn : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  rw [linear_vertexMean]
  constructor
  · intro h
    have he : ∑ x ∈ s, f x = ∑ _x ∈ s, b := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      calc
        _ = (s.card : ℝ) * ((s.card : ℝ)⁻¹ * ∑ x ∈ s, f x) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn), one_mul]
        _ = _ := by rw [h]
    exact (Finset.sum_eq_sum_iff_of_le hb).mp he
  · intro h
    rw [Finset.sum_congr rfl h]
    simp [ne_of_gt hn]

lemma vertexMean_eq_centroid {s : Finset E} (hs : s.Nonempty) :
    vertexMean s = s.centroid ℝ id := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, id_eq]
  exact Finset.smul_sum

lemma vertexMean_map {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : E ≃ᵃ[ℝ] F) {s : Finset E} (hs : s.Nonempty) :
    vertexMean (s.map f.toEquiv.toEmbedding) = f (vertexMean s) := by
  rw [vertexMean_eq_centroid hs, vertexMean_eq_centroid hs.map, Finset.centroid_map]
  simp only [Finset.centroid_def]
  convert (s.map_affineCombination id (s.centroidWeights ℝ)
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) f.toAffineMap).symm using 1 <;> rfl

def cell {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}

lemma exists_ray_boundary {I : Type*} [Fintype I]
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {c x : E}
    (hc : c ∈ cell a b) (hx : x ∈ cell a b)
    (hp : ∃ i, 0 < a i (x - c)) :
    ∃ (i : I) (t : ℝ), 1 ≤ t ∧
      c + t • (x - c) ∈ cell a b ∧
      a i (c + t • (x - c)) = b i ∧ a i c < b i ∧
      x ∈ segment ℝ c (c + t • (x - c)) := by
  classical
  let S : Finset I := Finset.univ.filter (fun i => 0 < a i (x - c))
  have hs : S.Nonempty := by
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image (fun i => (b i - a i c) / a i (x - c)) hs
  have hip : 0 < a i (x - c) := (Finset.mem_filter.mp hi).2
  let t := (b i - a i c) / a i (x - c)
  have ht : 1 ≤ t := by
    rw [le_div_iff₀ hip]
    simp only [one_mul, map_sub]
    linarith [hx i]
  have hteq : t * a i (x - c) = b i - a i c := by
    exact div_mul_cancel₀ _ (ne_of_gt hip)
  have hmem : c + t • (x - c) ∈ cell a b := by
    intro j
    simp only [map_add, map_smul, smul_eq_mul]
    by_cases hj : 0 < a j (x - c)
    · have hbound : t ≤ (b j - a j c) / a j (x - c) :=
        hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have hmul := (le_div_iff₀ hj).mp hbound
      linarith
    · have hmul : t * a j (x - c) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_not_gt hj)
      linarith [hc j]
  refine ⟨i, t, ht, hmem, ?_, ?_, ?_⟩
  · simp only [map_add, map_smul, smul_eq_mul]
    linarith
  · have : 0 < a i x - a i c := by simpa using hip
    linarith [hx i]
  · have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    refine ⟨1 - t⁻¹, t⁻¹, ?_, inv_nonneg.mpr ht0.le, by ring, ?_⟩
    · have := inv_le_one_of_one_le₀ ht
      linarith
    · simp only [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt ht0), one_smul,
        sub_smul, one_smul, smul_sub]
      module

section BoundedRay

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma bounded_cell_positive_direction {I : Type*}
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (hbounded : Bornology.IsBounded (cell a b))
    {c v : V} (hc : c ∈ cell a b) (hv : v ≠ 0) : ∃ i, 0 < a i v := by
  by_contra! h
  obtain ⟨R, hR⟩ := hbounded.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg c).trans (hR c hc)
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let t : ℝ := (R + ‖c‖ + 1) / ‖v‖
  have ht : 0 < t := div_pos (by positivity) hv0
  have hmem : c + t • v ∈ cell a b := by
    intro i
    simp only [map_add, map_smul, smul_eq_mul]
    have := mul_nonpos_of_nonneg_of_nonpos ht.le (h i)
    linarith [hc i]
  have hn : ‖t • v‖ ≤ R + ‖c‖ := by
    calc
      ‖t • v‖ = ‖(c + t • v) - c‖ := by congr 1; abel
      _ ≤ ‖c + t • v‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ R + ‖c‖ := add_le_add (hR _ hmem) le_rfl
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hn
  have hteq : t * ‖v‖ = R + ‖c‖ + 1 := div_mul_cancel₀ _ (ne_of_gt hv0)
  linarith

lemma bounded_exists_ray_boundary {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (hbounded : Bornology.IsBounded (cell a b))
    {c x : V} (hc : c ∈ cell a b) (hx : x ∈ cell a b) (hxc : x ≠ c) :
    ∃ (i : I) (t : ℝ), 1 ≤ t ∧
      c + t • (x - c) ∈ cell a b ∧
      a i (c + t • (x - c)) = b i ∧ a i c < b i ∧
      x ∈ segment ℝ c (c + t • (x - c)) :=
  exists_ray_boundary a b hc hx
    (bounded_cell_positive_direction a b hbounded hc (sub_ne_zero.mpr hxc))

end BoundedRay

lemma boundary_ray_unique {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {c y z : E}
    (hy : y ∈ cell a b) (hz : z ∈ cell a b)
    (hyi : ∃ i, a i y = b i ∧ a i c < b i)
    (hzi : ∃ i, a i z = b i ∧ a i c < b i)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (he : t • (y - c) = u • (z - c)) : t = u ∧ y = z := by
  obtain ⟨i, hiy, hic⟩ := hyi
  obtain ⟨j, hjz, hjc⟩ := hzi
  have he1 := congrArg (a i) he
  have he2 := congrArg (a j) he
  simp only [map_smul, map_sub, smul_eq_mul, hiy] at he1
  simp only [map_smul, map_sub, smul_eq_mul, hjz] at he2
  have htu : t ≤ u := by
    have hi := hz i
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hi (a i c)) hu.le
    nlinarith
  have hut : u ≤ t := by
    have hj := hy j
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hj (a j c)) ht.le
    nlinarith
  have h : t = u := le_antisymm htu hut
  refine ⟨h, ?_⟩
  rw [← h] at he
  have hdiff : y - c = z - c := by
    have hh := congrArg ((t⁻¹ : ℝ) • ·) he
    simpa [smul_smul, ne_of_gt ht] using hh
  exact sub_left_injective hdiff

lemma linear_eq_on_affineSpan (f : E →ₗ[ℝ] ℝ) {S : Set E} {b : ℝ}
    (hS : ∀ x ∈ S, f x = b) {x : E} (hx : x ∈ affineSpan ℝ S) : f x = b := by
  refine affineSpan_induction hx hS ?_
  intro t u v w hu hv hw
  simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, hu, hv, hw,
    sub_self, smul_zero, zero_add]

lemma affineIndependent_of_prefix_hyperplanes {n : ℕ} (p : Fin n → E)
    (h : ∀ i : Fin n, i.val ≠ 0 → ∃ (f : E →ₗ[ℝ] ℝ) (b : ℝ),
      (∀ j : Fin n, j < i → f (p j) = b) ∧ f (p i) ≠ b) :
    AffineIndependent ℝ p := by
  induction n with
  | zero => exact affineIndependent_of_subsingleton ℝ p
  | succ n ih =>
    cases n with
    | zero =>
      let : Subsingleton (Fin (0+1)) := Fin.subsingleton_one
      exact affineIndependent_of_subsingleton ℝ p
    | succ n =>
      have hpre : AffineIndependent ℝ (fun j : Fin (n+1) => p j.castSucc) := by
        apply ih
        intro i hi
        obtain ⟨f, b, hf, hne⟩ := h i.castSucc hi
        exact ⟨f, b, fun j hj => hf j.castSucc hj, hne⟩
      have hsub : AffineIndependent ℝ (fun j : {j : Fin (n+2) // j ≠ Fin.last (n+1)} => p j) := by
        rw [← affineIndependent_equiv (finSuccAboveEquiv (Fin.last (n+1)))]
        simpa only [Function.comp_def, finSuccAboveEquiv_apply, Fin.succAbove_last] using hpre
      apply hsub.affineIndependent_of_notMem_span
      obtain ⟨f, b, hf, hne⟩ := h (Fin.last (n+1)) (by simp)
      intro hmem
      apply hne
      apply linear_eq_on_affineSpan f (S := p '' {j | j ≠ Fin.last (n+1)}) _ hmem
      rintro y ⟨j, hj, rfl⟩
      exact hf j (Fin.lt_last_iff_ne_last.mpr hj)

lemma convexHull_inter_supporting (S : Set E) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hS : ∀ x ∈ S, f x ≤ b) :
    convexHull ℝ S ∩ {x | f x = b} = convexHull ℝ (S ∩ {x | f x = b}) := by
  let T := convexHull ℝ (S ∩ {x | f x = b})
  let C := {x : E | f x ≤ b ∧ (f x = b → x ∈ T)}
  have hSC : S ⊆ C := by
    intro x hx
    exact ⟨hS x hx, fun he => subset_convexHull ℝ _ ⟨hx, he⟩⟩
  have hC : Convex ℝ C := by
    intro x hx y hy u v hu hv huv
    change f (u • x + v • y) ≤ b ∧ (f (u • x + v • y) = b → _)
    simp only [map_add, map_smul, smul_eq_mul]
    have hew : u*b + v*b = b := by rw [← add_mul, huv, one_mul]
    have hux : 0 ≤ u*(b-f x) := mul_nonneg hu (sub_nonneg.mpr hx.1)
    have hvy : 0 ≤ v*(b-f y) := mul_nonneg hv (sub_nonneg.mpr hy.1)
    refine ⟨?_, ?_⟩
    · nlinarith only [hew, hux, hvy]
    · intro he
      by_cases hu0 : u = 0
      · have hv1 : v = 1 := by linarith
        have hyb : f y = b := by simpa [hu0, hv1] using he
        simpa [hu0, hv1] using hy.2 hyb
      by_cases hv0 : v = 0
      · have hu1 : u = 1 := by linarith
        have hxb : f x = b := by simpa [hv0, hu1] using he
        simpa [hv0, hu1] using hx.2 hxb
      have hux0 : u*(b-f x) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hvy0 : v*(b-f y) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hxb : f x = b := (sub_eq_zero.mp ((mul_eq_zero.mp hux0).resolve_left hu0)).symm
      have hyb : f y = b := (sub_eq_zero.mp ((mul_eq_zero.mp hvy0).resolve_left hv0)).symm
      exact (convex_convexHull ℝ _) (hx.2 hxb) (hy.2 hyb) hu hv huv
  apply subset_antisymm
  · intro x hx
    exact (convexHull_min hSC hC hx.1).2 hx.2
  · intro x hx
    refine ⟨convexHull_mono Set.inter_subset_left hx, ?_⟩
    exact linear_eq_on_affineSpan f (fun _ hy => hy.2)
      (convexHull_subset_affineSpan _ hx)

lemma vertexMean_notMem_supporting_affineSpan (f : E →ₗ[ℝ] ℝ)
    {s : Finset E} (hs : s.Nonempty) {b : ℝ}
    (hb : ∀ x ∈ s, f x ≤ b) (hp : ∃ x ∈ s, f x < b) :
    vertexMean s ∉ affineSpan ℝ {x | x ∈ s ∧ f x = b} := by
  intro hmem
  have hme : f (vertexMean s) = b :=
    linear_eq_on_affineSpan f (fun _ h => h.2) hmem
  obtain ⟨x, hx, hlt⟩ := hp
  exact (ne_of_lt hlt) ((linear_vertexMean_eq_iff f hs hb).mp hme x hx)

lemma exists_positive_ray_of_mem_convexHull_insert {S : Set E} {c x : E}
    (hx : x ∈ convexHull ℝ (insert c S)) (hxc : x ≠ c) :
    ∃ y ∈ convexHull ℝ S, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      x = c + t • (y-c) ∧ x ∈ segment ℝ c y := by
  have hS : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hx
    have : x = c := by simpa using hx
    exact hxc this
  rw [convexHull_insert hS, convexJoin_singleton_left] at hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
  have hseg := hxy
  obtain ⟨u, t, hu, ht, hut, he⟩ := hxy
  have ht0 : t ≠ 0 := by
    intro ht0
    have hu1 : u = 1 := by linarith
    apply hxc
    simpa [ht0, hu1] using he.symm
  refine ⟨y, hy, t, lt_of_le_of_ne ht (Ne.symm ht0), by linarith, ?_, hseg⟩
  rw [← he, show u = 1-t by linarith, sub_smul, one_smul, smul_sub]
  abel

def radialBoundary {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (c : E) : Set E :=
  {y | y ∈ cell a b ∧ ∃ i, a i y = b i ∧ a i c < b i}

lemma center_notMem_radialBoundary {I : Type*} (a : I → E →ₗ[ℝ] ℝ)
    (b : I → ℝ) (c : E) : c ∉ radialBoundary a b c := by
  rintro ⟨_, i, he, hi⟩
  exact (ne_of_lt hi) he

lemma cone_hull_inter {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    {c : E} {S T : Set E}
    (hS : convexHull ℝ S ⊆ radialBoundary a b c)
    (hT : convexHull ℝ T ⊆ radialBoundary a b c)
    (hST : convexHull ℝ S ∩ convexHull ℝ T ⊆ convexHull ℝ (S ∩ T)) :
    convexHull ℝ (insert c S) ∩ convexHull ℝ (insert c T) =
      convexHull ℝ (insert c (S ∩ T)) := by
  apply subset_antisymm
  · intro x hx
    by_cases hxc : x = c
    · subst x
      exact subset_convexHull ℝ _ (Set.mem_insert c _)
    obtain ⟨y, hy, t, ht, _, hxy, hseg⟩ :=
      exists_positive_ray_of_mem_convexHull_insert hx.1 hxc
    obtain ⟨z, hz, u, hu, _, hxz, _⟩ :=
      exists_positive_ray_of_mem_convexHull_insert hx.2 hxc
    have hray : t • (y-c) = u • (z-c) := by
      exact add_left_cancel (hxy.symm.trans hxz)
    have hyz := (boundary_ray_unique a b (hS hy).1 (hT hz).1
      (hS hy).2 (hT hz).2 ht hu hray).2
    have hyST : y ∈ convexHull ℝ (S ∩ T) := hST ⟨hy, hyz ▸ hz⟩
    exact (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (Set.mem_insert c _))
      (convexHull_mono (Set.subset_insert c _) hyST) hseg
  · exact Set.subset_inter
      (convexHull_mono (Set.insert_subset_insert Set.inter_subset_left))
      (convexHull_mono (Set.insert_subset_insert Set.inter_subset_right))

lemma cone_hull_inter_boundary {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    {c : E} {S T : Set E}
    (hS : convexHull ℝ S ⊆ radialBoundary a b c)
    (hT : convexHull ℝ T ⊆ radialBoundary a b c)
    (hST : convexHull ℝ S ∩ convexHull ℝ T ⊆ convexHull ℝ (S ∩ T)) :
    convexHull ℝ (insert c S) ∩ convexHull ℝ T = convexHull ℝ (S ∩ T) := by
  apply subset_antisymm
  · intro x hx
    have hxc : x ≠ c := by
      intro hh
      exact center_notMem_radialBoundary a b c (hh ▸ hT hx.2)
    obtain ⟨y, hy, t, ht, _, hxy, _⟩ :=
      exists_positive_ray_of_mem_convexHull_insert hx.1 hxc
    have hray : t • (y-c) = (1 : ℝ) • (x-c) := by
      rw [one_smul, hxy]
      abel
    have hyx := (boundary_ray_unique a b (hS hy).1 (hT hx.2).1
      (hS hy).2 (hT hx.2).2 ht zero_lt_one hray).2
    exact hST ⟨hyx ▸ hy, hx.2⟩
  · exact Set.subset_inter
      (convexHull_mono (Set.inter_subset_left.trans (Set.subset_insert c S)))
      (convexHull_mono Set.inter_subset_right)

lemma affineIndependent_insert {S : Set E} {c : E}
    (hS : AffineIndependent ℝ ((↑) : S → E)) (hc : c ∉ affineSpan ℝ S) :
    AffineIndependent ℝ (fun x : (insert c S : Set E) => (x : E)) := by
  let i : (insert c S : Set E) := ⟨c, Set.mem_insert c S⟩
  let f : {j : (insert c S : Set E) // j ≠ i} → S := fun j =>
    ⟨j.val.val, by
      rcases j.val.property with he | hm
      · exact False.elim (j.property (Subtype.ext he))
      · exact hm⟩
  have hf : Function.Injective f := by
    intro j k hjk
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S => (z : E)) hjk
  have hi : AffineIndependent ℝ (fun j : {j : (insert c S : Set E) // j ≠ i} =>
      (j.val : E)) := hS.comp_embedding ⟨f, hf⟩
  apply hi.affineIndependent_of_notMem_span
  intro hmem
  apply hc
  apply affineSpan_mono ℝ (s₁ := (fun x : (insert c S : Set E) => (x : E)) '' {j | j ≠ i})
    (s₂ := S) ?_ hmem
  rintro x ⟨j, hj, rfl⟩
  exact (f ⟨j, hj⟩).property

variable [DecidableEq E]

def coneFaces (B : Geometry.SimplicialComplex ℝ E) (c : E) : Set (Finset E) :=
  {{c}} ∪ B.faces ∪ (fun s => insert c s) '' B.faces

lemma mem_coneFaces_iff (B : Geometry.SimplicialComplex ℝ E) (c : E) (s : Finset E) :
    s ∈ coneFaces B c ↔ s = {c} ∨ s ∈ B.faces ∨ ∃ t ∈ B.faces, s = insert c t := by
  simp only [coneFaces, Set.mem_union, Set.mem_singleton_iff, Set.mem_image]
  aesop

lemma coneFaces_down_closed (B : Geometry.SimplicialComplex ℝ E) (c : E) :
    IsRelLowerSet (coneFaces B c) Finset.Nonempty := by
  intro s hs
  rw [mem_coneFaces_iff] at hs
  have hpos : s.Nonempty := by
    rcases hs with rfl | hs | ⟨t, _, rfl⟩
    · exact Finset.singleton_nonempty _
    · exact B.nonempty_of_mem_faces hs
    · exact Finset.insert_nonempty _ _
  refine ⟨hpos, ?_⟩
  intro t hts ht
  rw [mem_coneFaces_iff]
  rcases hs with rfl | hs | ⟨u, hu, rfl⟩
  · left
    exact Finset.Subset.antisymm hts (Finset.singleton_subset_iff.mpr
      (by obtain ⟨x, hx⟩ := ht; simpa only [Finset.mem_singleton.mp (hts hx)] using hx))
  · exact Or.inr (Or.inl (B.down_closed hs hts ht))
  · by_cases hct : c ∈ t
    · by_cases he : t.erase c = ∅
      · exact Or.inl ((Finset.erase_eq_empty_iff t c).mp he |>.resolve_left ht.ne_empty)
      · right; right
        refine ⟨t.erase c, B.down_closed hu ?_ (Finset.nonempty_iff_ne_empty.mpr he),
          (Finset.insert_erase hct).symm⟩
        intro x hx
        exact (Finset.mem_insert.mp (hts (Finset.mem_of_mem_erase hx))).resolve_left
          (Finset.ne_of_mem_erase hx)
    · right; left
      apply B.down_closed hu _ ht
      intro x hx
      rcases Finset.mem_insert.mp (hts hx) with rfl | hu'
      · exact False.elim (hct hx)
      · exact hu'

lemma center_mem_hull_coneFace_iff {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c) {s : Finset E} (hs : s ∈ coneFaces B c) :
    c ∈ convexHull ℝ (s : Set E) ↔ c ∈ s := by
  constructor
  · intro hc
    rcases (mem_coneFaces_iff B c s).mp hs with rfl | hs | ⟨t, _, rfl⟩
    · exact Finset.mem_singleton_self _
    · exact False.elim (center_notMem_radialBoundary a b c
        (hB (B.convexHull_subset_space hs hc)))
    · exact Finset.mem_insert_self _ _
  · intro hc
    exact subset_convexHull ℝ (s : Set E) hc

lemma coneFaces_inter_subset {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    {s t : Finset E} (hs : s ∈ coneFaces B c) (ht : t ∈ coneFaces B c) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
  intro x hx
  by_cases hxc : x = c
  · subst x
    exact subset_convexHull ℝ _
      ⟨(center_mem_hull_coneFace_iff a b B c hB hs).mp hx.1,
       (center_mem_hull_coneFace_iff a b B c hB ht).mp hx.2⟩
  have hnotS : s ≠ {c} := by
    intro hh
    apply hxc
    simpa [hh] using hx.1
  have hnotT : t ≠ {c} := by
    intro hh
    apply hxc
    simpa [hh] using hx.2
  have hs' := ((mem_coneFaces_iff B c s).mp hs).resolve_left hnotS
  have ht' := ((mem_coneFaces_iff B c t).mp ht).resolve_left hnotT
  have hcone (u v : Finset E) (hu : u ∈ B.faces) (hv : v ∈ B.faces) :=
    cone_hull_inter a b (B.convexHull_subset_space hu |>.trans hB)
      (B.convexHull_subset_space hv |>.trans hB) (B.inter_subset_convexHull hu hv)
  have hmixed (u v : Finset E) (hu : u ∈ B.faces) (hv : v ∈ B.faces) :=
    cone_hull_inter_boundary a b (B.convexHull_subset_space hu |>.trans hB)
      (B.convexHull_subset_space hv |>.trans hB) (B.inter_subset_convexHull hu hv)
  rcases hs' with hs | ⟨u, hu, rfl⟩ <;> rcases ht' with ht | ⟨v, hv, rfl⟩
  · exact B.inter_subset_convexHull hs ht hx
  · have hh : x ∈ convexHull ℝ ((v : Set E) ∩ s) := by
      rw [← hmixed v s hv hs]
      exact ⟨by simpa only [Finset.coe_insert] using hx.2, hx.1⟩
    exact convexHull_mono (by intro y hy; exact ⟨hy.2, Finset.mem_insert_of_mem hy.1⟩) hh
  · have hh : x ∈ convexHull ℝ ((u : Set E) ∩ t) := by
      rw [← hmixed u t hu ht]
      exact ⟨by simpa only [Finset.coe_insert] using hx.1, hx.2⟩
    exact convexHull_mono (by intro y hy; exact ⟨Finset.mem_insert_of_mem hy.1, hy.2⟩) hh
  · have hh : x ∈ convexHull ℝ (insert c ((u : Set E) ∩ v)) := by
      rw [← hcone u v hu hv]
      simpa only [Finset.coe_insert] using hx
    apply convexHull_mono _ hh
    intro y hy
    rcases hy with rfl | hy
    · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
    · exact ⟨Finset.mem_insert_of_mem hy.1, Finset.mem_insert_of_mem hy.2⟩

def coneComplex {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    (hspan : ∀ s ∈ B.faces, c ∉ affineSpan ℝ (s : Set E)) :
    Geometry.SimplicialComplex ℝ E where
  faces := coneFaces B c
  isRelLowerSet_faces := coneFaces_down_closed B c
  indep := by
    intro s hs
    rcases (mem_coneFaces_iff B c s).mp hs with rfl | hs | ⟨t, ht, rfl⟩
    · exact affineIndependent_of_subsingleton ℝ _
    · exact B.indep hs
    · have hh := affineIndependent_insert (B.indep ht) (hspan t ht)
      rw [← Finset.coe_insert] at hh
      exact hh
  inter_subset_convexHull := coneFaces_inter_subset a b B c hB

lemma coneComplex_finite {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    (hspan : ∀ s ∈ B.faces, c ∉ affineSpan ℝ (s : Set E))
    (hfinite : B.faces.Finite) : (coneComplex a b B c hB hspan).faces.Finite := by
  exact ((Set.finite_singleton _).union hfinite).union (hfinite.image _)

omit [DecidableEq E] in

lemma center_notMem_affineSpan_boundaryFace {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    {s : Finset E} (hs : s ∈ B.faces) : c ∉ affineSpan ℝ (s : Set E) := by
  have hn := B.nonempty_of_mem_faces hs
  obtain ⟨_, i, hi, hic⟩ := hB (B.convexHull_subset_space hs
    (vertexMean_mem_convexHull hn))
  have hle : ∀ x ∈ s, a i x ≤ b i := fun x hx =>
    (hB (B.subset_space hs hx)).1 i
  have he := (linear_vertexMean_eq_iff (a i) hn hle).mp hi
  intro hc
  exact (ne_of_lt hic) (linear_eq_on_affineSpan (a i) he hc)

lemma mem_coneComplex_space_iff {I : Type*}
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (B : Geometry.SimplicialComplex ℝ E) (c : E)
    (hB : B.space ⊆ radialBoundary a b c)
    (hspan : ∀ s ∈ B.faces, c ∉ affineSpan ℝ (s : Set E)) (x : E) :
    x ∈ (coneComplex a b B c hB hspan).space ↔
      x = c ∨ ∃ y ∈ B.space, x ∈ segment ℝ c y := by
  classical
  constructor
  · intro hx
    by_cases hxc : x = c
    · exact Or.inl hxc
    right
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    rcases (mem_coneFaces_iff B c s).mp hs with rfl | hs | ⟨t, ht, rfl⟩
    · exact (hxc (by simpa using hx)).elim
    · exact ⟨x, B.convexHull_subset_space hs hx, right_mem_segment _ _ _⟩
    · obtain ⟨y, hy, _, _, _, _, hxy⟩ :=
        exists_positive_ray_of_mem_convexHull_insert (by simpa using hx) hxc
      exact ⟨y, B.convexHull_subset_space ht hy, hxy⟩
  · intro hh
    rcases hh with hxc | ⟨y, hy, hx⟩
    · subst x
      apply Geometry.SimplicialComplex.mem_space_iff.mpr
      exact ⟨{c}, (mem_coneFaces_iff B c {c}).mpr (Or.inl rfl), by simp⟩
    · obtain ⟨s, hs, hy⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hy
      apply Geometry.SimplicialComplex.mem_space_iff.mpr
      refine ⟨insert c s, (mem_coneFaces_iff B c _).mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩)), ?_⟩
      apply (convex_convexHull ℝ (insert c s : Finset E)).segment_subset _ _ hx
      · exact subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
      · exact convexHull_mono (by intro z hz; exact Finset.mem_insert_of_mem hz) hy

omit [DecidableEq E] in
lemma convex_cell {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    Convex ℝ (cell a b) := by
  intro x hx y hy r s hr hs hrs i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    r * a i x + s * a i y ≤ r * b i + s * b i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
        (mul_le_mul_of_nonneg_left (hy i) hs)
    _ = b i := by rw [← add_mul, hrs, one_mul]

lemma coneComplex_space_eq_cell {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [DecidableEq V]
    {I : Type*} [Fintype I] (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hbounded : Bornology.IsBounded (cell a b))
    (B : Geometry.SimplicialComplex ℝ V) (c : V) (hc : c ∈ cell a b)
    (hB : B.space = radialBoundary a b c) :
    (coneComplex a b B c hB.subset
      (fun _ hs => center_notMem_affineSpan_boundaryFace a b B c hB.subset hs)).space
      = cell a b := by
  ext x
  rw [mem_coneComplex_space_iff]
  constructor
  · rintro (rfl | ⟨y, hy, hx⟩)
    · exact hc
    · exact (convex_cell a b).segment_subset hc (hB.subset hy).1 hx
  · intro hx
    by_cases hxc : x = c
    · exact Or.inl hxc
    obtain ⟨i, t, _, hy, hi, hic, hxy⟩ :=
      bounded_exists_ray_boundary a b hbounded hc hx hxc
    exact Or.inr ⟨c + t • (x-c), hB.symm.subset ⟨hy, i, hi, hic⟩, hxy⟩

end BassTrace.Sparse.Cuts

end OAI
