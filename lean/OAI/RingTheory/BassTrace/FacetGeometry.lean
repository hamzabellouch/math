import OAI.RingTheory.BassTrace.Incidence

namespace OAI

noncomputable section

/-! Two-sided facet incidence inside a single affine carrier, without a manifold hypothesis. -/

namespace BassTrace.Sparse

section

open Set Finset

open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma exists_weights_of_mem_affineSpan {s : Finset E} {v : E}
    (hv : v ∈ affineSpan ℝ (s : Set E)) :
    ∃ w : E → ℝ, ∑ x ∈ s, w x = 1 ∧ v = ∑ x ∈ s, w x • x := by
  classical
  have hv' : v ∈ affineSpan ℝ (Set.range (fun x : s => (x : E))) := by simpa using hv
  obtain ⟨w, hw, hvw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hv'
  let w' : E → ℝ := fun x => if h : x ∈ s then w ⟨x, h⟩ else 0
  have hsum : ∑ x ∈ s, w' x = ∑ x : s, w x := by
    rw [← Finset.sum_attach]
    simp [w']
  refine ⟨w', hsum.trans hw, ?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at hvw
  rw [← Finset.sum_attach]
  simpa [w'] using hvw

lemma exists_small_positive_weights {I : Type*} (s : Finset I) (w : I → ℝ)
    {c : ℝ} (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ i ∈ s, 0 < δ * w i + (1-δ) * c := by
  have he : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i ∈ s, 0 < δ * w i + (1-δ) * c := by
    apply (s.eventually_all).mpr
    intro i _
    have hcont : Continuous (fun δ : ℝ => δ * w i + (1-δ) * c) := by fun_prop
    exact hcont.continuousAt.eventually (eventually_gt_nhds (by simpa using hc))
  have he' := he.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hlt := (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  exact (hpos.and (hlt.and he')).exists

lemma sum_weights_mem_convexHull (s : Finset E) {w : E → ℝ}
    (hw : ∀ x ∈ s, 0 ≤ w x) (hsum : ∑ x ∈ s, w x = 1) :
    ∑ x ∈ s, w x • x ∈ convexHull ℝ (s : Set E) :=
  (convex_convexHull ℝ (s : Set E)).sum_mem hw hsum
    (fun _ hx => subset_convexHull ℝ (s : Set E) hx)

end

section

open Set Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma same_side_cone_overlap [DecidableEq E] {F : Finset E} (hF : F.Nonempty) {u v : E}
    (huF : u ∉ F) (hvspan : v ∈ affineSpan ℝ ((insert u F : Finset E) : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hu : b < f u) (hv : b < f v) :
    ∃ p, p ∈ convexHull ℝ ((insert u F : Finset E) : Set E) ∧
      p ∈ convexHull ℝ ((insert v F : Finset E) : Set E) ∧ b < f p := by
  classical
  obtain ⟨w, hw, hvw⟩ := exists_weights_of_mem_affineSpan hvspan
  have hsum : w u + ∑ x ∈ F, w x = 1 := by simpa [Finset.sum_insert huF] using hw
  have hfv : f v = w u * f u + (∑ x ∈ F, w x) * b := by
    rw [hvw, map_sum, Finset.sum_insert huF]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun x hx => congrArg (w x * ·) (hFb x hx))]
    rw [Finset.sum_mul]
  have hwu : 0 < w u := by
    have he : f v - b = w u * (f u - b) := by linear_combination hfv + b * hsum
    have hm : 0 < w u * (f u - b) := he ▸ sub_pos.mpr hv
    exact (mul_pos_iff_of_pos_right (sub_pos.mpr hu)).mp hm
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr hF.card_pos)
  have hcsum : ∑ _x ∈ F, c = 1 := by
    simp [c, ne_of_gt (Nat.cast_pos.mpr hF.card_pos : (0 : ℝ) < F.card)]
  let q : E := ∑ x ∈ F, c • x
  have hq : q ∈ convexHull ℝ (F : Set E) :=
    sum_weights_mem_convexHull F (fun _ _ => hc.le) hcsum
  have hfq : f q = b := by
    change f (∑ x ∈ F, c • x) = b
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun x hx => congrArg (c * ·) (hFb x hx)),
      ← Finset.sum_mul, hcsum, one_mul]
  obtain ⟨δ, hδ, hδ1, hδw⟩ := exists_small_positive_weights F w hc
  let r : E → ℝ := fun x => if x = u then 0 else c
  have hrF (x : E) (hx : x ∈ F) : r x = c := by
    simp [r, ne_of_mem_of_not_mem hx huF]
  have hru : r u = 0 := by simp [r]
  have hrsum : ∑ x ∈ insert u F, r x = 1 := by
    rw [Finset.sum_insert huF, hru, zero_add]
    rw [Finset.sum_congr rfl hrF]
    exact hcsum
  have hrq : ∑ x ∈ insert u F, r x • x = q := by
    rw [Finset.sum_insert huF, hru, zero_smul, zero_add]
    exact Finset.sum_congr rfl (fun x hx => by rw [hrF x hx])
  let z : E → ℝ := fun x => δ * w x + (1-δ) * r x
  have hz : ∀ x ∈ insert u F, 0 ≤ z x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp only [z, hru, mul_zero, add_zero]
      exact (mul_pos hδ hwu).le
    · simpa only [z, hrF x hx] using (hδw x hx).le
  have hzsum : ∑ x ∈ insert u F, z x = 1 := by
    simp only [z, Finset.sum_add_distrib, ← Finset.mul_sum, hw, hrsum]
    ring
  have hzp : ∑ x ∈ insert u F, z x • x = δ • v + (1-δ) • q := by
    simp only [z, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [← hvw, hrq]
  refine ⟨δ • v + (1-δ) • q, ?_, ?_, ?_⟩
  · rw [← hzp]
    exact sum_weights_mem_convexHull _ hz hzsum
  · apply (convex_convexHull ℝ ((insert v F : Finset E) : Set E))
      (subset_convexHull ℝ _ (Finset.mem_insert_self v F))
      ((convexHull_mono (show (F : Set E) ⊆ ((insert v F : Finset E) : Set E) from
        Finset.subset_insert _ _)) hq) hδ.le (sub_nonneg.mpr hδ1.le)
    ring
  · simp only [map_add, map_smul, smul_eq_mul, hfq]
    nlinarith [mul_pos hδ (sub_pos.mpr hv)]

end

section

open Set Finset

open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma apex_notMem_affineSpan {F : Finset E} {u : E} (hu : u ∉ F)
    (h : AffineIndependent ℝ ((↑) : ↥(insert u F) → E)) :
    u ∉ affineSpan ℝ (F : Set E) := by
  let i : ↥(insert u F) := ⟨u, Finset.mem_insert_self _ _⟩
  have hnot := h.notMem_affineSpan_sdiff i Set.univ
  have he : ((↑) : ↥(insert u F) → E) '' (Set.univ \ {i}) = (F : Set E) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases Finset.mem_insert.mp j.property with hj' | hj'
      · exact False.elim (hj.2 (Set.mem_singleton_iff.mpr (Subtype.ext hj')))
      · exact hj'
    · intro hx
      refine ⟨⟨x, Finset.mem_insert_of_mem hx⟩, ⟨Set.mem_univ _, ?_⟩, rfl⟩
      intro hi
      have hxu : x = u := congrArg Subtype.val (Set.mem_singleton_iff.mp hi)
      exact hu (hxu ▸ hx)
  simpa only [he] using hnot

lemma exists_facet_form {F : Finset E} (hF : F.Nonempty) {u : E}
    (hu : u ∉ affineSpan ℝ (F : Set E)) :
    ∃ (f : E →ₗ[ℝ] ℝ) (b : ℝ), (∀ x ∈ F, f x = b) ∧ f u ≠ b := by
  obtain ⟨a, ha⟩ := hF
  have has : a ∈ affineSpan ℝ (F : Set E) := subset_affineSpan ℝ _ ha
  have hua : u - a ∉ (affineSpan ℝ (F : Set E)).direction := by
    simpa only [← AffineSubspace.vsub_right_mem_direction_iff_mem has u,
      vsub_eq_sub] using hu
  obtain ⟨f, hfu, hfker⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hua inferInstance
  refine ⟨f, f a, ?_, ?_⟩
  · intro x hx
    have hxa : x - a ∈ (affineSpan ℝ (F : Set E)).direction :=
      (AffineSubspace.vsub_right_mem_direction_iff_mem has x).mpr
        (subset_affineSpan ℝ _ hx)
    have hz : f (x-a) = 0 := by
      have hm : f (x-a) ∈ (affineSpan ℝ (F : Set E)).direction.map f :=
        Submodule.mem_map.mpr ⟨x-a, hxa, rfl⟩
      rw [hfker, Submodule.mem_bot] at hm
      exact hm
    simpa only [map_sub, sub_eq_zero] using hz
  · simpa only [map_sub, sub_ne_zero] using hfu

lemma affineForm_eq_on_convexHull {F : Finset E} (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (h : ∀ x ∈ F, f x = b) {p : E} (hp : p ∈ convexHull ℝ (F : Set E)) : f p = b := by
  have he : (F : Set E).EqOn f.toAffineMap (AffineMap.const ℝ E b) := h
  exact AffineMap.eqOn_affineSpan he (convexHull_subset_affineSpan _ hp)

lemma eq_of_facet_same_side (K : Geometry.SimplicialComplex ℝ E)
    {F : Finset E} (hF : F.Nonempty) {u v : E} (huF : u ∉ F) (hvF : v ∉ F)
    (huK : insert u F ∈ K.faces) (hvK : insert v F ∈ K.faces)
    (hspan : v ∈ affineSpan ℝ ((insert u F : Finset E) : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hu : b < f u) (hv : b < f v) : u = v := by
  by_contra huv
  obtain ⟨p, hpu, hpv, hp⟩ := same_side_cone_overlap hF huF hspan f b hFb hu hv
  have hinter : ((insert u F : Finset E) : Set E) ∩
      ((insert v F : Finset E) : Set E) = (F : Set E) := by
    ext x
    simp only [Finset.coe_insert, Set.mem_inter_iff, Set.mem_insert_iff]
    aesop
  have hpf := K.inter_subset_convexHull huK hvK ⟨hpu, hpv⟩
  rw [hinter] at hpf
  exact (ne_of_gt hp) (affineForm_eq_on_convexHull f b hFb hpf)

lemma facet_apex_card_le_two (K : Geometry.SimplicialComplex ℝ E)
    {F A : Finset E} (hF : F.Nonempty)
    (hAK : ∀ u ∈ A, insert u F ∈ K.faces) (hAF : ∀ u ∈ A, u ∉ F)
    (hcarrier : ∀ u ∈ A, ∀ v ∈ A,
      affineSpan ℝ ((insert u F : Finset E) : Set E) =
        affineSpan ℝ ((insert v F : Finset E) : Set E)) : A.card ≤ 2 := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  obtain ⟨f, b, hFb, hab⟩ := exists_facet_form hF
    (apex_notMem_affineSpan (hAF a ha) (K.indep (hAK a ha)))
  have hne (u : E) (hu : u ∈ A) : f u ≠ b := by
    intro hub
    have hon : ((insert u F : Finset E) : Set E).EqOn
        f.toAffineMap (AffineMap.const ℝ E b) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hub
      · exact hFb x hx
    have he := AffineMap.eqOn_affineSpan hon
    apply hab
    apply he
    rw [hcarrier u hu a ha]
    exact subset_affineSpan ℝ _ (Finset.mem_insert_self _ _)
  let side : A → Bool := fun u => decide (b < f u)
  have hinj : Function.Injective side := by
    intro u v huv
    apply Subtype.ext
    have hs : (b < f u) ↔ (b < f v) := by
      exact decide_eq_decide.mp huv
    have hspan : (v : E) ∈ affineSpan ℝ ((insert (u : E) F : Finset E) : Set E) := by
      rw [hcarrier u u.property v v.property]
      exact subset_affineSpan ℝ _ (Finset.mem_insert_self _ _)
    by_cases hu : b < f u
    · exact eq_of_facet_same_side K hF (hAF u u.property) (hAF v v.property)
        (hAK u u.property) (hAK v v.property) hspan f b hFb hu (hs.mp hu)
    · have hv : ¬ b < f v := fun hv => hu (hs.mpr hv)
      have hul : f u < b := lt_of_le_of_ne (le_of_not_gt hu) (hne u u.property)
      have hvl : f v < b := lt_of_le_of_ne (le_of_not_gt hv) (hne v v.property)
      exact eq_of_facet_same_side K hF (hAF u u.property) (hAF v v.property)
        (hAK u u.property) (hAK v v.property) hspan (-f) (-b)
        (fun x hx => congrArg Neg.neg (hFb x hx))
        (neg_lt_neg hul) (neg_lt_neg hvl)
  simpa using Fintype.card_le_of_injective side hinj

lemma affineSpan_eq_of_card_eq {s t : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E)) (hc : t.card = s.card) :
    affineSpan ℝ (t : Set E) = affineSpan ℝ (s : Set E) := by
  have hle : affineSpan ℝ (t : Set E) ≤ affineSpan ℝ (s : Set E) :=
    affineSpan_le.mpr (hst.trans (convexHull_subset_affineSpan _))
  by_contra hne
  have hlt := ht.card_lt_card_of_affineSpan_lt_affineSpan (lt_of_le_of_ne hle hne)
  omega

lemma facet_coface_card_le_two (K : Geometry.SimplicialComplex ℝ E)
    {F S : Finset E} {B : Finset (Finset E)} (hF : F.Nonempty)
    (hS : S.card = F.card + 1) (hB : ∀ t ∈ B, t ∈ K.faces)
    (hFB : ∀ t ∈ B, F ⊆ t ∧ t.card = F.card + 1)
    (hBS : ∀ t ∈ B, (t : Set E) ⊆ convexHull ℝ (S : Set E)) : B.card ≤ 2 := by
  have hex (t : B) : ∃ u ∉ F, insert u F = (t : Finset E) :=
    Finset.exists_eq_insert_iff.mpr ⟨(hFB t t.property).1, (hFB t t.property).2.symm⟩
  let apex : B → E := fun t => (hex t).choose
  have ha (t : B) : apex t ∉ F ∧ insert (apex t) F = (t : Finset E) :=
    (hex t).choose_spec
  let A : Finset E := Finset.univ.image apex
  have hAK : ∀ u ∈ A, insert u F ∈ K.faces := by
    intro u hu
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    rw [(ha t).2]
    exact hB t t.property
  have hAF : ∀ u ∈ A, u ∉ F := by
    intro u hu
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    exact (ha t).1
  have hsp (u : E) (hu : u ∈ A) :
      affineSpan ℝ ((insert u F : Finset E) : Set E) = affineSpan ℝ (S : Set E) := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    rw [(ha t).2]
    exact affineSpan_eq_of_card_eq (K.indep (hB t t.property)) (hBS t t.property)
      ((hFB t t.property).2.trans hS.symm)
  have hA := facet_apex_card_le_two K hF hAK hAF
    (fun u hu v hv => (hsp u hu).trans (hsp v hv).symm)
  have hinj : Function.Injective apex := by
    intro t t' he
    apply Subtype.ext
    calc (t : Finset E) = insert (apex t) F := (ha t).2.symm
         _ = insert (apex t') F := by rw [he]
         _ = (t' : Finset E) := (ha t').2
  have hc : A.card = B.card := by simp [A, Finset.card_image_of_injective _ hinj]
  rwa [hc] at hA

end

section

open Set Finset

open scoped Topology Classical

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma positiveCombination_carrier {F T : Finset E}
    (hF : AffineIndependent ℝ ((↑) : F → E)) (hTF : T ⊆ F)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hq : (∑ x ∈ F, w x • x) ∈ convexHull ℝ (T : Set E)) : F ⊆ T := by
  classical
  obtain ⟨a,_,has,hap⟩ := Finset.mem_convexHull'.mp hq
  let a' : E → ℝ := fun x => if x ∈ T then a x else 0
  have hs : ∑ x ∈ F, a' x = 1 := by
    calc
      _ = ∑ x ∈ T, a' x := (Finset.sum_subset hTF (fun x _ hx => by simp [a',hx])).symm
      _ = ∑ x ∈ T, a x := Finset.sum_congr rfl (fun x hx => by simp [a',hx])
      _ = 1 := has
  have hp : ∑ x ∈ F, a' x • x = ∑ x ∈ F, w x • x := by
    calc
      _ = ∑ x ∈ T, a' x • x :=
        (Finset.sum_subset hTF (fun x _ hx => by simp [a',hx])).symm
      _ = ∑ x ∈ T, a x • x := Finset.sum_congr rfl (fun x hx => by simp [a',hx])
      _ = _ := hap
  have he := hF.eq_of_sum_eq_sum_subtype (hs.trans hws.symm) hp
  intro x hx
  by_contra hxt
  have hzero : w x = 0 := by simpa [a',hxt] using (he x hx).symm
  exact (ne_of_gt (hw x hx)) hzero

lemma simplex_contains_positivePoint (K : Geometry.SimplicialComplex ℝ E)
    {F T : Finset E} (hF : F ∈ K.faces) (hT : T ∈ K.faces)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hq : (∑ x ∈ F, w x • x) ∈ convexHull ℝ (T : Set E)) : F ⊆ T := by
  classical
  have hqF := sum_weights_mem_convexHull F (fun x hx => (hw x hx).le) hws
  have hqI := K.inter_subset_convexHull hF hT ⟨hqF,hq⟩
  have hs := positiveCombination_carrier (K.indep hF) Finset.inter_subset_left w hw hws
    (by simpa only [Finset.coe_inter] using hqI)
  exact hs.trans Finset.inter_subset_right

lemma eventually_coface_at_positivePoint (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {F : Finset E} (hF : F ∈ K.faces)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1) :
    ∀ᶠ q in 𝓝 (∑ x ∈ F, w x • x),
      ∀ T ∈ K.faces, q ∈ convexHull ℝ (T : Set E) → F ⊆ T := by
  classical
  apply (hK.eventually_all).mpr
  intro T hT
  by_cases hFT : F ⊆ T
  · exact Filter.Eventually.of_forall (fun _ _ => hFT)
  · have hnot : (∑ x ∈ F, w x • x) ∉ convexHull ℝ (T : Set E) := by
      intro hq
      exact hFT (simplex_contains_positivePoint K hF hT w hw hws hq)
    have hc : IsClosed (convexHull ℝ (T : Set E)) := (T.finite_toSet.isCompact_convexHull ℝ).isClosed
    have he : ∀ᶠ q in 𝓝 (∑ x ∈ F, w x • x), q ∉ convexHull ℝ (T : Set E) :=
      hc.isOpen_compl.mem_nhds hnot
    exact he.mono (fun _ hq hh => False.elim (hq hh))

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_facet_coface_on_side (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    {F : Finset E} (hF : F ∈ K.faces)
    (hdim : ∀ T ∈ K.faces, T.card ≤ F.card+1)
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    {v : E} (hv : v ∈ K.space) (hfv : b < f v) :
    ∃ u ∉ F, insert u F ∈ K.faces ∧ b < f u := by
  classical
  have hFn := K.nonempty_of_mem_faces hF
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr hFn.card_pos)
  have hcs : ∑ _x ∈ F, c = 1 := by
    simp [c,ne_of_gt (Nat.cast_pos.mpr hFn.card_pos : (0:ℝ) < F.card)]
  let q : E := ∑ x ∈ F, c • x
  have hqF : q ∈ convexHull ℝ (F : Set E) :=
    sum_weights_mem_convexHull F (fun _ _ => hc.le) hcs
  have hfq : f q = b := affineForm_eq_on_convexHull f b hFb hqF
  have hev := eventually_coface_at_positivePoint K hK hF (fun _ => c) (fun _ _ => hc) hcs
  have hcont : Continuous (fun δ : ℝ => δ • v + (1-δ) • q) := by fun_prop
  have hlim : Filter.Tendsto (fun δ : ℝ => δ • v + (1-δ) • q) (𝓝 0) (𝓝 q) := by
    simpa using hcont.continuousAt.tendsto (x := 0)
  have he := (hlim.eventually hev).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hlt := (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ,hδ,hδ1,hδK⟩ := (hpos.and (hlt.and he)).exists
  have hδq : δ • v + (1-δ) • q ∈ K.space :=
    hconv hv (K.convexHull_subset_space hF hqF) hδ.le (sub_nonneg.mpr hδ1.le) (by ring)
  have hfδ : b < f (δ • v + (1-δ) • q) := by
    simp only [map_add,map_smul,smul_eq_mul,hfq]
    nlinarith [mul_pos hδ (sub_pos.mpr hfv)]
  obtain ⟨T,hT,hδT⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hδq
  have hFT := hδK T hT hδT
  have hne : F ≠ T := by
    intro heq
    subst T
    have heq := affineForm_eq_on_convexHull f b hFb hδT
    exact (ne_of_gt hfδ) heq
  have hcT : F.card+1 = T.card := by
    have hltc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hFT,hne⟩)
    have hh := hdim T hT
    omega
  obtain ⟨u,hu,rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hFT,hcT⟩
  refine ⟨u,hu,hT,?_⟩
  by_contra hfu
  have hleft : convexHull ℝ ((insert u F : Finset E) : Set E) ⊆ {x | f x ≤ b} := by
    apply convexHull_min _ (convex_halfSpace_le f.isLinear b)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_of_not_gt hfu
    · exact (hFb x hx).le
  exact (not_le_of_gt hfδ) (hleft hδT)

end

section

open Set Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

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
    have he : (S ∩ {x | f x = b}).EqOn f.toAffineMap (AffineMap.const ℝ E b) := fun _ hy => hy.2
    exact AffineMap.eqOn_affineSpan he (convexHull_subset_affineSpan _ hx)

end

open Set Finset

open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma full_face_affineSpan (K : Geometry.SimplicialComplex ℝ E) {S T : Finset E}
    (hspace : K.space ⊆ convexHull ℝ (S : Set E)) (hT : T ∈ K.faces)
    (hc : T.card = S.card) : affineSpan ℝ (T : Set E) = affineSpan ℝ (S : Set E) :=
  affineSpan_eq_of_card_eq (K.indep hT) ((subset_convexHull ℝ _).trans
    ((K.convexHull_subset_space hT).trans hspace)) hc

def facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) : Finset E :=
  (hK.toFinset.biUnion id).filter (fun u => u ∉ F ∧ insert u F ∈ K.faces)

@[simp] lemma mem_facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) (u : E) : u ∈ facetApexes K hK F ↔ u ∉ F ∧ insert u F ∈ K.faces := by
  simp only [facetApexes,Finset.mem_filter,Finset.mem_biUnion,Set.Finite.mem_toFinset,id_eq]
  exact ⟨fun h => h.2,fun h => ⟨⟨insert u F,h.2,Finset.mem_insert_self _ _⟩,h⟩⟩

lemma parent_card_bound (K : Geometry.SimplicialComplex ℝ E) {S : Finset E}
    (hspace : K.space ⊆ convexHull ℝ (S : Set E)) :
    ∀ T ∈ K.faces, T.card ≤ S.card := by
  intro T hT
  exact (K.indep hT).card_le_card_of_subset_affineSpan ((subset_convexHull ℝ _).trans
    ((K.convexHull_subset_space hT).trans (hspace.trans (convexHull_subset_affineSpan _))))

lemma facet_positive_apex_card (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {S F : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hF : F ∈ K.faces)
    (hc : F.card+1 = S.card) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hFb : ∀ x ∈ F, f x = b) :
    ((facetApexes K hK F).filter (fun u => b < f u)).card =
      if ∃ v ∈ S, b < f v then 1 else 0 := by
  let A := (facetApexes K hK F).filter (fun u => b < f u)
  have hAc : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨huA,hu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvA,hv⟩ := Finset.mem_filter.mp hv
    obtain ⟨huF,huK⟩ := (mem_facetApexes K hK F u).mp huA
    obtain ⟨hvF,hvK⟩ := (mem_facetApexes K hK F v).mp hvA
    apply eq_of_facet_same_side K (K.nonempty_of_mem_faces hF) huF hvF huK hvK _ f b hFb hu hv
    rw [full_face_affineSpan K hspace.subset huK (by simp [Finset.card_insert_of_notMem huF,hc])]
    exact convexHull_subset_affineSpan _ (hspace ▸ K.convexHull_subset_space hvK
      (subset_convexHull ℝ _ (Finset.mem_insert_self _ _)))
  have hAn : A.Nonempty ↔ ∃ v ∈ S, b < f v := by
    constructor
    · rintro ⟨u,hu⟩
      obtain ⟨huA,hu⟩ := Finset.mem_filter.mp hu
      have huK := ((mem_facetApexes K hK F u).mp huA).2
      by_contra hn
      push Not at hn
      have hh : convexHull ℝ (S : Set E) ⊆ {x | f x ≤ b} :=
        convexHull_min hn (convex_halfSpace_le f.isLinear b)
      exact (not_le_of_gt hu) (hh (hspace ▸ K.convexHull_subset_space huK
        (subset_convexHull ℝ _ (Finset.mem_insert_self _ _))))
    · rintro ⟨v,hv,hfv⟩
      obtain ⟨u,hu,huK,hfu⟩ := exists_facet_coface_on_side K hK
        (hspace.symm ▸ convex_convexHull ℝ (S : Set E)) hF
        (fun T hT => hc ▸ parent_card_bound K hspace.subset T hT) f b hFb
        (hspace.symm ▸ subset_convexHull ℝ (S : Set E) hv) hfv
      exact ⟨u,Finset.mem_filter.mpr ⟨(mem_facetApexes K hK F u).mpr ⟨hu,huK⟩,hfu⟩⟩
  change A.card = _
  split_ifs with h
  · have := (hAn.mpr h).card_pos
    omega
  · have := not_congr hAn |>.mpr h
    simp only [Finset.not_nonempty_iff_eq_empty.mp this,Finset.card_empty]

end BassTrace.Sparse

end

end OAI
