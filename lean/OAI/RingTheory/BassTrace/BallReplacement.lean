import OAI.RingTheory.BassTrace.EquivariantSurgery

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [Fintype C]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi

omit [IsCancelSMul H Y] [Fintype C] in

lemma meeting_simplex_patch (c : C → FinProbability Y) (h : H) (i : C)
    {R t : ℝ} (hR : 0≤R) (htR : t≤R)
    (s : Finset Y) (hs : s∈K.faces)
    (hmeet : (convexHull ℝ ((fun y : Y => Finsupp.single y (1:ℝ)) '' (s : Set Y)) ∩
      {v | centerDistance Γ hΓ K n (h • c i) v<t}).Nonempty) :
    convexHull ℝ ((fun y : Y => Finsupp.single y (1:ℝ)) '' (s : Set Y)) ⊆
      BallOrbitForms.translatedPatch (fun i => ballSupport Γ (c i) n R) K h i := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  have hsp : convexHull ℝ ((fun y : Y => Finsupp.single y (1:ℝ)) '' (s : Set Y)) ⊆
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
    rw [← Finset.coe_image]
    exact (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space ⟨s,hs,rfl⟩
  obtain ⟨v,hvs,hvt⟩ := hmeet
  let p := pointProbability K ⟨v,hsp hvs⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hpS : p.coeff.support ⊆ s := by
    have hv := (convexHull_single_eq_probabilitySet s) ▸ hvs
    exact hp.symm ▸ hv.2.2
  have hpK := pointProbability_face K ⟨v,hsp hvs⟩
  have hball : FinProbability.rho n (h • c i) p≤R := by
    change centerDistance Γ hΓ K n (h • c i) v<t at hvt
    rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at hvt
    exact hvt.le.trans htR
  let s' := s.map (MulAction.toPerm h⁻¹).toEmbedding
  obtain ⟨σ,hσ,hsσ,hcard,hconn⟩ := hK s' (hact h⁻¹ s hs)
  have hp' : (h⁻¹ • p).coeff.support ⊆ σ := by
    rw [smul_probability_support]
    exact (Finset.map_subset_map.mpr hpS).trans hsσ
  have hball' : FinProbability.rho n (c i) (h⁻¹ • p)≤R := by
    have he := smul_probability_rho hi h⁻¹ n (h • c i) p
    rw [inv_smul_smul] at he
    exact he.symm ▸ hball
  have hσS : σ ⊆ S i :=
    (meeting_simplex_vertices Γ hΓ hn (c i) (h⁻¹ • p) σ hcard hconn hp' R hR hball').trans
      Finset.subset_union_right
  intro w hw
  let q := pointProbability K ⟨w,hsp hw⟩
  have hq : q.coeff=w := pointProbability_coeff K _
  have hqS : q.coeff.support ⊆ s := by
    have hh := (convexHull_single_eq_probabilitySet s) ▸ hw
    exact hq.symm ▸ hh.2.2
  rw [← hq]
  apply (BallOrbitForms.translatedPatch_mem S K h i q).mpr
  refine ⟨hq.symm ▸ hsp hw,?_⟩
  rw [smul_probability_support]
  exact (Finset.map_subset_map.mpr hqS).trans (hsσ.trans hσS)

lemma ballComplement_marked (c : C → FinProbability Y) (h : H) (i : C)
    {R t : ℝ} (hR : 0≤R) (ht : 0<t) (htR : t≤R)
    (T : Cuts.Subdivision (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) :
    let S := fun i => ballSupport Γ (c i) n R
    let D := OrbitForms.cuts (H := H) (BallOrbitForms.data S c n) ht
    Cuts.IsMarked (D.refine T).complex
      ((Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space \
        {v | centerDistance Γ hΓ K n (h • c i) v<t}) := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  let D := OrbitForms.cuts (H := H) (BallOrbitForms.data S c n) ht
  let P := BallOrbitForms.translatedPatch S K h i
  let O := D.outerPatch P (BallOrbitForms.branches S h i)
  apply (D.refine T).marked_complement_of_patch _ P O
  · exact D.outerPatch_marked ((D.refine T).preserves_marked
      (BallOrbitForms.translatedPatch_marked S K h i)) _
  · ext v
    constructor
    · intro hv
      have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := hv.1.1
      let p := pointProbability K ⟨v,hvK⟩
      have hp : p.coeff=v := pointProbability_coeff K _
      rw [← hp] at hv ⊢
      have hh := (BallOrbitForms.outerPatch_mem S c n hi
        (fun i => ballSupport_center Γ (c i) n R) K h i p ht).mp hv
      refine ⟨hh.1,?_⟩
      change ¬centerDistance Γ hΓ K n (h • c i) p.coeff<t
      rw [centerDistance_apply Γ hΓ K n _ p (pointProbability_face K ⟨v,hvK⟩)]
      exact not_lt.mpr hh.2
    · rintro ⟨hv,hout⟩
      have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := hv.1
      let p := pointProbability K ⟨v,hvK⟩
      have hp : p.coeff=v := pointProbability_coeff K _
      rw [← hp] at hv hout ⊢
      apply (BallOrbitForms.outerPatch_mem S c n hi
        (fun i => ballSupport_center Γ (c i) n R) K h i p ht).mpr
      refine ⟨hv,?_⟩
      change ¬centerDistance Γ hΓ K n (h • c i) p.coeff<t at hout
      rw [centerDistance_apply Γ hΓ K n _ p (pointProbability_face K ⟨v,hvK⟩)] at hout
      exact not_lt.mp hout
  · rintro _ ⟨s,hs,rfl⟩ hmeet
    rw [Finset.coe_image] at hmeet ⊢
    exact meeting_simplex_patch Γ hΓ rfl hn K hK hact hi c h i hR htR s hs hmeet

end Sparse.GraphGeometry

namespace Sparse

open Set Finset

variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype C]

lemma finite_translated_support_meeting (S : C → Finset Y) (s : Finset Y) :
    {j : H × C | ∃ w ∈ S j.2, j.1 • w ∈ s}.Finite := by
  have hi : (⋃ i : C, (fun h : H => (h,i)) ''
      (⋃ w ∈ (S i : Set Y), {h : H | h • w ∈ s})).Finite := by
    apply Set.finite_iUnion
    intro i
    apply Set.Finite.image
    apply Set.Finite.biUnion (S i).finite_toSet
    intro w _
    exact Set.Finite.preimage (fun h _ k _ he => IsCancelSMul.right_cancel h k w he)
      s.finite_toSet
  apply hi.subset
  rintro ⟨h,i⟩ ⟨w,hw,hs⟩
  exact Set.mem_iUnion.mpr ⟨i,h,Set.mem_iUnion₂.mpr ⟨w,hw,hs⟩,rfl⟩

end Sparse

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [Fintype C]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi

lemma finite_ball_incidence (c : C → FinProbability Y) {R : ℝ} (hR : 0≤R)
    (s : Finset (Y →₀ ℝ)) (hs : s∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces) :
    {j : H × C | ({v | centerDistance Γ hΓ K n (j.1 • c j.2) v≤R} ∩
      convexHull ℝ (s : Set (Y →₀ ℝ))).Nonempty}.Finite := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  obtain ⟨σ,hσ,rfl⟩ := hs
  apply (finite_translated_support_meeting (H := H) S σ).subset
  rintro ⟨h,i⟩ ⟨v,hv,hvs⟩
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space ⟨σ,hσ,rfl⟩ hvs
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hpK := pointProbability_face K ⟨v,hvK⟩
  have hpσ : p.coeff.support⊆σ := by
    rw [Finset.coe_image] at hvs
    have hh := (convexHull_single_eq_probabilitySet σ) ▸ hvs
    exact hp.symm ▸ hh.2.2
  have hball : FinProbability.rho n (h • c i) p≤R := by
    change centerDistance Γ hΓ K n (h • c i) v≤R at hv
    rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at hv
    exact hv
  have hsub := ballSupport_inverse Γ hΓ rfl hn K hK hact hi c h i p hpK hR hball
  obtain ⟨y,hy⟩ := p.coeff_support_nonempty
  have hymap := (BallOrbitForms.inverse_support_iff h p (S i)).mp hsub hy
  obtain ⟨w,hw,he⟩ := Finset.mem_map.mp hymap
  refine ⟨w,hw,?_⟩
  have hey : h • w = y := he
  rw [hey]
  exact hpσ hy

end Sparse.GraphGeometry

namespace Sparse.Cuts.SubdivisionFamily

open Set Finset MeasureTheory

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] [CompactSpace X]

variable {K : Geometry.SimplicialComplex ℝ V}

lemma countable_exceptional_levels (T : SubdivisionFamily X K) (hK : K.faces.Countable)
    {J : Type*} [Countable J] (a : J → V → ℝ) :
    {t : ℝ | ¬∀ x s, s ∈ (T.val x).complex.faces →
      ∀ j y, y ∈ s → a j y ≠ t}.Countable := by
  let bad : Set ℝ := ⋃ j, a j '' (⋃ x, (T.val x).complex.vertices)
  have hb : bad.Countable := Set.countable_iUnion fun j => (T.countable_vertices hK).image (a j)
  apply hb.mono
  intro t ht
  simp only [Set.mem_ofPred_eq,not_forall,not_not] at ht
  obtain ⟨x,s,hs,j,y,hy,he⟩ := ht
  exact Set.mem_iUnion.mpr ⟨j,y,Set.mem_iUnion.mpr ⟨x,
    (T.val x).complex.down_closed hs (Finset.singleton_subset_iff.mpr hy)
      (Finset.singleton_nonempty _)⟩,he⟩

end Sparse.Cuts.SubdivisionFamily

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y C X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y] [Fintype C]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)

variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)

variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))

include hm hn hK hact hi

omit [Countable H] [Countable Y] [CompactSpace X] in

theorem exists_ball_replacement
    (T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (P : Cuts.MarkedFamily T)
    {R t : ℝ} (hR : 0<R) (ht : 0<t) (htR : t≤R)
    (old : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P)
    (hT : OrbitForms.Equivariant (H := H) old.next)
    (hP : OrbitForms.MarkedEquivariant (H := H) P)
    (hZ : OrbitForms.MarkedEquivariant (H := H) old.zero)
    (c : C → FinProbability Y) (B : C → Set X) (hB : ∀ i, IsClopen (B i))
    (hgeneric : ∀ x F, F ∈ (T.val x).complex.faces →
      ∀ j : H × BallOrbitForms.Index (fun i => ballSupport Γ (c i) n R),
      ∃ v∈F, OrbitForms.form (BallOrbitForms.data (fun i => ballSupport Γ (c i) n R) c n) j v≠t) :
    ∃ A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P,
      OrbitForms.Equivariant (H := H) A.next ∧
      OrbitForms.MarkedEquivariant (H := H) A.zero ∧
      ∀ x, A.zero.val x = Cuts.replacementSet (P.val x) (old.zero.val x)
        (fun j : H × C => {v | centerDistance Γ hΓ K n (j.1 • c j.2) v<t})
        (fun j : H × C => {v | centerDistance Γ hΓ K n (j.1 • c j.2) v=t})
        (fun j : H × C => (fun x => j.1⁻¹ • x) ⁻¹' B j.2) x := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  let d := BallOrbitForms.data S c n
  let D := OrbitForms.cuts (H := H) d ht
  let f := fun j : H × C => centerDistance Γ hΓ K n (j.1 • c j.2)
  let patch := fun j : H × C => BallOrbitForms.translatedPatch S K j.1 j.2
  let branches := fun j : H × C => BallOrbitForms.branches S j.1 j.2
  let act := fun j : H × C => (fun x => j.1⁻¹ • x) ⁻¹' B j.2
  have hsphere (j : H × C) := sphere_eq_patch Γ hΓ rfl hn K hK hact hi c
    j.1 j.2 hR.le ht htR
  have hfin (s) (hs : s∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces) :=
    finite_ball_incidence Γ hΓ rfl hn K hK hact hi c hR.le s hs
  let A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P := by
    refine D.replacementStep T P (realizationDistance Γ hΓ K n) R t old
      f patch branches act (fun j => (hB j.2).preimage (continuous_const_smul j.1⁻¹))
      (fun j => BallOrbitForms.translatedPatch_marked S K j.1 j.2)
      hsphere (fun x j => ballComplement_marked Γ hΓ rfl hn K hK hact hi c
        j.1 j.2 hR.le ht htR (old.next.val x)) (fun _ => rfl) hgeneric ?_ ?_ ?_ ?_ htR
    · intro s hs
      apply (hfin s hs).subset
      rintro j ⟨v,hv,hvs⟩
      exact ⟨v,hv.le.trans htR,hvs⟩
    · intro s hs
      apply (hfin s hs).subset
      rintro j ⟨v,hv,hvs⟩
      rw [← hsphere j] at hv
      refine ⟨v,?_,hvs⟩
      change centerDistance Γ hΓ K n (j.1 • c j.2) v ≤ R
      rw [hv.2]
      exact htR
    · intro j
      apply continuousOn_centerDistance Γ hΓ hn K
        (fun s hs => by obtain ⟨σ,hσ,hsσ,hcard,_⟩ := hK s hs; exact ⟨σ,hσ,hsσ,hcard⟩)
      intro σ hσ
      obtain ⟨τ,_,hστ,hτ,hconn⟩ := hK σ hσ.1
      have hσcard : σ.card=n+1 := hσ.2
      have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by omega)
      rw [he]
      exact hconn
    · intro j p hp q hq
      exact realizationDistance_center_triangle Γ hΓ K n (j.1 • c j.2) p hp q hq
  have hPk (x : X) : P.val x ⊆ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
    rw [← (T.val x).space_eq]
    exact (P.marked x).subset_space
  have hval (x : X) : A.zero.val x = Cuts.replacementSet (P.val x) (old.zero.val x)
      (fun j => {v | f j v<t}) (fun j => {v | f j v=t}) act x := by
    change Cuts.replacementSet (P.val x) (old.zero.val x) _
      (fun j => D.spherePatch (patch j) (branches j)) _ _ = _
    unfold Cuts.replacementSet Cuts.activatedUnion
    have hh (j : H × C) : D.spherePatch (patch j) (branches j) =
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∩ {v | f j v=t} :=
      (hsphere j).symm
    simp_rw [hh]
    ext v
    simp only [Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff,Set.mem_iUnion]
    constructor
    · rintro (hv | ⟨hp,j,hj⟩)
      · exact Or.inl hv
      · apply Or.inr
        refine ⟨hp,j,?_⟩
        by_cases hh : x∈act j
        · simp only [hh,ite_true] at hj ⊢
          exact hj.2
        · simpa only [hh,ite_false] using hj
    · rintro (hv | ⟨hp,j,hj⟩)
      · exact Or.inl hv
      · apply Or.inr
        refine ⟨hp,j,?_⟩
        by_cases hh : x∈act j
        · simp only [hh,ite_true] at hj ⊢
          exact ⟨hPk x hp,hj⟩
        · simpa only [hh,ite_false] using hj
  refine ⟨A,OrbitForms.refineFamily_equivariant d ht old.next hT,?_,hval⟩
  intro k x v hv
  rw [hval x] at hv
  rw [hval (k • x)]
  have hfk (j : H × C) (hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
      f (k*j.1,j.2) (OrbitForms.push k v)=f j v := by
    dsimp only [f]
    rw [mul_smul,centerDistance_push K hact Γ hΓ hi n k (j.1 • c j.2) v hvK]
  have hactk (j : H × C) : k • x∈act (k*j.1,j.2) ↔ x∈act j := by
    change (k*j.1)⁻¹ • (k • x)∈B j.2 ↔ j.1⁻¹ • x∈B j.2
    rw [mul_inv_rev,mul_smul,inv_smul_smul]
  rcases hv with hv | ⟨hp,hj⟩
  · refine Or.inl ⟨hZ k x v hv.1,?_⟩
    intro hh
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hh
    by_cases hjx : k • x∈act j
    · simp only [hjx,ite_true] at hj
      apply hv.2
      apply Set.mem_iUnion.mpr
      refine ⟨(k⁻¹*j.1,j.2),?_⟩
      have ha : x∈act (k⁻¹*j.1,j.2) := by
        change (k⁻¹*j.1)⁻¹ • x∈B j.2
        change j.1⁻¹ • (k • x)∈B j.2 at hjx
        simpa only [mul_inv_rev,inv_inv,mul_smul] using hjx
      simp only [ha,ite_true]
      have he := hfk (k⁻¹*j.1,j.2) (hPk x (old.subset x hv.1))
      simp only [mul_inv_cancel_left] at he
      change f j (OrbitForms.push k v)<t at hj
      change f (k⁻¹*j.1,j.2) v<t
      rw [← he]
      exact hj
    · simp only [hjx,ite_false,Set.mem_empty_iff_false] at hj
  · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hj
    refine Or.inr ⟨hP k x v hp,Set.mem_iUnion.mpr ⟨(k*j.1,j.2),?_⟩⟩
    by_cases hjx : x∈act j
    · have hjkx := (hactk j).mpr hjx
      simp only [hjx,ite_true] at hj
      simp only [hjkx,ite_true]
      change f (k*j.1,j.2) (OrbitForms.push k v)=t
      rw [hfk j (hPk x hp)]
      exact hj
    · simp only [hjx,ite_false,Set.mem_empty_iff_false] at hj

end Sparse.GraphGeometry

end BassTrace

end

end OAI
