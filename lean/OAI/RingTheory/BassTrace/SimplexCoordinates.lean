import OAI.RingTheory.BassTrace.HausdorffArea

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open MeasureTheory Set Finset

open scoped ENNReal InnerProductSpace

lemma barycentricParam_potential {n : ℕ} (ℓ : Fin (n+1) → ℝ) (x : Fin n → ℝ) :
    ∑ i, ℓ i * barycentricParam x i = ℓ 0 + ∑ i, (ℓ i.succ-ℓ 0)*x i := by
  rw [Fin.sum_univ_succ]
  simp only [barycentricParam_zero,barycentricParam_succ,sub_mul,Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

lemma treeParam_potential {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (ℓ : Fin (n+1) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ℓ i * treeParam T hT x i) / Real.sqrt n =
      ⟪treeGradient T hT ℓ,x⟫_ℝ + ℓ 0 / Real.sqrt n := by
  rw [treeParam,barycentricParam_potential,add_div,treeChart_potential]
  rw [real_inner_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  ring

lemma treeArea_coarea {n : ℕ} (hn : 0<n)
    (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (hℓ : ∀ i j u v, T.Adj u v → |ℓ i j u-ℓ i j v|≤1)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) (r b : ℝ) :
    (∫⁻ t in Ioo r b, treeArea T hT (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) ≤
      treeArea T hT d ((⋃ i,Q i) ∩ {p | f p≤b}) := by
  classical
  let s' i := (s i).image (treeCoordinates T hT)
  let Q' i := treeParam T hT ⁻¹' Q i
  have hQs' (i : I) : Q' i ⊆ convexHull ℝ (s' i : Set (EuclideanSpace ℝ (Fin n))) := by
    have hh := Set.preimage_mono (f := treeParam T hT) (hQs i)
    rw [treeParam_preimage_simplex T hT (s i) (hplane i)] at hh
    simpa only [s',Finset.coe_image] using hh
  have hh := finite_max_coarea s' d (fun i => (Finset.card_image_le).trans (hs i))
    (by simpa only [finrank_euclideanSpace_fin] using hd) Q'
    (fun i => (hQ i).preimage (continuous_treeParam T hT).measurable) hQs'
    (fun i j => treeGradient T hT (ℓ i j))
    (fun i j => treeGradient_norm_le_one hn T hT (ℓ i j) (hℓ i j))
    (fun i j => ℓ i j 0 / Real.sqrt n) (f ∘ treeParam T hT)
    (fun i p hp => by
      rw [Function.comp_apply,hf i _ hp]
      congr 1
      funext j
      exact treeParam_potential T hT (ℓ i j) p) r b
  simpa only [treeArea,Set.preimage_inter,Set.preimage_iUnion,Set.preimage_ofPred_eq,
    Function.comp_apply,Q'] using hh

lemma measurable_treeArea_slices {n : ℕ}
    (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) :
    Measurable (fun t => treeArea T hT (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) := by
  classical
  let s' i := (s i).image (treeCoordinates T hT)
  let Q' i := treeParam T hT ⁻¹' Q i
  have hQs' (i : I) : Q' i ⊆ convexHull ℝ (s' i : Set (EuclideanSpace ℝ (Fin n))) := by
    have hh := Set.preimage_mono (f := treeParam T hT) (hQs i)
    rw [treeParam_preimage_simplex T hT (s i) (hplane i)] at hh
    simpa only [s',Finset.coe_image] using hh
  have hh := measurable_finite_max_slices s' d (fun i => (Finset.card_image_le).trans (hs i))
    (by simpa only [finrank_euclideanSpace_fin] using hd) Q'
    (fun i => (hQ i).preimage (continuous_treeParam T hT).measurable) hQs'
    (fun i j => treeGradient T hT (ℓ i j))
    (fun i j => ℓ i j 0 / Real.sqrt n) (f ∘ treeParam T hT)
    (fun i p hp => by
      rw [Function.comp_apply,hf i _ hp]
      congr 1
      funext j
      exact treeParam_potential T hT (ℓ i j) p)
  simpa only [treeArea,Set.preimage_inter,Set.preimage_iUnion,Set.preimage_ofPred_eq,
    Function.comp_apply,Q'] using hh

lemma simplexArea_coarea {n : ℕ} (hn : 0<n)
    (Γ : SimpleGraph (Fin (n+1)))
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (hℓ : ∀ i j u v, Γ.Adj u v → |ℓ i j u-ℓ i j v|≤1)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) (r b : ℝ) :
    (∫⁻ t in Ioo r b, simplexArea Γ (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) ≤
      simplexArea Γ d ((⋃ i,Q i) ∩ {p | f p≤b}) := by
  classical
  have hm (T : SpanningTree Γ) := measurable_treeArea_slices T.val T.property.2
    s d hs hd hplane Q hQ hQs ℓ f hf
  simp only [simplexArea,div_eq_mul_inv]
  rw [lintegral_mul_const _ (Finset.measurable_sum _ (fun T _ => hm T)),
    lintegral_finsetSum _ (fun T _ => hm T)]
  apply mul_le_mul_left
  apply Finset.sum_le_sum
  intro T _
  exact treeArea_coarea hn T.val T.property.2 s d hs hd hplane Q hQ hQs ℓ
    (fun i j u v huv => hℓ i j u v (T.property.1 huv)) f hf r b

lemma measurable_simplexArea_slices {n : ℕ}
    (Γ : SimpleGraph (Fin (n+1)))
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) :
    Measurable (fun t => simplexArea Γ (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) := by
  classical
  unfold simplexArea
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun T _ => measurable_treeArea_slices T.val T.property.2
    s d hs hd hplane Q hQ hQs ℓ f hf)

end

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y : Type*} [DecidableEq Y]

lemma simplexEmbed_nonneg {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Fin (n+1) → ℝ} (hp : ∀ i,0≤p i) (y : Y) : 0 ≤ simplexEmbed s hs p y := by
  by_cases hy : y∈s
  · obtain ⟨i,hi⟩ := (simplexEnumeration s hs).surjective ⟨y,hy⟩
    have h := congrFun (simplexCoordinates_embed s hs p) i
    change simplexEmbed s hs p (simplexEnumeration s hs i).val = p i at h
    rw [hi] at h
    rw [h]
    exact hp i
  · rw [Finsupp.notMem_support_iff.mp (fun h => hy (simplexEmbed_support s hs p h))]

omit [DecidableEq Y] in
lemma simplexEmbed_total {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : (simplexEmbed s hs p).sum (fun _ r=>r)=∑ i,p i := by
  rw [Finsupp.sum_of_support_subset _ (simplexEmbed_support s hs p) _ (by intros; rfl)]
  rw [← (Finset.sum_attach s (fun y : Y => simplexEmbed s hs p y))]
  change (∑ y : s, simplexEmbed s hs p y.val) = _
  rw [← (simplexEnumeration s hs).sum_comp (fun y : s => simplexEmbed s hs p y.val)]
  congr 1
  funext i
  exact congrFun (simplexCoordinates_embed s hs p) i

def simplexPoint {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) (hp : p∈fullBarycentricSimplex n) : FinProbability Y where
  coeff := simplexEmbed s hs p
  nonneg := simplexEmbed_nonneg s hs hp.1
  total := (simplexEmbed_total s hs p).trans hp.2

variable [MetricSpace Y]

def chartDistance {n : ℕ} (s : Finset Y) (hs : s.card=n+1) (c : FinProbability Y)
    (p : Fin (n+1) → ℝ) : ℝ :=
  if hp : p∈fullBarycentricSimplex n then FinProbability.rho n c (simplexPoint s hs p hp) else 0

lemma chartDistance_apply {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (c : FinProbability Y) (p : Fin (n+1) → ℝ) (hp : p∈fullBarycentricSimplex n) :
    chartDistance s hs c p = FinProbability.rho n c (simplexPoint s hs p hp) := by
  simp only [chartDistance,dite_eq_left hp]

omit [MetricSpace Y] in
lemma ballBranch_coordinates {n : ℕ} (s S : Finset Y) (hs : s.card=n+1) (hsS : s⊆S)
    (c : FinProbability Y) (l : S→ℝ) (p : Fin (n+1) → ℝ) :
    ballBranch S c n l (simplexEmbed s hs p) =
      (∑ i,(centerBranchValue S c l-l ⟨(simplexEnumeration s hs i).val,
        hsS (simplexEnumeration s hs i).property⟩)*p i)/Real.sqrt n := by
  rw [ballBranch_apply]
  have hm : ∑ y : S,((centerBranchValue S c l-l y)/Real.sqrt n)*simplexEmbed s hs p y =
      ∑ y : s,((centerBranchValue S c l-l ⟨y.val,hsS y.property⟩)/Real.sqrt n)*
        simplexEmbed s hs p y := by
    apply Finset.sum_bij_ne_zero (fun y _ _ => ⟨y.val,by
      by_contra hy
      have hzero := Finsupp.notMem_support_iff.mp
        (fun h => hy (simplexEmbed_support s hs p h))
      simp [hzero] at *⟩)
    · intros; simp
    · intro a ha hna b hb hnb he
      exact Subtype.ext (congrArg (fun z : s => z.val) he)
    · intro y _ hy
      exact ⟨⟨y.val,hsS y.property⟩,by simp,by simpa using hy,rfl⟩
    · intros; rfl
  rw [hm,← (simplexEnumeration s hs).sum_comp]
  simp_rw [show ∀ i, simplexEmbed s hs p (simplexEnumeration s hs i).val=p i from
    fun i=>congrFun (simplexCoordinates_embed s hs p) i,
    div_mul_eq_mul_div,Finset.sum_div]

def distancePotential {n : ℕ} (s S : Finset Y) (hs : s.card=n+1) (hsS : s⊆S)
    (c : FinProbability Y) (l : S → ℝ) (i : Fin (n+1)) : ℝ :=
  centerBranchValue S c l-l ⟨(simplexEnumeration s hs i).val,
    hsS (simplexEnumeration s hs i).property⟩

omit [DecidableEq Y] in
lemma distancePotential_edge {n : ℕ} (s S : Finset Y) (hs : s.card=n+1)
    (hsS : s⊆S) (c : FinProbability Y) (l : S→ℝ) (hl : l∈potentialVertices)
    (u v : Fin (n+1))
    (huv : dist (simplexEnumeration s hs u).val (simplexEnumeration s hs v).val≤1) :
    |distancePotential s S hs hsS c l u-distancePotential s S hs hsS c l v|≤1 := by
  have hh := (potentialVertices_subset l hl).2
    ⟨(simplexEnumeration s hs v).val,hsS (simplexEnumeration s hs v).property⟩
    ⟨(simplexEnumeration s hs u).val,hsS (simplexEnumeration s hs u).property⟩
  unfold distancePotential
  rw [show ∀ a b d : ℝ,(a-b)-(a-d)=d-b from by intros; ring]
  exact hh.trans (by simpa only [Subtype.dist_eq,dist_comm] using huv)

lemma chartDistance_max {n : ℕ} (s S : Finset Y) (hs : s.card=n+1) (hsS : s⊆S)
    (c : FinProbability Y) (hc : c.coeff.support⊆S)
    [Nonempty (potentialVertices : Finset (S→ℝ))]
    (p : Fin (n+1) → ℝ) (hp : p∈fullBarycentricSimplex n) :
    chartDistance s hs c p=Finset.univ.sup' Finset.univ_nonempty
      (fun l : (potentialVertices : Finset (S→ℝ)) =>
        (∑ i,distancePotential s S hs hsS c l.val i*p i)/Real.sqrt n) := by
  have hpS : (simplexPoint s hs p hp).coeff.support⊆S :=
    (simplexEmbed_support s hs p).trans hsS
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer S c (simplexPoint s hs p hp) hc hpS n
  rw [chartDistance_apply s hs c p hp]
  apply le_antisymm
  · rw [heq]
    change ballBranch S c n l (simplexEmbed s hs p)≤_
    rw [ballBranch_coordinates s S hs hsS]
    change (∑ i,distancePotential s S hs hsS c l i*p i)/Real.sqrt n ≤ _
    exact Finset.le_sup' (fun l : (potentialVertices : Finset (S→ℝ)) =>
      (∑ i,distancePotential s S hs hsS c l.val i*p i)/Real.sqrt n)
      (Finset.mem_univ (⟨l,hl⟩ : (potentialVertices : Finset (S→ℝ))))
  · apply Finset.sup'_le
    intro l _
    have hh := hmax l.val l.property
    change ballBranch S c n l.val (simplexEmbed s hs p)≤_ at hh
    simpa only [ballBranch_coordinates s S hs hsS,distancePotential] using hh

theorem graphBall_coarea {n : ℕ} (hn : 0<n)
    (σ : Finset Y) (hσ : σ.card=n+1) (c : FinProbability Y)
    (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : ∀ u v, Γ.Adj u v →
      dist (simplexEnumeration σ hσ u).val (simplexEnumeration σ hσ v).val≤1)
    {I : Type*} [Fintype I]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i,(s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p,p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i,MeasurableSet (Q i))
    (hQs : ∀ i,Q i⊆convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (hfull : ∀ i,Q i⊆fullBarycentricSimplex n) (r b : ℝ) :
    (∫⁻ t in Ioo r b, simplexArea Γ (d-1) ((⋃ i,Q i) ∩ {p | chartDistance σ hσ c p=t})) ≤
      simplexArea Γ d ((⋃ i,Q i) ∩ {p | chartDistance σ hσ c p≤b}) := by
  let S := σ ∪ c.coeff.support
  have hσS : σ⊆S := Finset.subset_union_left
  have hcS : c.coeff.support⊆S := Finset.subset_union_right
  obtain ⟨l,hl,-⟩ := exists_ballBranch_maximizer S c c hcS hcS n
  let : Nonempty (potentialVertices : Finset (S→ℝ)) := ⟨⟨l,hl⟩⟩
  exact simplexArea_coarea hn Γ s d hs hd hplane Q hQ hQs
    (fun _ (l : (potentialVertices : Finset (S→ℝ))) => distancePotential σ S hσ hσS c l.val)
    (fun _ l u v huv => distancePotential_edge σ S hσ hσS c l.val l.property u v (hΓ u v huv))
    (chartDistance σ hσ c) (fun i p hp => chartDistance_max σ S hσ hσS c hcS p (hfull i hp)) r b

lemma measurable_graphBall_slices {n : ℕ}
    (σ : Finset Y) (hσ : σ.card=n+1) (c : FinProbability Y)
    (Γ : SimpleGraph (Fin (n+1))) {I : Type*} [Fintype I]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i,(s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p,p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i,MeasurableSet (Q i))
    (hQs : ∀ i,Q i⊆convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (hfull : ∀ i,Q i⊆fullBarycentricSimplex n) :
    Measurable (fun t => simplexArea Γ (d-1)
      ((⋃ i,Q i) ∩ {p | chartDistance σ hσ c p=t})) := by
  let S := σ ∪ c.coeff.support
  have hσS : σ⊆S := Finset.subset_union_left
  have hcS : c.coeff.support⊆S := Finset.subset_union_right
  obtain ⟨l,hl,-⟩ := exists_ballBranch_maximizer S c c hcS hcS n
  let : Nonempty (potentialVertices : Finset (S→ℝ)) := ⟨⟨l,hl⟩⟩
  exact measurable_simplexArea_slices Γ s d hs hd hplane Q hQ hQs
    (fun _ (l : (potentialVertices : Finset (S→ℝ))) => distancePotential σ S hσ hσS c l.val)
    (chartDistance σ hσ c) (fun i p hp => chartDistance_max σ S hσ hσS c hcS p (hfull i hp))

end BassTrace.Sparse

end

end OAI
