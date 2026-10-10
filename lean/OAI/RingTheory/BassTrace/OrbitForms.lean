import OAI.RingTheory.BassTrace.GraphRealization

namespace OAI

noncomputable section

namespace BassTrace.Sparse.FinProbability

open Set Finset

variable {Y Z W : Type*}

def push (e : Y ≃ Z) (p : FinProbability Y) : FinProbability Z where
  coeff := Finsupp.equivMapDomain e p.coeff
  nonneg z := p.nonneg (e.symm z)
  total := by
    classical
    change ∑ z ∈ p.coeff.support.map e.toEmbedding, p.coeff (e.symm z) = 1
    rw [Finset.sum_map]
    simpa [Finsupp.sum] using p.total

@[simp] lemma push_coeff_apply (e : Y ≃ Z) (p : FinProbability Y) (z : Z) :
    (push e p).coeff z = p.coeff (e.symm z) := rfl

lemma push_support (e : Y ≃ Z) (p : FinProbability Y) :
    (push e p).coeff.support = p.coeff.support.map e.toEmbedding := rfl

@[simp] lemma push_refl (p : FinProbability Y) : push (Equiv.refl Y) p = p := by
  ext y
  rfl

lemma push_trans (e : Y ≃ Z) (f : Z ≃ W) (p : FinProbability Y) :
    push (e.trans f) p = push f (push e p) := by
  ext y
  rfl

@[simp] lemma push_symm_push (e : Y ≃ Z) (p : FinProbability Y) :
    push e.symm (push e p) = p := by
  ext y
  simp

lemma push_expectation (e : Y ≃ Z) (p : FinProbability Y) (f : Z → ℝ) :
    (push e p).expectation f = p.expectation (f ∘ e) := by
  classical
  unfold expectation Finsupp.sum
  rw [push_support,Finset.sum_map]
  simp

lemma push_gap (e : Y ≃ Z) (p q : FinProbability Y) (f : Z → ℝ) :
    (push e p).gap (push e q) f = p.gap q (f ∘ e) := by
  simp [gap,push_expectation]

lemma transport_push_le [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (e : Y ≃ Z) (he : LipschitzWith 1 e) (p q : FinProbability Y) :
    (push e p).transport (push e q) ≤ p.transport q := by
  apply transport_le
  intro f hf
  rw [push_gap]
  apply gap_le_transport
  simpa using hf.comp he

lemma transport_push [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (e : Y ≃ Z) (he : Isometry e) (p q : FinProbability Y) :
    (push e p).transport (push e q) = p.transport q := by
  apply le_antisymm (transport_push_le e he.lipschitzWith p q)
  have hei : Isometry e.symm := by
    intro z w
    simpa using (he (e.symm z) (e.symm w)).symm
  simpa using transport_push_le e.symm hei.lipschitzWith (push e p) (push e q)

lemma rho_push [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (e : Y ≃ Z) (he : Isometry e) (n : ℕ) (p q : FinProbability Y) :
    rho n (push e p) (push e q) = rho n p q := by
  simp [rho,transport_push e he]

end BassTrace.Sparse.FinProbability

namespace BassTrace.Sparse

open scoped Pointwise

variable {H Y : Type*} [Group H] [MulAction H Y]

scoped instance probabilityMulAction : MulAction H (FinProbability Y) where
  smul h p := p.push (MulAction.toPerm h)
  one_smul p := by
    ext y
    change p.coeff ((1 : H)⁻¹ • y) = p.coeff y
    simp
  mul_smul h k p := by
    ext y
    change p.coeff ((h * k)⁻¹ • y) = p.coeff (k⁻¹ • (h⁻¹ • y))
    simp [mul_smul]

open scoped BassTrace.Sparse

@[simp] lemma smul_probability_coeff (h : H) (p : FinProbability Y) (y : Y) :
    (h • p).coeff y = p.coeff (h⁻¹ • y) := rfl

lemma smul_probability_support (h : H) (p : FinProbability Y) :
    (h • p).coeff.support = p.coeff.support.map (MulAction.toPerm h).toEmbedding := rfl

lemma smul_probability_rho [PseudoMetricSpace Y]
    (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (h : H) (n : ℕ) (p q : FinProbability Y) :
    FinProbability.rho n (h • p) (h • q) = FinProbability.rho n p q :=
  FinProbability.rho_push (MulAction.toPerm h) (hi h) n p q

end BassTrace.Sparse

namespace BassTrace.Sparse.OrbitForms

open Set Finset

variable {H Y I : Type*} [Group H] [MulAction H Y]

def push (h : H) : (Y →₀ ℝ) ≃ₗ[ℝ] (Y →₀ ℝ) :=
  Finsupp.domLCongr (MulAction.toPerm h)

@[simp] lemma push_apply (h : H) (p : Y →₀ ℝ) (y : Y) :
    push h p y = p (h⁻¹ • y) := by rfl

@[simp] lemma push_one (p : Y →₀ ℝ) : push (1:H) p = p := by ext y; simp

lemma push_mul (h k : H) (p : Y →₀ ℝ) : push (h*k) p = push h (push k p) := by
  ext y
  simp [mul_smul]

@[simp] lemma push_inv_push (h : H) (p : Y →₀ ℝ) : push h⁻¹ (push h p) = p := by
  rw [← push_mul,inv_mul_cancel,push_one]

structure Data (I : Type*) (Y : Type*) where
  form : I → (Y →₀ ℝ) →ₗ[ℝ] ℝ
  support : I → Finset Y
  vanish : ∀ i p, (∀ y ∈ support i, p y = 0) → form i p = 0

variable (d : Data I Y)

def form (j : H × I) : (Y →₀ ℝ) →ₗ[ℝ] ℝ :=
  (d.form j.2).comp (push j.1⁻¹).toLinearMap

lemma form_apply (h : H) (i : I) (p : Y →₀ ℝ) :
    form d (h,i) p = d.form i (push h⁻¹ p) := rfl

lemma form_translate (k h : H) (i : I) (p : Y →₀ ℝ) :
    form d (k*h,i) (push k p) = form d (h,i) p := by
  change d.form i (push (k*h)⁻¹ (push k p)) = d.form i (push h⁻¹ p)
  rw [mul_inv_rev,push_mul,push_inv_push]

lemma form_ne_zero_support {j : H × I} {p : Y →₀ ℝ} (hp : form d j p ≠ 0) :
    ∃ y ∈ d.support j.2, j.1 • y ∈ p.support := by
  by_contra! hh
  apply hp
  apply d.vanish
  intro y hy
  simpa using Finsupp.notMem_support_iff.mp (hh y hy)

variable [IsCancelSMul H Y]

lemma finite_form_ne_zero (i : I) (p : Y →₀ ℝ) :
    {h : H | form d (h,i) p ≠ 0}.Finite := by
  apply (Set.Finite.biUnion (d.support i).finite_toSet (fun y _ =>
    Set.Finite.preimage (fun h _ k _ he => IsCancelSMul.right_cancel h k y he)
      p.support.finite_toSet)).subset
  intro h hh
  obtain ⟨y,hy,hyp⟩ := form_ne_zero_support d hh
  exact Set.mem_iUnion₂.mpr ⟨y,hy,hyp⟩

variable [Fintype I]

lemma finite_relevant (s : Finset (Y →₀ ℝ)) :
    {j : H × I | ∃ p ∈ s, form d j p ≠ 0}.Finite := by
  classical
  have hi : (⋃ i : I, (fun h : H => (h,i)) ''
      (⋃ p ∈ (s : Set (Y →₀ ℝ)), {h : H | form d (h,i) p ≠ 0})).Finite := by
    apply Set.finite_iUnion
    intro i
    exact (Set.Finite.biUnion s.finite_toSet
      (fun p _ => finite_form_ne_zero d i p)).image _
  apply hi.subset
  rintro ⟨h,i⟩ ⟨p,hp,hh⟩
  exact Set.mem_iUnion.mpr ⟨i,h,Set.mem_iUnion₂.mpr ⟨p,hp,hh⟩,rfl⟩

def relevant (s : Finset (Y →₀ ℝ)) : Finset (H × I) := (finite_relevant d s).toFinset

@[simp] lemma mem_relevant (s : Finset (Y →₀ ℝ)) (j : H × I) :
    j ∈ relevant d s ↔ ∃ p ∈ s, form d j p ≠ 0 := by simp [relevant]

lemma irrelevant_vanish (s : Finset (Y →₀ ℝ)) (j : H × I)
    (hj : j ∉ relevant d s) : ∀ p ∈ convexHull ℝ (s : Set (Y →₀ ℝ)), form d j p = 0 := by
  have hs : (s : Set (Y →₀ ℝ)) ⊆ (form d j).ker := by
    intro p hp
    by_contra hh
    exact hj ((mem_relevant d s j).mpr ⟨p,hp,hh⟩)
  exact convexHull_min hs (form d j).ker.convex

lemma relevant_translate (k h : H) (i : I) (s : Finset (Y →₀ ℝ)) :
    (k*h,i) ∈ relevant d (s.map (push k).toEmbedding) ↔ (h,i) ∈ relevant d s := by
  simp only [mem_relevant]
  constructor
  · rintro ⟨p,hp,hh⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    exact ⟨q,hq,by simpa [form_translate] using hh⟩
  · rintro ⟨p,hp,hh⟩
    exact ⟨push k p,Finset.mem_map.mpr ⟨p,hp,rfl⟩,by simpa [form_translate] using hh⟩

def relevantEquiv (k : H) (s : Finset (Y →₀ ℝ)) :
    relevant (H := H) d s ≃ relevant (H := H) d (s.map (push k).toEmbedding) where
  toFun j := ⟨(k*j.val.1,j.val.2),(relevant_translate d k j.val.1 j.val.2 s).mpr j.property⟩
  invFun j := ⟨(k⁻¹*j.val.1,j.val.2),by
    have hh := (relevant_translate d k (k⁻¹*j.val.1) j.val.2 s)
    simpa using hh.mp (by simpa only [mul_inv_cancel_left] using j.property)⟩
  left_inv j := by ext <;> simp
  right_inv j := by ext <;> simp

lemma relevantEquiv_form (k : H) (s : Finset (Y →₀ ℝ)) (i : relevant (H := H) d s) :
    (form d (relevantEquiv d k s i).val).comp (push k).toLinearMap = form d i.val := by
  apply LinearMap.ext
  intro p
  exact form_translate d k i.val.1 i.val.2 p

end BassTrace.Sparse.OrbitForms

namespace BassTrace.Sparse.BallOrbitForms

open Set Finset

open scoped BassTrace.Sparse

variable {H Y C : Type*} [Group H] [MulAction H Y] [MetricSpace Y]

variable (S : C → Finset Y) (c : C → FinProbability Y) (n : ℕ)

abbrev Index := Σ i : C, ↥(potentialVertices : Finset (S i → ℝ))

def data : OrbitForms.Data (Index S) Y where
  form j := (ballBranch (S j.1) (c j.1) n j.2.val).toLinearMap
  support j := S j.1
  vanish j p hp := by
    rw [ContinuousLinearMap.coe_coe,ballBranch_apply]
    apply Finset.sum_eq_zero
    intro y _
    rw [hp y y.property,mul_zero]

omit [MetricSpace Y] in
lemma push_coeff (h : H) (p : FinProbability Y) :
    OrbitForms.push h p.coeff = (h • p).coeff := by
  ext y
  rfl

lemma branch_apply (h : H) (j : Index S) (p : FinProbability Y) :
    OrbitForms.form (data S c n) (h,j) p.coeff =
      ballBranch (S j.1) (c j.1) n j.2.val (h⁻¹ • p).coeff := by
  change ballBranch (S j.1) (c j.1) n j.2.val (OrbitForms.push h⁻¹ p.coeff) = _
  rw [push_coeff]

lemma exists_maximizer (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i) (h : H) (i : C)
    (p : FinProbability Y) (hp : (h⁻¹ • p).coeff.support ⊆ S i) :
    ∃ l : ↥(potentialVertices : Finset (S i → ℝ)),
      FinProbability.rho n (h • c i) p =
        OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff ∧
      ∀ l' : ↥(potentialVertices : Finset (S i → ℝ)),
        OrbitForms.form (data S c n) (h,⟨i,l'⟩) p.coeff ≤
          FinProbability.rho n (h • c i) p := by
  have he : FinProbability.rho n (h • c i) p = FinProbability.rho n (c i) (h⁻¹ • p) := by
    simpa only [smul_inv_smul] using smul_probability_rho hi h n (c i) (h⁻¹ • p)
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer (S i) (c i) (h⁻¹ • p) (hc i) hp n
  refine ⟨⟨l,hl⟩,?_,?_⟩
  · rw [branch_apply,he]
    exact heq
  · intro l'
    rw [branch_apply,he]
    exact hmax _ l'.property

lemma distance_le_iff (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i) (h : H) (i : C)
    (p : FinProbability Y) (hp : (h⁻¹ • p).coeff.support ⊆ S i) (t : ℝ) :
    FinProbability.rho n (h • c i) p ≤ t ↔
      ∀ l : ↥(potentialVertices : Finset (S i → ℝ)),
        OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff ≤ t := by
  obtain ⟨l,he,hm⟩ := exists_maximizer S c n hi hc h i p hp
  exact ⟨fun hh l' => (hm l').trans hh,fun hh => he ▸ hh l⟩

lemma distance_ge_iff (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i) (h : H) (i : C)
    (p : FinProbability Y) (hp : (h⁻¹ • p).coeff.support ⊆ S i) (t : ℝ) :
    t ≤ FinProbability.rho n (h • c i) p ↔
      ∃ l : ↥(potentialVertices : Finset (S i → ℝ)),
        t ≤ OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff := by
  obtain ⟨l,he,hm⟩ := exists_maximizer S c n hi hc h i p hp
  exact ⟨fun hh => ⟨l,he ▸ hh⟩,fun ⟨l',hh⟩ => hh.trans (hm l')⟩

lemma distance_eq_iff (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i) (h : H) (i : C)
    (p : FinProbability Y) (hp : (h⁻¹ • p).coeff.support ⊆ S i) (t : ℝ) :
    FinProbability.rho n (h • c i) p = t ↔
      (∀ l : ↥(potentialVertices : Finset (S i → ℝ)),
        OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff ≤ t) ∧
      ∃ l : ↥(potentialVertices : Finset (S i → ℝ)),
        OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff = t := by
  obtain ⟨l,he,hm⟩ := exists_maximizer S c n hi hc h i p hp
  constructor
  · intro hh
    exact ⟨fun l' => hh ▸ hm l',l,he.symm.trans hh⟩
  · rintro ⟨hle,l',hlt⟩
    exact le_antisymm (he ▸ hle l) (hlt ▸ hm l')

end BassTrace.Sparse.BallOrbitForms

namespace BassTrace.Sparse.OrbitForms

open Set Finset

open scoped BassTrace.Sparse

variable {H Y I X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype I]

variable (d : Data I Y) {t : ℝ} (ht : 0 < t)

def cuts : Cuts.UniversalCuts (Y →₀ ℝ) (H × I) where
  form := form d
  level := fun _ => t
  positive := fun _ => ht
  relevant := relevant d
  vanish := irrelevant_vanish d

lemma cuts_map {K L : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)} (k : H)
    (hKL : ∀ s ∈ K.faces, s.map (push k).toEmbedding ∈ L.faces)
    {s : Finset (Y →₀ ℝ)} (hs : s ∈ ((cuts (H := H) d ht).onComplex K).globalComplex.faces) :
    s.map (push k).toEmbedding ∈ ((cuts (H := H) d ht).onComplex L).globalComplex.faces := by
  apply Cuts.LocalCutData.globalComplex_map ((cuts (H := H) d ht).onComplex K)
    ((cuts (H := H) d ht).onComplex L) (push k).toLinearMap (push k).injective hKL
    (fun u _ => relevantEquiv d k u) _ _ hs
  · intro u _ j
    exact relevantEquiv_form d k u j
  · intros
    rfl

variable [TopologicalSpace X] [MulAction H X]

def Equivariant {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    (T : Cuts.SubdivisionFamily X K) : Prop :=
  ∀ (k : H) (x : X) s, s ∈ (T.val x).complex.faces →
    s.map (push k).toEmbedding ∈ (T.val (k • x)).complex.faces

lemma refineFamily_equivariant {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    (T : Cuts.SubdivisionFamily X K) (hT : Equivariant (H := H) T) :
    Equivariant (H := H) ((cuts (H := H) d ht).refineFamily T) := by
  intro k x s hs
  exact cuts_map d ht k (hT k x) hs

end BassTrace.Sparse.OrbitForms

end

end OAI
