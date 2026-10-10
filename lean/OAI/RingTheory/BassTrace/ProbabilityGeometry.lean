import OAI.RingTheory.BassTrace.NormedVectors

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open Finset

open scoped BassTrace.Sparse

variable {Y : Type*} [MetricSpace Y]

namespace FinProbability

omit [MetricSpace Y] in
lemma expectation_on_finset (p : FinProbability Y) (S : Finset Y)
    (hp : p.coeff.support ⊆ S) (f : Y → ℝ) :
    p.expectation f = ∑ y : S, p.coeff y * f y := by
  rw [expectation,p.coeff.sum_of_support_subset hp _ (by intros; simp)]
  exact Finset.sum_subtype S (fun _ => Iff.rfl) _

omit [MetricSpace Y] in
lemma total_on_finset (p : FinProbability Y) (S : Finset Y)
    (hp : p.coeff.support ⊆ S) : ∑ y : S, p.coeff y = 1 := by
  simpa only [mul_one] using (p.expectation_on_finset S hp (fun _ => 1)).symm.trans
    (p.expectation_const 1)

omit [MetricSpace Y] in
lemma gap_on_finset (c p : FinProbability Y) (S : Finset Y)
    (hc : c.coeff.support ⊆ S) (hp : p.coeff.support ⊆ S) (f : Y → ℝ) :
    c.gap p f = ∑ y : S, (c.coeff y-p.coeff y)*f y := by
  rw [gap,c.expectation_on_finset S hc,p.expectation_on_finset S hp]
  simp only [sub_mul,Finset.sum_sub_distrib]

end FinProbability

def centerBranchValue (S : Finset Y) (c : FinProbability Y) (l : S → ℝ) : ℝ :=
  ∑ y : S, c.coeff y * l y

def ballBranch (S : Finset Y) (c : FinProbability Y) (n : ℕ) (l : S → ℝ) :
    (Y →₀ ℝ) →L[ℝ] ℝ :=
  ∑ y : S, ((centerBranchValue S c l - l y) / Real.sqrt n) • coordinateCLM (y : Y)

omit [MetricSpace Y] in
lemma ballBranch_apply (S : Finset Y) (c : FinProbability Y) (n : ℕ)
    (l : S → ℝ) (p : Y →₀ ℝ) :
    ballBranch S c n l p = ∑ y : S,
      ((centerBranchValue S c l-l y)/Real.sqrt n) * p y := by
  simp only [ballBranch,_root_.sum_apply,smul_apply,
    coordinateCLM_apply,smul_eq_mul]

omit [MetricSpace Y] in
lemma ballBranch_eq_pairing (S : Finset Y) (c p : FinProbability Y)
    (hp : p.coeff.support ⊆ S) (n : ℕ) (l : S → ℝ) :
    ballBranch S c n l p.coeff =
      (∑ y : S, (c.coeff y-p.coeff y)*l y) / Real.sqrt n := by
  rw [ballBranch_apply]
  simp_rw [div_mul_eq_mul_div,← Finset.sum_div,sub_mul]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,p.total_on_finset S hp,mul_one]
  simp only [centerBranchValue,Finset.sum_sub_distrib]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

omit [MetricSpace Y] in
lemma ballBranch_vanish (S : Finset Y) (c : FinProbability Y) (n : ℕ)
    (l : S → ℝ) (p : Y →₀ ℝ) (hp : Disjoint S p.support) :
    ballBranch S c n l p = 0 := by
  classical
  rw [ballBranch_apply]
  apply Finset.sum_eq_zero
  intro y _
  have hy : y.val ∉ p.support := fun hy => Finset.disjoint_left.mp hp y.property hy
  rw [Finsupp.notMem_support_iff.mp hy,mul_zero]

theorem exists_ballBranch_maximizer (S : Finset Y) (c p : FinProbability Y)
    (hc : c.coeff.support ⊆ S) (hp : p.coeff.support ⊆ S) (n : ℕ) :
    ∃ l ∈ (potentialVertices : Finset (S → ℝ)),
      FinProbability.rho n c p = ballBranch S c n l p.coeff ∧
      ∀ l' ∈ (potentialVertices : Finset (S → ℝ)),
        ballBranch S c n l' p.coeff ≤ FinProbability.rho n c p := by
  classical
  have hS : S.Nonempty := c.coeff_support_nonempty.mono hc
  let k : S → ℝ := fun y => c.coeff y-p.coeff y
  have hk : ∑ y, k y = 0 := by
    simp only [k,Finset.sum_sub_distrib,c.total_on_finset S hc,p.total_on_finset S hp,
      sub_self]
  obtain ⟨l,hl,⟨f,hf,hfl⟩,hmax⟩ := exists_global_vertex_maximizer S hS k hk
  have heq : c.transport p = ∑ y : S, k y*l y := by
    apply le_antisymm
    · apply FinProbability.transport_le
      intro g hg
      rw [c.gap_on_finset p S hc hp]
      exact hmax g hg
    · have hh := c.gap_le_transport p f hf
      rw [c.gap_on_finset p S hc hp] at hh
      simpa only [k,hfl] using hh
  refine ⟨l,hl,?_,?_⟩
  · rw [FinProbability.rho,heq,ballBranch_eq_pairing S c p hp]
  · intro l' hl'
    obtain ⟨g,hg,hgl⟩ := exists_global_potential_extension S (potentialVertices_subset l' hl')
    rw [ballBranch_eq_pairing S c p hp,FinProbability.rho]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hh := c.gap_le_transport p g hg
    rw [c.gap_on_finset p S hc hp] at hh
    simpa only [hgl] using hh

lemma rho_le_iff_ballBranches (S : Finset Y) (c p : FinProbability Y)
    (hc : c.coeff.support ⊆ S) (hp : p.coeff.support ⊆ S) (n : ℕ) (t : ℝ) :
    FinProbability.rho n c p ≤ t ↔
      ∀ l ∈ (potentialVertices : Finset (S → ℝ)), ballBranch S c n l p.coeff ≤ t := by
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer S c p hc hp n
  exact ⟨fun h l' hl' => (hmax l' hl').trans h,fun h => heq ▸ h l hl⟩

lemma rho_eq_iff_ballBranches (S : Finset Y) (c p : FinProbability Y)
    (hc : c.coeff.support ⊆ S) (hp : p.coeff.support ⊆ S) (n : ℕ) (t : ℝ) :
    FinProbability.rho n c p = t ↔
      (∀ l ∈ (potentialVertices : Finset (S → ℝ)), ballBranch S c n l p.coeff ≤ t) ∧
      ∃ l ∈ (potentialVertices : Finset (S → ℝ)), ballBranch S c n l p.coeff = t := by
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer S c p hc hp n
  constructor
  · intro h
    exact ⟨fun l' hl' => h ▸ hmax l' hl',l,hl,heq.symm.trans h⟩
  · rintro ⟨hle,l',hl',hlt⟩
    exact le_antisymm (heq ▸ hle l hl) (hlt ▸ hmax l' hl')

end

open Set Finset

open scoped BassTrace.Sparse

section

variable {Y : Type*}

def coefficientSum : (Y →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ : Y => (1 : ℝ))

@[simp] lemma coefficientSum_apply (v : Y →₀ ℝ) :
    coefficientSum v = v.sum (fun _ r => r) := by
  simp [coefficientSum,Finsupp.linearCombination_apply]

@[simp] lemma coefficientSum_single (y : Y) (r : ℝ) :
    coefficientSum (Finsupp.single y r) = r := by simp

def probabilitySet (s : Finset Y) : Set (Y →₀ ℝ) :=
  {v | (∀ y, 0 ≤ v y) ∧ coefficientSum v = 1 ∧ v.support ⊆ s}

lemma convex_probabilitySet (s : Finset Y) : Convex ℝ (probabilitySet s) := by
  intro v hv w hw a b ha hb hab
  refine ⟨?_,?_,?_⟩
  · intro y
    change 0 ≤ a * v y + b * w y
    exact add_nonneg (mul_nonneg ha (hv.1 y)) (mul_nonneg hb (hw.1 y))
  · change coefficientSum (a • v + b • w) = 1
    rw [map_add,map_smul,map_smul,hv.2.1,hw.2.1]
    simpa using hab
  · intro y hy
    by_contra h
    have hv0 : v y = 0 := Finsupp.notMem_support_iff.mp (fun hy => h (hv.2.2 hy))
    have hw0 : w y = 0 := Finsupp.notMem_support_iff.mp (fun hy => h (hw.2.2 hy))
    exact (Finsupp.mem_support_iff.mp hy) (by simp [Finsupp.add_apply,Finsupp.smul_apply,hv0,hw0])

lemma single_mem_probabilitySet (s : Finset Y) {y : Y} (hy : y ∈ s) :
    Finsupp.single y (1 : ℝ) ∈ probabilitySet s := by
  classical
  refine ⟨?_, by simp, ?_⟩
  · intro z
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  · simpa using Finset.singleton_subset_iff.mpr hy

lemma sum_single_of_support_subset (s : Finset Y) (v : Y →₀ ℝ)
    (hv : v.support ⊆ s) :
    ∑ y ∈ s, v y • Finsupp.single y (1 : ℝ) = v := by
  classical
  ext z
  simp only [Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,Finsupp.single_apply]
  by_cases hz : z ∈ s
  · simp [hz,eq_comm]
  · have hvz := Finsupp.notMem_support_iff.mp (fun h => hz (hv h))
    simp [hz,hvz,eq_comm]

lemma sum_coeff_of_support_subset (s : Finset Y) (v : Y →₀ ℝ)
    (hv : v.support ⊆ s) : ∑ y ∈ s, v y = coefficientSum v := by
  rw [coefficientSum_apply,Finsupp.sum]
  exact (Finset.sum_subset hv (fun y _ hy => Finsupp.notMem_support_iff.mp hy)).symm

lemma convexHull_single_eq_probabilitySet (s : Finset Y) :
    convexHull ℝ ((fun y : Y => Finsupp.single y (1 : ℝ)) '' (s : Set Y)) =
      probabilitySet s := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨y,hy,rfl⟩
      exact single_mem_probabilitySet s hy
    · exact convex_probabilitySet s
  · intro v hv
    rw [← sum_single_of_support_subset s v hv.2.2]
    apply (convex_convexHull ℝ _).sum_mem
    · exact fun y _ => hv.1 y
    · exact (sum_coeff_of_support_subset s v hv.2.2).trans hv.2.1
    · intro y hy
      exact subset_convexHull ℝ _ ⟨y,hy,rfl⟩

lemma FinProbability.mem_geometric_simplex (p : FinProbability Y) (s : Finset Y) :
    p.coeff ∈ convexHull ℝ
        ((fun y : Y => Finsupp.single y (1 : ℝ)) '' (s : Set Y)) ↔
      p.coeff.support ⊆ s := by
  rw [convexHull_single_eq_probabilitySet]
  exact ⟨fun h => h.2.2,fun h => ⟨p.nonneg,by simpa using p.total,h⟩⟩

lemma probabilitySet_eq (s : Finset Y) :
    probabilitySet s = {v | ∃ p : FinProbability Y, p.coeff = v ∧ p.coeff.support ⊆ s} := by
  ext v
  constructor
  · intro h
    exact ⟨⟨v,h.1,by simpa using h.2.1⟩,rfl,h.2.2⟩
  · rintro ⟨p,rfl,hp⟩
    exact ⟨p.nonneg,by simpa using p.total,hp⟩

lemma geometric_simplex_compact (s : Finset Y) :
    IsCompact (probabilitySet s) := by
  rw [← convexHull_single_eq_probabilitySet]
  exact (s.finite_toSet.image _).isCompact_convexHull ℝ

end

section

variable {Y : Type*} [DecidableEq Y]

lemma onFinsupp_faces (K : PreAbstractSimplicialComplex Y) :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces =
      (fun s : Finset Y => s.image (fun y => Finsupp.single y (1 : ℝ))) '' K.faces := rfl

lemma onFinsupp_space (K : PreAbstractSimplicialComplex Y) :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space =
      {v | ∃ p : FinProbability Y, p.coeff = v ∧ p.coeff.support ∈ K.faces} := by
  ext v
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨s,hs,hv⟩
    rw [onFinsupp_faces] at hs
    obtain ⟨t,ht,rfl⟩ := hs
    rw [Finset.coe_image,convexHull_single_eq_probabilitySet,probabilitySet_eq] at hv
    obtain ⟨p,hp,hpt⟩ := hv
    exact ⟨p,hp,(K.isRelLowerSet_faces ht).2 hpt p.coeff_support_nonempty⟩
  · rintro ⟨p,rfl,hp⟩
    refine ⟨p.coeff.support.image (fun y => Finsupp.single y (1 : ℝ)),?_,?_⟩
    · exact ⟨p.coeff.support,hp,rfl⟩
    · rw [Finset.coe_image,p.mem_geometric_simplex]

end

variable {Y : Type*} [MetricSpace Y]

@[instance_reducible] def FinProbability.rhoMetric (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) : MetricSpace (FinProbability Y) where
  dist := FinProbability.rho n
  dist_self p := by simp [FinProbability.rho,FinProbability.transport_self]
  dist_comm := FinProbability.rho_comm n
  dist_triangle := FinProbability.rho_triangle n
  eq_of_dist_eq_zero := by
    intro p q hpq
    apply (FinProbability.transport_eq_zero_iff p q hd).mp
    rw [← FinProbability.sqrt_mul_rho hn,hpq,mul_zero]

def simplexProbability (S : Finset Y) (v : probabilitySet S) : FinProbability Y :=
  ⟨v.val,v.property.1,by simpa using v.property.2.1⟩

omit [MetricSpace Y] in
lemma simplexProbability_support (S : Finset Y) (v : probabilitySet S) :
    (simplexProbability S v).coeff.support ⊆ S := v.property.2.2

lemma potentialVertices_nonempty (S : Finset Y) (hS : S.Nonempty) :
    (potentialVertices : Finset (S → ℝ)).Nonempty := by
  let : Nonempty S := hS.to_subtype
  obtain ⟨l,hl,_⟩ := exists_potential_vertex_maximizer (V := S) (0 : (S → ℝ) →L[ℝ] ℝ)
  exact ⟨l,hl⟩

lemma rho_eq_vertex_sup (S : Finset Y) (hS : S.Nonempty) (n : ℕ)
    (p q : FinProbability Y) (hp : p.coeff.support ⊆ S) (hq : q.coeff.support ⊆ S) :
    FinProbability.rho n p q =
      (potentialVertices : Finset (S → ℝ)).sup' (potentialVertices_nonempty S hS)
        (fun l => (∑ y : S, (p.coeff y-q.coeff y)*l y)/Real.sqrt n) := by
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer S p q hp hq n
  apply le_antisymm
  · rw [heq,ballBranch_eq_pairing S p q hq]
    exact Finset.le_sup' (fun l => (∑ y : S, (p.coeff y-q.coeff y)*l y)/Real.sqrt n) hl
  · apply (Finset.sup'_le_iff _ _).mpr
    intro l' hl'
    rw [← ballBranch_eq_pairing S p q hq]
    exact hmax l' hl'

lemma continuous_simplexProbability (S : Finset Y) (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) :
    let := FinProbability.rhoMetric n hn hd
    Continuous (simplexProbability S) := by
  let := FinProbability.rhoMetric n hn hd
  by_cases hS : S.Nonempty
  · rw [continuous_iff_continuous_dist]
    have heq : (fun p : probabilitySet S × probabilitySet S =>
        dist (simplexProbability S p.1) (simplexProbability S p.2)) =
        fun p => (potentialVertices : Finset (S → ℝ)).sup' (potentialVertices_nonempty S hS)
          (fun l => (∑ y : S, (p.1.val y-p.2.val y)*l y)/Real.sqrt n) := by
      funext p
      exact rho_eq_vertex_sup S hS n _ _ p.1.property.2.2 p.2.property.2.2
    rw [heq]
    apply Continuous.finset_sup'_apply
    intro l _
    apply Continuous.div_const
    apply continuous_finsetSum
    intro y _
    apply Continuous.mul_const
    apply Continuous.sub
    · exact (coordinateCLM (y : Y)).continuous.comp (continuous_subtype_val.comp continuous_fst)
    · exact (coordinateCLM (y : Y)).continuous.comp (continuous_subtype_val.comp continuous_snd)
  · have : IsEmpty (probabilitySet S) := ⟨fun v => hS
        ((simplexProbability S v).coeff_support_nonempty.mono v.property.2.2)⟩
    exact continuous_iff_continuousAt.mpr (fun v => isEmptyElim v)

lemma isCompact_probability_simplex (S : Finset Y) (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) :
    let := FinProbability.rhoMetric n hn hd
    IsCompact {p : FinProbability Y | p.coeff.support ⊆ S} := by
  let := FinProbability.rhoMetric n hn hd
  let : CompactSpace (probabilitySet S) := isCompact_iff_compactSpace.mp (geometric_simplex_compact S)
  have heq : {p : FinProbability Y | p.coeff.support ⊆ S} =
      Set.range (simplexProbability S) := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨p.coeff,p.nonneg,by simpa using p.total,hp⟩,rfl⟩
    · rintro ⟨v,rfl⟩
      exact v.property.2.2
  rw [heq]
  exact isCompact_range (continuous_simplexProbability S n hn hd)

end BassTrace.Sparse

end

end OAI
