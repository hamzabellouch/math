import Mathlib

namespace OAI

/-! Cubical free nullity and change of basepoint. -/

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology Topology.Homotopy

namespace NearbyLagrangian.CubicalFreeNullity
variable {N : Type*} [Fintype N] [Nonempty N]

def radius (t : N → unitInterval) : ℝ := ‖fun i => 2*(t i:ℝ)-1‖
omit [Nonempty N] in
lemma radius_nonneg (t : N → unitInterval) : 0 ≤ radius t := norm_nonneg _
omit [Nonempty N] in
lemma radius_le_one (t : N → unitInterval) : radius t ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  rw [Real.norm_eq_abs,abs_le]
  have hi₀ := (t i).property.1
  have hi₁ := (t i).property.2
  constructor <;> linarith
omit [Nonempty N] in
lemma continuous_radius : Continuous (radius (N:=N)) :=
  (continuous_pi fun i => (continuous_const.mul
    (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const).norm
omit [Nonempty N] in
lemma radius_boundary {t : N → unitInterval} (ht : t ∈ Cube.boundary N) : radius t = 1 := by
  apply le_antisymm (radius_le_one t)
  obtain ⟨i,hi⟩ := ht
  have hh := norm_le_pi_norm (fun i => 2*(t i:ℝ)-1) i
  rcases hi with hi | hi
  · simpa [radius,hi] using hh
  · norm_num [hi] at hh
    exact hh

def collarTime (s : unitInterval) (t : N → unitInterval) : unitInterval :=
  ⟨min (s:ℝ) (2*(1-radius t)),
    le_min s.property.1 (by have := radius_le_one t; linarith),
    (min_le_left _ _).trans s.property.2⟩
omit [Nonempty N] in
lemma continuous_collarTime : Continuous (fun a : unitInterval × (N → unitInterval) => collarTime a.1 a.2) :=
  ((continuous_subtype_val.comp continuous_fst).min
    (continuous_const.mul (continuous_const.sub (continuous_radius.comp continuous_snd)))).subtype_mk _
omit [Nonempty N] in
@[simp] lemma collarTime_zero (t : N → unitInterval) : collarTime 0 t = 0 := by
  apply Subtype.ext
  change min 0 (2*(1-radius t)) = 0
  apply min_eq_left
  have := radius_le_one t
  linarith
omit [Nonempty N] in
lemma collarTime_boundary (s : unitInterval) {t : N → unitInterval} (ht : t ∈ Cube.boundary N) :
    collarTime s t = 0 := by
  apply Subtype.ext
  change min (s:ℝ) (2*(1-radius t)) = 0
  rw [radius_boundary ht]
  simp only [sub_self,mul_zero,min_eq_right s.property.1]

lemma denominator_pos (s : unitInterval) : 0 < 1-(s:ℝ)/2 := by
  have := s.property.2
  linarith

def expand (s : unitInterval) (t : N → unitInterval) : N → unitInterval :=
  fun i => projIcc 0 1 (zero_le_one' ℝ) (((t i:ℝ)-(s:ℝ)/4)/(1-(s:ℝ)/2))
omit [Fintype N] [Nonempty N] in
lemma continuous_expand : Continuous (fun a : unitInterval × (N → unitInterval) => expand a.1 a.2) := by
  apply continuous_pi
  intro i
  apply continuous_projIcc.comp
  exact ((continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)).sub
    ((continuous_subtype_val.comp continuous_fst).div_const 4)).div
      (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2))
      (fun a => ne_of_gt (denominator_pos a.1))
omit [Fintype N] [Nonempty N] in
@[simp] lemma expand_zero (t : N → unitInterval) : expand 0 t = t := by
  funext i
  change projIcc 0 1 _ (((t i:ℝ)-(0:ℝ)/4)/(1-(0:ℝ)/2)) = t i
  simp only [zero_div,sub_zero,div_one,projIcc_val]

lemma expand_mem_boundary {s : unitInterval} {t : N → unitInterval}
    (ht : 1-(s:ℝ)/2 ≤ radius t) : expand s t ∈ Cube.boundary N := by
  obtain ⟨⟨i,hi⟩,_⟩ := IsGreatest.pi_norm (fun i => 2*(t i:ℝ)-1)
  have habs : 1-(s:ℝ)/2 ≤ |2*(t i:ℝ)-1| := by
    change ‖2*(t i:ℝ)-1‖ = radius t at hi
    rw [Real.norm_eq_abs] at hi
    exact ht.trans_eq hi.symm
  rcases (le_abs.mp habs) with h | h
  · refine ⟨i,Or.inr ?_⟩
    apply projIcc_of_right_le
    apply (le_div_iff₀ (denominator_pos s)).mpr
    linarith
  · refine ⟨i,Or.inl ?_⟩
    apply projIcc_of_le_left
    apply div_nonpos_of_nonpos_of_nonneg _ (denominator_pos s).le
    linarith

lemma expand_boundary (s : unitInterval) {t : N → unitInterval} (ht : t ∈ Cube.boundary N) :
    expand s t ∈ Cube.boundary N := by
  apply expand_mem_boundary
  rw [radius_boundary ht]
  have := s.property.1
  linarith

variable {X : Type*} [TopologicalSpace X]

theorem null_of_moving_base {x y : X} (f : GenLoop N X x)
    (H : f.1.Homotopy (ContinuousMap.const _ y))
    (p : C(unitInterval,X))
    (hp : ∀ s t, t ∈ Cube.boundary N → H (s,t) = p s) :
    GenLoop.Homotopic f GenLoop.const := by
  let z : N → unitInterval := fun _ => 0
  have hz : z ∈ Cube.boundary N := ⟨Classical.choice inferInstance,Or.inl rfl⟩
  have hp0 : p 0 = x := by
    rw [← hp 0 z hz,H.apply_zero]
    exact GenLoop.boundary f z hz
  have hp1 : p 1 = y := by rw [← hp 1 z hz,H.apply_one]; rfl
  let a : C(N → unitInterval,X) := p.comp ⟨fun t => collarTime 1 t,
    continuous_collarTime.comp (continuous_const.prodMk continuous_id)⟩
  have ha (t : N → unitInterval) : H (collarTime 1 t,expand 1 t) = a t := by
    change H (collarTime 1 t,expand 1 t) = p (collarTime 1 t)
    by_cases ht : collarTime 1 t = 1
    · rw [ht,H.apply_one,hp1]; rfl
    · apply hp
      apply expand_mem_boundary
      have hk : (collarTime 1 t:ℝ) < 1 := lt_of_le_of_ne (collarTime 1 t).property.2
        (fun h => ht (Subtype.ext h))
      change min 1 (2*(1-radius t)) < 1 at hk
      have hr : 2*(1-radius t) < 1 := by simpa only [min_lt_iff,lt_self_iff_false,false_or] using hk
      change 1-(1:ℝ)/2 ≤ radius t
      linarith
  let H₁ : f.1.HomotopyRel a (Cube.boundary N) := {
    toFun := fun q => H (collarTime q.1 q.2,expand q.1 q.2)
    continuous_toFun := H.continuous.comp (continuous_collarTime.prodMk continuous_expand)
    map_zero_left := by intro t; simp only [collarTime_zero,expand_zero,H.apply_zero]
    map_one_left := ha
    prop' := by
      intro s t ht
      change H (collarTime s t,expand s t) = f t
      rw [collarTime_boundary s ht,hp 0 _ (expand_boundary s ht),hp0,GenLoop.boundary f t ht] }
  let H₂ : a.HomotopyRel (ContinuousMap.const _ x) (Cube.boundary N) := {
    toFun := fun q => p ⟨(1-(q.1:ℝ))*(collarTime 1 q.2:ℝ),
      mul_nonneg (by linarith [q.1.property.2]) (collarTime _ _).property.1,
      (mul_le_of_le_one_left (collarTime _ _).property.1
        (by linarith [q.1.property.1])).trans (collarTime _ _).property.2⟩
    continuous_toFun := p.continuous.comp (Continuous.subtype_mk
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp (continuous_collarTime.comp (continuous_const.prodMk continuous_snd)))) _)
    map_zero_left := by
      intro t
      change p _ = p (collarTime 1 t)
      congr 1
      apply Subtype.ext
      change (1-(0:ℝ))*(collarTime 1 t:ℝ) = (collarTime 1 t:ℝ)
      ring
    map_one_left := by
      intro t
      change p _ = x
      convert hp0 using 1
      congr 1
      apply Subtype.ext
      change (1-(1:ℝ))*(collarTime 1 t:ℝ) = 0
      ring
    prop' := by
      intro s t ht
      change p _ = p (collarTime 1 t)
      rw [collarTime_boundary 1 ht]
      congr 1
      apply Subtype.ext
      change (1-(s:ℝ))*(0:ℝ) = 0
      ring }
  exact ⟨H₁.trans H₂⟩

end NearbyLagrangian.CubicalFreeNullity

end

noncomputable section
universe u v w
open scoped Classical Topology Topology.Homotopy

namespace NearbyLagrangian.CubicalFreeNullity
variable {N : Type*} [Fintype N] [Nonempty N]
variable {X : Type*} [TopologicalSpace X] {x y : X}

def outerTime (s : unitInterval) (t : N → unitInterval) : unitInterval :=
  ⟨max 0 ((s:ℝ)-2*(1-radius t)),le_max_left _ _,by
    apply max_le zero_le_one
    have := radius_le_one t
    linarith [s.property.2]⟩
omit [Nonempty N] in
lemma continuous_outerTime : Continuous (fun a : unitInterval × (N → unitInterval) => outerTime a.1 a.2) :=
  ((continuous_const.max ((continuous_subtype_val.comp continuous_fst).sub
    (continuous_const.mul (continuous_const.sub (continuous_radius.comp continuous_snd)))))).subtype_mk _

omit [Nonempty N] in
lemma outerTime_eq_zero {s : unitInterval} {t : N → unitInterval}
    (h : radius t ≤ 1-(s:ℝ)/2) : outerTime s t = 0 := by
  apply Subtype.ext
  change max 0 ((s:ℝ)-2*(1-radius t)) = 0
  apply max_eq_left
  linarith

omit [Nonempty N] in
lemma outerTime_boundary (s : unitInterval) {t : N → unitInterval}
    (h : t ∈ Cube.boundary N) : outerTime s t = s := by
  apply Subtype.ext
  change max 0 ((s:ℝ)-2*(1-radius t)) = s
  rw [radius_boundary h]
  simp only [sub_self,mul_zero,sub_zero,max_eq_right s.property.1]

def rebaseValue (f : GenLoop N X x) (p : Path x y) (s : unitInterval)
    (t : N → unitInterval) : X :=
  if radius t ≤ 1-(s:ℝ)/2 then f (expand s t) else p (outerTime s t)

lemma continuous_rebaseValue (f : GenLoop N X x) (p : Path x y) :
    Continuous (fun q : unitInterval × (N → unitInterval) => rebaseValue f p q.1 q.2) := by
  apply (f.1.continuous.comp continuous_expand).if_le
    (p.continuous.comp continuous_outerTime) (continuous_radius.comp continuous_snd)
    (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2))
  intro q h
  change f (expand q.1 q.2) = p (outerTime q.1 q.2)
  change radius q.2 = 1-(q.1:ℝ)/2 at h
  rw [GenLoop.boundary f _ (expand_mem_boundary h.ge),outerTime_eq_zero h.le,p.source]

omit [Nonempty N] in
@[simp] lemma rebaseValue_zero (f : GenLoop N X x) (p : Path x y)
    (t : N → unitInterval) : rebaseValue f p 0 t = f t := by
  rw [rebaseValue,ite_eq_left (by simpa using radius_le_one t),expand_zero]

omit [Nonempty N] in
lemma rebaseValue_boundary (f : GenLoop N X x) (p : Path x y)
    (s : unitInterval) {t : N → unitInterval} (ht : t ∈ Cube.boundary N) :
    rebaseValue f p s t = p s := by
  rw [rebaseValue]
  split_ifs with h
  · have hs : s = 0 := by
      apply Subtype.ext
      change (s:ℝ) = 0
      rw [radius_boundary ht] at h
      linarith [s.property.1]
    rw [hs,expand_zero,GenLoop.boundary f t ht,p.source]
  · rw [outerTime_boundary s ht]

def rebase (f : GenLoop N X x) (p : Path x y) : GenLoop N X y :=
  ⟨⟨fun t => rebaseValue f p 1 t,
    (continuous_rebaseValue f p).comp (continuous_const.prodMk continuous_id)⟩,
    fun _t ht => (rebaseValue_boundary f p 1 ht).trans p.target⟩

def rebaseHomotopy (f : GenLoop N X x) (p : Path x y) : f.1.Homotopy (rebase f p).1 where
  toFun q := rebaseValue f p q.1 q.2
  continuous_toFun := continuous_rebaseValue f p
  map_zero_left := rebaseValue_zero f p
  map_one_left _ := rfl

end NearbyLagrangian.CubicalFreeNullity

end

end OAI
