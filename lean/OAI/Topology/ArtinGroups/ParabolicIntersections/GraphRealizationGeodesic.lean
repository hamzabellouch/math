import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphRealizationSpace
import OAI.Topology.ArtinGroups.ParabolicIntersections.MetricUnitCurves
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! Shortest paths in the unit-interval realization of a connected graph. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
variable {V : Type} (H : SimpleGraph V) (hH : H.Connected)

lemma arc_curve (e : H.Dart) (t s : Set.Icc (0 : ℝ) 1) :
    HasCurve (arc H hH e t) (arc H hH e s) |(t : ℝ)-s| := by
  let f : ℝ → Space H hH := fun r => arc H hH e (Set.projIcc 0 1 (by norm_num) r)
  have hf (a b : ℝ) : dist (f a) (f b) ≤ |a-b| := by
    rw [dist_arc]
    simpa only [Subtype.dist_eq,Real.dist_eq,NNReal.coe_one,one_mul] using
      (LipschitzWith.projIcc (by norm_num : (0 : ℝ) ≤ 1)).dist_le_mul a b
  have ht : f t=arc H hH e t := by
    simp only [f,Set.projIcc_val]
  have hs : f s=arc H hH e s := by
    simp only [f,Set.projIcc_val]
  simpa only [ht,hs] using curve_subsegment f hf (t : ℝ) (s : ℝ)

lemma curve_to_anchor (p : Point H) (i : Bool) :
    HasCurve (embed H hH p) (vertex H hH (anchor H p i)) (weight H p i) := by
  cases p with
  | vertex v => exact curve_const _
  | edge e t =>
    cases i
    · have h := arc_curve H hH e t ⟨0,by norm_num⟩
      change HasCurve (arc H hH e t) (vertex H hH e.fst) (t : ℝ)
      simpa only [arc_zero,sub_zero,abs_of_nonneg t.property.1] using h
    · have h := arc_curve H hH e t ⟨1,by norm_num⟩
      change HasCurve (arc H hH e t) (vertex H hH e.snd) (1-(t : ℝ))
      simpa only [arc_one,abs_of_nonpos (sub_nonpos.mpr t.property.2),neg_sub] using h

lemma curve_of_adj {x y : V} (hxy : H.Adj x y) :
    HasCurve (vertex H hH x) (vertex H hH y) 1 := by
  let e : H.Dart := ⟨(x,y),hxy⟩
  have h := arc_curve H hH e ⟨0,by norm_num⟩ ⟨1,by norm_num⟩
  simpa only [arc_zero,arc_one,zero_sub,abs_neg,abs_one] using h

lemma curve_of_walk {x y : V} (p : H.Walk x y) :
    HasCurve (vertex H hH x) (vertex H hH y) (p.length : ℝ) := by
  induction p with
  | @nil x => simpa only [SimpleGraph.Walk.length_nil,Nat.cast_zero] using curve_const (vertex H hH x)
  | @cons x z y hxz p ih =>
    have h := curve_concat (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg p.length)
      (curve_of_adj H hH hxz) ih
    simpa only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one,add_comm] using h

lemma curve_between_vertices (x y : V) :
    HasCurve (vertex H hH x) (vertex H hH y) (H.dist x y : ℝ) := by
  obtain ⟨p,hp⟩ := hH.exists_walk_length_eq_dist x y
  simpa only [hp] using curve_of_walk H hH p

lemma curve_via (p q : Point H) (i j : Bool) :
    HasCurve (embed H hH p) (embed H hH q) (route H p q i j) := by
  have hc := curve_concat (weight_nonneg H p i)
    (Nat.cast_nonneg (H.dist (anchor H p i) (anchor H q j)))
    (curve_to_anchor H hH p i) (curve_between_vertices H hH (anchor H p i) (anchor H q j))
  exact curve_concat (add_nonneg (weight_nonneg H p i) (Nat.cast_nonneg _))
    (weight_nonneg H q j) hc (curve_reverse (curve_to_anchor H hH q j))

theorem curve_between (x y : Space H hH) : HasCurve x y (dist x y) := by
  obtain ⟨p,rfl⟩ := embed_surjective H hH x
  obtain ⟨q,rfl⟩ := embed_surjective H hH y
  rw [dist_embed]
  rcases distance_cases H p q with ⟨e,t,s,rfl,rfl,hd⟩|⟨i,j,hd⟩
  · rw [hd]
    exact arc_curve H hH e t s
  · rw [hd]
    exact curve_via H hH p q i j

theorem realization_geodesic (x y : Space H hH) :
    ∃ γ : Set.Icc (0 : ℝ) (dist x y) → Space H hH, Isometry γ ∧
      γ ⟨0,le_rfl,dist_nonneg⟩=x ∧ γ ⟨dist x y,dist_nonneg,le_rfl⟩=y :=
  curve_realizes_distance (curve_between H hH x y)

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
