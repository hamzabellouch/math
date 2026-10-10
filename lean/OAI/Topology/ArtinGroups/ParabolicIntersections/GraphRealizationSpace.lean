import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphRealizationDistance

namespace OAI

/-! The metric realization of a connected graph by unit intervals. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (H : SimpleGraph V)

lemma distance_vertices (x y : V) : distance H (.vertex x) (.vertex y)=(H.dist x y : ℝ) := by
  simp [distance,via,route,anchor,weight]

lemma distance_edge (e : H.Dart) (t s : Set.Icc (0 : ℝ) 1) :
    distance H (.edge e t) (.edge e s)=|(t : ℝ)-s| := by
  apply le_antisymm (distance_le_direct H e t s)
  rcases distance_cases H (.edge e t) (.edge e s) with ⟨f,a,b,he,he',hd⟩|⟨i,j,hd⟩
  · cases he
    cases he'
    exact hd.ge
  · rw [hd]
    have hdist : H.dist e.fst e.snd=1 := H.dist_eq_one_iff_adj.mpr e.adj
    have hdist' : H.dist e.snd e.fst=1 := H.dist_eq_one_iff_adj.mpr e.adj.symm
    cases i <;> cases j <;>
      simp only [route,anchor,weight,hdist,hdist',SimpleGraph.dist_self,Nat.cast_zero,Nat.cast_one]
    all_goals apply abs_le.mpr; constructor <;> linarith [t.property.1,t.property.2,s.property.1,s.property.2]

lemma weight_le_one (p : Point H) (i : Bool) : weight H p i ≤ 1 := by
  cases p with
  | vertex v => norm_num [weight]
  | edge e t => cases i <;> simp only [weight] <;> linarith [t.property.1,t.property.2]

lemma distance_anchor_le (p : Point H) (i : Bool) :
    distance H p (.vertex (anchor H p i)) ≤ weight H p i := by
  simpa [route,anchor,weight] using distance_le_route H p (.vertex (anchor H p i)) i false

def Space (hH : H.Connected) :=
  @SeparationQuotient (Point H) (premetric H hH).toUniformSpace.toTopologicalSpace

noncomputable instance spaceMetric (hH : H.Connected) : MetricSpace (Space H hH) :=
  @SeparationQuotient.instMetricSpace (Point H) (premetric H hH)

noncomputable def embed (hH : H.Connected) : Point H → Space H hH :=
  @SeparationQuotient.mk (Point H) (premetric H hH).toUniformSpace.toTopologicalSpace

lemma dist_embed (hH : H.Connected) (p q : Point H) :
    dist (embed H hH p) (embed H hH q)=distance H p q := rfl

lemma embed_surjective (hH : H.Connected) : Function.Surjective (embed H hH) :=
  @SeparationQuotient.surjective_mk (Point H) (premetric H hH).toUniformSpace.toTopologicalSpace

noncomputable def vertex (hH : H.Connected) (v : V) : Space H hH := embed H hH (.vertex v)

lemma dist_vertex (hH : H.Connected) (x y : V) :
    dist (vertex H hH x) (vertex H hH y)=(H.dist x y : ℝ) := distance_vertices H x y

lemma vertex_injective (hH : H.Connected) : Function.Injective (vertex H hH) := by
  intro x y he
  have hd : (H.dist x y : ℝ)=0 := by rw [←dist_vertex H hH,he,dist_self]
  exact hH.dist_eq_zero_iff.mp (Nat.cast_eq_zero.mp hd)

lemma exists_near_vertex (hH : H.Connected) (x : Space H hH) :
    ∃ v,dist x (vertex H hH v) ≤ 1 := by
  obtain ⟨p,rfl⟩ := embed_surjective H hH x
  exact ⟨anchor H p false,(distance_anchor_le H p false).trans (weight_le_one H p false)⟩

noncomputable def arc (hH : H.Connected) (e : H.Dart) (t : Set.Icc (0 : ℝ) 1) : Space H hH :=
  embed H hH (.edge e t)

lemma dist_arc (hH : H.Connected) (e : H.Dart) (t s : Set.Icc (0 : ℝ) 1) :
    dist (arc H hH e t) (arc H hH e s)=|(t : ℝ)-s| := distance_edge H e t s

lemma arc_zero (hH : H.Connected) (e : H.Dart) :
    arc H hH e ⟨0,by norm_num⟩=vertex H hH e.fst := by
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  exact distance_anchor_le H (.edge e ⟨0,by norm_num⟩) false

lemma arc_one (hH : H.Connected) (e : H.Dart) :
    arc H hH e ⟨1,by norm_num⟩=vertex H hH e.snd := by
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  change distance H (.edge e ⟨1,by norm_num⟩) (.vertex e.snd) ≤ 0
  simpa only [anchor,weight,sub_self] using distance_anchor_le H (.edge e ⟨1,by norm_num⟩) true

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
