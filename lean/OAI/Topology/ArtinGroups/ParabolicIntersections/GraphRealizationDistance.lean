import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphMetric
import Mathlib.Tactic.Linarith

namespace OAI

/-! The path distance on unit intervals attached to graph edges. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} (H : SimpleGraph V)

/-- Endpoints are retained at this stage and identified by the metric quotient. -/
inductive Point where
  | vertex : V → Point
  | edge : H.Dart → Set.Icc (0 : ℝ) 1 → Point

def anchor : Point H → Bool → V
  | .vertex v, _ => v
  | .edge e _, false => e.fst
  | .edge e _, true => e.snd

def weight : Point H → Bool → ℝ
  | .vertex _, _ => 0
  | .edge _ t, false => t
  | .edge _ t, true => 1-t

noncomputable def route (p q : Point H) (i j : Bool) : ℝ :=
  weight H p i+(H.dist (anchor H p i) (anchor H q j) : ℝ)+weight H q j

noncomputable def via (p q : Point H) : ℝ :=
  min (route H p q false false) (min (route H p q false true)
    (min (route H p q true false) (route H p q true true)))

noncomputable def distance : Point H → Point H → ℝ
  | .edge e t, .edge f s => if e=f then min |(t : ℝ)-s| (via H (.edge e t) (.edge f s))
      else via H (.edge e t) (.edge f s)
  | p,q => via H p q

lemma weight_nonneg (p : Point H) (i : Bool) : 0 ≤ weight H p i := by
  cases p with
  | vertex v => rfl
  | edge e t => cases i <;> simp only [weight] <;> linarith [t.property.1,t.property.2]

lemma route_nonneg (p q : Point H) (i j : Bool) : 0 ≤ route H p q i j := by
  exact add_nonneg (add_nonneg (weight_nonneg H p i) (Nat.cast_nonneg _)) (weight_nonneg H q j)

lemma via_le_route (p q : Point H) (i j : Bool) : via H p q ≤ route H p q i j := by
  cases i <;> cases j <;> simp only [via] <;> order

lemma via_eq_route (p q : Point H) : ∃ i j, via H p q=route H p q i j := by
  rcases min_choice (route H p q false false)
    (min (route H p q false true) (min (route H p q true false) (route H p q true true))) with h|h
  · exact ⟨false,false,h⟩
  · rcases min_choice (route H p q false true)
      (min (route H p q true false) (route H p q true true)) with h'|h'
    · exact ⟨false,true,h.trans h'⟩
    · rcases min_choice (route H p q true false) (route H p q true true) with h''|h''
      · exact ⟨true,false,h.trans (h'.trans h'')⟩
      · exact ⟨true,true,h.trans (h'.trans h'')⟩

lemma distance_le_via (p q : Point H) : distance H p q ≤ via H p q := by
  cases p <;> cases q <;> simp only [distance]
  all_goals first | exact le_rfl | (split_ifs <;> order)

lemma distance_le_route (p q : Point H) (i j : Bool) : distance H p q ≤ route H p q i j :=
  (distance_le_via H p q).trans (via_le_route H p q i j)

lemma distance_le_direct (e : H.Dart) (t s : Set.Icc (0 : ℝ) 1) :
    distance H (.edge e t) (.edge e s) ≤ |(t : ℝ)-s| := by
  simp [distance]

lemma distance_cases (p q : Point H) :
    (∃ e t s,p=.edge e t ∧ q=.edge e s ∧ distance H p q=|(t : ℝ)-s|) ∨
      ∃ i j,distance H p q=route H p q i j := by
  cases p with
  | vertex x => exact Or.inr (via_eq_route H _ _)
  | edge e t =>
    cases q with
    | vertex y => exact Or.inr (via_eq_route H _ _)
    | edge f s =>
      by_cases he : e=f
      · subst f
        rcases min_choice |(t : ℝ)-s| (via H (.edge e t) (.edge e s)) with h|h
        · exact Or.inl ⟨e,t,s,rfl,rfl,by simpa [distance] using h⟩
        · obtain ⟨i,j,hv⟩ := via_eq_route H (.edge e t) (.edge e s)
          exact Or.inr ⟨i,j,by simpa [distance] using h.trans hv⟩
      · simpa only [distance,ite_eq_right he] using Or.inr (via_eq_route H (.edge e t) (.edge f s))

lemma distance_nonneg (p q : Point H) : 0 ≤ distance H p q := by
  rcases distance_cases H p q with ⟨e,t,s,rfl,rfl,hd⟩|⟨i,j,hd⟩
  · rw [hd]; exact abs_nonneg _
  · rw [hd]; exact route_nonneg H p q i j

lemma route_comm (p q : Point H) (i j : Bool) : route H p q i j=route H q p j i := by
  unfold route
  rw [H.dist_comm]
  ring

lemma distance_comm (p q : Point H) : distance H p q=distance H q p := by
  have h (p q : Point H) : distance H p q ≤ distance H q p := by
    rcases distance_cases H q p with ⟨e,t,s,rfl,rfl,hd⟩|⟨i,j,hd⟩
    · rw [hd,abs_sub_comm]
      exact distance_le_direct H e s t
    · rw [hd,route_comm]
      exact distance_le_route H p q j i
  exact le_antisymm (h p q) (h q p)

lemma distance_self (p : Point H) : distance H p p=0 := by
  apply le_antisymm _ (distance_nonneg H p p)
  cases p with
  | vertex v => simpa [route,anchor,weight] using distance_le_route H (.vertex v) (.vertex v) false false
  | edge e t => simpa using distance_le_direct H e t t

lemma anchor_bridge (p : Point H) (i j : Bool) :
    (H.dist (anchor H p i) (anchor H p j) : ℝ) ≤ weight H p i+weight H p j := by
  cases p with
  | vertex v => simp [anchor,weight]
  | edge e t =>
    have hd : H.dist e.fst e.snd=1 := H.dist_eq_one_iff_adj.mpr e.adj
    have hd' : H.dist e.snd e.fst=1 := H.dist_eq_one_iff_adj.mpr e.adj.symm
    cases i <;> cases j <;> simp only [anchor,weight,hd,hd',SimpleGraph.dist_self,Nat.cast_zero,Nat.cast_one]
    all_goals linarith [t.property.1,t.property.2]

lemma edge_weight_le (e : H.Dart) (t s : Set.Icc (0 : ℝ) 1) (i : Bool) :
    weight H (.edge e t) i ≤ weight H (.edge e s) i+|(t : ℝ)-s| := by
  cases i <;> simp only [weight]
  · linarith [le_abs_self ((t : ℝ)-s)]
  · linarith [neg_le_abs ((t : ℝ)-s)]

lemma route_triangle (hH : H.Connected) (p q r : Point H) (i j k l : Bool) :
    route H p r i l ≤ route H p q i j+route H q r k l := by
  have h₁ := hH.dist_triangle (u := anchor H p i) (v := anchor H q j) (w := anchor H r l)
  have h₂ := hH.dist_triangle (u := anchor H q j) (v := anchor H q k) (w := anchor H r l)
  have h₁' : (H.dist (anchor H p i) (anchor H r l) : ℝ) ≤
      H.dist (anchor H p i) (anchor H q j)+H.dist (anchor H q j) (anchor H r l) := by exact_mod_cast h₁
  have h₂' : (H.dist (anchor H q j) (anchor H r l) : ℝ) ≤
      H.dist (anchor H q j) (anchor H q k)+H.dist (anchor H q k) (anchor H r l) := by exact_mod_cast h₂
  have hb := anchor_bridge H q j k
  unfold route
  linarith

theorem distance_triangle (hH : H.Connected) (p q r : Point H) :
    distance H p r ≤ distance H p q+distance H q r := by
  rcases distance_cases H p q with ⟨e,t,s,hp,hq,hd⟩|⟨i,j,hd⟩
  · subst p; subst q
    rcases distance_cases H (.edge e s) r with ⟨f,a,b,he,hr,hd'⟩|⟨i,j,hd'⟩
    · cases he
      subst r
      have ht := abs_sub_le (t : ℝ) s b
      exact (distance_le_direct H e t b).trans (by rw [hd,hd']; exact ht)
    · have hle := distance_le_route H (.edge e t) r i j
      have hw := edge_weight_le H e t s i
      rw [hd,hd']
      refine hle.trans ?_
      unfold route
      have ha : anchor H (.edge e t) i=anchor H (.edge e s) i := by cases i <;> rfl
      rw [ha]
      linarith
  · rcases distance_cases H q r with ⟨e,t,s,hq,hr,hd'⟩|⟨k,l,hd'⟩
    · subst q; subst r
      have hle := distance_le_route H p (.edge e s) i j
      have hw := edge_weight_le H e s t j
      rw [hd,hd']
      refine hle.trans ?_
      unfold route
      have ha : anchor H (.edge e s) j=anchor H (.edge e t) j := by cases j <;> rfl
      rw [ha]
      rw [abs_sub_comm (s : ℝ) t] at hw
      linarith
    · rw [hd,hd']
      exact (distance_le_route H p r i l).trans (route_triangle H hH p q r i j k l)

@[instance_reducible]
noncomputable def premetric (hH : H.Connected) : PseudoMetricSpace (Point H) where
  dist := distance H
  dist_self := distance_self H
  dist_comm := distance_comm H
  dist_triangle := distance_triangle H hH

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
