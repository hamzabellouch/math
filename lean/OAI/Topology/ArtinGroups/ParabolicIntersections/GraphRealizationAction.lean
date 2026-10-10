import OAI.Topology.ArtinGroups.ParabolicIntersections.GraphRealizationSpace
import OAI.Topology.ArtinGroups.ParabolicIntersections.TreeActionDefinitions

namespace OAI

/-! An action on a graph extends isometrically to its unit-interval realization. -/
namespace HarmonicArtin.ParabolicIntersections.GraphRealization
open TreeAction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G V : Type} [Group G] [MulAction G V]
variable (H : SimpleGraph V) (hA : PreservesAdj (G := G) H)

def actDart (g : G) (e : H.Dart) : H.Dart := ⟨(g • e.fst,g • e.snd),hA g e.adj⟩

lemma actDart_injective (g : G) : Function.Injective (actDart H hA g) := by
  intro e f he
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · exact (MulAction.toPerm g).injective (congrArg (fun d : H.Dart => d.fst) he)
  · exact (MulAction.toPerm g).injective (congrArg (fun d : H.Dart => d.snd) he)

def actPoint (g : G) : Point H → Point H
  | .vertex v => .vertex (g • v)
  | .edge e t => .edge (actDart H hA g e) t

lemma actPoint_one (p : Point H) : actPoint H hA 1 p=p := by
  cases p with
  | vertex v => simp [actPoint]
  | edge e t =>
    change Point.edge (actDart H hA 1 e) t=Point.edge e t
    apply congrArg (fun d : H.Dart => Point.edge d t)
    apply SimpleGraph.Dart.ext
    simp [actDart,one_smul]

lemma actPoint_mul (g h : G) (p : Point H) :
    actPoint H hA (g*h) p=actPoint H hA g (actPoint H hA h p) := by
  cases p with
  | vertex v => simp [actPoint,mul_smul]
  | edge e t =>
    change Point.edge (actDart H hA (g*h) e) t=
      Point.edge (actDart H hA g (actDart H hA h e)) t
    apply congrArg (fun d : H.Dart => Point.edge d t)
    apply SimpleGraph.Dart.ext
    simp [actDart,mul_smul]

lemma anchor_act (g : G) (p : Point H) (i : Bool) :
    anchor H (actPoint H hA g p) i=g • anchor H p i := by
  cases p <;> cases i <;> rfl

lemma weight_act (g : G) (p : Point H) (i : Bool) :
    weight H (actPoint H hA g p) i=weight H p i := by
  cases p <;> cases i <;> rfl

lemma route_act (hH : H.Connected) (g : G) (p q : Point H) (i j : Bool) :
    route H (actPoint H hA g p) (actPoint H hA g q) i j=route H p q i j := by
  simp only [route,anchor_act,weight_act,graph_action_dist H hH hA]

lemma distance_act (hH : H.Connected) (g : G) (p q : Point H) :
    distance H (actPoint H hA g p) (actPoint H hA g q)=distance H p q := by
  have hv (p q : Point H) : via H (actPoint H hA g p) (actPoint H hA g q)=via H p q := by
    simp only [via,route_act H hA hH]
  cases p with
  | vertex x => cases q <;> exact hv _ _
  | edge e t =>
    cases q with
    | vertex y =>
      change via H (actPoint H hA g (.edge e t)) (actPoint H hA g (.vertex y))=via H (.edge e t) (.vertex y)
      exact hv _ _
    | edge f s =>
      have he : actDart H hA g e=actDart H hA g f ↔ e=f := (actDart_injective H hA g).eq_iff
      simp only [actPoint,distance,he]
      rw [←actPoint,←actPoint,hv]

noncomputable def act (hH : H.Connected) (g : G) : Space H hH → Space H hH := by
  let _ := premetric H hH
  exact SeparationQuotient.map (actPoint H hA g)

lemma act_embed (hH : H.Connected) (g : G) (p : Point H) :
    act H hA hH g (embed H hH p)=embed H hH (actPoint H hA g p) := by
  let _ := premetric H hH
  have hi : Isometry (actPoint H hA g) := by
    apply isometry_iff_dist_eq.mpr
    exact distance_act H hA hH g
  exact SeparationQuotient.map_mk hi.uniformContinuous p

@[instance_reducible]
noncomputable def action (hH : H.Connected) : MulAction G (Space H hH) where
  smul := act H hA hH
  one_smul x := by
    obtain ⟨p,rfl⟩ := embed_surjective H hH x
    change act H hA hH 1 (embed H hH p)=embed H hH p
    rw [act_embed,actPoint_one]
  mul_smul g h x := by
    obtain ⟨p,rfl⟩ := embed_surjective H hH x
    change act H hA hH (g*h) (embed H hH p)=act H hA hH g (act H hA hH h (embed H hH p))
    rw [act_embed,act_embed,act_embed,actPoint_mul]

lemma action_isometric (hH : H.Connected) (g : G) :
    let _ := action H hA hH
    Isometry (fun x : Space H hH => g • x) := by
  let _ := action H hA hH
  apply isometry_iff_dist_eq.mpr
  intro x y
  obtain ⟨p,rfl⟩ := embed_surjective H hH x
  obtain ⟨q,rfl⟩ := embed_surjective H hH y
  change dist (act H hA hH g (embed H hH p)) (act H hA hH g (embed H hH q))= _
  rw [act_embed,act_embed,dist_embed,dist_embed,distance_act H hA hH g]

lemma act_vertex (hH : H.Connected) (g : G) (v : V) :
    act H hA hH g (vertex H hH v)=vertex H hH (g • v) := act_embed H hA hH g (.vertex v)

end HarmonicArtin.ParabolicIntersections.GraphRealization

end OAI
