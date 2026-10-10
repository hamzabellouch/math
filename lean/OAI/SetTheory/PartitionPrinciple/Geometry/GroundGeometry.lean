import OAI.SetTheory.PartitionPrinciple.Forcing.InitialRowForcing
import OAI.SetTheory.PartitionPrinciple.Transfinite.FinalInsertionStages

namespace OAI

namespace PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

open CountableColumns
variable (Label : Type 1)

theorem final_insertion_data (C E D : FinalPoint Label) (F : MeetFilter (finalOrder Label)) :
    ∃ (a : Column) (c e d : (stage Label a).Point) (H : MeetFilter (stage Label a).order),
      (finalInclusion Label a).toFun c = C ∧ (finalInclusion Label a).toFun e = E ∧
      (finalInclusion Label a).toFun d = D ∧ pushFilter (finalInclusion Label a) H = F := by
  rcases final_filters_localized Label F with ⟨a, localized⟩
  rcases (diagram Label).orders.system.triple_cover (diagram Label).orders.system
    (diagram Label).orders.system C E D with ⟨b, c, e, d, hc, he, hd⟩
  let inc := finalInclusion Label (max a b)
  have localize : ∀ x, F.mem x → ∃ y, F.mem (inc.toFun y) ∧ (finalOrder Label).le (inc.toFun y) x := by
    intro x hx
    rcases localized x hx with ⟨y, hy, lower⟩
    refine ⟨(transition Label (le_max_left a b)).points.toFun y, ?_, ?_⟩
    · change F.mem ((finalInclusion Label (max a b)).toFun _)
      rw [final_points_coherent]
      exact hy
    · change (finalOrder Label).le ((finalInclusion Label (max a b)).toFun _) x
      rw [final_points_coherent]
      exact lower
  let H : MeetFilter (stage Label (max a b)).order := {
    mem := fun y => F.mem (inc.toFun y)
    nonempty := by
      rcases F.nonempty with ⟨x, hx⟩
      rcases localize x hx with ⟨y, hy, _⟩
      exact ⟨y, hy⟩
    upward := fun hx lower => F.upward hx ((inc.le_iff _ _).mpr lower)
    closed_meet := by
      intro x y hx hy
      rw [inc.map_meet]
      exact F.closed_meet hx hy }
  refine ⟨max a b, (transition Label (le_max_right a b)).points.toFun c,
    (transition Label (le_max_right a b)).points.toFun e,
    (transition Label (le_max_right a b)).points.toFun d, H,
    (final_points_coherent Label (le_max_right a b) c).trans hc,
    (final_points_coherent Label (le_max_right a b) e).trans he,
    (final_points_coherent Label (le_max_right a b) d).trans hd, ?_⟩
  apply meetFilter_ext
  intro x
  constructor
  · rintro ⟨y, hy, lower⟩
    exact F.upward hy lower
  · intro hx
    exact localize x hx

theorem final_insertion (C E D : FinalPoint Label) (F : MeetFilter (finalOrder Label))
    (ce : (finalOrder Label).le C E) (strict : ¬ (finalOrder Label).le E C)
    (above : ∀ x, F.mem x → (finalOrder Label).le E x) :
    HasInsertionFamily (finalAction Label) Label C E D F.mem := by
  rcases final_insertion_data Label C E D F with ⟨a, c, e, d, H, hc, he, hd, hF⟩
  have ce' : (stage Label a).order.le c e := by
    apply ((finalInclusion Label a).le_iff _ _).mp
    rw [hc, he]
    exact ce
  have strict' : ¬ (stage Label a).order.le e c := by
    intro lower
    apply strict
    rw [← he, ← hc]
    exact ((finalInclusion Label a).le_iff _ _).mpr lower
  have above' : ∀ x, H.mem x → (stage Label a).order.le e x := by
    intro x hx
    apply ((finalInclusion Label a).le_iff _ _).mp
    rw [he]
    apply above
    rw [← hF]
    exact ⟨x, hx, (finalOrder Label).refl _⟩
  have result := final_inserts_at Label a c e d H ce' strict' above'
  rw [hc, he, hd, hF] at result
  exact result

theorem countableOrdinalLabels_final_insertion (C E D : FinalPoint Column)
    (F : MeetFilter (finalOrder Column))
    (ce : (finalOrder Column).le C E) (strict : ¬ (finalOrder Column).le E C)
    (above : ∀ x, F.mem x → (finalOrder Column).le E x) :
    HasInsertionFamily (finalAction Column) Column C E D F.mem :=
  final_insertion Column C E D F ce strict above

theorem final_insertion_distinct_caps (C E D : FinalPoint Label)
    (F : MeetFilter (finalOrder Label))
    (ce : (finalOrder Label).le C E) (strict : ¬ (finalOrder Label).le E C)
    (above : ∀ x, F.mem x → (finalOrder Label).le E x) :
    ∃ caps : Label → FinalPoint Label, Function.Injective caps ∧
      ∀ l, (finalOrder Label).le C (caps l) ∧ ¬ (finalOrder Label).le (caps l) C := by
  classical
  rcases final_insertion Label C E D F ce strict above with
    ⟨caps, _, _, _, strictCaps, _, pairs, _⟩
  refine ⟨caps, ?_, strictCaps⟩
  intro i j eq
  by_cases same : i = j
  · exact same
  · have meet := pairs i j same
    rw [eq, meet_eq_left_of_le (finalOrder Label) ((finalOrder Label).refl (caps j))] at meet
    exact False.elim ((strictCaps j).2 (meet ▸ (finalOrder Label).refl (caps j)))

end PartitionPilot.Compression.RecursiveMaps.MainStage.OrdinalRun

namespace PartitionPilot.Compression.RecursiveMaps

open Cardinal CosetGeometry Chronological
open scoped Cardinal

structure GroundGeometryLaws {A G : Type 1} [Group G] (P : MeetOrder A)
    (a : OrderAction G P) (κ : Cardinal.{1}) : Prop where
  nodes_small : #A < κ
  actors_small : #G < κ
  bottom : ∃ b, ∀ x, P.le b x
  countable_upper : ∀ B : Set A, B.Countable → ∃ top, ∀ x ∈ B, P.le x top
  strict_extension : ∀ x, ∃ y, P.le x y ∧ ¬ P.le y x
  filter_basis : AllFiltersCountable P
  separation : ∀ W D X, P.le W D → P.le W X →
    ∃ g, (∀ z, P.le z W → (a.iso g).toFun z = z) ∧ P.meet ((a.iso g).toFun D) X = W
  rectangles : ∀ (r : ActionRectangle P a.iso) X,
    P.le ((a.iso r.first).toFun r.D) X → P.le ((a.iso r.second).toFun r.D) X →
    ∃ h1 h2,
      (∀ z, P.le z r.C → (a.iso h1).toFun z = (a.iso r.first).toFun z) ∧
      (∀ z, P.le z r.C → (a.iso h2).toFun z = (a.iso r.second).toFun z) ∧
      (∀ z, P.le z r.B → (a.iso h1).toFun z = (a.iso h2).toFun z) ∧
      P.meet ((a.iso h1).toFun r.D) X = (a.iso r.first).toFun r.C ∧
      P.meet ((a.iso h2).toFun r.D) X = (a.iso r.second).toFun r.C ∧
      P.meet ((a.iso h1).toFun r.D) ((a.iso h2).toFun r.D) = (a.iso h1).toFun r.B
  insertion : ∀ C E D (F : MeetFilter P), P.le C E → ¬ P.le E C →
    (∀ x, F.mem x → P.le E x) → HasInsertionFamily a CountableColumns.Column C E D F.mem

namespace MainStage.OrdinalRun
open CountableColumns

theorem countableOrdinalLabels_ground_geometry (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) :
    GroundGeometryLaws (finalOrder Column) (finalAction Column) κ where
  nodes_small := (countableOrdinalLabels_final_cardinal_bounds κ inaccessible).1
  actors_small := (countableOrdinalLabels_final_cardinal_bounds κ inaccessible).2
  bottom := ⟨finalBottom Column, finalBottom_least Column⟩
  countable_upper := final_countable_upper_bound Column
  strict_extension := final_no_maximal Column
  filter_basis := final_all_filters_countable Column
  separation := final_separation Column
  rectangles := final_rectangles Column
  insertion := countableOrdinalLabels_final_insertion

end MainStage.OrdinalRun

end PartitionPilot.Compression.RecursiveMaps

end OAI
