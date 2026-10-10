import OAI.SetTheory.PartitionPrinciple.Transfinite.FinalStageBounds

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps.MainStage

section

open CosetGeometry
universe u

namespace Transition
variable {s t : MainStage.{u}}

def Separates (f : Transition s t) (W D X : s.Point) : Prop :=
  ∃ g : t.Actor,
    (∀ z, t.order.le z (f.points.toFun W) → (t.action.iso g).toFun z = z) ∧
    t.order.meet ((t.action.iso g).toFun (f.points.toFun D)) (f.points.toFun X) = f.points.toFun W

theorem separates_transport {t' : MainStage.{u}} (f : Transition s t) (eq : t = t')
    (W D X : s.Point) : (f.transport rfl eq).Separates W D X ↔ f.Separates W D X := by
  cases eq
  rfl

end Transition

variable (s : MainStage.{u}) (Label : Type u)

noncomputable def separationActor (W : s.Point) : (s.next Label).Actor :=
  generator s.Actor (s.requests Label).Letters ⟨.separation W, ⟨()⟩⟩

theorem separation_internal (W : s.Point) (x : (s.internal Label).Point)
    (lower : (s.internal Label).order.le x ((s.internalTransition Label).points.toFun W)) :
    ((s.next Label).action.iso (s.separationActor Label W)).toFun
      ((s.externalTransition Label).points.toFun x) = (s.externalTransition Label).points.toFun x := by
  change (((s.requests Label).extensionAction (s.internal Label).action).iso
    (s.separationActor Label W)).toFun
    (((s.requests Label).extensionCopy (s.internal Label).action 1).toFun x) = _
  erw [(s.requests Label).extensionAction_copy, mul_one]
  apply congrArg some
  have eq := (s.requests Label).transfer_child_root (s.internal Label).action 1
    (.separation W) ⟨()⟩ x x
    (TileRequests.Request.separation_agrees (s.internal Label).top (s.internal Label).greatest
      ((s.internalTransition Label).points.toFun W) x lower)
  simp only [one_mul] at eq
  exact eq

theorem separation_fixes_ideal (W : s.Point) (z : (s.next Label).Point)
    (lower : (s.next Label).order.le z ((s.nextTransition Label).points.toFun W)) :
    ((s.next Label).action.iso (s.separationActor Label W)).toFun z = z := by
  let e := (s.requests Label).extensionCopy (s.internal Label).action 1
  rcases e.ideal ((s.internalTransition Label).points.toFun W) z lower with ⟨x, rfl⟩
  exact s.separation_internal Label W x ((e.le_iff _ _).mp lower)

theorem separation_meet (W D X : s.Point) (wd : s.order.le W D) (wx : s.order.le W X) :
    (s.next Label).order.meet
      (((s.next Label).action.iso (s.separationActor Label W)).toFun
        ((s.nextTransition Label).points.toFun D))
      ((s.nextTransition Label).points.toFun X) = (s.nextTransition Label).points.toFun W := by
  change ((s.requests Label).extensionOrder (s.internal Label).action).meet
    ((((s.requests Label).extensionAction (s.internal Label).action).iso
      (s.separationActor Label W)).toFun
      (((s.requests Label).extensionCopy (s.internal Label).action 1).toFun
        ((s.internalTransition Label).points.toFun D))) _ = _
  erw [(s.requests Label).extensionAction_copy, mul_one]
  apply congrArg some
  have eq := (s.requests Label).transfer_child_root_meet (s.internal Label).action 1
    (.separation W) ⟨()⟩ ((s.internalTransition Label).points.toFun D)
    ((s.internalTransition Label).points.toFun X) ((s.internalTransition Label).points.toFun W)
    (BinaryTiles.separation_cross_meet (s.internal Label).order
      ((s.internalTransition Label).points.toFun W) ((s.internalTransition Label).points.toFun D)
      ((s.internalTransition Label).points.toFun X)
      (((s.internalTransition Label).points.le_iff _ _).mpr wd)
      (((s.internalTransition Label).points.le_iff _ _).mpr wx))
  simp only [one_mul] at eq
  exact eq

theorem next_separates (W D X : s.Point) (wd : s.order.le W D) (wx : s.order.le W X) :
    (s.nextTransition Label).Separates W D X :=
  ⟨s.separationActor Label W, s.separation_fixes_ideal Label W, s.separation_meet Label W D X wd wx⟩

end



section

open CosetGeometry
universe u
variable (s : MainStage.{u}) (Label : Type u) (r : ActionRectangle s.order s.action.iso)

def rectangleOldActor (j : Bool) : s.Actor := if j then r.second else r.first

noncomputable def rectangleActor (j : Bool) : (s.next Label).Actor :=
  generator s.Actor (s.requests Label).Letters ⟨.rectangle r, ⟨j⟩⟩

noncomputable def rectangleInput : Rectangle.Input (s.internal Label).order :=
  (((s.tasks Label).compressionAlgebra.liftRectangle r).toInput
    (s.internal Label).top (s.internal Label).greatest)

theorem rectangle_internal_C (j : Bool) (x : (s.internal Label).Point)
    (lower : (s.internal Label).order.le x ((s.internalTransition Label).points.toFun r.C)) :
    ((s.next Label).action.iso (s.rectangleActor Label r j)).toFun
      ((s.externalTransition Label).points.toFun x) =
      (s.externalTransition Label).points.toFun
        (((s.internal Label).action.iso (s.rectangleOldActor r j)).toFun x) := by
  change (((s.requests Label).extensionAction (s.internal Label).action).iso
    (s.rectangleActor Label r j)).toFun
    (((s.requests Label).extensionCopy (s.internal Label).action 1).toFun x) = _
  erw [(s.requests Label).extensionAction_copy, mul_one]
  apply congrArg some
  cases j with
  | false =>
    have eq := (s.requests Label).transfer_child_root (s.internal Label).action 1
      (.rectangle r) ⟨false⟩ x (((s.rectangleInput Label r).g1).toFun x)
      ((s.rectangleInput Label r).first_agrees x lower)
    simp only [one_mul] at eq
    exact eq
  | true =>
    have eq := (s.requests Label).transfer_child_root (s.internal Label).action 1
      (.rectangle r) ⟨true⟩ x (((s.rectangleInput Label r).g2).toFun x)
      ((s.rectangleInput Label r).second_agrees x lower)
    simp only [one_mul] at eq
    exact eq

theorem rectangle_internal_B (x : (s.internal Label).Point)
    (lower : (s.internal Label).order.le x ((s.internalTransition Label).points.toFun r.B)) :
    ((s.next Label).action.iso (s.rectangleActor Label r false)).toFun
      ((s.externalTransition Label).points.toFun x) =
    ((s.next Label).action.iso (s.rectangleActor Label r true)).toFun
      ((s.externalTransition Label).points.toFun x) := by
  change (((s.requests Label).extensionAction (s.internal Label).action).iso
    (s.rectangleActor Label r false)).toFun
    (((s.requests Label).extensionCopy (s.internal Label).action 1).toFun x) =
    (((s.requests Label).extensionAction (s.internal Label).action).iso
    (s.rectangleActor Label r true)).toFun
    (((s.requests Label).extensionCopy (s.internal Label).action 1).toFun x)
  erw [(s.requests Label).extensionAction_copy, (s.requests Label).extensionAction_copy,
    mul_one, mul_one]
  apply congrArg some
  have eq := congrArg ((s.requests Label).placedTile (s.internal Label).action 1 (.rectangle r)).toFun
    (((s.rectangleInput Label r).children_intersection x x).mpr ⟨lower, rfl⟩)
  change ((s.requests Label).placedTile (s.internal Label).action 1 (.rectangle r)).toFun
    ((((s.requests Label).tile (.rectangle r)).child ⟨false⟩).toFun x) =
    ((s.requests Label).placedTile (s.internal Label).action 1 (.rectangle r)).toFun
    ((((s.requests Label).tile (.rectangle r)).child ⟨true⟩).toFun x) at eq
  erw [(s.requests Label).child_identification, (s.requests Label).child_identification] at eq
  simp only [one_mul] at eq
  exact eq

theorem rectangle_agrees_C (j : Bool) (z : (s.next Label).Point)
    (lower : (s.next Label).order.le z ((s.nextTransition Label).points.toFun r.C)) :
    ((s.next Label).action.iso (s.rectangleActor Label r j)).toFun z =
      ((s.next Label).action.iso ((s.nextTransition Label).actors (s.rectangleOldActor r j))).toFun z := by
  let e := (s.requests Label).extensionCopy (s.internal Label).action 1
  rcases e.ideal ((s.internalTransition Label).points.toFun r.C) z lower with ⟨x, rfl⟩
  exact (s.rectangle_internal_C Label r j x ((e.le_iff _ _).mp lower)).trans
    ((s.requests Label).extension_extends_old (s.internal Label).action (s.rectangleOldActor r j) x).symm

theorem rectangle_agrees_B (z : (s.next Label).Point)
    (lower : (s.next Label).order.le z ((s.nextTransition Label).points.toFun r.B)) :
    ((s.next Label).action.iso (s.rectangleActor Label r false)).toFun z =
      ((s.next Label).action.iso (s.rectangleActor Label r true)).toFun z := by
  let e := (s.requests Label).extensionCopy (s.internal Label).action 1
  rcases e.ideal ((s.internalTransition Label).points.toFun r.B) z lower with ⟨x, rfl⟩
  exact s.rectangle_internal_B Label r x ((e.le_iff _ _).mp lower)

end



section

universe u
variable (s : MainStage.{u}) (Label : Type u) (r : ActionRectangle s.order s.action.iso)

theorem rectangle_meet_internal (j : Bool) (x : (s.internal Label).Point) :
    (s.next Label).order.meet
      (((s.next Label).action.iso (s.rectangleActor Label r j)).toFun
        ((s.nextTransition Label).points.toFun r.D))
      ((s.externalTransition Label).points.toFun x) =
      (s.externalTransition Label).points.toFun ((s.internal Label).order.meet
        (((s.internal Label).action.iso (s.rectangleOldActor r j)).toFun
          ((s.internalTransition Label).points.toFun r.C)) x) := by
  change ((s.requests Label).extensionOrder (s.internal Label).action).meet
    ((((s.requests Label).extensionAction (s.internal Label).action).iso
      (s.rectangleActor Label r j)).toFun
      (((s.requests Label).extensionCopy (s.internal Label).action 1).toFun
        ((s.internalTransition Label).points.toFun r.D))) _ = _
  erw [(s.requests Label).extensionAction_copy, mul_one]
  apply congrArg some
  cases j with
  | false =>
    have eq := (s.requests Label).transfer_child_root_meet (s.internal Label).action 1
      (.rectangle r) ⟨false⟩ (s.rectangleInput Label r).D x _
      ((s.rectangleInput Label r).first_meet_root x)
    simp only [one_mul] at eq
    exact eq
  | true =>
    have eq := (s.requests Label).transfer_child_root_meet (s.internal Label).action 1
      (.rectangle r) ⟨true⟩ (s.rectangleInput Label r).D x _
      ((s.rectangleInput Label r).second_meet_root x)
    simp only [one_mul] at eq
    exact eq

theorem rectangle_meet_root (j : Bool) (X : s.Point) :
    (s.next Label).order.meet
      (((s.next Label).action.iso (s.rectangleActor Label r j)).toFun
        ((s.nextTransition Label).points.toFun r.D))
      ((s.nextTransition Label).points.toFun X) =
      (s.nextTransition Label).points.toFun
        (s.order.meet (((s.action.iso (s.rectangleOldActor r j))).toFun r.C) X) := by
  have eq := s.rectangle_meet_internal Label r j ((s.internalTransition Label).points.toFun X)
  have localMeet : (s.internal Label).order.meet
      (((s.internal Label).action.iso (s.rectangleOldActor r j)).toFun
        ((s.internalTransition Label).points.toFun r.C))
      ((s.internalTransition Label).points.toFun X) =
      (s.internalTransition Label).points.toFun
        (s.order.meet ((s.action.iso (s.rectangleOldActor r j)).toFun r.C) X) :=
    (congrArg (fun z => (s.internal Label).order.meet z ((s.internalTransition Label).points.toFun X))
      ((s.internalTransition Label).equivariant (s.rectangleOldActor r j) r.C)).trans
      ((s.internalTransition Label).points.map_meet _ _).symm
  exact eq.trans (congrArg (s.externalTransition Label).points.toFun localMeet)

theorem rectangle_meet_pair :
    (s.next Label).order.meet
      (((s.next Label).action.iso (s.rectangleActor Label r false)).toFun
        ((s.nextTransition Label).points.toFun r.D))
      (((s.next Label).action.iso (s.rectangleActor Label r true)).toFun
        ((s.nextTransition Label).points.toFun r.D)) =
      ((s.next Label).action.iso (s.rectangleActor Label r false)).toFun
        ((s.nextTransition Label).points.toFun r.B) := by
  change ((s.requests Label).extensionOrder (s.internal Label).action).meet
    ((((s.requests Label).extensionAction (s.internal Label).action).iso
      (s.rectangleActor Label r false)).toFun
      (((s.requests Label).extensionCopy (s.internal Label).action 1).toFun
        ((s.internalTransition Label).points.toFun r.D)))
    ((((s.requests Label).extensionAction (s.internal Label).action).iso
      (s.rectangleActor Label r true)).toFun
      (((s.requests Label).extensionCopy (s.internal Label).action 1).toFun
        ((s.internalTransition Label).points.toFun r.D))) =
    ((((s.requests Label).extensionAction (s.internal Label).action).iso
      (s.rectangleActor Label r false)).toFun
      (((s.requests Label).extensionCopy (s.internal Label).action 1).toFun
        ((s.internalTransition Label).points.toFun r.B)))
  erw [(s.requests Label).extensionAction_copy, (s.requests Label).extensionAction_copy,
    (s.requests Label).extensionAction_copy, mul_one, mul_one]
  apply congrArg some
  have eq := (s.requests Label).transfer_child_child_meet (s.internal Label).action 1
    (.rectangle r) ⟨false⟩ ⟨true⟩ (s.rectangleInput Label r).D (s.rectangleInput Label r).D
    (s.rectangleInput Label r).B (s.rectangleInput Label r).children_meet
  simp only [one_mul] at eq
  exact eq

namespace Transition
variable {s t : MainStage.{u}}

def Rectangles (f : Transition s t) (r : ActionRectangle s.order s.action.iso) (X : s.Point) : Prop :=
  ∃ h : Bool → t.Actor,
    (∀ j z, t.order.le z (f.points.toFun r.C) →
      (t.action.iso (h j)).toFun z = (t.action.iso (f.actors (s.rectangleOldActor r j))).toFun z) ∧
    (∀ z, t.order.le z (f.points.toFun r.B) →
      (t.action.iso (h false)).toFun z = (t.action.iso (h true)).toFun z) ∧
    (∀ j, t.order.meet ((t.action.iso (h j)).toFun (f.points.toFun r.D)) (f.points.toFun X) =
      f.points.toFun (s.order.meet ((s.action.iso (s.rectangleOldActor r j)).toFun r.C) X)) ∧
    t.order.meet ((t.action.iso (h false)).toFun (f.points.toFun r.D))
      ((t.action.iso (h true)).toFun (f.points.toFun r.D)) =
      (t.action.iso (h false)).toFun (f.points.toFun r.B)

theorem rectangles_transport {t' : MainStage.{u}} (f : Transition s t) (eq : t = t')
    (r : ActionRectangle s.order s.action.iso) (X : s.Point) :
    (f.transport rfl eq).Rectangles r X ↔ f.Rectangles r X := by cases eq; rfl

end Transition

theorem next_rectangles (X : s.Point) : (s.nextTransition Label).Rectangles r X :=
  ⟨s.rectangleActor Label r, s.rectangle_agrees_C Label r, s.rectangle_agrees_B Label r,
    fun j => s.rectangle_meet_root Label r j X, s.rectangle_meet_pair Label r⟩

end



namespace OrdinalRun

open CountableColumns
variable (Label : Type 1)

theorem stage_successor_separates (a : Column) (W D X : (stage Label a).Point)
    (wd : (stage Label a).order.le W D) (wx : (stage Label a).order.le W X) :
    (transition Label (lt_start a).le).Separates W D X := by
  apply (Transition.separates_transport _ (stage_successor Label a) W D X).mp
  rw [transition_successor]
  exact (stage Label a).next_separates Label W D X wd wx

theorem final_separation_at (a : Column) (W D X : (stage Label a).Point)
    (wd : (stage Label a).order.le W D) (wx : (stage Label a).order.le W X) :
    ∃ g : FinalActor Label,
      (∀ z, (finalOrder Label).le z ((finalInclusion Label a).toFun W) →
        ((finalAction Label).iso g).toFun z = z) ∧
      (finalOrder Label).meet
        (((finalAction Label).iso g).toFun ((finalInclusion Label a).toFun D))
        ((finalInclusion Label a).toFun X) = (finalInclusion Label a).toFun W := by
  rcases stage_successor_separates Label a W D X wd wx with ⟨g, fixes, meet⟩
  refine ⟨finalGroupInclusion Label (start a) g, ?_, ?_⟩
  · intro z lower
    have h : (finalOrder Label).le z ((finalInclusion Label (start a)).toFun
        ((transition Label (lt_start a).le).points.toFun W)) := by
      erw [final_points_coherent]
      exact lower
    have agree := final_agreement Label (start a) g 1
      ((transition Label (lt_start a).le).points.toFun W)
      (fun y hy => (fixes y hy).trans ((stage Label (start a)).action.one y).symm) z h
    simpa only [map_one, (finalAction Label).one] using agree
  · erw [← final_points_coherent Label (lt_start a).le D,
      ← final_points_coherent Label (lt_start a).le X,
      final_action_stage, ← (finalInclusion Label (start a)).map_meet,
      meet, final_points_coherent]

theorem final_separation (W D X : FinalPoint Label)
    (wd : (finalOrder Label).le W D) (wx : (finalOrder Label).le W X) :
    ∃ g : FinalActor Label,
      (∀ z, (finalOrder Label).le z W → ((finalAction Label).iso g).toFun z = z) ∧
      (finalOrder Label).meet (((finalAction Label).iso g).toFun D) X = W := by
  rcases (diagram Label).orders.system.triple_cover (diagram Label).orders.system
    (diagram Label).orders.system W D X with ⟨a, W, D, X, rfl, rfl, rfl⟩
  exact final_separation_at Label a W D X
    (((finalInclusion Label a).le_iff _ _).mp wd) (((finalInclusion Label a).le_iff _ _).mp wx)

end OrdinalRun

end PartitionPilot.Compression.RecursiveMaps.MainStage

end OAI
