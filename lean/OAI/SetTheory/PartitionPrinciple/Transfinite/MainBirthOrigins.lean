import Mathlib.Data.Prod.Lex
import OAI.SetTheory.PartitionPrinciple.Geometry.MainRectangles

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

section

open CosetGeometry RationalHeights
universe u

theorem IdealEmbedding.preserves_bottom {A B : Type u} {P : MeetOrder A} {Q : MeetOrder B}
    (e : IdealEmbedding P Q) (bottom : A) (least : ∀ x, P.le bottom x) (y : B) :
    Q.le (e.toFun bottom) y := by
  rcases e.ideal bottom (Q.meet (e.toFun bottom) y) (Q.meet_le_left _ _) with ⟨x, eq⟩
  have lower := (e.le_iff bottom x).mpr (least x)
  rw [eq] at lower
  exact Q.trans lower (Q.meet_le_right _ _)

structure MainStage where
  Point : Type u
  order : MeetOrder Point
  Actor : Type u
  [group : Group Actor]
  action : OrderAction Actor order
  bottom : Point
  least : ∀ x, order.le bottom x
  top : Point
  greatest : ∀ x, order.le x top
  height : StrictHeight order (lexOrder CountableColumns.order).toHeightOrder
  countable_height : CountableRange height.value

attribute [instance] MainStage.group

namespace MainStage

structure Transition (s t : MainStage.{u}) where
  points : MeetEmbedding s.order t.order
  actors : s.Actor →* t.Actor
  actors_injective : Function.Injective actors
  equivariant : ∀ g x, (t.action.iso (actors g)).toFun (points.toFun x) =
    points.toFun ((s.action.iso g).toFun x)
  bottom : points.toFun s.bottom = t.bottom
  height : ∀ x, t.height.value (points.toFun x) = s.height.value x
  agreement : ∀ g h v,
    (∀ x, s.order.le x v → (s.action.iso g).toFun x = (s.action.iso h).toFun x) →
    ∀ x, t.order.le x (points.toFun v) →
      (t.action.iso (actors g)).toFun x = (t.action.iso (actors h)).toFun x

namespace Transition
variable {s t r : MainStage.{u}}

def identity (s : MainStage.{u}) : Transition s s where
  points := (identityIso s.order).toMeetEmbedding
  actors := MonoidHom.id s.Actor
  actors_injective := Function.injective_id
  equivariant _ _ := rfl
  bottom := rfl
  height _ := rfl
  agreement _ _ _ agree := agree

def comp (f : Transition s t) (g : Transition t r) : Transition s r where
  points := compose f.points g.points
  actors := g.actors.comp f.actors
  actors_injective := g.actors_injective.comp f.actors_injective
  equivariant a x := by
    change (r.action.iso (g.actors (f.actors a))).toFun (g.points.toFun (f.points.toFun x)) = _
    rw [g.equivariant, f.equivariant]
    rfl
  bottom := by
    change g.points.toFun (f.points.toFun s.bottom) = r.bottom
    rw [f.bottom, g.bottom]
  height x := (g.height (f.points.toFun x)).trans (f.height x)
  agreement a b v agree :=
    g.agreement (f.actors a) (f.actors b) (f.points.toFun v) (f.agreement a b v agree)

end Transition
end MainStage

end



namespace MainStage

open CosetGeometry RationalHeights
universe u
variable (s : MainStage.{u}) (Label : Type u)

noncomputable def tasks : TaskSystem s.order s.Actor (s.action.AllTasks Label) Label :=
  s.action.allTaskSystem s.top s.greatest Label

noncomputable def internal : MainStage.{u} where
  Point := (s.tasks Label).Union
  order := (s.tasks Label).unionOrder
  Actor := s.Actor
  action := {
    iso := (s.tasks Label).unionAutomorphism
    one := (s.tasks Label).unionAction_one
    mul := (s.tasks Label).unionAction_mul }
  bottom := (s.tasks Label).originalEmbedding.toFun s.bottom
  least := (s.tasks Label).union_bottom s.bottom s.least
  top := (s.tasks Label).originalEmbedding.toFun s.top
  greatest := (s.tasks Label).union_top
  height := (s.tasks Label).rationalUnionHeight CountableColumns.order s.height s.countable_height
  countable_height := (s.tasks Label).rationalUnionHeight_countable
    CountableColumns.order s.height s.countable_height

noncomputable def internalTransition : Transition s (s.internal Label) where
  points := (s.tasks Label).originalEmbedding
  actors := MonoidHom.id s.Actor
  actors_injective := Function.injective_id
  equivariant _ _ := rfl
  bottom := rfl
  height := (s.tasks Label).rationalUnionHeight_original
    CountableColumns.order s.height s.countable_height
  agreement := (s.tasks Label).union_agreement

inductive RequestIndex where
  | compression (task : s.action.AllTasks Label)
  | separation (W : s.Point)
  | rectangle (data : ActionRectangle s.order s.action.iso)

noncomputable def request : s.RequestIndex Label → TileRequests.Request (s.internal Label).order
  | .compression i => .compression ((s.tasks Label).unionCap i) ((s.tasks Label).unionCompressionIso i)
  | .separation W => .separation ((s.internalTransition Label).points.toFun W)
  | .rectangle r => .rectangle
      (((s.tasks Label).compressionAlgebra.liftRectangle r).toInput
        (s.internal Label).top (s.internal Label).greatest)

noncomputable def requests : TileRequests.Family (s.internal Label).order (s.RequestIndex Label) where
  top := (s.internal Label).top
  greatest := (s.internal Label).greatest
  request := s.request Label

noncomputable def next : MainStage.{u} where
  Point := (s.requests Label).Extension (s.internal Label).action
  order := (s.requests Label).extensionOrder (s.internal Label).action
  Actor := External s.Actor (s.requests Label).Letters
  action := (s.requests Label).extensionAction (s.internal Label).action
  bottom := ((s.requests Label).extensionCopy (s.internal Label).action 1).toFun (s.internal Label).bottom
  least := ((s.requests Label).extensionCopy (s.internal Label).action 1).preserves_bottom
    (s.internal Label).bottom (s.internal Label).least
  top := none
  greatest := (s.requests Label).extension_greatest (s.internal Label).action
  height := (s.requests Label).ordinalExtensionHeight (s.internal Label).action
    (s.internal Label).height (s.internal Label).countable_height
  countable_height := (s.requests Label).ordinalExtensionHeight_countable (s.internal Label).action
    (s.internal Label).height (s.internal Label).countable_height

noncomputable def externalTransition : Transition (s.internal Label) (s.next Label) where
  points := ((s.requests Label).extensionCopy (s.internal Label).action 1).toMeetEmbedding
  actors := old s.Actor (s.requests Label).Letters
  actors_injective := old_injective s.Actor (s.requests Label).Letters
  equivariant := (s.requests Label).extension_extends_old (s.internal Label).action
  bottom := rfl
  height := (s.requests Label).ordinalExtensionHeight_original (s.internal Label).action
    (s.internal Label).height (s.internal Label).countable_height
  agreement := by
    intro g h v agree x lower
    rcases ((s.requests Label).extensionCopy (s.internal Label).action 1).ideal v x lower with ⟨y, rfl⟩
    have eq := agree y
      (((s.requests Label).extensionCopy (s.internal Label).action 1).le_iff y v |>.mp lower)
    exact ((s.requests Label).extension_extends_old (s.internal Label).action g y).trans
      ((congrArg ((s.requests Label).extensionCopy (s.internal Label).action 1).toFun eq).trans
        ((s.requests Label).extension_extends_old (s.internal Label).action h y).symm)

noncomputable def nextTransition : Transition s (s.next Label) :=
  (s.internalTransition Label).comp (s.externalTransition Label)

theorem next_strict_top (x : s.Point) :
    ¬ (s.next Label).order.le (s.next Label).top ((s.nextTransition Label).points.toFun x) :=
  ((s.requests Label).extension_strict_top (s.internal Label).action 1
    ((s.internalTransition Label).points.toFun x)).2

theorem compression_requested (i : s.action.AllTasks Label) :
    (s.requests Label).request (.compression i) =
      .compression ((s.tasks Label).unionCap i) ((s.tasks Label).unionCompressionIso i) := rfl

theorem separation_requested (W : s.Point) :
    (s.requests Label).request (.separation W) =
      .separation ((s.internalTransition Label).points.toFun W) := rfl

theorem rectangle_requested (r : ActionRectangle s.order s.action.iso) :
    (s.requests Label).request (.rectangle r) =
      .rectangle (((s.tasks Label).compressionAlgebra.liftRectangle r).toInput
        (s.internal Label).top (s.internal Label).greatest) := rfl

end MainStage



namespace MainStage

open Chronological
universe u
variable (s : MainStage.{u}) (Label : Type u) {Stage : Type u}
    (seed : s.Point → Stage) (inside outside : Nat → Stage) (topStamp : Stage)

noncomputable def internalBirth : (s.internal Label).Point → Stage :=
  (s.tasks Label).recordedUnionBirth seed inside

noncomputable def nextBirth : (s.next Label).Point → Stage :=
  FixedTop.birth ((s.requests Label).externalBirth (s.internal Label).action
    (s.internalBirth Label seed inside) (fun n _ => outside n)) topStamp

theorem nextBirth_original (x : s.Point) :
    s.nextBirth Label seed inside outside topStamp ((s.nextTransition Label).points.toFun x) =
      seed x := by
  change (s.requests Label).externalBirth (s.internal Label).action
    (s.internalBirth Label seed inside) (fun n _ => outside n)
    (((s.requests Label).copy (s.internal Label).action 1).toFun
      ((s.tasks Label).originalEmbedding.toFun x)) = seed x
  erw [(s.requests Label).externalBirth_original]
  rfl

theorem nextBirth_top :
    s.nextBirth Label seed inside outside topStamp (s.next Label).top = topStamp := rfl

theorem nextBirth_cases (x : (s.next Label).Point) :
    (∃ y, s.nextBirth Label seed inside outside topStamp x = seed y) ∨
    (∃ n, s.nextBirth Label seed inside outside topStamp x = inside n) ∨
    (∃ n, s.nextBirth Label seed inside outside topStamp x = outside n) ∨
      s.nextBirth Label seed inside outside topStamp x = topStamp := by
  cases x with
  | none => exact Or.inr (Or.inr (Or.inr rfl))
  | some x =>
    rcases (s.requests Label).externalBirth_cases (s.internal Label).action
      (s.internalBirth Label seed inside) (fun n _ => outside n) x with ⟨y, eq⟩ | ⟨n, _, eq⟩
    · rcases (s.tasks Label).recordedBirth_cases seed inside y with ⟨z, hz⟩ | ⟨n, hn⟩
      · exact Or.inl ⟨z, eq.trans hz⟩
      · exact Or.inr (Or.inl ⟨n, eq.trans hn⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨n, eq⟩))

variable [LinearOrder Stage] (seed_before : ∀ x n, seed x < inside n)
    (internal_before : ∀ n m, inside n < outside m)

include seed_before internal_before in
theorem internalBirth_before_external (x : (s.internal Label).Point) (n : Nat) :
    s.internalBirth Label seed inside x < outside n := by
  change (s.tasks Label).recordedUnionBirth seed inside x < outside n
  rcases (s.tasks Label).recordedBirth_cases seed inside x with ⟨y, eq⟩ | ⟨m, eq⟩
  · exact eq ▸ lt_trans (seed_before y 0) (internal_before 0 n)
  · exact eq ▸ internal_before m n

variable (external_top : ∀ n, outside n < topStamp)

include seed_before internal_before external_top in
theorem nextBirth_le (x : (s.next Label).Point) :
    s.nextBirth Label seed inside outside topStamp x ≤ topStamp := by
  rcases s.nextBirth_cases Label seed inside outside topStamp x with
    ⟨y, eq⟩ | ⟨n, eq⟩ | ⟨n, eq⟩ | eq
  · exact eq ▸ (lt_trans (seed_before y 0)
      (lt_trans (internal_before 0 0) (external_top 0))).le
  · exact eq ▸ (lt_trans (internal_before n 0) (external_top 0)).le
  · exact eq ▸ (external_top n).le
  · exact eq.le

include seed_before internal_before external_top in
theorem nextBirth_old_meet
    (inside_increasing : ∀ n m, n < m → inside n < inside m)
    (outside_increasing : ∀ n m, n < m → outside n < outside m)
    (initial : OldMeet (P := s.order) seed) :
    OldMeet (P := (s.next Label).order) (s.nextBirth Label seed inside outside topStamp) := by
  apply FixedTop.old_meet_preserved
  · intro x
    rcases (s.requests Label).externalBirth_cases (s.internal Label).action
      (s.internalBirth Label seed inside) (fun n _ => outside n) x with ⟨y, eq⟩ | ⟨n, _, eq⟩
    · exact eq ▸ lt_trans
        (s.internalBirth_before_external Label seed inside outside seed_before internal_before y 0)
        (external_top 0)
    · exact eq ▸ external_top n
  · apply (s.requests Label).externalBirth_old_meet (s.internal Label).action
      (s.internalBirth Label seed inside) (fun n _ => outside n)
    · intro x n _
      exact s.internalBirth_before_external Label seed inside outside seed_before internal_before x n
    · intro n m _ _ lower
      exact outside_increasing n m lower
    · exact (s.tasks Label).recordedUnionBirth_old_meet seed inside seed_before inside_increasing initial

end MainStage



namespace MainStage.BirthLabels

open CountableColumns

abbrev Index := Column ×ₗ (Nat ×ₗ Nat)

def main (t : Index) : Column := (ofLex t).1
def inside (a : Column) (n : Nat) : Index := toLex (a, toLex (0, n))
def outside (a : Column) (n : Nat) : Index := toLex (a, toLex (1, n))
def top (a : Column) : Index := toLex (a, toLex (2, 0))

theorem main_inside (a : Column) (n : Nat) : main (inside a n) = a := rfl
theorem main_outside (a : Column) (n : Nat) : main (outside a n) = a := rfl
theorem main_top (a : Column) : main (top a) = a := rfl

theorem top_before {a b : Column} (h : a < b) (n : Nat) : top a < inside b n :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

theorem inside_before (a : Column) (n m : Nat) : inside a n < outside a m :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl Nat.zero_lt_one)⟩)

theorem outside_top (a : Column) (n : Nat) : outside a n < top a :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl (Nat.lt_succ_self 1))⟩)

theorem inside_increasing (a : Column) (n m : Nat) (h : n < m) : inside a n < inside a m :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
    Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)

theorem outside_increasing (a : Column) (n m : Nat) (h : n < m) : outside a n < outside a m :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
    Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)⟩)

theorem top_mono {a b : Column} (h : a ≤ b) : top a ≤ top b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact Prod.Lex.toLex_le_toLex.mpr (Or.inl h)
  · exact le_rfl

theorem main_le {t : Index} {a : Column} (h : t ≤ top a) : main t ≤ a :=
  Prod.Lex.monotone_fst t (top a) h

end MainStage.BirthLabels




universe u
namespace RootedGluing.Scheme
variable {V Stage : Type u} (d : Scheme V)
    (seed : d.Space d.root → Stage) (stamp : ∀ n, (d.stages n).Layer → Stage)

theorem stageBirth_source (n : Nat) (x : (d.stages n).Point) :
    (∃ y, (d.vertex d.root).toFun y = d.chain.point n x ∧
      d.stageBirth seed stamp n x = seed y) ∨
      ∃ m v, d.stageBirth seed stamp n x = stamp m v := by
  induction n with
  | zero =>
    left
    refine ⟨x, ?_, rfl⟩
    erw [d.vertex_at d.root 0 d.depth_root.le]
    rfl
  | succ n ih =>
    cases x with
    | inl x =>
      rcases ih x with ⟨y, eq, born⟩ | fresh
      · left
        refine ⟨y, ?_, born⟩
        have keep := d.chain.include_up (Nat.le_succ n) x
        erw [d.chain.up_succ (le_refl n), d.chain.up_self] at keep
        exact eq.trans keep.symm
      · exact Or.inr fresh
    | inr x => exact Or.inr ⟨n, x.1, rfl⟩

theorem unionBirth_source (x : d.Node) :
    (∃ y, (d.vertex d.root).toFun y = x ∧ d.unionBirth seed stamp x = seed y) ∨
      ∃ n v, d.unionBirth seed stamp x = stamp n v := by
  rcases d.chain.cover x with ⟨n, x, rfl⟩
  exact d.stageBirth_source seed stamp n x

end RootedGluing.Scheme

namespace TileRequests.Family
open CosetGeometry
variable {A J R Stage : Type u} [Group J] {P : MeetOrder A}
    (f : Family P R) (a : OrderAction J P)
    (seed : A → Stage) (stamp : ∀ n, f.Layer a n → Stage)

theorem externalBirth_source (x : f.Node a) :
    (∃ y, (f.copy a 1).toFun y = x ∧ f.externalBirth a seed stamp x = seed y) ∨
      ∃ n v, f.externalBirth a seed stamp x = stamp n v := by
  rcases (f.diagram a).scheme.unionBirth_source seed stamp x with ⟨y, eq, born⟩ | fresh
  · exact Or.inl ⟨y, (f.copy_one a y).trans eq, born⟩
  · exact Or.inr fresh

end TileRequests.Family

namespace MainStage
open BirthLabels CountableColumns
variable (s : MainStage.{1}) (Label : Type 1) (a : Column) (seed : s.Point → Index)

theorem nextBirth_source (x : (s.next Label).Point) :
    (∃ y, (s.nextTransition Label).points.toFun y = x ∧
      s.nextBirth Label seed (inside a) (outside a) (BirthLabels.top a) x = seed y) ∨
      main (s.nextBirth Label seed (inside a) (outside a) (BirthLabels.top a) x) = a := by
  cases x with
  | none => exact Or.inr rfl
  | some x =>
    rcases (s.requests Label).externalBirth_source (s.internal Label).action
      (s.internalBirth Label seed (inside a)) (fun n _ => outside a n) x with
      ⟨y, eq, born⟩ | ⟨n, _, born⟩
    · cases y with
      | inl y => exact Or.inl ⟨y, congrArg some eq, born⟩
      | inr y =>
        right
        exact congrArg main born
    · right
      exact congrArg main born

end MainStage


end PartitionPilot.Compression.RecursiveMaps

end OAI
