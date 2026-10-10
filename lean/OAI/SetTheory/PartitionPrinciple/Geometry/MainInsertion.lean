import OAI.SetTheory.PartitionPrinciple.Transfinite.MainBirthExtensions

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.MainStage

open CosetGeometry
universe u
variable (s : MainStage.{u}) (Label : Type u)

noncomputable def compressionActor (i : s.action.AllTasks Label) : (s.next Label).Actor :=
  generator s.Actor (s.requests Label).Letters ⟨.compression i, ⟨()⟩⟩

noncomputable def compressionCap (i : s.action.AllTasks Label) : (s.next Label).Point :=
  (s.externalTransition Label).points.toFun ((s.tasks Label).unionCap i)

theorem compression_internal (i : s.action.AllTasks Label) (x : (s.internal Label).Point) :
    ((s.next Label).action.iso (s.compressionActor Label i)).toFun
      ((s.externalTransition Label).points.toFun x) =
      (s.externalTransition Label).points.toFun (((s.tasks Label).unionCompressionIso i).toFun x).val := by
  change (((s.requests Label).extensionAction (s.internal Label).action).iso
    (s.compressionActor Label i)).toFun
    (((s.requests Label).extensionCopy (s.internal Label).action 1).toFun x) = _
  erw [(s.requests Label).extensionAction_copy, mul_one]
  apply congrArg some
  have eq := (s.requests Label).transfer_child_root (s.internal Label).action 1
    (.compression i) ⟨()⟩ x (((s.tasks Label).unionCompressionIso i).toFun x).val
    (TileRequests.Request.compression_agrees (s.internal Label).top (s.internal Label).greatest
      ((s.tasks Label).unionCap i) ((s.tasks Label).unionCompressionIso i) x)
  simp only [one_mul] at eq
  exact eq

theorem compression_below_cap (i : s.action.AllTasks Label) (D : s.Point) :
    (s.next Label).order.le
      (((s.next Label).action.iso (s.compressionActor Label i)).toFun
        ((s.nextTransition Label).points.toFun D)) (s.compressionCap Label i) := by
  change (s.next Label).order.le
    (((s.next Label).action.iso (s.compressionActor Label i)).toFun
      ((s.externalTransition Label).points.toFun ((s.internalTransition Label).points.toFun D))) _
  rw [s.compression_internal]
  exact ((s.externalTransition Label).points.le_iff _ _).mpr
    (((s.tasks Label).unionCompressionIso i).toFun ((s.internalTransition Label).points.toFun D)).property

theorem compression_agrees_ideal (i : s.action.AllTasks Label) (z : (s.next Label).Point)
    (lower : (s.next Label).order.le z ((s.nextTransition Label).points.toFun i.val.source)) :
    ((s.next Label).action.iso (s.compressionActor Label i)).toFun z =
      ((s.next Label).action.iso ((s.nextTransition Label).actors ((s.tasks Label).representative i))).toFun z := by
  let e := (s.requests Label).extensionCopy (s.internal Label).action 1
  rcases e.ideal ((s.internalTransition Label).points.toFun i.val.source) z lower with ⟨x, rfl⟩
  have hx := (e.le_iff _ _).mp lower
  have base := (s.tasks Label).compressionAlgebra.base_agreement i x hx
  change (((s.tasks Label).unionCompressionIso i).toFun x).val =
    ((s.internal Label).action.iso ((s.tasks Label).representative i)).toFun x at base
  change ((s.next Label).action.iso (s.compressionActor Label i)).toFun
    ((s.externalTransition Label).points.toFun x) = _
  rw [s.compression_internal, base]
  exact ((s.externalTransition Label).equivariant ((s.tasks Label).representative i) x).symm

end PartitionPilot.Compression.RecursiveMaps.MainStage



namespace PartitionPilot.Compression.RecursiveMaps.MainStage

open Attachment
universe u
variable (s : MainStage.{u}) (Label : Type u)

def insertionDatum (C E : s.Point) (F : MeetFilter s.order) (label : Label) :
    TaskDatum s.order Label where
  source := C
  target := C
  baseMap := { toFun := Subtype.val, le_iff := fun _ _ => Iff.rfl, map_meet := fun _ _ => rfl }
  separator := E
  filter := F
  label := label

def insertionTask (C E : s.Point) (F : MeetFilter s.order)
    (ce : s.order.le C E) (strict : ¬ s.order.le E C)
    (above : ∀ x, F.mem x → s.order.le E x) (label : Label) : s.action.AllTasks Label :=
  ⟨s.insertionDatum Label C E F label,
    ⟨⟨(fun x => x.property), (fun y hy => ⟨⟨y, hy⟩, rfl⟩), ce, strict, above⟩,
      ⟨1, fun x => s.action.one x.val⟩⟩⟩

theorem insertionTask_injective (C E : s.Point) (F : MeetFilter s.order)
    (ce : s.order.le C E) (strict : ¬ s.order.le E C)
    (above : ∀ x, F.mem x → s.order.le E x) :
    Function.Injective (s.insertionTask Label C E F ce strict above) := by
  intro i j eq
  exact congrArg (fun t : s.action.AllTasks Label => t.val.label) eq

theorem insertion_representative_fixes (C E : s.Point) (F : MeetFilter s.order)
    (ce : s.order.le C E) (strict : ¬ s.order.le E C)
    (above : ∀ x, F.mem x → s.order.le E x) (label : Label)
    (x : s.Point) (lower : s.order.le x C) :
    (s.action.iso ((s.tasks Label).representative
      (s.insertionTask Label C E F ce strict above label))).toFun x = x :=
  (s.tasks Label).represents (s.insertionTask Label C E F ce strict above label) ⟨x, lower⟩

end PartitionPilot.Compression.RecursiveMaps.MainStage



namespace PartitionPilot.Compression.RecursiveMaps.MainStage

universe u
namespace Transition
variable {s t : MainStage.{u}}

def Inserts (f : Transition s t) (Label : Type u) (C E D : s.Point) (F : MeetFilter s.order) : Prop :=
  ∃ (caps : Label → t.Point) (actors : Label → t.Actor),
    (∀ l z, t.order.le z (f.points.toFun C) → (t.action.iso (actors l)).toFun z = z) ∧
    (∀ l, t.order.le ((t.action.iso (actors l)).toFun (f.points.toFun D)) (caps l)) ∧
    (∀ l, t.order.le (f.points.toFun C) (caps l) ∧ ¬ t.order.le (caps l) (f.points.toFun C)) ∧
    (∀ l, ¬ t.order.le (f.points.toFun E) (caps l)) ∧
    (∀ i j, i ≠ j → t.order.meet (caps i) (caps j) = f.points.toFun C) ∧
    (∀ l x, t.order.le (f.points.toFun E) x →
      (PositiveOver f.points F.mem x → t.order.le (caps l) x) ∧
      (¬ PositiveOver f.points F.mem x → t.order.meet (caps l) x = f.points.toFun C))

theorem inserts_transport {t' : MainStage.{u}} (f : Transition s t) (eq : t = t')
    (Label : Type u) (C E D : s.Point) (F : MeetFilter s.order) :
    (f.transport rfl eq).Inserts Label C E D F ↔ f.Inserts Label C E D F := by
  cases eq
  rfl

end Transition

variable (s : MainStage.{u}) (Label : Type u)

theorem next_inserts (C E D : s.Point) (F : MeetFilter s.order)
    (ce : s.order.le C E) (strict : ¬ s.order.le E C)
    (above : ∀ x, F.mem x → s.order.le E x) :
    (s.nextTransition Label).Inserts Label C E D F := by
  let task := s.insertionTask Label C E F ce strict above
  let inc := (s.internalTransition Label).points
  let ext := (s.externalTransition Label).points
  refine ⟨(fun l => s.compressionCap Label (task l)),
    (fun l => s.compressionActor Label (task l)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l z lower
    have agrees := s.compression_agrees_ideal Label (task l) z lower
    have fixes := (s.nextTransition Label).agreement ((s.tasks Label).representative (task l)) 1 C
      (fun x hx => (s.insertion_representative_fixes Label C E F ce strict above l x hx).trans
        (s.action.one x).symm) z lower
    exact agrees.trans (fixes.trans (by rw [map_one, (s.next Label).action.one]))
  · intro l
    exact s.compression_below_cap Label (task l) D
  · intro l
    have strictCap := (s.tasks Label).compressionAlgebra.strict (task l)
    exact ⟨(ext.le_iff _ _).mpr strictCap.1, fun h => strictCap.2 ((ext.le_iff _ _).mp h)⟩
  · intro l h
    exact (s.tasks Label).compressionAlgebra.separator (task l) ((ext.le_iff _ _).mp h)
  · intro i j different
    have neq : task i ≠ task j := fun eq => different
      (s.insertionTask_injective Label C E F ce strict above eq)
    have meet := (s.tasks Label).union_equal_base_caps (task i) (task j) neq rfl
    change (s.next Label).order.meet (ext.toFun _) (ext.toFun _) = ext.toFun (inc.toFun C)
    erw [← ext.map_meet]
    exact congrArg ext.toFun meet
  · intro l
    have old : Profile (s.internal Label).order (inc.toFun C) (inc.toFun E)
        ((s.tasks Label).unionCap (task l)) (imageFamily inc F.mem) := by
      intro x lower
      have h := (s.tasks Label).compressionAlgebra.profile (task l) x lower
      exact ⟨fun hp => h.1 ((positive_imageFamily inc F.mem x).mp hp),
        fun hn => h.2 (fun hp => hn ((positive_imageFamily inc F.mem x).mpr hp))⟩
    have nonempty : ∃ x, imageFamily inc F.mem x := by
      rcases F.nonempty with ⟨x, hx⟩
      exact ⟨inc.toFun x, x, hx, rfl⟩
    have persists := s.external_preservesProfiles Label (inc.toFun C) (inc.toFun E)
      ((s.tasks Label).unionCap (task l)) (imageFamily inc F.mem) nonempty
      ((s.tasks Label).compressionAlgebra.separator (task l)) old
    intro x lower
    have positive := positiveOver_imageFamily inc ext F.mem x
    exact ⟨fun hp => (persists x lower).1 (positive.mpr hp),
      fun hn => (persists x lower).2 (fun hp => hn (positive.mp hp))⟩

end PartitionPilot.Compression.RecursiveMaps.MainStage

end

end OAI
