import OAI.SetTheory.PartitionPrinciple.Transfinite.GluingBirthRanges

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment CosetGeometry
universe u

def groupDataOfGroup (G : Type u) [Group G] : GroupData G where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul := inv_mul_cancel
  mul_inv := mul_inv_cancel

namespace CosetGeometry.OrderAction
variable {A G Label : Type u} [Group G] {P : MeetOrder A} (a : OrderAction G P)

def Eligible (d : TaskDatum P Label) : Prop :=
  d.Geometry ∧ ∃ g, ∀ x : {x // P.le x d.source}, (a.iso g).toFun x.val = d.baseMap.toFun x

def AllTasks (Label : Type u) := {d : TaskDatum P Label // a.Eligible d}

theorem eligible_transform (g : G) (d : TaskDatum P Label) (eligible : a.Eligible d) :
    a.Eligible (TaskDatum.transform (a.iso g) d) := by
  refine ⟨TaskDatum.geometry_transform (a.iso g) d eligible.1, ?_⟩
  rcases eligible.2 with ⟨h, represents⟩
  refine ⟨g * h, ?_⟩
  intro x
  change (a.iso (g * h)).toFun x.val = (a.iso g).toFun (d.baseMap.toFun x)
  erw [a.mul, represents]

theorem eligible_source_proper (top : A) (greatest : ∀ x, P.le x top)
    (d : TaskDatum P Label) (eligible : a.Eligible d) : ¬ P.le top d.source := by
  rcases eligible with ⟨geometry, g, represents⟩
  have baseTop : d.baseMap.toFun ⟨d.source, P.refl _⟩ = d.target := by
    apply P.antisymm (geometry.base_bound _)
    rcases geometry.base_onto d.target (P.refl _) with ⟨x, eq⟩
    rw [← eq]
    exact (d.baseMap.le_iff _ _).mpr x.property
  have sourceImage : (a.iso g).toFun d.source = d.target := (represents _).trans baseTop
  intro lower
  have targetTop := ((a.iso g).le_iff top d.source).mpr lower
  rw [a.fixes_top top greatest, sourceImage] at targetTop
  exact geometry.separator_not_le_base (P.trans (greatest d.separator) targetTop)

noncomputable def allTaskSystem (top : A) (greatest : ∀ x, P.le x top) (Label : Type u) :
    TaskSystem P G (a.AllTasks Label) Label where
  group := groupDataOfGroup G
  action := a.iso
  action_one := a.one
  action_mul := a.mul
  datum := Subtype.val
  faithful _ _ eq := Subtype.ext eq
  geometry d := d.property.1
  invariant g d := ⟨⟨TaskDatum.transform (a.iso g) d.val, a.eligible_transform g d.val d.property⟩, rfl⟩
  representable d := d.property.2
  top := top
  greatest := greatest
  source_proper d := a.eligible_source_proper top greatest d.val d.property

theorem allTaskSystem_complete (top : A) (greatest : ∀ x, P.le x top)
    (d : TaskDatum P Label) (eligible : a.Eligible d) :
    ∃ i, (a.allTaskSystem top greatest Label).datum i = d := ⟨⟨d, eligible⟩, rfl⟩

theorem allTaskSystem_literal (top : A) (greatest : ∀ x, P.le x top)
    (i j : a.AllTasks Label) :
    (a.allTaskSystem top greatest Label).datum i = (a.allTaskSystem top greatest Label).datum j ↔
      i = j := ⟨Subtype.ext, congrArg Subtype.val⟩

def labelledTask (d : TaskDatum P Label) (eligible : a.Eligible d) (label : Label) : a.AllTasks Label :=
  ⟨{ d with label := label },
    ⟨⟨eligible.1.base_bound, eligible.1.base_onto, eligible.1.base_le_separator,
      eligible.1.separator_not_le_base, eligible.1.separator_le_filter⟩, eligible.2⟩⟩

theorem labelledTask_label (d : TaskDatum P Label) (eligible : a.Eligible d) (label : Label) :
    (a.labelledTask d eligible label).val.label = label := rfl

theorem labelledTask_injective (d : TaskDatum P Label) (eligible : a.Eligible d) :
    Function.Injective (a.labelledTask d eligible) := by
  intro i j eq
  exact congrArg (fun task : a.AllTasks Label => task.val.label) eq

end CosetGeometry.OrderAction
end PartitionPilot.Compression.RecursiveMaps



namespace PartitionPilot.Compression.RecursiveMaps

universe u
structure ActionRectangle {A G : Type u} (P : MeetOrder A) (action : G → MeetIso P P) where
  C : A
  B : A
  D : A
  first : G
  second : G
  C_le_D : P.le C D
  B_le_D : P.le B D
  agree : ∀ x, P.le x (P.meet C B) → (action first).toFun x = (action second).toFun x
  separated : P.meet ((action first).toFun D) ((action second).toFun D) =
    (action first).toFun (P.meet C B)

namespace ActionRectangle
variable {A G : Type u} {P : MeetOrder A} {action : G → MeetIso P P}

def toInput (r : ActionRectangle P action) (top : A) (greatest : ∀ x, P.le x top) :
    Rectangle.Input P where
  top := top
  greatest := greatest
  C := r.C
  B := r.B
  D := r.D
  C_le_D := r.C_le_D
  B_le_D := r.B_le_D
  g1 := action r.first
  g2 := action r.second
  agree := r.agree
  separated := r.separated

end ActionRectangle

namespace CompressionAlgebra
variable {A G Task Label : Type u} {P : MeetOrder A} {f : TaskSystem P G Task Label}
    (e : CompressionAlgebra f)

def liftRectangle (r : ActionRectangle P f.action) : ActionRectangle e.order e.action where
  C := e.original.toFun r.C
  B := e.original.toFun r.B
  D := e.original.toFun r.D
  first := r.first
  second := r.second
  C_le_D := (e.original.le_iff _ _).mpr r.C_le_D
  B_le_D := (e.original.le_iff _ _).mpr r.B_le_D
  agree x lower := by
    rw [← e.original.map_meet] at lower
    exact e.agreement r.first r.second (P.meet r.C r.B) r.agree x lower
  separated := by
    rw [e.action_original, e.action_original, ← e.original.map_meet, r.separated]
    rw [← e.original.map_meet, e.action_original]

end CompressionAlgebra

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
