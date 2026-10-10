import OAI.SetTheory.PartitionPrinciple.Geometry.FinalProfilePersistence

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

open Cardinal
open scoped Cardinal
universe u

namespace CosetGeometry
variable (J S : Type u) [Group J]

def factorCode : (Σ b, Factor J S b) → J ⊕ FreeGroup S
  | ⟨false, x⟩ => .inl x
  | ⟨true, x⟩ => .inr x

omit [Group J] in
theorem factorCode_injective : Function.Injective (factorCode J S) := by
  rintro ⟨firstTag, first⟩ ⟨secondTag, second⟩ equal
  cases firstTag <;> cases secondTag
  · have values := Sum.inl.inj equal
    cases values
    rfl
  · change Sum.inl first = Sum.inr second at equal
    cases equal
  · change Sum.inr first = Sum.inl second at equal
    cases equal
  · have values := Sum.inr.inj equal
    cases values
    rfl

theorem freeGroup_cardinal_lt (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (small : #S < κ) : #(FreeGroup S) < κ := by
  have signed : #(S × Bool) < κ := by
    simpa only [mk_prod, lift_id, lift_uzero, mk_bool, lift_ofNat] using
      (mul_lt_of_lt inaccessible.1.le small ((ofNat_lt_aleph0 (n := 2)).trans inaccessible.1))
  exact (mk_quot_le (r := FreeGroup.Red.Step)).trans_lt (SizeBounds.list_lt κ inaccessible signed)

theorem external_cardinal_lt (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (oldSmall : #J < κ) (letters : #S < κ) : #(External J S) < κ := by
  have factors : #(Σ b, Factor J S b) < κ :=
    (mk_le_of_injective (factorCode_injective J S)).trans_lt
      (SizeBounds.sum_lt κ inaccessible oldSmall (freeGroup_cardinal_lt S κ inaccessible letters))
  have words : #(List (Σ b, Factor J S b)) < κ := SizeBounds.list_lt κ inaccessible factors
  exact (mk_quotient_le (s := (conGen (Monoid.CoprodI.Rel (Factor J S))).toSetoid)).trans_lt words

end CosetGeometry

namespace TileRequests

def Request.childCode {A : Type u} {P : MeetOrder A} : (r : Request P) → r.Child → Bool
  | .separation _, _ => false
  | .compression _ _, _ => false
  | .rectangle _, j => j.down

theorem Request.childCode_injective {A : Type u} {P : MeetOrder A} (r : Request P) :
    Function.Injective r.childCode := by
  cases r with
  | separation _ => intro x y _; exact ULift.ext _ _ (Subsingleton.elim x.down y.down)
  | compression _ _ => intro x y _; exact ULift.ext _ _ (Subsingleton.elim x.down y.down)
  | rectangle _ => intro x y eq; exact ULift.ext _ _ eq

namespace Family
open CosetGeometry
variable {A J R : Type u} [Group J] {P : MeetOrder A} (f : Family P R)

def letterCode (l : f.Letters) : R × Bool := (l.1, (f.request l.1).childCode l.2)

theorem letterCode_injective : Function.Injective f.letterCode := by
  rintro ⟨r, i⟩ ⟨s, j⟩ eq
  have same : r = s := congrArg Prod.fst eq
  cases same
  have child := (f.request r).childCode_injective (congrArg Prod.snd eq)
  cases child
  rfl

theorem letters_cardinal_lt (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (requests : #R < κ) : #f.Letters < κ := by
  apply (mk_le_of_injective f.letterCode_injective).trans_lt
  simpa only [mk_prod, lift_id, lift_uzero, mk_bool, lift_ofNat] using
    (mul_lt_of_lt inaccessible.1.le requests ((ofNat_lt_aleph0 (n := 2)).trans inaccessible.1))

theorem node_cardinal_lt (a : OrderAction J P) (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (nodes : #A < κ) (oldGroup : #J < κ) (requests : #R < κ) : #(f.Node a) < κ := by
  have cover : Function.Surjective (fun p : External J f.Letters × A => (f.copy a p.1).toFun p.2) := by
    intro x
    rcases f.copy_cover a x with ⟨w, y, eq⟩
    exact ⟨(w, y), eq⟩
  exact (mk_le_of_surjective cover).trans_lt (SizeBounds.prod_lt κ inaccessible
    (external_cardinal_lt J f.Letters κ inaccessible oldGroup (f.letters_cardinal_lt κ inaccessible requests)) nodes)

theorem extension_cardinal_lt (a : OrderAction J P) (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (nodes : #A < κ) (oldGroup : #J < κ) (requests : #R < κ) : #(f.Extension a) < κ :=
  SizeBounds.option_lt κ inaccessible (f.node_cardinal_lt a κ inaccessible nodes oldGroup requests)

end Family
end TileRequests






namespace TaskDatum
variable {A Label : Type u} {P : MeetOrder A}

def sizeCode (d : TaskDatum P Label) : A × A × A × Label × Set A × Set (A × A) :=
  (d.source, d.target, d.separator, d.label, d.filter.mem,
    {p | ∃ h : P.le p.1 d.source, d.baseMap.toFun ⟨p.1, h⟩ = p.2})

theorem sizeCode_injective : Function.Injective (sizeCode (P := P) (Label := Label)) := by
  intro d e eq
  rcases d with ⟨s, t, m, v, F, l⟩
  rcases e with ⟨s', t', m', v', F', l'⟩
  simp only [sizeCode, Prod.mk.injEq] at eq
  have hs := eq.1
  have ht := eq.2.1
  have hv := eq.2.2.1
  have hl := eq.2.2.2.1
  have hF := congrArg Prod.fst eq.2.2.2.2
  have graph := congrArg Prod.snd eq.2.2.2.2
  dsimp only at hF graph
  cases hs
  cases ht
  cases hv
  cases hl
  have filters : F = F' := meetFilter_ext F F' (fun x => by rw [hF])
  cases filters
  have maps : m = m' := by
    apply meetEmbedding_ext
    intro x
    have hx : (x.val, m.toFun x) ∈ {p | ∃ h : P.le p.1 s, m.toFun ⟨p.1, h⟩ = p.2} :=
      ⟨x.property, rfl⟩
    rw [graph] at hx
    rcases hx with ⟨_, eq⟩
    exact eq.symm
  cases maps
  rfl

theorem cardinal_lt (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (nodes : #A < κ) (labels : #Label < κ) : #(TaskDatum P Label) < κ := by
  apply (mk_le_of_injective (sizeCode_injective (P := P) (Label := Label))).trans_lt
  exact SizeBounds.prod_lt κ inaccessible nodes (SizeBounds.prod_lt κ inaccessible nodes
    (SizeBounds.prod_lt κ inaccessible nodes (SizeBounds.prod_lt κ inaccessible labels
      (SizeBounds.prod_lt κ inaccessible (SizeBounds.sets_lt κ inaccessible nodes)
        (SizeBounds.sets_lt κ inaccessible (SizeBounds.prod_lt κ inaccessible nodes nodes))))))

end TaskDatum

namespace MainStage
variable (s : MainStage.{u}) (Label : Type u)

theorem tasks_cardinal_lt (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (nodes : #s.Point < κ) (labels : #Label < κ) : #(s.action.AllTasks Label) < κ :=
  SizeBounds.subtype_lt κ (TaskDatum.cardinal_lt κ inaccessible nodes labels) _

theorem internal_cardinal_lt (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (nodes : #s.Point < κ) (labels : #Label < κ) : #(s.internal Label).Point < κ :=
  (s.tasks Label).union_cardinal_lt κ inaccessible.1 nodes
    (s.tasks_cardinal_lt Label κ inaccessible nodes labels)

end MainStage






namespace ActionRectangle
variable {A G : Type u} {P : MeetOrder A} {action : G → MeetIso P P}

def sizeCode (r : ActionRectangle P action) : A × A × A × G × G :=
  (r.C, r.B, r.D, r.first, r.second)

theorem sizeCode_injective : Function.Injective (sizeCode (P := P) (action := action)) := by
  intro r s eq
  cases r
  cases s
  simp only [sizeCode, Prod.mk.injEq] at eq
  rcases eq with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

theorem cardinal_lt (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (nodes : #A < κ) (actors : #G < κ) : #(ActionRectangle P action) < κ :=
  (mk_le_of_injective (sizeCode_injective (P := P) (action := action))).trans_lt
    (SizeBounds.prod_lt κ inaccessible nodes (SizeBounds.prod_lt κ inaccessible nodes
      (SizeBounds.prod_lt κ inaccessible nodes (SizeBounds.prod_lt κ inaccessible actors actors))))

end ActionRectangle

namespace MainStage
variable (s : MainStage.{u}) (Label : Type u)

def CardinalBound (κ : Cardinal.{u}) : Prop := #s.Point < κ ∧ #s.Actor < κ

def requestCode : s.RequestIndex Label →
    s.action.AllTasks Label ⊕ (s.Point ⊕ ActionRectangle s.order s.action.iso)
  | .compression t => .inl t
  | .separation x => .inr (.inl x)
  | .rectangle r => .inr (.inr r)

theorem requestCode_injective : Function.Injective (s.requestCode Label) := by
  intro i j eq
  cases i <;> cases j <;> simp only [requestCode, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl] at eq
  all_goals cases eq; rfl

theorem requests_cardinal_lt (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (small : s.CardinalBound κ) (labels : #Label < κ) : #(s.RequestIndex Label) < κ :=
  (mk_le_of_injective (s.requestCode_injective Label)).trans_lt
    (SizeBounds.sum_lt κ inaccessible (s.tasks_cardinal_lt Label κ inaccessible small.1 labels)
      (SizeBounds.sum_lt κ inaccessible small.1 (ActionRectangle.cardinal_lt κ inaccessible small.1 small.2)))

theorem next_cardinal_bound (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (small : s.CardinalBound κ) (labels : #Label < κ) : (s.next Label).CardinalBound κ := by
  have requests := s.requests_cardinal_lt Label κ inaccessible small labels
  have internal := s.internal_cardinal_lt Label κ inaccessible small.1 labels
  exact ⟨(s.requests Label).extension_cardinal_lt (s.internal Label).action κ inaccessible internal small.2 requests,
    CosetGeometry.external_cardinal_lt s.Actor (s.requests Label).Letters κ inaccessible small.2
      ((s.requests Label).letters_cardinal_lt κ inaccessible requests)⟩

end MainStage






namespace DirectSystem
variable {I : Type u} [LinearOrder I] (d : DirectSystem I)

theorem cardinal_lt (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (indices : #I < κ) (stages : ∀ i, #(d.Point i) < κ) : #d.Union < κ :=
  SizeBounds.image_cover_lt κ inaccessible indices d.Point stages d.point d.cover

end DirectSystem

namespace MainStage

theorem cardinal_bound_of_eq {s t : MainStage.{u}} (eq : s = t) (κ : Cardinal.{u})
    (small : t.CardinalBound κ) : s.CardinalBound κ := by cases eq; exact small

theorem initial_cardinal_bound (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible) :
    initial.{u}.CardinalBound κ := by
  constructor
  · exact SizeBounds.countable_lt κ inaccessible (A := ULift.{u} Bool)
  · have injective : Function.Injective (fun _ : initial.{u}.Actor => (⟨()⟩ : ULift.{u} Unit)) := by
      intro x y _
      exact (initial_group_trivial x).trans (initial_group_trivial y).symm
    exact (mk_le_of_injective injective).trans_lt
      (SizeBounds.countable_lt κ inaccessible (A := ULift.{u} Unit))

namespace Diagram
variable {I : Type u} [LinearOrder I] (d : Diagram I)

theorem union_cardinal_bounds (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (indices : #I < κ) (small : ∀ i, (d.stage i).CardinalBound κ) :
    #d.orders.system.Union < κ ∧ #d.groups.system.Union < κ :=
  ⟨d.orders.system.cardinal_lt κ inaccessible indices (fun i => (small i).1),
    d.groups.system.cardinal_lt κ inaccessible indices (fun i => (small i).2)⟩

theorem limit_cardinal_bound [Nonempty I] [Countable I]
    (κ : Cardinal.{u}) (inaccessible : κ.IsInaccessible)
    (small : ∀ i, (d.stage i).CardinalBound κ) : d.limit.CardinalBound κ := by
  have bounds := d.union_cardinal_bounds κ inaccessible (SizeBounds.countable_lt κ inaccessible) small
  exact ⟨SizeBounds.option_lt κ inaccessible bounds.1, bounds.2⟩

end Diagram

open CountableColumns

theorem ordinalStep_cardinal_bound (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a))
    (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) (labels : #Label < κ)
    (small : ∀ i, (d.stage i).CardinalBound κ) : (ordinalStep Label a d).apex.CardinalBound κ := by
  classical
  by_cases inhabited : Nonempty (Set.Iio a)
  · by_cases hasLast : ∃ last : Set.Iio a, ∀ i, i ≤ last
    · exact cardinal_bound_of_eq (ordinalStep_last Label a d hasLast.choose hasLast.choose_spec) κ
        ((d.stage hasLast.choose).next_cardinal_bound Label κ inaccessible (small hasLast.choose) labels)
    · let _ := inhabited
      have eq : ordinalStep Label a d = d.limitCone := (dite_eq_left inhabited).trans (dite_eq_right hasLast)
      exact cardinal_bound_of_eq (congrArg Diagram.Cone.apex eq) κ
        (d.limit_cardinal_bound κ inaccessible small)
  · exact cardinal_bound_of_eq (ordinalStep_empty Label a d inhabited) κ (initial_cardinal_bound κ inaccessible)

end MainStage

end PartitionPilot.Compression.RecursiveMaps



namespace PartitionPilot.Compression.RecursiveMaps

open Cardinal
open scoped Cardinal

namespace CountableColumns

theorem cardinal_eq_aleph_one : #Column = (ℵ₁ : Cardinal.{1}) := by
  have types : Column = Set.Iio (ℵ₁ : Cardinal.{0}).ord :=
    congrArg Subtype (funext (fun o => propext (membership_iff o)))
  rw [types, Cardinal.mk_Iio_ordinal, Cardinal.card_ord, Cardinal.lift_aleph, Ordinal.lift_one]

theorem cardinal_lt_inaccessible (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) : #Column < κ := by
  rw [cardinal_eq_aleph_one, ← Cardinal.succ_aleph0]
  exact inaccessible.isSuccLimit.succ_lt inaccessible.aleph0_lt

end CountableColumns

namespace MainStage.OrdinalRun
open CountableColumns
variable (Label : Type 1)

theorem stage_cardinal_bound (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible)
    (labels : #Label < κ) (a : Column) : (stage Label a).CardinalBound κ := by
  have wf : WellFounded ((· < ·) : Column → Column → Prop) := wellFounded_lt
  induction a using wf.induction with
  | h a ih =>
    apply cardinal_bound_of_eq (Transfinite.stage_generated (ordinalStep Label) a) κ
    exact ordinalStep_cardinal_bound Label a (before Label a) κ inaccessible labels (fun i => ih i.val i.property)

theorem final_cardinal_bounds (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible)
    (labels : #Label < κ) : #(FinalPoint Label) < κ ∧ #(FinalActor Label) < κ :=
  (diagram Label).union_cardinal_bounds κ inaccessible (cardinal_lt_inaccessible κ inaccessible)
    (stage_cardinal_bound Label κ inaccessible labels)

theorem countableOrdinalLabels_final_cardinal_bounds (κ : Cardinal.{1}) (inaccessible : κ.IsInaccessible) :
    #(FinalPoint Column) < κ ∧ #(FinalActor Column) < κ :=
  final_cardinal_bounds Column κ inaccessible (cardinal_lt_inaccessible κ inaccessible)

end MainStage.OrdinalRun

end PartitionPilot.Compression.RecursiveMaps

end OAI
