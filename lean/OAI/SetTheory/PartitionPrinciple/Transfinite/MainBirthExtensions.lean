import OAI.SetTheory.PartitionPrinciple.Geometry.MainDiagramGluing

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps.MainStage

section

universe u
namespace Diagram
variable {I : Type u} [LinearOrder I]

theorem ext_of_prefixes (d e : Diagram I)
    (same : ∀ i, d.reindex (fun j : Set.Iic i => j.val) (fun _ _ h => h) =
      e.reindex (fun j : Set.Iic i => j.val) (fun _ _ h => h)) : d = e := by
  apply ext_of_transport _ _
    (fun i => congrArg (fun d => d.stage ⟨i, le_refl i⟩) (same i))
  intro i j h
  exact transition_of_eq _ _ (same j) (i := ⟨i, h⟩) (j := ⟨j, le_refl j⟩) h

theorem Cone.append_prefix {a b : I} {d : Diagram (Set.Iio a)} (c : d.Cone) (h : b < a) :
    c.append.restrictLE h.le =
      d.reindex (fun i : Set.Iic b => ⟨i.val, lt_of_le_of_lt i.property h⟩) (fun _ _ h => h) := by
  exact congrArg (fun e : Diagram (Set.Iio a) =>
    e.reindex (fun i : Set.Iic b => ⟨i.val, lt_of_le_of_lt i.property h⟩) (fun _ _ h => h))
    c.append_restrict

end Diagram

namespace Transfinite
variable {I : Type u} [LinearOrder I]

def pastFamily (a : I) (past : ∀ b, b < a → Diagram (Set.Iic b))
    (i : Set.Iio a) : Diagram (Set.Iic i) :=
  (past i.val i.property).reindex
    (fun j : Set.Iic i => (⟨j.val.val, j.property⟩ : Set.Iic i.val)) (fun _ _ h => h)

theorem pastCompatible (a : I) (past : ∀ b, b < a → Diagram (Set.Iic b))
    (coherent : ∀ i j (hi : i < a) (hj : j < a) (h : i ≤ j),
      (past j hj).restrictLE h = past i hi) : Diagram.Compatible (pastFamily a past) := by
  intro i j h
  exact congrArg (fun d : Diagram (Set.Iic i.val) =>
    d.reindex (fun k : Set.Iic i => (⟨k.val.val, k.property⟩ : Set.Iic i.val))
      (fun _ _ h => h)) (coherent i.val j.val i.property j.property h)

theorem past_glue_prefix (a : I) (past : ∀ b, b < a → Diagram (Set.Iic b))
    (compatible : Diagram.Compatible (pastFamily a past)) (b : I) (h : b < a) :
    compatible.glue.reindex
      (fun i : Set.Iic b => (⟨i.val, lt_of_le_of_lt i.property h⟩ : Set.Iio a))
      (fun _ _ h => h) = past b h := by
  exact congrArg (fun d : Diagram (Set.Iic (⟨b, h⟩ : Set.Iio a)) =>
    d.reindex (fun i : Set.Iic b =>
      (⟨⟨i.val, lt_of_le_of_lt i.property h⟩, i.property⟩ : Set.Iic (⟨b, h⟩ : Set.Iio a)))
      (fun _ _ h => h)) (compatible.glue_restrict ⟨b, h⟩)

variable (extend : ∀ a : I, (d : Diagram (Set.Iio a)) → d.Cone)

noncomputable def runStep (a : I) (past : ∀ b, b < a → Diagram (Set.Iic b)) :
    Diagram (Set.Iic a) := by
  classical
  exact if compatible : Diagram.Compatible (pastFamily a past) then
    (extend a compatible.glue).append
  else Diagram.constant initial

variable [WellFoundedLT I]

noncomputable def run : ∀ a : I, Diagram (Set.Iic a) :=
  wellFounded_lt.fix (runStep extend)

theorem run_eq (a : I) :
    run extend a = runStep extend a (fun b _ => run extend b) := wellFounded_lt.fix_eq _ a

theorem coherent_at (a : I) : ∀ b (h : b ≤ a), (run extend a).restrictLE h = run extend b := by
  refine (show WellFounded ((· < ·) : I → I → Prop) from wellFounded_lt).induction
    (C := fun a => ∀ b (h : b ≤ a), (run extend a).restrictLE h = run extend b) a ?_
  intro a ih
  have compatible : Diagram.Compatible (pastFamily a (fun b _ => run extend b)) :=
    pastCompatible a _ (fun i j _ hj h => ih j hj i h)
  have generated : run extend a = (extend a compatible.glue).append :=
    (run_eq extend a).trans
      (dite_eq_left (c := Diagram.Compatible (pastFamily a (fun b _ => run extend b))) compatible)
  intro b h
  rcases lt_or_eq_of_le h with lower | rfl
  · rw [generated, Diagram.Cone.append_prefix _ lower]
    exact past_glue_prefix a _ compatible b lower
  · exact Diagram.restrictLE_self _

theorem compatible : Diagram.Compatible (run extend) := fun {_ j} h => coherent_at extend j _ h

noncomputable def diagram : Diagram I := Diagram.Compatible.glue (f := run extend) (compatible extend)

theorem diagram_prefix (a : I) :
    (diagram extend).reindex (fun i : Set.Iic a => i.val) (fun _ _ h => h) = run extend a :=
  Diagram.Compatible.glue_restrict (f := run extend) (compatible extend) a

noncomputable def before (a : I) : Diagram (Set.Iio a) :=
  (diagram extend).reindex (fun i : Set.Iio a => i.val) (fun _ _ h => h)

theorem before_prefix {a b : I} (h : b < a) :
    (before extend a).reindex
      (fun i : Set.Iic b => (⟨i.val, lt_of_le_of_lt i.property h⟩ : Set.Iio a))
      (fun _ _ h => h) = run extend b := diagram_prefix extend b

theorem past_glue_before (a : I)
    (coherent : Diagram.Compatible (pastFamily a (fun b _ => run extend b))) :
    coherent.glue = before extend a := by
  apply Diagram.ext_of_prefixes
  intro i
  have old := before_prefix extend i.property
  have built := past_glue_prefix a _ coherent i.val i.property
  have eq := built.trans old.symm
  exact congrArg (fun d : Diagram (Set.Iic i.val) =>
    d.reindex (fun j : Set.Iic i => (⟨j.val.val, j.property⟩ : Set.Iic i.val))
      (fun _ _ h => h)) eq

theorem run_generated (a : I) : run extend a = (extend a (before extend a)).append := by
  have coherent : Diagram.Compatible (pastFamily a (fun b _ => run extend b)) :=
    pastCompatible a _ (fun i j _ _ h => coherent_at extend j i h)
  have generated : run extend a = (extend a coherent.glue).append :=
    (run_eq extend a).trans (dite_eq_left (c := Diagram.Compatible (pastFamily a (fun b _ => run extend b))) coherent)
  rw [generated, past_glue_before extend a coherent]

theorem stage_generated (a : I) :
    (diagram extend).stage a = (extend a (before extend a)).apex := by
  have eq := congrArg (fun d : Diagram (Set.Iic a) => d.stage ⟨a, le_refl a⟩)
    (run_generated extend a)
  exact eq.trans ((extend a (before extend a)).append_stage_top)

end Transfinite





namespace Diagram
variable {I : Type u} [LinearOrder I]

theorem transition_indices (d : Diagram I) {i j i' j' : I} (h : i ≤ j) (h' : i' ≤ j')
    (hi : i = i') (hj : j = j') :
    (d.transition h).transport (congrArg d.stage hi) (congrArg d.stage hj) = d.transition h' := by
  cases hi; cases hj; rfl

theorem Cone.append_leg {a : I} {d : Diagram (Set.Iio a)} (c : d.Cone) (i : Set.Iio a) :
    (c.append.transition (i := ⟨i.val, i.property.le⟩) (j := ⟨a, le_refl a⟩) i.property.le).transport
      (c.append_stage_old i) c.append_stage_top = c.leg i := by
  exact transition_indices c.augmented
    (Cone.endIndex_mono (show (⟨i.val, i.property.le⟩ : Set.Iic a) ≤ ⟨a, le_refl a⟩ from i.property.le))
    (show (i : WithTop (Set.Iio a)) ≤ ⊤ from le_top)
    (Cone.endIndex_old i) Cone.endIndex_top

end Diagram

namespace Transfinite
variable {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (extend : ∀ a : I, (d : Diagram (Set.Iio a)) → d.Cone)

theorem transition_generated (a : I) (i : Set.Iio a) :
    ((diagram extend).transition i.property.le).transport rfl (stage_generated extend a) =
      (extend a (before extend a)).leg i := by
  let c := extend a (before extend a)
  have eq : (diagram extend).reindex (fun j : Set.Iic a => j.val) (fun _ _ h => h) = c.append :=
    (diagram_prefix extend a).trans (run_generated extend a)
  have maps := Diagram.transition_of_eq _ _ eq
    (i := ⟨i.val, i.property.le⟩) (j := ⟨a, le_refl a⟩) i.property.le
  have lifted := congrArg (fun f => f.transport (c.append_stage_old i) c.append_stage_top) maps
  erw [Transition.transport_twice] at lifted
  exact lifted.trans (c.append_leg i)

end Transfinite

namespace Transition

theorem strict_top_of_transport {s t t' : MainStage.{u}} (f : Transition s t) (eq : t = t')
    (strict : ∀ x, ¬ t'.order.le t'.top ((f.transport rfl eq).points.toFun x)) :
    ∀ x, ¬ t.order.le t.top (f.points.toFun x) := by cases eq; exact strict

end Transition

end



namespace OrdinalRun

open CountableColumns
variable (Label : Type 1)

noncomputable def diagram : Diagram Column := Transfinite.diagram (ordinalStep Label)

noncomputable def stage (a : Column) : MainStage.{1} := (diagram Label).stage a

noncomputable def transition {a b : Column} (h : a ≤ b) : Transition (stage Label a) (stage Label b) :=
  (diagram Label).transition h

noncomputable def before (a : Column) : Diagram (Set.Iio a) := Transfinite.before (ordinalStep Label) a

theorem stage_zero : stage Label (natural 0) = initial :=
  (Transfinite.stage_generated (ordinalStep Label) (natural 0)).trans (ordinalStep_zero Label _)

theorem stage_successor (a : Column) : stage Label (start a) = (stage Label a).next Label :=
  (Transfinite.stage_generated (ordinalStep Label) (start a)).trans (ordinalStep_successor Label a _)

theorem stage_limit (a : Column) (limit : Order.IsSuccLimit a.val) :
    letI : Nonempty (Set.Iio a) := ⟨⟨natural 0, limit.pos⟩⟩
    stage Label a = (before Label a).limit := by
  let : Nonempty (Set.Iio a) := ⟨⟨natural 0, limit.pos⟩⟩
  exact (Transfinite.stage_generated (ordinalStep Label) a).trans (ordinalStep_limit Label a _ limit)

theorem transition_self (a : Column) : transition Label (le_refl a) = Transition.identity (stage Label a) :=
  (diagram Label).self a

theorem transition_comp {a b c : Column} (hab : a ≤ b) (hbc : b ≤ c) :
    transition Label (le_trans hab hbc) = (transition Label hab).comp (transition Label hbc) :=
  (diagram Label).comp hab hbc

theorem strict_top {a b : Column} (h : a < b) (x : (stage Label a).Point) :
    ¬ (stage Label b).order.le (stage Label b).top ((transition Label h.le).points.toFun x) := by
  apply Transition.strict_top_of_transport (transition Label h.le)
    (Transfinite.stage_generated (ordinalStep Label) b) _ x
  intro y
  have maps : (transition Label h.le).transport rfl
      (Transfinite.stage_generated (ordinalStep Label) b) =
        (ordinalStep Label b (before Label b)).leg ⟨a, h⟩ :=
    Transfinite.transition_generated (ordinalStep Label) b ⟨a, h⟩
  rw [maps]
  exact ordinalStep_strict_top Label b (before Label b) ⟨a, h⟩ y

theorem transition_height {a b : Column} (h : a ≤ b) (x : (stage Label a).Point) :
    (stage Label b).height.value ((transition Label h).points.toFun x) = (stage Label a).height.value x :=
  (transition Label h).height x

theorem transition_bottom {a b : Column} (h : a ≤ b) :
    (transition Label h).points.toFun (stage Label a).bottom = (stage Label b).bottom :=
  (transition Label h).bottom

theorem transition_agreement {a b : Column} (h : a ≤ b) (g k : (stage Label a).Actor)
    (v : (stage Label a).Point)
    (agree : ∀ x, (stage Label a).order.le x v →
      ((stage Label a).action.iso g).toFun x = ((stage Label a).action.iso k).toFun x) :
    ∀ x, (stage Label b).order.le x ((transition Label h).points.toFun v) →
      ((stage Label b).action.iso ((transition Label h).actors g)).toFun x =
        ((stage Label b).action.iso ((transition Label h).actors k)).toFun x :=
  (transition Label h).agreement g k v agree

noncomputable def countableOrdinalLabels : Diagram Column := diagram Column

end OrdinalRun



section

open Chronological CountableColumns BirthLabels

structure BirthRecord (s : MainStage.{1}) (a : Column) where
  birth : s.Point → Index
  bounded : ∀ x, birth x ≤ BirthLabels.top a
  old_meet : OldMeet (P := s.order) birth

namespace BirthRecord
variable {s t q : MainStage.{1}} {a b : Column}

def constant (s : MainStage.{1}) (a : Column) : BirthRecord s a where
  birth _ := BirthLabels.top a
  bounded _ := le_rfl
  old_meet _ _ earlier _ := False.elim (lt_irrefl _ earlier)

def transport (r : BirthRecord s a) (eq : s = t) : BirthRecord t a := eq ▸ r

theorem transport_back_apply (r : BirthRecord t a) (eq : s = t)
    (f : Transition q s) (x : q.Point) :
    (r.transport eq.symm).birth (f.points.toFun x) =
      r.birth ((f.transport rfl eq).points.toFun x) := by cases eq; rfl

noncomputable def successor (r : BirthRecord s b) (Label : Type 1) (h : b < a) :
    BirthRecord (s.next Label) a where
  birth := s.nextBirth Label r.birth (inside a) (outside a) (BirthLabels.top a)
  bounded := s.nextBirth_le Label r.birth (inside a) (outside a) (BirthLabels.top a)
    (fun x n => lt_of_le_of_lt (r.bounded x) (top_before h n))
    (inside_before a) (outside_top a)
  old_meet := s.nextBirth_old_meet Label r.birth (inside a) (outside a) (BirthLabels.top a)
    (fun x n => lt_of_le_of_lt (r.bounded x) (top_before h n))
    (inside_before a) (outside_top a) (inside_increasing a) (outside_increasing a) r.old_meet

theorem successor_original (r : BirthRecord s b) (Label : Type 1) (h : b < a) (x : s.Point) :
    (r.successor Label h).birth ((s.nextTransition Label).points.toFun x) = r.birth x :=
  s.nextBirth_original Label r.birth (inside a) (outside a) (BirthLabels.top a) x

theorem successor_source (r : BirthRecord s b) (Label : Type 1) (h : b < a)
    (x : (s.next Label).Point) :
    (∃ y, (s.nextTransition Label).points.toFun y = x ∧
      (r.successor Label h).birth x = r.birth y) ∨ main ((r.successor Label h).birth x) = a :=
  s.nextBirth_source Label a r.birth x

end BirthRecord

namespace Diagram
variable {a : Column} (d : Diagram (Set.Iio a))
    (seed : ∀ i, BirthRecord (d.stage i) i.val)

def BirthCoherent : Prop := ∀ {i j} (h : i ≤ j) x,
  (seed j).birth ((d.transition h).points.toFun x) = (seed i).birth x

variable (coherent : d.BirthCoherent seed)

noncomputable def unionRecordedBirth : d.orders.system.Union → Index :=
  d.orders.system.descend (fun i => (seed i).birth) coherent

theorem unionRecordedBirth_stage (i : Set.Iio a) (x : (d.stage i).Point) :
    d.unionRecordedBirth seed coherent (d.orders.system.point i x) = (seed i).birth x := rfl

theorem unionRecordedBirth_before (x : d.orders.system.Union) :
    d.unionRecordedBirth seed coherent x < BirthLabels.top a := by
  rcases d.orders.system.cover x with ⟨i, x, rfl⟩
  apply lt_of_le_of_lt ((seed i).bounded x)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl i.property)

theorem unionRecordedBirth_old_meet :
    OldMeet (P := d.orders.unionOrder) (d.unionRecordedBirth seed coherent) :=
  oldMeet_of_covered_stages (fun i => (d.stage i).order)
    (d.unionRecordedBirth seed coherent) (fun i => (seed i).birth) d.orders.inclusion
    (fun _ _ => rfl) (d.orders.system.pair_cover d.orders.system) (fun i => (seed i).old_meet)

variable [Nonempty (Set.Iio a)]

noncomputable def limitBirthRecord : BirthRecord d.limit a where
  birth := FixedTop.birth (d.unionRecordedBirth seed coherent) (BirthLabels.top a)
  bounded := FixedTop.birth_le _ _ (d.unionRecordedBirth_before seed coherent)
  old_meet := FixedTop.old_meet_preserved d.orders.unionOrder _ _
    (d.unionRecordedBirth_before seed coherent) (d.unionRecordedBirth_old_meet seed coherent)

theorem limitBirthRecord_stage (i : Set.Iio a) (x : (d.stage i).Point) :
    (d.limitBirthRecord seed coherent).birth ((d.limitTransition i).points.toFun x) =
      (seed i).birth x := rfl

theorem limitBirthRecord_source (x : d.limit.Point) :
    (∃ i y, (d.limitTransition i).points.toFun y = x ∧
      (d.limitBirthRecord seed coherent).birth x = (seed i).birth y) ∨
      main ((d.limitBirthRecord seed coherent).birth x) = a := by
  cases x with
  | none => exact Or.inr rfl
  | some x =>
    rcases d.orders.system.cover x with ⟨i, y, rfl⟩
    exact Or.inl ⟨i, y, rfl, rfl⟩

end Diagram
end



section

open CountableColumns
universe u

namespace Diagram.Cone
variable {I : Type u} [LinearOrder I] {d : Diagram I}

theorem leg_transport {c e : d.Cone} (eq : c = e) (i : I) :
    (c.leg i).transport rfl (congrArg Diagram.Cone.apex eq) = e.leg i := by cases eq; rfl

end Diagram.Cone

theorem ordinalStep_last_leg (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a))
    (last : Set.Iio a) (greatest : ∀ i, i ≤ last) :
    ((ordinalStep Label a d).leg last).transport rfl (ordinalStep_last Label a d last greatest) =
      (d.stage last).nextTransition Label := by
  classical
  have inhabited : Nonempty (Set.Iio a) := ⟨last⟩
  have hasLast : ∃ last : Set.Iio a, ∀ i, i ≤ last := ⟨last, greatest⟩
  have chosen : hasLast.choose = last := le_antisymm (greatest _) (hasLast.choose_spec last)
  have eq : ordinalStep Label a d =
      (d.lastCone last greatest).extend (d := d) ((d.stage last).nextTransition Label) := by
    simp only [ordinalStep, dite_eq_left inhabited, dite_eq_left hasLast]
    let build (p : {last : Set.Iio a // ∀ i, i ≤ last}) : d.Cone :=
      (d.lastCone p.val p.property).extend (d := d) ((d.stage p.val).nextTransition Label)
    change build ⟨hasLast.choose, hasLast.choose_spec⟩ = build ⟨last, greatest⟩
    exact congrArg build (Subtype.ext chosen)
  have maps := Diagram.Cone.leg_transport eq last
  have same : (((d.lastCone last greatest).extend (d := d)
      ((d.stage last).nextTransition Label)).leg last) = (d.stage last).nextTransition Label := by
    change (d.transition (greatest last)).comp ((d.stage last).nextTransition Label) = _
    rw [d.self, Transition.identity_comp]
  exact maps.trans same

namespace OrdinalRun
variable (Label : Type 1)

theorem transition_successor (a : Column) :
    (transition Label (lt_start a).le).transport rfl (stage_successor Label a) =
      (stage Label a).nextTransition Label := by
  have maps := Transfinite.transition_generated (ordinalStep Label) (start a) (predecessor a)
  have lifted := congrArg (fun f => f.transport rfl
    (ordinalStep_successor Label a (before Label (start a)))) maps
  erw [Transition.transport_twice] at lifted
  exact lifted.trans (ordinalStep_last_leg Label (start a) (before Label (start a))
    (predecessor a) (predecessor_greatest a))

end OrdinalRun

end




open CountableColumns BirthLabels

namespace Diagram
variable {a : Column} (d : Diagram (Set.Iio a)) (c : d.Cone)
    (seed : ∀ i, BirthRecord (d.stage i) i.val)

structure ConeBirth where
  record : BirthRecord c.apex a
  preserves : ∀ i x, record.birth ((c.leg i).points.toFun x) = (seed i).birth x
  source : ∀ x,
    (∃ i y, (c.leg i).points.toFun y = x ∧ record.birth x = (seed i).birth y) ∨
      main (record.birth x) = a

variable (coherent : d.BirthCoherent seed)

noncomputable def nextConeBirth (Label : Type 1) (last : Set.Iio a) (greatest : ∀ i, i ≤ last) :
    d.ConeBirth ((d.lastCone last greatest).extend (d := d)
      ((d.stage last).nextTransition Label)) seed where
  record := (seed last).successor Label last.property
  preserves i x := ((seed last).successor_original Label last.property
    ((d.transition (greatest i)).points.toFun x)).trans (coherent (greatest i) x)
  source x := by
    rcases (seed last).successor_source Label last.property x with ⟨y, eq, born⟩ | fresh
    · left
      refine ⟨last, y, ?_, born⟩
      change ((d.stage last).nextTransition Label).points.toFun
        ((d.transition (greatest last)).points.toFun y) = x
      rw [d.self]
      exact eq
    · exact Or.inr fresh

noncomputable def limitConeBirth [Nonempty (Set.Iio a)] : d.ConeBirth d.limitCone seed where
  record := d.limitBirthRecord seed coherent
  preserves := d.limitBirthRecord_stage seed coherent
  source := d.limitBirthRecord_source seed coherent

end Diagram

noncomputable def ordinalConeBirth (Label : Type 1) (a : Column) (d : Diagram (Set.Iio a))
    (seed : ∀ i, BirthRecord (d.stage i) i.val) (coherent : d.BirthCoherent seed) :
    d.ConeBirth (ordinalStep Label a d) seed := by
  classical
  unfold ordinalStep
  split
  · rename_i inhabited
    split
    · rename_i hasLast
      exact d.nextConeBirth seed coherent Label hasLast.choose hasLast.choose_spec
    · letI := inhabited
      exact d.limitConeBirth seed coherent
  · rename_i empty
    exact {
      record := BirthRecord.constant initial a
      preserves := fun i => False.elim (empty ⟨i⟩)
      source := fun _ => Or.inr rfl }






namespace Diagram.ConeBirth
variable {a : Column} {d : Diagram (Set.Iio a)} {c : d.Cone}
    {seed : ∀ i, BirthRecord (d.stage i) i.val} (r : d.ConeBirth c seed)

include r in
theorem pullback (t : MainStage.{1}) (eq : t = c.apex)
    (leg : ∀ i, Transition (d.stage i) t)
    (same : ∀ i, (leg i).transport rfl eq = c.leg i) :
    ∃ q : BirthRecord t a,
      (∀ i x, q.birth ((leg i).points.toFun x) = (seed i).birth x) ∧
      (∀ x, (∃ i y, (leg i).points.toFun y = x ∧ q.birth x = (seed i).birth y) ∨
        main (q.birth x) = a) := by
  cases eq
  have maps (i : Set.Iio a) : leg i = c.leg i := same i
  refine ⟨r.record, ?_, ?_⟩
  · intro i x
    rw [maps]
    exact r.preserves i x
  · intro x
    rcases r.source x with ⟨i, y, eq, born⟩ | fresh
    · exact Or.inl ⟨i, y, (congrArg (fun f => f.points.toFun y) (maps i)).trans eq, born⟩
    · exact Or.inr fresh

end Diagram.ConeBirth

namespace OrdinalRun
variable (Label : Type 1) (a : Column)

abbrev EarlierBirths := ∀ i : Set.Iio a, BirthRecord (stage Label i.val) i.val

def EarlierCoherent (seed : EarlierBirths Label a) : Prop :=
  (before Label a).BirthCoherent seed

variable (seed : EarlierBirths Label a) (coherent : EarlierCoherent Label a seed)

include coherent in
theorem birth_extension_exists :
    ∃ q : BirthRecord (stage Label a) a,
      (∀ i x, q.birth ((transition Label i.property.le).points.toFun x) = (seed i).birth x) ∧
      (∀ x, (∃ i y, (transition Label i.property.le).points.toFun y = x ∧
        q.birth x = (seed i).birth y) ∨ main (q.birth x) = a) :=
  (ordinalConeBirth Label a (before Label a) seed coherent).pullback (stage Label a)
    (Transfinite.stage_generated (ordinalStep Label) a)
    (fun i => transition Label i.property.le)
    (Transfinite.transition_generated (ordinalStep Label) a)

noncomputable def extendBirths : BirthRecord (stage Label a) a :=
  Classical.choose (birth_extension_exists Label a seed coherent)

theorem extendBirths_preserves (i : Set.Iio a) (x : (stage Label i.val).Point) :
    (extendBirths Label a seed coherent).birth ((transition Label i.property.le).points.toFun x) =
      (seed i).birth x :=
  (Classical.choose_spec (birth_extension_exists Label a seed coherent)).1 i x

theorem extendBirths_source (x : (stage Label a).Point) :
    (∃ i y, (transition Label i.property.le).points.toFun y = x ∧
      (extendBirths Label a seed coherent).birth x = (seed i).birth y) ∨
      main ((extendBirths Label a seed coherent).birth x) = a :=
  (Classical.choose_spec (birth_extension_exists Label a seed coherent)).2 x

end OrdinalRun

end PartitionPilot.Compression.RecursiveMaps.MainStage

end OAI
