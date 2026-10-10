import Mathlib.Logic.Relation
import OAI.SetTheory.PartitionPrinciple.Geometry.Compression

namespace OAI

section

namespace PartitionPilot
universe u
variable {α : Type u} (P : MeetOrder α) (A : α → Prop)

theorem MeetOrder.meet_assoc (a b c : α) :
    P.meet (P.meet a b) c = P.meet a (P.meet b c) := by
  apply P.antisymm
  · exact P.le_meet
      (P.trans (P.meet_le_left _ _) (P.meet_le_left _ _))
      (P.le_meet (P.trans (P.meet_le_left _ _) (P.meet_le_right _ _)) (P.meet_le_right _ _))
  · exact P.le_meet
      (P.le_meet (P.meet_le_left _ _) (P.trans (P.meet_le_right _ _) (P.meet_le_left _ _)))
      (P.trans (P.meet_le_right _ _) (P.meet_le_right _ _))

def meetGeneratorStep (x y : α) : Prop := ∃ a, A a ∧ y = P.meet x a

def generatedMeetPredicate (x : α) : Prop :=
  ∃ a, A a ∧ ∃ b, Relation.ReflTransGen (meetGeneratorStep P A) a b ∧ P.le b x

theorem meetGeneratorPath_left {x y : α}
    (path : Relation.ReflTransGen (meetGeneratorStep P A) x y) (z : α) :
    Relation.ReflTransGen (meetGeneratorStep P A) (P.meet z x) (P.meet z y) := by
  apply path.lift (P.meet z)
  intro x y step
  obtain ⟨a, ha, rfl⟩ := step
  exact ⟨a, ha, (P.meet_assoc z x a).symm⟩

theorem generatedMeetPredicate_contains {x : α} (hx : A x) : generatedMeetPredicate P A x :=
  ⟨x, hx, x, .refl, P.refl x⟩

def generatedMeetFilter (nonempty : ∃ a, A a) : Compression.MeetFilter P where
  mem := generatedMeetPredicate P A
  nonempty := by
    obtain ⟨a, ha⟩ := nonempty
    exact ⟨a, generatedMeetPredicate_contains P A ha⟩
  upward := by
    rintro x y ⟨a, ha, b, path, lower⟩ xy
    exact ⟨a, ha, b, path, P.trans lower xy⟩
  closed_meet := by
    rintro x y ⟨a, ha, b, first, bx⟩ ⟨c, hc, d, second, dy⟩
    refine ⟨a, ha, P.meet b d, ?_, ?_⟩
    · exact (first.tail ⟨c, hc, rfl⟩).trans (meetGeneratorPath_left P A second b)
    · exact P.le_meet (P.trans (P.meet_le_left b d) bx) (P.trans (P.meet_le_right b d) dy)

theorem generatedMeetPredicate_least (F : Compression.MeetFilter P)
    (contains : ∀ a, A a → F.mem a) {x : α} (hx : generatedMeetPredicate P A x) : F.mem x := by
  obtain ⟨a, ha, b, path, lower⟩ := hx
  have hb : F.mem b := by
    clear lower
    induction path with
    | refl => exact contains a ha
    | tail path step ih =>
      obtain ⟨c, hc, rfl⟩ := step
      exact F.closed_meet ih (contains c hc)
  exact F.upward hb lower

theorem generatedMeetPredicate_lower_bound (e : α) (above : ∀ a, A a → P.le e a)
    {x : α} (hx : generatedMeetPredicate P A x) : P.le e x := by
  obtain ⟨a, ha, b, path, lower⟩ := hx
  have hb : P.le e b := by
    clear lower
    induction path with
    | refl => exact above a ha
    | tail path step ih =>
      obtain ⟨c, hc, rfl⟩ := step
      exact P.le_meet ih (above c hc)
  exact P.trans hb lower

end PartitionPilot

end

end OAI
