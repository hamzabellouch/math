import OAI.SetTheory.PartitionPrinciple.Forcing.ExternalAction

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.AllGeometry

open Attachment CosetGeometry
universe u
variable {A J : Type u} [Group J] {P : MeetOrder A}
variable (T : A) (greatest : ∀ x, P.le x T) (a : OrderAction J P)

noncomputable def rootEmbedding : IdealEmbedding P ((family T greatest).gluedOrder a) :=
  (family T greatest).copy a 1

noncomputable def letter (r : Request P) (j : r.Child) :
    MeetIso ((family T greatest).gluedOrder a) ((family T greatest).gluedOrder a) :=
  ((family T greatest).externalAction a).iso (generator J (Letters T greatest) ⟨r, j⟩)

theorem letter_root (r : Request P) (j : r.Child) (x : A) :
    (letter T greatest a r j).toFun ((rootEmbedding T greatest a).toFun x) =
      ((family T greatest).copy a (generator J (Letters T greatest) ⟨r, j⟩)).toFun x :=
  (family T greatest).generator_on_root a ⟨r, j⟩ x

theorem separation_letter_fixes (W x : A) (below : P.le x W) :
    (letter T greatest a (.separation W) ⟨()⟩).toFun ((rootEmbedding T greatest a).toFun x) =
      (rootEmbedding T greatest a).toFun x := by
  erw [letter_root]
  simpa only [one_mul, rootEmbedding] using separation_fixes T greatest a 1 W x below

theorem separation_letter_meet (W D X : A) (belowD : P.le W D) (belowX : P.le W X) :
    ((family T greatest).gluedOrder a).meet
      ((letter T greatest a (.separation W) ⟨()⟩).toFun ((rootEmbedding T greatest a).toFun D))
      ((rootEmbedding T greatest a).toFun X) = (rootEmbedding T greatest a).toFun W := by
  erw [letter_root]
  simpa only [one_mul, rootEmbedding] using separation_meet T greatest a 1 W D X belowD belowX

theorem compression_letter_restriction (K : A) (S : MeetIso P (idealOrder P K)) (x : A) :
    (letter T greatest a (.compression K S) ⟨()⟩).toFun ((rootEmbedding T greatest a).toFun x) =
      (rootEmbedding T greatest a).toFun (S.toFun x).val := by
  erw [letter_root]
  simpa only [one_mul, rootEmbedding] using compression_restriction T greatest a 1 K S x

theorem compression_letter_top (K : A) (S : MeetIso P (idealOrder P K)) :
    (letter T greatest a (.compression K S) ⟨()⟩).toFun ((rootEmbedding T greatest a).toFun T) =
      (rootEmbedding T greatest a).toFun K := by
  erw [letter_root]
  simpa only [one_mul, rootEmbedding] using compression_top T greatest a 1 K S

theorem compression_letter_agrees (K C : A) (S : MeetIso P (idealOrder P K)) (gamma : MeetIso P P)
    (agreement : ∀ x, P.le x C → (S.toFun x).val = gamma.toFun x) (x : A) (below : P.le x C) :
    (letter T greatest a (.compression K S) ⟨()⟩).toFun ((rootEmbedding T greatest a).toFun x) =
      (rootEmbedding T greatest a).toFun (gamma.toFun x) := by
  rw [compression_letter_restriction, agreement x below]

theorem rectangle_letters_root (r : Rectangle.Input P) (x : A) (below : P.le x r.C) :
    (letter T greatest a (.rectangle r) ⟨false⟩).toFun ((rootEmbedding T greatest a).toFun x) =
      (rootEmbedding T greatest a).toFun (r.g1.toFun x) ∧
    (letter T greatest a (.rectangle r) ⟨true⟩).toFun ((rootEmbedding T greatest a).toFun x) =
      (rootEmbedding T greatest a).toFun (r.g2.toFun x) := by
  constructor
  · erw [letter_root]
    simpa only [one_mul, rootEmbedding] using rectangle_first_agrees T greatest a 1 r x below
  · erw [letter_root]
    simpa only [one_mul, rootEmbedding] using rectangle_second_agrees T greatest a 1 r x below

theorem rectangle_letters_agree (r : Rectangle.Input P) (x : A) (below : P.le x r.B) :
    (letter T greatest a (.rectangle r) ⟨false⟩).toFun ((rootEmbedding T greatest a).toFun x) =
      (letter T greatest a (.rectangle r) ⟨true⟩).toFun ((rootEmbedding T greatest a).toFun x) := by
  erw [letter_root, letter_root]
  simpa only [one_mul] using (rectangle_children_intersection T greatest a 1 r x x).mpr ⟨below, rfl⟩

theorem rectangle_letters_meet_root (r : Rectangle.Input P) (x : A) :
    ((family T greatest).gluedOrder a).meet
      ((letter T greatest a (.rectangle r) ⟨false⟩).toFun ((rootEmbedding T greatest a).toFun r.D))
      ((rootEmbedding T greatest a).toFun x) =
      (rootEmbedding T greatest a).toFun (P.meet (r.g1.toFun r.C) x) ∧
    ((family T greatest).gluedOrder a).meet
      ((letter T greatest a (.rectangle r) ⟨true⟩).toFun ((rootEmbedding T greatest a).toFun r.D))
      ((rootEmbedding T greatest a).toFun x) =
      (rootEmbedding T greatest a).toFun (P.meet (r.g2.toFun r.C) x) := by
  constructor
  · erw [letter_root]
    simpa only [one_mul, rootEmbedding] using rectangle_first_meet_root T greatest a 1 r x
  · erw [letter_root]
    simpa only [one_mul, rootEmbedding] using rectangle_second_meet_root T greatest a 1 r x

theorem rectangle_letters_meet (r : Rectangle.Input P) :
    ((family T greatest).gluedOrder a).meet
      ((letter T greatest a (.rectangle r) ⟨false⟩).toFun ((rootEmbedding T greatest a).toFun r.D))
      ((letter T greatest a (.rectangle r) ⟨true⟩).toFun ((rootEmbedding T greatest a).toFun r.D)) =
      (letter T greatest a (.rectangle r) ⟨false⟩).toFun ((rootEmbedding T greatest a).toFun r.B) ∧
    (letter T greatest a (.rectangle r) ⟨false⟩).toFun ((rootEmbedding T greatest a).toFun r.B) =
      (letter T greatest a (.rectangle r) ⟨true⟩).toFun ((rootEmbedding T greatest a).toFun r.B) := by
  constructor
  · erw [letter_root, letter_root, letter_root]
    simpa only [one_mul] using rectangle_children_meet T greatest a 1 r
  · exact rectangle_letters_agree T greatest a r r.B (P.refl _)

end PartitionPilot.Compression.RecursiveMaps.TileRequests.AllGeometry

end

end OAI
