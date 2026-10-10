import OAI.SetTheory.PartitionPrinciple.Geometry.TileStarIncomingCodes
import OAI.SetTheory.PartitionPrinciple.Models.ExternalCopyQuotient

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation

open Forcing
universe u
variable {B : Type u} (s : Presentation B) (r : Setoid B) {E : ZFSet.{u}}
variable (equivalence : EquivalenceRelationCode s.carrier E)
variable (related : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ E ↔ r.r x y)

noncomputable def quotientEncode : Quotient r → ZFSet.{u} :=
  Quotient.lift (fun x => equivalenceClass s.carrier E (s.encode x))
    (fun x y h => (equivalence.class_eq_iff (s.encode_mem x) (s.encode_mem y)).2
      ((related x y).2 h))

theorem quotientEncode_mk (x : B) :
    s.quotientEncode r equivalence related (Quotient.mk r x) =
      equivalenceClass s.carrier E (s.encode x) := rfl

theorem quotientEncode_injective :
    Function.Injective (s.quotientEncode r equivalence related) := by
  intro q q'
  refine Quotient.inductionOn₂ q q' ?_
  intro x y equal
  exact Quotient.sound ((related x y).1
    ((equivalence.class_eq_iff (s.encode_mem x) (s.encode_mem y)).1 equal))

theorem mem_equivalenceClasses_iff_quotientEncode (C : ZFSet.{u}) :
    C ∈ equivalenceClasses s.carrier E ↔
      ∃ q, s.quotientEncode r equivalence related q = C := by
  constructor
  · intro hC
    obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClasses s.carrier E C).1 hC
    obtain ⟨b, rfl⟩ := (s.mem_carrier x).1 hx
    exact ⟨Quotient.mk r b, rfl⟩
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro x
    exact equivalenceClass_mem (s.encode_mem x)

noncomputable def quotientPresentation : Presentation (Quotient r) where
  carrier := equivalenceClasses s.carrier E
  encode := s.quotientEncode r equivalence related
  injective := s.quotientEncode_injective r equivalence related
  mem_carrier := s.mem_equivalenceClasses_iff_quotientEncode r equivalence related

theorem quotientPresentation_carrier :
    (s.quotientPresentation r equivalence related).carrier = equivalenceClasses s.carrier E := rfl

theorem quotientPresentation_encode_mk (x : B) :
    (s.quotientPresentation r equivalence related).encode (Quotient.mk r x) =
      equivalenceClass s.carrier E (s.encode x) := rfl

theorem quotientPresentation_classifier_entry_iff (x : B) (q : Quotient r) :
    ZFSet.pair (s.encode x) ((s.quotientPresentation r equivalence related).encode q) ∈
      equivalenceClassifier s.carrier E ↔ Quotient.mk r x = q := by
  rw [pair_mem_equivalenceClassifier]
  constructor
  · rintro ⟨_, equal⟩
    apply (s.quotientPresentation r equivalence related).injective
    exact equal.symm
  · rintro rfl
    exact ⟨s.encode_mem x, rfl⟩

theorem quotientClassifier_eq_graph :
    equivalenceClassifier s.carrier E =
      s.graph (s.quotientPresentation r equivalence related) (Quotient.mk r) := by
  apply ZFSet.ext
  intro z
  rw [mem_equivalenceClassifier, mem_graph]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (s.mem_carrier y).1 hy
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨s.encode x, s.encode_mem x, rfl⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u

variable (M : TransitiveGround.{u}) {B : Type u} (s : Presentation B)
variable (r : Setoid B) {E : ZFSet.{u}}
variable (equivalence : EquivalenceRelationCode s.carrier E)
variable (related : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ E ↔ r.r x y)

theorem quotientPresentation_carrier_mem
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : s.carrier ∈ M.sets) (hE : E ∈ M.sets) :
    (s.quotientPresentation r equivalence related).carrier ∈ M.sets :=
  M.equivalenceClasses_mem powers separation hA hE

theorem quotientMapGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : s.carrier ∈ M.sets) (hE : E ∈ M.sets) :
    s.graph (s.quotientPresentation r equivalence related) (Quotient.mk r) ∈ M.sets := by
  rw [← s.quotientClassifier_eq_graph r equivalence related]
  exact M.equivalenceClassifier_mem pairing unions powers separation hA hE

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps Attachment CosetGeometry
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) {steps : ZFSet.{u}}
variable (edges : ∀ x y, ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈ steps ↔ f.FlatStep a x y)
variable (hE : s.carrier ∈ M.sets) (hU : t.carrier ∈ M.sets)

include pairing unions powers separation infinite edges hE hU in
theorem flatCopyEquivalence_code :
    EquivalenceRelationCode (ZFSet.prod s.carrier t.carrier)
      (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps) :=
  M.finitePathClosure_equivalence pairing unions separation infinite (s.product t) (f.FlatStep a)
    edges (M.prod_mem pairing unions powers separation hE hU) (fun _ _ h => h.symm)

include pairing unions powers separation infinite edges hE hU in
theorem pair_mem_flatCopyEquivalence (x y : f.FlatLabel (J := J)) :
    ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈
      M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps ↔ f.FlatPath a x y :=
  M.pair_mem_finitePathClosure pairing unions separation infinite (s.product t) (f.FlatStep a)
    edges (M.prod_mem pairing unions powers separation hE hU) x y

noncomputable def flatCopyPresentation : Presentation (f.Node a) :=
  ((s.product t).quotientPresentation (f.flatSetoid a)
    (M.flatCopyEquivalence_code pairing unions powers separation infinite f a s t edges hE hU)
    (M.pair_mem_flatCopyEquivalence pairing unions powers separation infinite f a s t edges hE hU)).reindex
    (f.flatQuotientEquiv a).symm

theorem flatCopyPresentation_carrier :
    (M.flatCopyPresentation pairing unions powers separation infinite f a s t edges hE hU).carrier =
      equivalenceClasses (ZFSet.prod s.carrier t.carrier)
        (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps) := rfl

theorem flatCopyPresentation_encode_copy (w : External J f.Letters) (x : A) :
    (M.flatCopyPresentation pairing unions powers separation infinite f a s t edges hE hU).encode
      ((f.copy a w).toFun x) =
      equivalenceClass (ZFSet.prod s.carrier t.carrier)
        (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps)
        (ZFSet.pair (s.encode w) (t.encode x)) := by
  change (s.product t).quotientEncode (f.flatSetoid a)
    (M.flatCopyEquivalence_code pairing unions powers separation infinite f a s t edges hE hU)
    (M.pair_mem_flatCopyEquivalence pairing unions powers separation infinite f a s t edges hE hU)
    ((f.flatQuotientEquiv a).symm ((f.copy a w).toFun x)) = _
  rw [← f.flatQuotientEquiv_class a w x, Equiv.symm_apply_apply]
  rfl

theorem flatCopyClassifier_eq_graph :
    equivalenceClassifier (ZFSet.prod s.carrier t.carrier)
      (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps) =
    (s.product t).graph (M.flatCopyPresentation pairing unions powers separation infinite f a s t edges hE hU)
      (fun x => (f.copy a x.1).toFun x.2) := by
  apply ZFSet.ext
  intro z
  rw [mem_equivalenceClassifier, Presentation.mem_graph]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨⟨w, x⟩, rfl⟩ := ((s.product t).mem_carrier y).1 hy
    exact ⟨(w, x), by rw [M.flatCopyPresentation_encode_copy]; rfl⟩
  · rintro ⟨⟨w, x⟩, rfl⟩
    refine ⟨ZFSet.pair (s.encode w) (t.encode x), (s.product t).encode_mem (w, x), ?_⟩
    rw [M.flatCopyPresentation_encode_copy]
    rfl

theorem flatCopyPresentation_ground (hSteps : steps ∈ M.sets) :
    (M.flatCopyPresentation pairing unions powers separation infinite f a s t edges hE hU).carrier ∈ M.sets ∧
    equivalenceClassifier (ZFSet.prod s.carrier t.carrier)
      (M.finitePathClosure (ZFSet.prod s.carrier t.carrier) steps) ∈ M.sets := by
  have labels := M.prod_mem pairing unions powers separation hE hU
  have paths := M.finitePathClosure_mem pairing unions powers separation infinite labels hSteps
  exact ⟨M.equivalenceClasses_mem powers separation labels paths,
    M.equivalenceClassifier_mem pairing unions powers separation labels paths⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
