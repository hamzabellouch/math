import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalLocalHeightSelection

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "U" => completion.algebra.union.fields 0
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "qPoint" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)

theorem externalCopyGraph_eq_graph :
    letI := group.toGroup
    let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
    ∀ w, completion.externalCopyGraph P0 r0 μ0 A0 ((sGroup).encode w) =
      (SetMembers.presentation U).graph (qPoint) ((family).copy a w).toFun := by
  let := group.toGroup
  dsimp only
  intro w
  have classed := data.externalPointClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  have graph := flatCopyEmbeddingGraph_eq_graph (family)
    (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet)
    (sGroup) (SetMembers.presentation U) (qPoint) classed w
  rw [data.externalPointPresentation_carrier] at graph
  exact graph

include data group oldAction pairing unions powers separation infinite hG in
theorem externalCopy_ideal {w : ZFSet.{u}} (hw : w ∈ M.externalGroupCarrier G letters m one) :
    IdealEmbeddingCode U (completion.externalPointCarrier P0 r0 μ0 A0)
      (completion.algebra.union.fields 1) (completion.externalPointOrder P0 r0 μ0 A0)
      (completion.algebra.union.fields 2) (completion.externalPointMeet P0 r0 μ0 A0)
      (completion.externalCopyGraph P0 r0 μ0 A0 w) := by
  let := group.toGroup
  let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
  let s := sGroup
  let q := qPoint
  have sCarrier := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 (sCarrier.symm ▸ hw)
  have entries := data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG
  have code := (SetMembers.presentation U).idealEmbeddingCode q ((family).copy a w)
    (fun _ _ => Iff.rfl) entries.1
    (fun x y z => (completion.algebra.union.meet.toSmallMeetOrder_meet_eq_iff x y z).symm) entries.2.1
  rw [← data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG w] at code
  dsimp only [q] at code
  rw [data.externalPointPresentation_carrier] at code
  exact code

include data group oldAction pairing unions powers separation infinite hG in
theorem externalIdentityCopy_ideal :
    IdealEmbeddingCode U (completion.externalPointCarrier P0 r0 μ0 A0)
      (completion.algebra.union.fields 1) (completion.externalPointOrder P0 r0 μ0 A0)
      (completion.algebra.union.fields 2) (completion.externalPointMeet P0 r0 μ0 A0)
      (completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)) :=
  data.externalCopy_ideal group oldAction pairing unions powers separation infinite hG
    data.group.group_code.identity_mem

end PartitionPilot.Forcing.GroundExternalGeometryInputs



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "U" => completion.algebra.union.fields 0
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "qPoint" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "copyGraph" => completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)

include data group oldAction pairing unions powers separation infinite hG in
theorem externalIdentityCopy_equivariant {g g' x y x' y' : ZFSet.{u}}
    (actor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (first : ZFSet.pair x x' ∈ copyGraph) (second : ZFSet.pair y y' ∈ copyGraph)
    (acted : ZFSet.pair (ZFSet.pair g x) y ∈ completion.algebra.union.fields 12) :
    ZFSet.pair (ZFSet.pair g' x') y' ∈ completion.externalPointAction P0 r0 μ0 A0 := by
  let := group.toGroup
  let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
  rw [completion.externalFamilyGroupPresentation_old group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground] at actor
  obtain ⟨g, equal⟩ := ((SetMembers.presentation G).mem_graph (sGroup) _ _).1 actor
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  have identity := completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  rw [identity, data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG 1] at first second
  obtain ⟨x, equal⟩ := ((SetMembers.presentation U).mem_graph (qPoint) _ _).1 first
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  obtain ⟨y, equal⟩ := ((SetMembers.presentation U).mem_graph (qPoint) _ _).1 second
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  have actionEq := (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet g x y).2 acted
  have entries := data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG
  apply (entries.2.2.1 _ _ _).2
  change (((family).externalAction a).iso (old (SetMembers G) (family).Letters g)).toFun
    (((family).copy a 1).toFun x) = ((family).copy a 1).toFun y
  rw [(family).extends_old_action, actionEq]

include data group oldAction pairing unions powers separation infinite hG in
theorem externalIdentityCopy_agreement (hP : P0 ∈ M.sets)
    {g h g' h' v v' : ZFSet.{u}}
    (firstActor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (secondActor : ZFSet.pair h h' ∈ M.externalOldInclusion G letters m one)
    (image : ZFSet.pair v v' ∈ copyGraph)
    (agree : ActionAgreementBelow U (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 12) g h v) :
    ActionAgreementBelow (completion.externalPointCarrier P0 r0 μ0 A0)
      (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointAction P0 r0 μ0 A0) g' h' v' := by
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have firstShape := ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 firstActor)
  have secondShape := ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 secondActor)
  exact ideal.actionAgreementBelow completion.algebra.union.action geometry.action
    firstShape.1 firstShape.2 secondShape.2 image agree
    (fun _ _ _ _ _ _ first second acted => data.externalIdentityCopy_equivariant group oldAction
      pairing unions powers separation infinite hG firstActor first second acted)
    (fun _ _ _ _ _ _ first second acted => data.externalIdentityCopy_equivariant group oldAction
      pairing unions powers separation infinite hG secondActor first second acted)

include data group oldAction pairing unions powers separation infinite hG in
theorem externalOriginal_agreement (hP : P0 ∈ M.sets)
    {g h g' h' v v' : ZFSet.{u}}
    (firstActor : ZFSet.pair g g' ∈ M.externalOldInclusion G letters m one)
    (secondActor : ZFSet.pair h h' ∈ M.externalOldInclusion G letters m one)
    (hv : v ∈ P0) (image : ZFSet.pair v v' ∈ copyGraph)
    (agree : ActionAgreementBelow P0 r0 A0 g h v) :
    ActionAgreementBelow (completion.externalPointCarrier P0 r0 μ0 A0)
      (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointAction P0 r0 μ0 A0) g' h' v' := by
  have hg := (ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 firstActor)).1
  have hh := (ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 secondActor)).1
  exact data.externalIdentityCopy_agreement group oldAction pairing unions powers separation infinite hG hP
    firstActor secondActor image (data.original.agreement g hg h hh v hv agree)

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end

end OAI
