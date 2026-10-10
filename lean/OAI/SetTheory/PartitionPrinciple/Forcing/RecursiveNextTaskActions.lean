import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveNextMapInputs

namespace OAI

section

namespace PartitionPilot.Forcing

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}

def RecursiveRepresentativeCompatibility
    (_h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A) (T : ZFSet.{u}) : Prop :=
  ∀ g i j a u v x y z, ZFSet.pair (ZFSet.pair g i) j ∈ T →
    ZFSet.pair i a ∈ Sources → ZFSet.pair i u ∈ Reps → ZFSet.pair j v ∈ Reps →
    x ∈ d.batchCarrier → ZFSet.pair x a ∈ d.batchOrder →
    ZFSet.pair (ZFSet.pair u x) y ∈ A → ZFSet.pair (ZFSet.pair v x) z ∈ A →
      ZFSet.pair (ZFSet.pair g y) z ∈ A

namespace CodedRecursiveTaskAction

variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T)

theorem toTaskSymmetry_compatible (compatible : RecursiveRepresentativeCompatibility h T)
    (g : {g : ZFSet.{u} // g ∈ G}) (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh)
    (below : d.templates.extension.le x (.inl (h.toInputs.source i))) :
    (s.toTaskSymmetry g).current.toFun ((h.toInputs.representative i).toFun x) =
      (h.toInputs.representative ((s.toTaskSymmetry g).perm i)).toFun x := by
  apply d.coding.encode_injective
  exact h.action.toSetAction.entry_unique
    (s.toTaskSymmetry_current_entry g ((h.toInputs.representative i).toFun x))
    (compatible g.val i.val ((s.toTaskSymmetry g).perm i).val (h.source i).val
      (h.actor i).val (h.actor ((s.toTaskSymmetry g).perm i)).val
      (d.coding.encode x) _ _ (s.toTaskSymmetry_perm_entry g i)
      (h.source_entry i) (h.actor_entry i) (h.actor_entry ((s.toTaskSymmetry g).perm i))
      (d.coding.encode_mem x) ((d.coding.le_encode x (.inl (h.toInputs.source i))).2 below)
      (h.toInputs_representative_entry i x)
      (h.toInputs_representative_entry ((s.toTaskSymmetry g).perm i) x))

include s in
theorem liftSection_equivariant (M : TransitiveGround.{u}) (next : h.NextInputs M)
    (compatible : RecursiveRepresentativeCompatibility h T)
    {g i j x y z : ZFSet.{u}} (transport : ZFSet.pair (ZFSet.pair g i) j ∈ T)
    (first : ZFSet.pair x y ∈ h.liftSection M next i)
    (second : ZFSet.pair x z ∈ h.liftSection M next j) :
    ZFSet.pair (ZFSet.pair g y) z ∈ h.nextActionGraph T := by
  have shape := s.taskAction.entry_shape transport
  let actor : {g : ZFSet.{u} // g ∈ G} := ⟨g, shape.1⟩
  let index : {i : ZFSet.{u} // i ∈ I} := ⟨i, shape.2.1⟩
  let target : {i : ZFSet.{u} // i ∈ I} := ⟨j, shape.2.2⟩
  have perm : (s.toTaskSymmetry actor).perm index = target :=
    Subtype.ext (s.taskAction.entry_unique (s.toTaskSymmetry_perm_entry actor index) transport)
  have hx := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next shape.2.1).1 first)).1
  obtain ⟨X, rfl⟩ := d.coding.encode_surjective x hx
  rw [(h.liftSection_entry_iff M next index X y).1 first,
    (h.liftSection_entry_iff M next target X z).1 second]
  have equation := (s.toTaskSymmetry actor).lift_equivariant
    (s.toTaskSymmetry_compatible compatible actor) index X
  rw [perm] at equation
  have entry := s.nextAction_entry M next actor (h.toInputs.lift index X)
  rwa [equation] at entry

end CodedRecursiveTaskAction

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.CodedRecursiveTaskAction

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T)

include s in
theorem nextTaskAction_of_family (M : TransitiveGround.{u}) (next : h.NextInputs M)
    (compatible : RecursiveRepresentativeCompatibility h T)
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔
      i ∈ I ∧ f = h.liftSection M next i)
    (inputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T)) : CodedRecursiveTaskAction inputs T := by
  refine ⟨s.taskAction, s.source, ?_⟩
  intro g i j f f' x y z transport firstFamily secondFamily first second
  obtain ⟨_, rfl⟩ := (entries i f).1 firstFamily
  obtain ⟨_, rfl⟩ := (entries j f').1 secondFamily
  exact s.liftSection_equivariant M next compatible transport first second

end PartitionPilot.Forcing.CodedRecursiveTaskAction

end

end OAI
