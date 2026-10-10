import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainSuccessorSeparation

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P m one r A)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "generators" => M.externalChildGenerators G letters m one
local notation "oldActors" => M.externalOldInclusion G letters m one
local notation "copyGraph" => completion.externalCopyGraph P r μ A (M.externalGroupIdentity G letters m one)
local notation "e" => completion.externalOriginalEmbedding P r μ A
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original) action 1
local notation "newAction" => completion.externalPointAction P r μ A
local notation "newOrder" => completion.externalPointOrder P r μ A
local notation "newMeet" => completion.externalPointMeet P r μ A
local notation "up" => completion.algebra.union.meet.toSmallMeetOrder
include data group oldAction pairing unions powers separation infinite hG hP

theorem external_rectangle_actor_pair {c b d g h k l : ZFSet.{u}}
    (eligible : ExternalRectangleCode P G r μ A c b d g h)
    (gen1 : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (externalRectangleCode c b d g h)) (natSetCode 0)) k ∈ generators)
    (gen2 : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (externalRectangleCode c b d g h)) (natSetCode 1)) l ∈ generators) :
    RectangleActorPairCode P μ A Q (M.externalGroupCarrier G letters m one)
      newOrder newMeet newAction e oldActors c b d g h k l := by
  let := group.toGroup
  let z := SetMembers.ofMem (externalRectangleCode c b d g h)
    ((externalRectangleCode_mem P G r μ A c b d g h).2 eligible)
  let rect := completion.externalRectangle group oldAction data.original z
  have tuple : externalRectangleCode (SetMembers.raw rect.C) (SetMembers.raw rect.B) (SetMembers.raw rect.D)
      (SetMembers.raw rect.first) (SetMembers.raw rect.second) = externalRectangleCode c b d g h := by
    simpa only [z, SetMembers.raw_ofMem] using (completion.externalRectangle_fields group oldAction data.original z)
  have fields := externalRectangleCode_inj.1 tuple
  have gen1' : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators := by
    simpa only [z, SetMembers.raw_ofMem] using gen1
  have gen2' : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators := by
    simpa only [z, SetMembers.raw_ofMem] using gen2
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have hk := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen1)).2
  have hl := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen2)).2
  have copied {x x' : ZFSet.{u}} (image : ZFSet.pair x x' ∈ e) : ZFSet.pair x x' ∈ copyGraph :=
    ((completion.externalOriginalEmbedding_entry_iff P r μ A x x').1 image).1
  have value (u : SetMembers U) {x x' : ZFSet.{u}} (same : SetMembers.raw u = x)
      (image : ZFSet.pair x x' ∈ e) : x' = (q).encode ((root).toFun u) :=
    (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG u x').1
      (same.symm ▸ copied image)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro c' _ g' _ h' _ ec ag ah
    obtain ⟨b', eb, _⟩ := ideal.injection.function.2 _ (SetMembers.raw_mem rect.B)
    have laws := data.rectangle_generators_full_ideals group oldAction pairing unions powers separation infinite hG hP
      z k l gen1' gen2' g' h' c' b'
      (fields.2.2.2.1.symm ▸ ag) (fields.2.2.2.2.symm ▸ ah) (fields.1.symm ▸ copied ec) eb
    exact ⟨laws.1, laws.2.1⟩
  · intro b' _ eb
    obtain ⟨c', ec, _⟩ := ideal.injection.function.2 _ (SetMembers.raw_mem rect.C)
    obtain ⟨g', ag, _⟩ := data.old_inclusion_injection.function.2 _ (SetMembers.raw_mem rect.first)
    obtain ⟨h', ah, _⟩ := data.old_inclusion_injection.function.2 _ (SetMembers.raw_mem rect.second)
    exact (data.rectangle_generators_full_ideals group oldAction pairing unions powers separation infinite hG hP
      z k l gen1' gen2' g' h' c' b' ag ah ec (fields.2.1.symm ▸ copied eb)).2.2
  · intro x hx v hv w hw d' hd' x' _ w' _ y _ acted met ed ex ew acted'
    let xu := SetMembers.ofMem x (data.original.subset hx)
    let vu := SetMembers.ofMem v (data.original.subset hv)
    let wu := SetMembers.ofMem w (data.original.subset hw)
    have eqD := value rect.D fields.2.2.1 ed
    have eqX := value xu (by simp only [xu, SetMembers.raw_ofMem]) ex
    have eqW := value wu (by simp only [wu, SetMembers.raw_ofMem]) ew
    have actEq : (((action).iso rect.first).toFun rect.C) = vu :=
      (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet rect.first rect.C vu).2
        (by simpa only [fields.2.2.2.1, fields.1, vu, SetMembers.raw_ofMem] using
          (data.original.action g c eligible.1 v).2 acted)
    have meetEq : (up).meet vu xu = wu :=
      (completion.algebra.union.meet.toSmallMeetOrder_meet_eq_iff vu xu wu).2
        (by simpa only [vu, xu, wu, SetMembers.raw_ofMem] using (data.original.meet v hv x hx w).2 met)
    obtain ⟨other, otherAct, _⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hl, hd'⟩)
    rw [eqD] at acted' otherAct
    have laws := data.rectangle_generators_root_meets group oldAction pairing unions powers separation infinite hG
      z xu k l gen1' gen2' y other acted' otherAct
    dsimp only [rect] at actEq
    simpa only [actEq, meetEq, ← eqX, ← eqW] using laws.1
  · intro x hx v hv w hw d' hd' x' _ w' _ y _ acted met ed ex ew acted'
    let xu := SetMembers.ofMem x (data.original.subset hx)
    let vu := SetMembers.ofMem v (data.original.subset hv)
    let wu := SetMembers.ofMem w (data.original.subset hw)
    have eqD := value rect.D fields.2.2.1 ed
    have eqX := value xu (by simp only [xu, SetMembers.raw_ofMem]) ex
    have eqW := value wu (by simp only [wu, SetMembers.raw_ofMem]) ew
    have actEq : (((action).iso rect.second).toFun rect.C) = vu :=
      (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet rect.second rect.C vu).2
        (by simpa only [fields.2.2.2.2, fields.1, vu, SetMembers.raw_ofMem] using
          (data.original.action h c eligible.1 v).2 acted)
    have meetEq : (up).meet vu xu = wu :=
      (completion.algebra.union.meet.toSmallMeetOrder_meet_eq_iff vu xu wu).2
        (by simpa only [vu, xu, wu, SetMembers.raw_ofMem] using (data.original.meet v hv x hx w).2 met)
    obtain ⟨other, otherAct, _⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hk, hd'⟩)
    rw [eqD] at acted' otherAct
    have laws := data.rectangle_generators_root_meets group oldAction pairing unions powers separation infinite hG
      z xu k l gen1' gen2' other y otherAct acted'
    dsimp only [rect] at actEq
    simpa only [actEq, meetEq, ← eqX, ← eqW] using laws.2
  · intro b' _ d' _ y _ v _ w _ eb ed act1 act2 actB
    have eqB := value rect.B fields.2.1 eb
    have eqD := value rect.D fields.2.2.1 ed
    rw [eqD] at act1 act2
    rw [eqB] at actB
    have laws := data.rectangle_generators_meet group oldAction pairing unions powers separation infinite hG
      z k l gen1' gen2' y v w act1 act2 actB
    dsimp only [rect] at eqB
    simpa only [← eqB] using laws

theorem externalBounded_rectangle_fulfillment :
    RectangleFulfillmentCode P G r μ A (completion.externalBoundedCarrier P r μ A)
      (M.externalGroupCarrier G letters m one) (completion.externalBoundedOrder P r μ A)
      (completion.externalBoundedMeet P r μ A) (completion.externalBoundedAction P r μ A) e oldActors := by
  intro c _ b _ d _ g _ h _ eligible
  have hz := (externalRectangleCode_mem P G r μ A c b d g h).2 eligible
  have letter1 := (rectangle_child_iff I P (externalRectangles P G r μ A)
    (externalRectangleCode c b d g h) (natSetCode 0)).2 ⟨hz, Or.inl rfl⟩
  have letter2 := (rectangle_child_iff I P (externalRectangles P G r μ A)
    (externalRectangleCode c b d g h) (natSetCode 1)).2 ⟨hz, Or.inr rfl⟩
  obtain ⟨k, gen1, _⟩ := data.generators_injection.function.2 _ letter1
  obtain ⟨l, gen2, _⟩ := data.generators_injection.function.2 _ letter2
  have hk := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen1)).2
  have hl := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen2)).2
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  refine ⟨k, hk, l, hl, ?_⟩
  exact (data.external_rectangle_actor_pair group oldAction pairing unions powers separation infinite hG hP
    eligible gen1 gen2).fixedTop geometry.meet geometry.action.function
    (fun _ _ image => data.externalOriginal_image_mem group oldAction pairing unions powers separation infinite hG hP image)

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end

end OAI
