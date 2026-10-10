import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFlatSuccessorFullActionGraph

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {L G : Type u} [PartialOrder L] [OrderBot L] [Group G]

theorem RowPositionBound.action (a : PosetAction G L) (s : Presentation L) (g : G)
    {mu f : ZFSet.{u}} {D : L}
    (bound : RowPositionBound mu s.nonbottom.carrier s.conditionOrder f (s.encode D)) :
    RowPositionBound mu s.nonbottom.carrier s.conditionOrder
      (rowPositionSequenceAction a s g mu f) (s.encode (a.iso g D)) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, _, _, x, hx, rfl, _, _⟩ :=
      (mem_relationCompose _ _ _ _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hi, hx⟩
  · intro i x entry
    obtain ⟨_, _, y, hy, original, moved⟩ :=
      (pair_mem_relationCompose _ _ _ _ _ i x).1 entry
    obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hy
    obtain ⟨v, hv⟩ := (s.nonbottom.mem_graph s.nonbottom (a.nonbottom.iso g) _).1 moved
    obtain ⟨same, value⟩ := ZFSet.pair_inj.1 hv
    have equal : v = y := s.nonbottom.injective same
    have lower := (s.pair_mem_conditionOrder y.val D).1 (bound.2 i _ original)
    have result := (s.pair_mem_conditionOrder (a.iso g y.val) (a.iso g D)).2
      ((a.iso g).monotone lower)
    rw [equal] at value
    exact value ▸ result

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

theorem refinementDataBound_act
    (I T S mu tuples A movedA level : ZFSet.{u}) (g : G) (C E D : L)
    (U Rf Rc u w : Name s)
    (tupleAction : ∀ f ∈ S, ∀ tau : Name s, ZFSet.pair f tau.val ∈ tuples →
      rowPositionSequenceAction d b g mu f ∈ S ∧
      ZFSet.pair (rowPositionSequenceAction d b g mu f) (a.act s g tau).val ∈ tuples)
    (bound : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val Rf.val Rc.val) u.val w.val)
      (b.encode D) ∈ stageOneDataBounds A I T S b.carrier mu b.nonbottom.carrier b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (movedMember : stageOneAssignment
      (refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
        (a.act s g U).val (a.act s g Rf).val (a.act s g Rc).val)
      (a.act s g u).val (a.act s g w).val ∈ movedA)
    (movedIndex : refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U).val (a.act s g Rf).val (a.act s g Rc).val ∈ I)
    (movedU : (a.act s g u).val ∈ T) (movedW : (a.act s g w).val ∈ T) :
    ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
        (a.act s g U).val (a.act s g Rf).val (a.act s g Rc).val)
      (a.act s g u).val (a.act s g w).val) (b.encode (d.iso g D)) ∈
      stageOneDataBounds movedA I T S b.carrier mu b.nonbottom.carrier b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples := by
  obtain ⟨_, _, _, _, _, rawE, _, fu, hfu, fw, hfw, anchor, lower,
      tupleU, tupleW, boundU, boundW⟩ :=
    (stageOneDataBounds_assignment_entry A I T S b.carrier mu b.nonbottom.carrier
      b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples _ u.val w.val (b.encode D)).1 bound
  have same : rawE = b.encode E :=
    ((refinementIndexFieldGraph_entry I b.carrier
      ![level, b.encode C, b.encode E, U.val, Rf.val, Rc.val] 2 rawE).1 anchor).2.2
  subst rawE
  obtain ⟨hfuMoved, tupleUMoved⟩ := tupleAction fu hfu u tupleU
  obtain ⟨hfwMoved, tupleWMoved⟩ := tupleAction fw hfw w tupleW
  refine (stageOneDataBounds_assignment_entry movedA I T S b.carrier mu b.nonbottom.carrier
    b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples _ _ _ _).2
    ⟨movedMember, b.encode_mem _, movedIndex, movedU, movedW,
      b.encode (d.iso g E), b.encode_mem _, rowPositionSequenceAction d b g mu fu, hfuMoved,
      rowPositionSequenceAction d b g mu fw, hfwMoved, ?_, ?_,
      tupleUMoved, tupleWMoved, boundU.action d b g, boundW.action d b g⟩
  · exact (refinementIndexFieldGraph_entry I b.carrier
      ![level, b.encode (d.iso g C), b.encode (d.iso g E),
        (a.act s g U).val, (a.act s g Rf).val, (a.act s g Rc).val] 2 _).2
      ⟨movedIndex, b.encode_mem _, rfl⟩
  · exact (b.pair_mem_conditionOrder (d.iso g E) (d.iso g D)).2
      ((d.iso g).monotone ((b.pair_mem_conditionOrder E D).1 lower))

end PartitionPilot.Forcing

end

end OAI
