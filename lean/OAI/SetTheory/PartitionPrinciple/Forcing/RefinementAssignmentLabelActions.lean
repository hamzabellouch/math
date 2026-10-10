import OAI.SetTheory.PartitionPrinciple.Models.GroundRefinementQuotientNames

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} [PartialOrder P] [OrderTop P]
variable [PartialOrder Q] [OrderTop Q] {G : Type v} [Group G]
variable (a : PosetAction G P) (e : PosetAction G Q)
variable (s : Presentation P) (upper : Presentation Q) (incl : P → Q)
variable (equivariant : ∀ g p, incl (a.iso g p) = e.iso g (incl p))
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)

include equivariant closed

theorem act_refinementAssignmentLabel (g : G) (idx movedIdx : ZFSet.{u})
    (Rf Rc : Name s)
    (occurrences : ∀ (v w : Name s) (p : Q) (_hv : v.val ∈ T) (_hw : w.val ∈ T),
      (∃ row A, upper.encode (e.iso g p) = ZFSet.pair row A ∧
        stageOneAssignment movedIdx (a.act s g v).val (a.act s g w).val ∈ A) ↔
      (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A)) :
    e.act upper g (refinementAssignmentLabel upper incl ⊤ T valid idx Rf Rc) =
      refinementAssignmentLabel upper incl ⊤ T valid movedIdx (a.act s g Rf) (a.act s g Rc) := by
  have paired (v w : Name s) :
      e.act upper g (orderedPair ⊤ (rename upper incl (refinementClass T valid Rc v))
        (rename upper incl (refinementClass T valid Rf w))) =
      orderedPair ⊤ (rename upper incl (refinementClass T valid (a.act s g Rc) (a.act s g v)))
        (rename upper incl (refinementClass T valid (a.act s g Rf) (a.act s g w))) := by
    change rename upper (e.iso g) _ = _
    rw [rename_orderedPair, (e.iso g).map_top]
    change orderedPair ⊤ (e.act upper g _) (e.act upper g _) = _
    rw [a.act_rename_of_equivariant e s upper incl equivariant,
      a.act_rename_of_equivariant e s upper incl equivariant,
      act_refinementClass a T valid closed, act_refinementClass a T valid closed]
  apply ext
  intro sigma p
  obtain ⟨sigma, rfl⟩ := (e.nameEquiv upper g).surjective sigma
  obtain ⟨p, rfl⟩ := (e.iso g).surjective p
  change Entry (e.act upper g sigma)
      (e.act upper g (refinementAssignmentLabel upper incl ⊤ T valid idx Rf Rc)) (e.iso g p) ↔
    Entry (e.act upper g sigma)
      (refinementAssignmentLabel upper incl ⊤ T valid movedIdx (a.act s g Rf) (a.act s g Rc)) (e.iso g p)
  rw [e.entry_act, entry_refinementAssignmentLabel, entry_refinementAssignmentLabel]
  constructor
  · rintro ⟨v, w, hv, hw, literal, equal⟩
    refine ⟨a.act s g v, a.act s g w, closed g v hv, closed g w hw,
      (occurrences v w p hv hw).2 literal, ?_⟩
    exact (paired v w).symm.trans (congrArg (e.act upper g) equal)
  · rintro ⟨v, w, hv, hw, literal, equal⟩
    let oldV := a.act s g⁻¹ v
    let oldW := a.act s g⁻¹ w
    have oldVmem : oldV.val ∈ T := closed g⁻¹ v hv
    have oldWmem : oldW.val ∈ T := closed g⁻¹ w hw
    have vEq : a.act s g oldV = v := a.act_inv_right s g v
    have wEq : a.act s g oldW = w := a.act_inv_right s g w
    have oldLiteral := (occurrences oldV oldW p oldVmem oldWmem).1
      (by rw [vEq, wEq]; exact literal)
    refine ⟨oldV, oldW, oldVmem, oldWmem, oldLiteral, ?_⟩
    apply (e.nameEquiv upper g).injective
    change e.act upper g _ = e.act upper g sigma
    rw [paired, vEq, wEq]
    exact equal

theorem refinementAssignmentLabel_support (idx : ZFSet.{u}) (Rf Rc : Name s)
    (K : Subgroup G)
    (occurrences : ∀ g ∈ K, ∀ (v w : Name s) (p : Q) (_hv : v.val ∈ T) (_hw : w.val ∈ T),
      (∃ row A, upper.encode (e.iso g p) = ZFSet.pair row A ∧
        stageOneAssignment idx (a.act s g v).val (a.act s g w).val ∈ A) ↔
      (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A))
    (fine : K ≤ a.stabilizer s Rf) (coarse : K ≤ a.stabilizer s Rc) :
    K ≤ e.stabilizer upper (refinementAssignmentLabel upper incl ⊤ T valid idx Rf Rc) := by
  intro g hg
  change e.act upper g _ = _
  rw [act_refinementAssignmentLabel a e s upper incl equivariant T valid closed
    g idx idx Rf Rc (occurrences g hg), fine hg, coarse hg]

theorem refinementAssignmentLabel_hs (F : NormalSubgroupFamily G)
    (children : ∀ z : Name s, z.val ∈ T → HereditarilySymmetric a s F z)
    (idx : ZFSet.{u}) (Rf Rc : Name s) (K : Subgroup G) (member : F.mem K)
    (occurrences : ∀ g ∈ K, ∀ (v w : Name s) (p : Q) (_hv : v.val ∈ T) (_hw : w.val ∈ T),
      (∃ row A, upper.encode (e.iso g p) = ZFSet.pair row A ∧
        stageOneAssignment idx (a.act s g v).val (a.act s g w).val ∈ A) ↔
      (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A))
    (fine : K ≤ a.stabilizer s Rf) (coarse : K ≤ a.stabilizer s Rc)
    (fineHS : HereditarilySymmetric a s F Rf) (coarseHS : HereditarilySymmetric a s F Rc) :
    HereditarilySymmetric e upper F
      (refinementAssignmentLabel upper incl ⊤ T valid idx Rf Rc) := by
  refine HereditarilySymmetric.mk
    (F.upward member (refinementAssignmentLabel_support a e s upper incl equivariant T valid closed
      idx Rf Rc K occurrences fine coarse)) ?_
  intro sigma p entry
  obtain ⟨v, w, hv, hw, _literal, rfl⟩ :=
    (entry_refinementAssignmentLabel upper incl ⊤ T valid idx Rf Rc sigma p).1 entry
  exact ((refinementClass_hs_of_hs a T valid closed F children Rc v coarseHS (children v hv)).rename
    e upper incl equivariant).orderedPair
      ((refinementClass_hs_of_hs a T valid closed F children Rf w fineHS (children w hw)).rename
        e upper incl equivariant)

end PartitionPilot.Forcing.Name

end OAI
