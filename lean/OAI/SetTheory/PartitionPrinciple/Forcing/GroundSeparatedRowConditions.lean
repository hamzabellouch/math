import OAI.SetTheory.PartitionPrinciple.Forcing.GroundOutsideRowNames

namespace OAI

section

namespace PartitionPilot.Forcing.PosetAction

universe u
variable {G L : Type u} [Group G] [PartialOrder L]

theorem moved_ne_of_separated (a : PosetAction G L) (g : G) (B D i : L)
    (overlap : ∀ x, x ≤ D → x ≤ a.iso g D → x ≤ B)
    (inside : i ≤ D) (outside : ¬ i ≤ B) : a.iso g i ≠ i := by
  intro fixed
  have moved := (a.iso g).monotone inside
  rw [fixed] at moved
  exact outside (overlap i inside moved)

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowAction_agree_of_separated
    (g : G) (B D : L)
    (fixed : g ∈ a.principalFix B)
    (overlap : ∀ x, x ≤ D → x ≤ a.iso g D → x ≤ B)
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
      (natSetCode 2) ZFSet.omega))
    (bound : ∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
      rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    ∀ x y z, ZFSet.pair x y ∈ SetMembers.raw p →
      ZFSet.pair x z ∈ SetMembers.raw (act.iso g p) → y = z := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act x y z left right
  have code := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega p).2.1
  have transported := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega (act.iso g p)).2.1
  have coords := (ZFSet.pair_mem_prod.1 (code.shape left)).1
  have hz := (ZFSet.pair_mem_prod.1 (transported.shape right)).2
  obtain ⟨j, hj, c, hc, rfl⟩ := ZFSet.mem_prod.1 coords
  obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier j).1 hj
  have inside := bound i (row_mem_rowUsedRows code left)
  have movedInside := M.internalRowAction_usedRows_bounded a s b C pairing unions powers separation
    infinite hL hC hG graph g p D bound i (row_mem_rowUsedRows transported right)
  have pointFixed := fixed i.val (overlap i.val inside movedInside)
  have sameEntry : ZFSet.pair (ZFSet.pair (s.encode i.val) c) z ∈ SetMembers.raw p := by
    apply (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p i c z hc hz).1
    rw [pointFixed]
    exact right
  exact code.unique _ y z left sameEntry

theorem internalRowAction_common_extension_of_separated
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (g : G) (B D : L)
    (fixed : g ∈ a.principalFix B)
    (overlap : ∀ x, x ≤ D → x ≤ a.iso g D → x ≤ B)
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
      (natSetCode 2) ZFSet.omega))
    (bound : ∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
      rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    ∃ r : SetMembers (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
        (natSetCode 2) ZFSet.omega),
      SetMembers.raw r = SetMembers.raw p ∪ SetMembers.raw (act.iso g p) ∧
      r ≤ p ∧ r ≤ act.iso g p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act
  exact M.countableFunction_common_extension pairing unions powers separation infinite choice
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) p (act.iso g p)
    (M.internalRowAction_agree_of_separated a s b C pairing unions powers separation infinite
      hL hC hG graph g B D fixed overlap p bound)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
