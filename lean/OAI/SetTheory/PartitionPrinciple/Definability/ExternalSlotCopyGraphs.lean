import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalTileSlotSupports

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def externalSlotCopyGraph
    (V E I U B action images j : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ V, ∃ u ∈ U, ∃ y ∈ B, ∃ w ∈ E, ∃ r ∈ I, ∃ x ∈ B,
    z = ZFSet.pair (ZFSet.pair v u) y ∧ v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r) ∧
      ZFSet.pair (ZFSet.pair (ZFSet.pair r j) u) x ∈ images ∧
      ZFSet.pair (ZFSet.pair w x) y ∈ action)
    (ZFSet.prod (ZFSet.prod V U) B)

theorem triple_mem_externalSlotCopyGraph (V E I U B action images j v u y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair v u) y ∈ externalSlotCopyGraph V E I U B action images j ↔
      v ∈ V ∧ u ∈ U ∧ y ∈ B ∧ ∃ w ∈ E, ∃ r ∈ I, ∃ x ∈ B,
        v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r) ∧
          ZFSet.pair (ZFSet.pair (ZFSet.pair r j) u) x ∈ images ∧
          ZFSet.pair (ZFSet.pair w x) y ∈ action := by
  rw [externalSlotCopyGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, u', hu, y', hy, w, hw, r, hr, x, hx, equal, rest⟩
    obtain ⟨left, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    exact ⟨hv, hu, hy, w, hw, r, hr, x, hx, rest⟩
  · rintro ⟨hv, hu, hy, w, hw, r, hr, x, hx, rest⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hu⟩, hy⟩,
      v, hv, u, hu, y, hy, w, hw, r, hr, x, hx, rfl, rest⟩

namespace BoundedFormula

def externalSlotCopyEntryFormula {n} (z V E I U B action images j one : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  exMem V (exMem U.succ (exMem B.succ.succ (exMem E.succ.succ.succ
    (exMem I.succ.succ.succ.succ (exMem B.succ.succ.succ.succ.succ
      (.conj (orderedTripleFormula (lift z) 5 4 3)
        (.conj (orderedRightTripleFormula 5 (lift one) 2 1)
          (.conj (slotImageMembershipFormula 1 (lift j) 4 0 (lift images))
            (tripleMembershipFormula 2 0 3 (lift action))))))))))

theorem truth_externalSlotCopyEntryFormula {n} (z V E I U B action images j one : Fin n)
    (env : Fin n → ZFSet.{u}) (oneEq : env one = natSetCode 1) :
    Truth (externalSlotCopyEntryFormula z V E I U B action images j one) env ↔
      env z ∈ externalSlotCopyGraph (env V) (env E) (env I) (env U) (env B)
        (env action) (env images) (env j) := by
  simp only [externalSlotCopyEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_orderedRightTripleFormula, truth_slotImageMembershipFormula, truth_tripleMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [oneEq, externalSlotCopyGraph, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨v, hv, u, hu, y, hy, _, _, _, _, _, _, equal, _⟩ := h
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hu⟩, hy⟩
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalSlotCopyGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {V E I U B action images j : ZFSet.{u}}
    (hV : V ∈ M.sets) (hE : E ∈ M.sets) (hI : I ∈ M.sets) (hU : U ∈ M.sets)
    (hB : B ∈ M.sets) (hAction : action ∈ M.sets) (hImages : images ∈ M.sets) (hj : j ∈ M.sets) :
    externalSlotCopyGraph V E I U B action images j ∈ M.sets := by
  have zero := M.empty_mem ⟨U, hU⟩
  have one : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions zero zero
  let params := extend V (extend E (extend I (extend U (extend B (extend action
    (extend images (extend j (extend (natSetCode 1) Fin.elim0))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalSlotCopyEntryFormula 0 1 2 3 4 5 6 7 8 9) params
    (Fin.cases hV (Fin.cases hE (Fin.cases hI (Fin.cases hU (Fin.cases hB
      (Fin.cases hAction (Fin.cases hImages (Fin.cases hj (Fin.cases one (fun i => Fin.elim0 i))))))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hV hU) hB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalSlotCopyEntryFormula 0 1 2 3 4 5 6 7 8 9) (extend z params))
      (ZFSet.prod (ZFSet.prod V U) B) = externalSlotCopyGraph V E I U B action images j := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_externalSlotCopyEntryFormula _ _ _ _ _ _ _ _ _ _ _ rfl]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected
end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
