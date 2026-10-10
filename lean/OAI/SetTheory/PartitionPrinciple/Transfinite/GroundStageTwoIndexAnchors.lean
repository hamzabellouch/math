import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNiceRefinementVisibility

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem refinementIndexFieldGraph_union (I J B : ZFSet.{u}) (j : Fin 6) :
    refinementIndexFieldGraph (I ∪ J) B j =
      refinementIndexFieldGraph I B j ∪ refinementIndexFieldGraph J B j := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 ((ZFSet.mem_sep.1 hz).1)
    obtain ⟨hx, hy, fields, ex, ey⟩ :=
      (pair_mem_refinementIndexFieldGraph (I ∪ J) B x y j).1 hz
    rcases ZFSet.mem_union.1 hx with hi | hj
    · exact ZFSet.mem_union.2 (Or.inl ((pair_mem_refinementIndexFieldGraph I B x y j).2
        ⟨hi, hy, fields, ex, ey⟩))
    · exact ZFSet.mem_union.2 (Or.inr ((pair_mem_refinementIndexFieldGraph J B x y j).2
        ⟨hj, hy, fields, ex, ey⟩))
  · intro hz
    rcases ZFSet.mem_union.1 hz with hi | hj
    · obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 ((ZFSet.mem_sep.1 hi).1)
      obtain ⟨hx, hy, fields, ex, ey⟩ := (pair_mem_refinementIndexFieldGraph I B x y j).1 hi
      exact (pair_mem_refinementIndexFieldGraph (I ∪ J) B x y j).2
        ⟨ZFSet.mem_union.2 (Or.inl hx), hy, fields, ex, ey⟩
    · obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 ((ZFSet.mem_sep.1 hj).1)
      obtain ⟨hx, hy, fields, ex, ey⟩ := (pair_mem_refinementIndexFieldGraph J B x y j).1 hj
      exact (pair_mem_refinementIndexFieldGraph (I ∪ J) B x y j).2
        ⟨ZFSet.mem_union.2 (Or.inr hx), hy, fields, ex, ey⟩

theorem refinementIndexAnchor_union_entry {L : Type u} (b : Presentation L)
    (I J level : ZFSet.{u}) (C E : L) (U Rf Rc y : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U Rf Rc) y ∈
      refinementIndexFieldGraph (I ∪ J) b.carrier 2 ↔
    refinementIndexCode level (b.encode C) (b.encode E) U Rf Rc ∈ I ∪ J ∧ y = b.encode E := by
  rw [refinementIndexCode, refinementIndexFieldGraph_entry]
  change (_ ∈ I ∪ J ∧ y ∈ b.carrier ∧ y = b.encode E) ↔ (_ ∈ I ∪ J ∧ y = b.encode E)
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨member, rfl⟩
    exact ⟨member, b.encode_mem E, rfl⟩

namespace NiceRefinementIndexSystem
variable {M : TransitiveGround.{u}} {G P Q L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder Q] [OrderTop Q] [PartialOrder L]
variable {a : PosetAction G P} {e : PosetAction G Q}
variable {s : Presentation P} {t : Presentation Q} {b : Presentation L} {d : PosetAction G L}
variable {level next T T2 U U2 : ZFSet.{u}}
variable {valid : ∀ z ∈ T, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
variable {upperValid : ∀ z ∈ U, IsName t z} {upperValid2 : ∀ z ∈ U2, IsName t z}
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "J" => M.niceRefinementIndices e t b d next U U2 upperValid

theorem union_anchor_data
    (first : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
    (second : NiceRefinementIndexSystem M e t b d next U U2 upperValid upperValid2)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (nodes : b.carrier ∈ M.sets) :
    I ∪ J ∈ M.sets ∧ refinementIndexFieldGraph (I ∪ J) b.carrier 2 ∈ M.sets ∧
      ZFSet.IsFunc (I ∪ J) b.carrier (refinementIndexFieldGraph (I ∪ J) b.carrier 2) ∧
      refinementIndexFieldGraph (I ∪ J) b.carrier 2 =
        refinementIndexFieldGraph I b.carrier 2 ∪ refinementIndexFieldGraph J b.carrier 2 := by
  have ground := M.binary_union_mem pairing unions first.index_ground second.index_ground
  refine ⟨ground, M.refinementIndexFieldGraph_mem pairing unions powers separation ground nodes 2,
    ?_, refinementIndexFieldGraph_union I J b.carrier 2⟩
  apply refinementIndexFieldGraph_function
  intro z hz
  rcases ZFSet.mem_union.1 hz with hi | hj
  · obtain ⟨C, E, X, Rf, Rc, equal⟩ := first.decoded z hi
    exact ⟨![level, b.encode C, b.encode E, X.val.val, Rf.val.val, Rc.val.val], equal, b.encode_mem E⟩
  · obtain ⟨C, E, X, Rf, Rc, equal⟩ := second.decoded z hj
    exact ⟨![next, b.encode C, b.encode E, X.val.val, Rf.val.val, Rc.val.val], equal, b.encode_mem E⟩

end NiceRefinementIndexSystem

end PartitionPilot.Forcing

end

end OAI
