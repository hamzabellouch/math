import OAI.SetTheory.PartitionPrinciple.Forcing.GroundCountableFunctionForcing
import OAI.SetTheory.PartitionPrinciple.Models.GroundSuccessorInjections

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace PartialFunctionCode

theorem insert_entry {X Y p x y : ZFSet.{u}} (h : PartialFunctionCode X Y p)
    (hx : x ∈ X) (hy : y ∈ Y)
    (agree : ∀ z, ZFSet.pair x z ∈ p → z = y) :
    PartialFunctionCode X Y (insert (ZFSet.pair x y) p) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with eq | hz
    · exact eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
    · exact h.shape hz
  · intro a b c hb hc
    rcases ZFSet.mem_insert_iff.1 hb with eqb | oldb
    · obtain ⟨ax, by'⟩ := ZFSet.pair_inj.1 eqb
      rcases ZFSet.mem_insert_iff.1 hc with eqc | oldc
      · exact by'.trans (ZFSet.pair_inj.1 eqc).2.symm
      · exact by'.trans (agree c (ax ▸ oldc)).symm
    · rcases ZFSet.mem_insert_iff.1 hc with eqc | oldc
      · obtain ⟨ax, cy⟩ := ZFSet.pair_inj.1 eqc
        exact (agree b (ax ▸ oldb)).trans cy.symm
      · exact h.unique a b c oldb oldc

end PartialFunctionCode

namespace TransitiveGround

open SetRealization SetFormula
variable (M : TransitiveGround.{u})

theorem countablePartialFunctions_insert
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y p x y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets)
    (hp : p ∈ M.smallPartialFunctions X Y ZFSet.omega) (hx : x ∈ X) (hy : y ∈ Y)
    (agree : ∀ z, ZFSet.pair x z ∈ p → z = y) :
    insert (ZFSet.pair x y) p ∈ M.smallPartialFunctions X Y ZFSet.omega := by
  obtain ⟨hpM, code, small⟩ := (M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp
  have entry := M.orderedPair_mem pairing (M.transitive hX hx) (M.transitive hY hy)
  exact (M.mem_smallPartialFunctions X Y ZFSet.omega _).2
    ⟨M.insert_mem pairing unions entry hpM, code.insert_entry hx hy agree,
      M.groundEmbeddable_insert pairing unions powers separation infinite hpM entry small⟩

def coordinateAssigned (X Y x : ZFSet.{u}) :
    Set (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)) :=
  {p | ∃ y ∈ Y, ZFSet.pair x y ∈ SetMembers.raw p}

theorem coordinateAssigned_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y x : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets)
    (values : Y.Nonempty) (hx : x ∈ X) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    Dense (M.coordinateAssigned X Y x) := by
  classical
  let coordinateOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro p
  by_cases assigned : p ∈ M.coordinateAssigned X Y x
  · exact ⟨p, le_rfl, assigned⟩
  · obtain ⟨y, hy⟩ := values
    have code := (M.smallFunction_raw_properties X Y ZFSet.omega p).2.1
    have agree : ∀ z, ZFSet.pair x z ∈ SetMembers.raw p → z = y := by
      intro z rel
      exact False.elim (assigned ⟨z, (ZFSet.pair_mem_prod.1 (code.shape rel)).2, rel⟩)
    have extended := M.countablePartialFunctions_insert pairing unions powers separation infinite
      hX hY (SetMembers.raw_mem p) hx hy agree
    let q := SetMembers.ofMem (insert (ZFSet.pair x y) (SetMembers.raw p)) extended
    have rawq : SetMembers.raw q = insert (ZFSet.pair x y) (SetMembers.raw p) :=
      SetMembers.raw_ofMem _ _
    refine ⟨q, (M.smallFunction_le_iff X Y ZFSet.omega q p).2 ?_, ?_⟩
    · intro z hz
      rw [rawq]
      exact ZFSet.mem_insert_of_mem _ hz
    · exact ⟨y, hy, rawq.symm ▸ ZFSet.mem_insert _ _⟩

theorem coordinateAssigned_downward (X Y x : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    DownwardClosed (M.coordinateAssigned X Y x) := by
  let coordinateOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro p q le hp
  obtain ⟨y, hy, rel⟩ := hp
  exact ⟨y, hy, (M.smallFunction_le_iff X Y ZFSet.omega q p).1 le rel⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
