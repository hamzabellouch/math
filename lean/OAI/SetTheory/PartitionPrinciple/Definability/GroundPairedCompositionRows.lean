import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparationFamilyImages

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem exists_pairedCompositionRow {I a R U B C H J F e g : ZFSet.{u}}
    (hI : I ∈ M.sets) (ha : a ∈ M.sets) (hR : R ∈ M.sets) (hU : U ∈ M.sets)
    (hB : B ∈ M.sets) (hC : C ∈ M.sets) (hH : H ∈ M.sets) (hJ : J ∈ M.sets)
    (hF : F ∈ M.sets) (he : e ∈ M.sets) (hg : g ∈ M.sets)
    (function : ZFSet.IsFunc I (ZFSet.prod R R) F) :
    ∃ row ∈ M.sets, FunctionGraphOn (ZFSet.prod {a} I) row ∧
      ∀ i f k z, ZFSet.pair i (ZFSet.pair f k) ∈ F →
        (ZFSet.pair (ZFSet.pair a i) z ∈ row ↔
          z = ZFSet.pair (relationCompose U B C f e) (relationCompose U H J k g)) := by
  let first := relationCompose I (ZFSet.prod R R) R F (productFirst R R)
  let second := relationCompose I (ZFSet.prod R R) R F (productSecond R R)
  have hRR := M.prod_mem pairing unions powers separation hR hR
  have firstGround : first ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hI hRR hR hF (M.productFirst_mem pairing unions powers separation hR hR)
  have secondGround : second ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hI hRR hR hF (M.productSecond_mem pairing unions powers separation hR hR)
  have firstFunction : ZFSet.IsFunc I R first :=
    relationCompose_function_of_subset function (productFirst_function R R) (fun _ h => h)
  have secondFunction : ZFSet.IsFunc I R second :=
    relationCompose_function_of_subset function (productSecond_function R R) (fun _ h => h)
  have entries (i f k : ZFSet.{u}) (entry : ZFSet.pair i (ZFSet.pair f k) ∈ F) :
      ZFSet.pair i f ∈ first ∧ ZFSet.pair i k ∈ second := by
    obtain ⟨hi, pairBound⟩ := ZFSet.pair_mem_prod.1 (function.1 entry)
    obtain ⟨hf, hk⟩ := ZFSet.pair_mem_prod.1 pairBound
    exact ⟨(pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hi, hf, _, pairBound, entry,
      (mem_productFirst R R _).2 ⟨f, hf, k, hk, rfl⟩⟩,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hi, hk, _, pairBound, entry,
      (mem_productSecond R R _).2 ⟨f, hf, k, hk, rfl⟩⟩⟩
  have hA : ({a} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing ha ha
  have hK := M.prod_mem pairing unions powers separation hA hI
  have one := M.groundPairCompositions_spec pairing unions powers separation
    hK hA hI hU hB hC firstGround
    (M.constantFamilyGraph_mem pairing unions powers separation hA he)
    ⟨R, firstFunction⟩ ⟨{e}, constantFamilyGraph_function {a} e⟩ (fun _ h => h)
  have two := M.groundPairCompositions_spec pairing unions powers separation
    hK hA hI hU hH hJ secondGround
    (M.constantFamilyGraph_mem pairing unions powers separation hA hg)
    ⟨R, secondFunction⟩ ⟨{g}, constantFamilyGraph_function {a} g⟩ (fun _ h => h)
  let row := pairedGraph (ZFSet.prod {a} I) (M.groundRelations U C) (M.groundRelations U J)
    (M.groundPairCompositions (ZFSet.prod {a} I) {a} I U B C first (constantFamilyGraph {a} e))
    (M.groundPairCompositions (ZFSet.prod {a} I) {a} I U H J second (constantFamilyGraph {a} g))
  have rowFunction := pairedGraph_function_of_subset one.2.1 two.2.1 (fun _ h => h)
  refine ⟨row, M.pairedGraph_mem pairing unions powers separation hK
    (M.groundRelations_mem pairing unions powers separation hU hC)
    (M.groundRelations_mem pairing unions powers separation hU hJ) one.1 two.1,
    ⟨_, rowFunction⟩, ?_⟩
  intro i f k z entry
  have hi := (ZFSet.pair_mem_prod.1 (function.1 entry)).1
  have keyMember : ZFSet.pair a i ∈ ZFSet.prod {a} I := ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hi⟩
  have left := one.2.2 a i f e (relationCompose U B C f e) (entries i f k entry).1
    ((pair_mem_constantFamilyGraph {a} e a e).2 ⟨ZFSet.mem_singleton.2 rfl, rfl⟩)
  have right := two.2.2 a i k g (relationCompose U H J k g) (entries i f k entry).2
    ((pair_mem_constantFamilyGraph {a} g a g).2 ⟨ZFSet.mem_singleton.2 rfl, rfl⟩)
  have leftEntry := left.2 ⟨keyMember, rfl⟩
  have rightEntry := right.2 ⟨keyMember, rfl⟩
  have actual : ZFSet.pair (ZFSet.pair a i)
      (ZFSet.pair (relationCompose U B C f e) (relationCompose U H J k g)) ∈ row :=
    (pair_mem_pairedGraph _ _ _ _ _ _ _ _).2 ⟨keyMember,
      (ZFSet.pair_mem_prod.1 (one.2.1.1 leftEntry)).2,
      (ZFSet.pair_mem_prod.1 (two.2.1.1 rightEntry)).2, leftEntry, rightEntry⟩
  exact ⟨fun hz => (FunctionGraphOn.unique ⟨_, rowFunction⟩ hz actual), fun equal => equal.symm ▸ actual⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
