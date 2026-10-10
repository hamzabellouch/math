import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitChronologyCore

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

noncomputable def heightRangeFamily : ZFSet.{u} := familyCodeGraph run.key
  (fun i => functionGraphRange (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.height)

noncomputable def heightRangeValues : ZFSet.{u} := ZFSet.range
  (fun i => functionGraphRange (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.height)

theorem heightRangeFamily_ground : run.heightRangeFamily ∈ M.sets :=
  M.familyCodeGraph_functionRanges_ground pairing unions powers separation run.key
    (fun i => (run.diagram.stage i).stage.carrier) (fun i => (run.diagram.stage i).stage.height)
    run.key_injective run.indices_ground run.carrierFamily_ground (run.stageFieldFamily_ground 10)

theorem heightRangeFamily_function : FunctionGraphOn run.indices run.heightRangeFamily :=
  familyCodeGraph_function run.key _ run.key_injective

theorem heightRangeFamily_entry (i : I) (R : ZFSet.{u}) :
    ZFSet.pair (run.key i) R ∈ run.heightRangeFamily ↔
      R = functionGraphRange (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.height :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i R

theorem heightRange_stage_eq (i : I) :
    functionGraphRange (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.height =
      relationImage (run.diagram.stage i).stage.carrier (ZFSet.prod C D) (run.diagram.stage i).stage.height := by
  apply ZFSet.ext
  intro y
  rw [mem_functionGraphRange, mem_relationImage]
  constructor
  · intro h
    obtain ⟨x, hx, entry⟩ := h
    exact ⟨(ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.height_code.function.1 entry)).2, x, hx, entry⟩
  · exact And.right

theorem heightRangeFamily_stage_entry (i : I) (R : ZFSet.{u}) :
    ZFSet.pair (run.key i) R ∈ run.heightRangeFamily ↔
      R = relationImage (run.diagram.stage i).stage.carrier (ZFSet.prod C D) (run.diagram.stage i).stage.height := by
  rw [run.heightRangeFamily_entry, run.heightRange_stage_eq]

theorem heightRangeValues_ground : run.heightRangeValues ∈ M.sets :=
  M.familyCodeGraph_valueRange_mem unions separation run.key _ run.indices_ground run.heightRangeFamily_ground

theorem heightRangeValues_union : ⋃₀ run.heightRangeValues = run.limitHeightRange := by
  apply ZFSet.ext
  intro t
  rw [heightRangeValues, familyCodeGraph_valueUnion_mem_iff, run.limitHeightRange_mem]
  simp only [mem_functionGraphRange]

theorem heightRangeFamily_rank_le_code : ZFSet.rank run.heightRangeFamily ≤ ZFSet.rank run.code :=
  (familyCodeGraph_functionRanges_rank_le run.key
    (fun i => (run.diagram.stage i).stage.carrier) (fun i => (run.diagram.stage i).stage.height)).trans
    (run.stageFieldFamily_rank_le_code 10)

theorem heightRangeValues_rank_le_code : ZFSet.rank run.heightRangeValues ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueRange_rank_le run.key _).trans run.heightRangeFamily_rank_le_code

theorem limitHeightRange_rank_le_code : ZFSet.rank run.limitHeightRange ≤ ZFSet.rank run.code := by
  rw [← run.heightRangeValues_union]
  exact (ZFSet.rank_sUnion_le _).trans run.heightRangeValues_rank_le_code

variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (indices : M.groundEmbeddable run.indices ZFSet.omega)
include infinite choice indices

theorem heightRangeValues_countable : M.groundEmbeddable run.heightRangeValues ZFSet.omega := by
  rw [heightRangeValues, familyCodeGraph_valueRange_eq run.key _]
  exact M.groundEmbeddable_function_image pairing unions powers separation choice
    run.indices_ground (M.union_mem unions (M.union_mem unions run.heightRangeFamily_ground))
    (M.omega_mem separation infinite) run.heightRangeFamily_ground
    run.heightRangeFamily_function.to_isFunc indices

theorem limitHeightRange_countable : M.groundEmbeddable run.limitHeightRange ZFSet.omega := by
  rw [← run.heightRangeValues_union]
  apply M.groundCountable_family_union pairing unions powers separation infinite choice
    run.heightRangeValues_ground (run.heightRangeValues_countable infinite choice indices)
  intro R hR
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hR
  change M.groundEmbeddable
    (functionGraphRange (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.height) ZFSet.omega
  rw [run.heightRange_stage_eq i]
  exact (run.diagram.stage i).stage.height_range_countable

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitHeight_relationImage_eq :
    relationImage run.limitPoints (ZFSet.prod C D) run.limitHeight = run.limitHeightRange := by
  apply ZFSet.ext
  intro y
  rw [limitHeightRange, mem_functionGraphRange, mem_relationImage]
  exact ⟨And.right, fun h =>
    ⟨(ZFSet.pair_mem_prod.1 (run.limitHeight_function.1 h.choose_spec.2)).2, h⟩⟩

theorem limitHeight_relationImage_countable
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (indices : M.groundEmbeddable run.indices ZFSet.omega) :
    M.groundEmbeddable (relationImage run.limitPoints (ZFSet.prod C D) run.limitHeight) ZFSet.omega := by
  rw [run.limitHeight_relationImage_eq]
  exact run.limitHeightRange_countable infinite choice indices

noncomputable def stageTopHeight (i : I) : ZFSet.{u} :=
  ((run.diagram.stage i).stage.height_code.value
    ⟨(run.diagram.stage i).stage.top, (run.diagram.stage i).stage.top_mem⟩).val

noncomputable def stageTopColumn (i : I) : ZFSet.{u} :=
  (show FunctionGraphOn (ZFSet.prod C D) (productFirst C D) from ⟨C, productFirst_function C D⟩).value
    ((run.diagram.stage i).stage.height_code.value
      ⟨(run.diagram.stage i).stage.top, (run.diagram.stage i).stage.top_mem⟩)

noncomputable def topHeightFamily : ZFSet.{u} := familyCodeGraph run.key run.stageTopHeight

noncomputable def topColumnFamily : ZFSet.{u} := familyCodeGraph run.key run.stageTopColumn

noncomputable def topColumnValues : ZFSet.{u} := ZFSet.range run.stageTopColumn

theorem stageTopHeight_entry (i : I) :
    ZFSet.pair (run.diagram.stage i).stage.top (run.stageTopHeight i) ∈ (run.diagram.stage i).stage.height :=
  (run.diagram.stage i).stage.height_code.value_entry _

theorem stageTopHeight_column (i : I) :
    run.stageTopColumn i ∈ C ∧ ∃ q ∈ D, run.stageTopHeight i = ZFSet.pair (run.stageTopColumn i) q := by
  have entry := (show FunctionGraphOn (ZFSet.prod C D) (productFirst C D) from
    ⟨C, productFirst_function C D⟩).value_entry
      ((run.diagram.stage i).stage.height_code.value
        ⟨(run.diagram.stage i).stage.top, (run.diagram.stage i).stage.top_mem⟩)
  obtain ⟨c, hc, q, hq, equal⟩ := (mem_productFirst C D _).1 entry
  have eqs := ZFSet.pair_inj.1 equal
  change run.stageTopHeight i = ZFSet.pair c q ∧ run.stageTopColumn i = c at eqs
  exact ⟨eqs.2.symm ▸ hc, q, hq, by simpa only [eqs.2] using eqs.1⟩

theorem topHeightFamily_ground : run.topHeightFamily ∈ M.sets := by
  apply M.familyCodeGraph_evaluation_ground pairing unions powers separation run.key
    (fun i => (run.diagram.stage i).stage.top) (fun i => (run.diagram.stage i).stage.height)
    run.stageTopHeight run.key_injective run.indices_ground (run.stageFieldFamily_ground 9)
    (run.stageFieldFamily_ground 10)
  intro i y
  exact ⟨fun entry => ((run.diagram.stage i).stage.height_code.value_eq_of_entry _ entry).symm,
    fun equal => equal.symm ▸ run.stageTopHeight_entry i⟩

theorem topColumnFamily_ground : run.topColumnFamily ∈ M.sets := by
  classical
  let coordinate (i : I) := (run.stageTopHeight_column i).2.choose
  have equal (i : I) : run.stageTopHeight i = ZFSet.pair (run.stageTopColumn i) (coordinate i) :=
    (run.stageTopHeight_column i).2.choose_spec.2
  have whole : familyCodeGraph run.key
      (fun i => ZFSet.pair (run.stageTopColumn i) (coordinate i)) ∈ M.sets := by
    simpa only [topHeightFamily, ← equal] using run.topHeightFamily_ground
  exact (M.familyCodeGraph_pair_projections pairing unions powers separation run.key
    run.stageTopColumn coordinate run.key_injective run.indices_ground whole).1

theorem topHeightFamily_function : FunctionGraphOn run.indices run.topHeightFamily :=
  familyCodeGraph_function run.key _ run.key_injective

theorem topColumnFamily_function : FunctionGraphOn run.indices run.topColumnFamily :=
  familyCodeGraph_function run.key _ run.key_injective

theorem topHeightFamily_entry (i : I) (y : ZFSet.{u}) :
    ZFSet.pair (run.key i) y ∈ run.topHeightFamily ↔ y = run.stageTopHeight i :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i y

theorem topColumnFamily_entry (i : I) (c : ZFSet.{u}) :
    ZFSet.pair (run.key i) c ∈ run.topColumnFamily ↔ c = run.stageTopColumn i :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i c

theorem topColumnValues_ground : run.topColumnValues ∈ M.sets :=
  M.familyCodeGraph_valueRange_mem unions separation run.key _ run.indices_ground run.topColumnFamily_ground

theorem topColumnValues_subset : run.topColumnValues ⊆ C := by
  intro c hc
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hc
  exact (run.stageTopHeight_column i).1

theorem topHeightFamily_rank_le_code : ZFSet.rank run.topHeightFamily ≤ ZFSet.rank run.code :=
  (familyCodeGraph_evaluation_rank_le run.key (fun i => (run.diagram.stage i).stage.top)
    (fun i => (run.diagram.stage i).stage.height) run.stageTopHeight run.stageTopHeight_entry).trans
    (run.stageFieldFamily_rank_le_code 10)

theorem topColumnFamily_rank_le_code : ZFSet.rank run.topColumnFamily ≤ ZFSet.rank run.code := by
  apply (familyCodeGraph_rank_mono run.key run.stageTopColumn run.stageTopHeight ?_).trans
    run.topHeightFamily_rank_le_code
  intro i
  obtain ⟨q, _, equal⟩ := (run.stageTopHeight_column i).2
  have member : run.stageTopColumn i ∈ ⋃₀ run.stageTopHeight i := by
    rw [equal]
    exact ZFSet.mem_sUnion.2 ⟨{run.stageTopColumn i}, by simp [ZFSet.pair], by simp⟩
  exact (ZFSet.rank_lt_of_mem member).le.trans (ZFSet.rank_sUnion_le _)

theorem topColumnValues_rank_le_code : ZFSet.rank run.topColumnValues ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueRange_rank_le run.key _).trans run.topColumnFamily_rank_le_code

theorem topColumnValues_countable
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (indices : M.groundEmbeddable run.indices ZFSet.omega) :
    M.groundEmbeddable run.topColumnValues ZFSet.omega := by
  rw [topColumnValues, familyCodeGraph_valueRange_eq run.key _]
  exact M.groundEmbeddable_function_image pairing unions powers separation choice
    run.indices_ground (M.union_mem unions (M.union_mem unions run.topColumnFamily_ground))
    (M.omega_mem separation infinite) run.topColumnFamily_ground
    run.topColumnFamily_function.to_isFunc indices

theorem height_column_below_topColumn (i : I) {x c q : ZFSet.{u}}
    (entry : ZFSet.pair x (ZFSet.pair c q) ∈ (run.diagram.stage i).stage.height) :
    c = run.stageTopColumn i ∨ c ∈ run.stageTopColumn i := by
  have hx := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.height_code.function.1 entry)).1
  obtain ⟨d, _, equal⟩ := (run.stageTopHeight_column i).2
  have topEntry : ZFSet.pair (run.diagram.stage i).stage.top (ZFSet.pair (run.stageTopColumn i) d) ∈
      (run.diagram.stage i).stage.height := equal ▸ run.stageTopHeight_entry i
  by_cases same : x = (run.diagram.stage i).stage.top
  · have eq : ZFSet.pair c q = ZFSet.pair (run.stageTopColumn i) d :=
      (show FunctionGraphOn (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.height from
        ⟨ZFSet.prod C D, (run.diagram.stage i).stage.height_code.function⟩).unique (same ▸ entry) topEntry
    exact Or.inl (ZFSet.pair_inj.1 eq).1
  · rcases (run.diagram.stage i).stage.height_code.strict x hx _ (run.diagram.stage i).stage.top_mem
      c q (run.stageTopColumn i) d ((run.diagram.stage i).stage.greatest x hx) same entry topEntry with less | eq
    · exact Or.inr less
    · exact Or.inl eq.1

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
