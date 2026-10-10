import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableProducts

namespace OAI

namespace PartitionPilot.Forcing

universe u

noncomputable def heightColumns (P C D old : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (relationImage P (ZFSet.prod C D) old) C (productFirst C D)

theorem mem_heightColumns_of_entry {P C D old x c q : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (entry : ZFSet.pair x (ZFSet.pair c q) ∈ old) : c ∈ heightColumns P C D old := by
  have shape := ZFSet.pair_mem_prod.1 (function.1 entry)
  have coordinates := ZFSet.pair_mem_prod.1 shape.2
  exact (mem_relationImage _ _ _ c).2 ⟨coordinates.1, ZFSet.pair c q,
    (mem_relationImage _ _ _ _).2 ⟨shape.2, x, shape.1, entry⟩,
    (mem_productFirst C D _).2 ⟨c, coordinates.1, q, coordinates.2, rfl⟩⟩

theorem height_range_subset_columns {P L C D old height : ZFSet.{u}}
    (columns : ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height →
      c ∈ heightColumns P C D old) :
    relationImage L (ZFSet.prod C D) height ⊆ ZFSet.prod (heightColumns P C D old) D := by
  intro y hy
  obtain ⟨hy, x, _, entry⟩ := (mem_relationImage L (ZFSet.prod C D) height y).1 hy
  obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 hy
  exact ZFSet.pair_mem_prod.2 ⟨columns x c q entry, hq⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightColumns_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P C D old : ZFSet.{u}} (hP : P ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hOld : old ∈ M.sets) : heightColumns P C D old ∈ M.sets :=
  M.relationImage_mem separation
    (M.relationImage_mem separation hP (M.prod_mem pairing unions powers separation hC hD) hOld)
    hC (M.productFirst_mem pairing unions powers separation hC hD)

theorem heightColumns_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P C D old : ZFSet.{u}} (hP : P ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hOld : old ∈ M.sets)
    (small : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega) :
    M.groundEmbeddable (heightColumns P C D old) ZFSet.omega :=
  M.groundEmbeddable_function_image pairing unions powers separation choice
    (M.relationImage_mem separation hP (M.prod_mem pairing unions powers separation hC hD) hOld)
    hC (M.omega_mem separation infinite)
    (M.productFirst_mem pairing unions powers separation hC hD) (productFirst_function C D) small

theorem countable_height_range_of_old_columns
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P L C D old height : ZFSet.{u}}
    (hP : P ∈ M.sets) (hL : L ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hOld : old ∈ M.sets) (hHeight : height ∈ M.sets)
    (oldSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega)
    (coordinateSmall : M.groundEmbeddable D ZFSet.omega)
    (columns : ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height →
      c ∈ heightColumns P C D old) :
    relationImage L (ZFSet.prod C D) height ∈ M.sets ∧
      M.groundEmbeddable (relationImage L (ZFSet.prod C D) height) ZFSet.omega := by
  have rangeMember := M.relationImage_mem separation hL
    (M.prod_mem pairing unions powers separation hC hD) hHeight
  have smallColumns := M.heightColumns_countable pairing unions powers separation infinite choice
    hP hC hD hOld oldSmall
  have smallProduct := M.groundEmbeddable_product pairing unions powers separation infinite
    (M.heightColumns_mem pairing unions powers separation hP hC hD hOld) hD
    smallColumns coordinateSmall
  exact ⟨rangeMember, M.groundEmbeddable_restrict separation rangeMember
    (M.omega_mem separation infinite) (height_range_subset_columns columns) smallProduct⟩

end TransitiveGround

theorem heightColumns_subset_of_bound {P C D height K : ZFSet.{u}}
    (bound : ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height → c ∈ K) :
    heightColumns P C D height ⊆ K := by
  intro c hc
  obtain ⟨_, y, hy, projected⟩ :=
    (mem_relationImage (relationImage P (ZFSet.prod C D) height) C (productFirst C D) c).1 hc
  obtain ⟨a, ha, q, hq, equal⟩ := (mem_productFirst C D _).1 projected
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  obtain ⟨_, x, _, entry⟩ := (mem_relationImage P (ZFSet.prod C D) height _).1 hy
  exact bound x c q entry

end PartitionPilot.Forcing

end OAI
