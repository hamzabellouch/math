import OAI.SetTheory.PartitionPrinciple.Definability.GroundBelowFunctionGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.GroundFunctionCoordinateDensity

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

noncomputable def rowCoordinateDomain (I C Y p : ZFSet.{u}) : ZFSet.{u} :=
  relationImage p (ZFSet.prod I C) (productFirst (ZFSet.prod I C) Y)

noncomputable def rowUsedColumns (I C Y p : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (rowCoordinateDomain I C Y p) C (productSecond I C)

theorem mem_rowCoordinateDomain (I C Y p x : ZFSet.{u}) :
    x ∈ rowCoordinateDomain I C Y p ↔
      x ∈ ZFSet.prod I C ∧ ∃ y ∈ Y, ZFSet.pair x y ∈ p := by
  rw [rowCoordinateDomain, mem_relationImage]
  constructor
  · rintro ⟨hx, z, hz, rel⟩
    obtain ⟨a, _, y, hy, eq⟩ := (mem_productFirst (ZFSet.prod I C) Y _).1 rel
    have entries := ZFSet.pair_inj.1 eq
    refine ⟨hx, y, hy, ?_⟩
    rw [entries.2]
    exact entries.1 ▸ hz
  · rintro ⟨hx, y, hy, entry⟩
    exact ⟨hx, ZFSet.pair x y, entry,
      (mem_productFirst (ZFSet.prod I C) Y _).2 ⟨x, hx, y, hy, rfl⟩⟩

theorem rowCoordinateDomain_subset (I C Y p : ZFSet.{u}) :
    rowCoordinateDomain I C Y p ⊆ ZFSet.prod I C :=
  fun x hx => ((mem_rowCoordinateDomain I C Y p x).1 hx).1

theorem mem_rowUsedColumns (I C Y p c : ZFSet.{u}) :
    c ∈ rowUsedColumns I C Y p ↔
      c ∈ C ∧ ∃ i ∈ I, ∃ y ∈ Y, ZFSet.pair (ZFSet.pair i c) y ∈ p := by
  rw [rowUsedColumns, mem_relationImage]
  constructor
  · rintro ⟨hc, x, hx, rel⟩
    obtain ⟨i, hi, d, _, eq⟩ := (mem_productSecond I C _).1 rel
    have entries := ZFSet.pair_inj.1 eq
    obtain ⟨_, y, hy, entry⟩ := (mem_rowCoordinateDomain I C Y p x).1 hx
    rw [entries.1, ← entries.2] at entry
    exact ⟨hc, i, hi, y, hy, entry⟩
  · rintro ⟨hc, i, hi, y, hy, entry⟩
    exact ⟨hc, ZFSet.pair i c,
      (mem_rowCoordinateDomain I C Y p _).2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hc⟩, y, hy, entry⟩,
      (mem_productSecond I C _).2 ⟨i, hi, c, hc, rfl⟩⟩

theorem rowUsedColumns_subset (I C Y p : ZFSet.{u}) : rowUsedColumns I C Y p ⊆ C :=
  fun c hc => ((mem_rowUsedColumns I C Y p c).1 hc).1

theorem not_mem_rowUsedColumns_iff {I C Y p c : ZFSet.{u}}
    (code : PartialFunctionCode (ZFSet.prod I C) Y p) (hc : c ∈ C) :
    c ∉ rowUsedColumns I C Y p ↔
      ∀ i y, ZFSet.pair (ZFSet.pair i c) y ∉ p := by
  constructor
  · intro fresh i y entry
    have bound := ZFSet.pair_mem_prod.1 (code.shape entry)
    have coordinates := ZFSet.pair_mem_prod.1 bound.1
    exact fresh ((mem_rowUsedColumns I C Y p c).2 ⟨hc, i, coordinates.1, y, bound.2, entry⟩)
  · intro fresh used
    obtain ⟨_, i, _, y, _, entry⟩ := (mem_rowUsedColumns I C Y p c).1 used
    exact fresh i y entry

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem rowCoordinateDomain_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) : rowCoordinateDomain I C Y p ∈ M.sets := by
  have coordinates := M.prod_mem pairing unions powers separation hI hC
  exact M.relationImage_mem separation hp coordinates
    (M.productFirst_mem pairing unions powers separation coordinates hY)

theorem rowUsedColumns_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) : rowUsedColumns I C Y p ∈ M.sets :=
  M.relationImage_mem separation
    (M.rowCoordinateDomain_mem pairing unions powers separation hI hC hY hp) hC
    (M.productSecond_mem pairing unions powers separation hI hC)

theorem rowCoordinateDomain_groundEmbeddable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) : M.groundEmbeddable (rowCoordinateDomain I C Y p) N := by
  have coordinates := M.prod_mem pairing unions powers separation hI hC
  exact M.groundEmbeddable_function_image pairing unions powers separation choice hp coordinates hN
    (M.productFirst_mem pairing unions powers separation coordinates hY)
    (productFirst_function (ZFSet.prod I C) Y) small

theorem rowUsedColumns_groundEmbeddable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) : M.groundEmbeddable (rowUsedColumns I C Y p) N :=
  M.groundEmbeddable_function_image pairing unions powers separation choice
    (M.rowCoordinateDomain_mem pairing unions powers separation hI hC hY hp) hC hN
    (M.productSecond_mem pairing unions powers separation hI hC) (productSecond_function I C)
    (M.rowCoordinateDomain_groundEmbeddable pairing unions powers separation choice hI hC hY hp hN small)

theorem exists_fresh_rowColumn
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) (large : ¬ M.groundEmbeddable C N) :
    ∃ c ∈ C, c ∉ rowUsedColumns I C Y p := by
  classical
  have columns := M.rowUsedColumns_groundEmbeddable pairing unions powers separation choice
    hI hC hY hp hN small
  by_contra! full
  have eq : rowUsedColumns I C Y p = C := by
    apply ZFSet.ext
    intro c
    exact ⟨fun hc => rowUsedColumns_subset I C Y p hc, full c⟩
  exact large (eq ▸ columns)

theorem countablePartialFunctions_fresh_column
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hp : p ∈ M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega) :
    ∃ c ∈ C, ∀ i y, ZFSet.pair (ZFSet.pair i c) y ∉ p := by
  obtain ⟨ground, code, small⟩ := (M.mem_smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega p).1 hp
  obtain ⟨c, hc, fresh⟩ := M.exists_fresh_rowColumn pairing unions powers separation choice
    hI hC hY ground (M.omega_mem separation infinite) small uncountable
  exact ⟨c, hc, (not_mem_rowUsedColumns_iff code hc).1 fresh⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem countablePartialFunctions_insert_two_rows
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C Y p i j c a b : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)
    (hi : i ∈ I) (hj : j ∈ I) (hc : c ∈ C) (ha : a ∈ Y) (hb : b ∈ Y)
    (distinct : i ≠ j) (fresh : ∀ k y, ZFSet.pair (ZFSet.pair k c) y ∉ p) :
    insert (ZFSet.pair (ZFSet.pair j c) b)
      (insert (ZFSet.pair (ZFSet.pair i c) a) p) ∈
        M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega := by
  have coordinates := M.prod_mem pairing unions powers separation hI hC
  have first := M.countablePartialFunctions_insert pairing unions powers separation infinite
    coordinates hY hp (ZFSet.pair_mem_prod.2 ⟨hi, hc⟩) ha
    (fun y entry => False.elim (fresh i y entry))
  apply M.countablePartialFunctions_insert pairing unions powers separation infinite
    coordinates hY first (ZFSet.pair_mem_prod.2 ⟨hj, hc⟩) hb
  intro y entry
  rcases ZFSet.mem_insert_iff.1 entry with eq | old
  · exact False.elim (distinct (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 eq).1).1.symm)
  · exact False.elim (fresh j y old)

def rowDistinguishing (I C Y i j : ZFSet.{u}) :
    Set (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)) :=
  {p | ∃ c ∈ C, ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧
    ZFSet.pair (ZFSet.pair i c) a ∈ SetMembers.raw p ∧
    ZFSet.pair (ZFSet.pair j c) b ∈ SetMembers.raw p}

theorem rowDistinguishing_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y i j : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hi : i ∈ I) (hj : j ∈ I) (distinct : i ≠ j)
    (values : ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
    Dense (M.rowDistinguishing I C Y i j) := by
  let := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
  intro p
  obtain ⟨c, hc, fresh⟩ := M.countablePartialFunctions_fresh_column
    pairing unions powers separation infinite choice hI hC hY (SetMembers.raw_mem p) uncountable
  obtain ⟨a, ha, b, hb, ne⟩ := values
  have extended := M.countablePartialFunctions_insert_two_rows
    pairing unions powers separation infinite hI hC hY (SetMembers.raw_mem p)
    hi hj hc ha hb distinct fresh
  let q := SetMembers.ofMem
    (insert (ZFSet.pair (ZFSet.pair j c) b)
      (insert (ZFSet.pair (ZFSet.pair i c) a) (SetMembers.raw p))) extended
  have rawq : SetMembers.raw q = insert (ZFSet.pair (ZFSet.pair j c) b)
      (insert (ZFSet.pair (ZFSet.pair i c) a) (SetMembers.raw p)) :=
    SetMembers.raw_ofMem _ _
  refine ⟨q, (M.smallFunction_le_iff (ZFSet.prod I C) Y ZFSet.omega q p).2 ?_, ?_⟩
  · intro z hz
    rw [rawq]
    exact ZFSet.mem_insert_of_mem _ (ZFSet.mem_insert_of_mem _ hz)
  · refine ⟨c, hc, a, ha, b, hb, ne, ?_, ?_⟩
    · rw [rawq]
      exact ZFSet.mem_insert_of_mem _ (ZFSet.mem_insert _ _)
    · rw [rawq]
      exact ZFSet.mem_insert _ _

theorem rowDistinguishing_downward (I C Y i j : ZFSet.{u}) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
    DownwardClosed (M.rowDistinguishing I C Y i j) := by
  let := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
  intro p q le hp
  obtain ⟨c, hc, a, ha, b, hb, ne, first, second⟩ := hp
  have includes := (M.smallFunction_le_iff (ZFSet.prod I C) Y ZFSet.omega q p).1 le
  exact ⟨c, hc, a, ha, b, hb, ne, includes first, includes second⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
