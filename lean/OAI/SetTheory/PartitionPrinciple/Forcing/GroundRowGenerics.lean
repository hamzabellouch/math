import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRowDistinguishing

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def coordinateAssignedFormula {n} (p x y : Fin n) : BoundedFormula n :=
  exMem y (pairMembershipFormula x.succ 0 p.succ)

theorem truth_coordinateAssignedFormula {n} (p x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (coordinateAssignedFormula p x y) env ↔
      ∃ b ∈ env y, ZFSet.pair (env x) b ∈ env p := by
  simp only [coordinateAssignedFormula, truth_exMem, truth_pairMembershipFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem coordinateAssigned_code_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y x : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (hx : x ∈ X) :
    (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)).subset
      (M.coordinateAssigned X Y x) ∈ M.sets := by
  let s := SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)
  let params := extend x (extend Y Fin.elim0)
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases (M.transitive hX hx) (Fin.cases hY (fun i => Fin.elim0 i))
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY
  have selected := M.separation_mem separation
    (BoundedFormula.coordinateAssignedFormula 0 1 2).toFormula params members carrier
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.coordinateAssignedFormula 0 1 2).toFormula (extend z params))
      (M.smallPartialFunctions X Y ZFSet.omega) = s.subset (M.coordinateAssigned X Y x) := by
    apply ZFSet.ext
    intro z
    erw [ZFSet.mem_sep, s.mem_subset]
    constructor
    · rintro ⟨hz, rel⟩
      obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 hz
      exact ⟨p, (BoundedFormula.truth_coordinateAssignedFormula 0 1 2 _).1
        ((BoundedFormula.realize_toFormula M _ _
          (Fin.cases (M.transitive carrier hz) members)).1 rel), rfl⟩
    · rintro ⟨p, assigned, rfl⟩
      exact ⟨s.encode_mem p, (BoundedFormula.realize_toFormula M _ _
        (Fin.cases (M.transitive carrier (s.encode_mem p)) members)).2
          ((BoundedFormula.truth_coordinateAssignedFormula 0 1 2 _).2 assigned)⟩
  exact eq ▸ selected

theorem generic_meets_coordinate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y x : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets)
    (values : Y.Nonempty) (hx : x ∈ X) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)),
      H.GenericFor (M.codedFamily (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega))) →
      H.Meets (M.coordinateAssigned X Y x) := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro H generic
  exact M.generic_meets_coded_dense _ H generic
    (M.coordinateAssigned_code_mem pairing unions powers separation infinite hX hY hx)
    (M.coordinateAssigned_dense pairing unions powers separation infinite hX hY values hx)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def countableGenericGraph (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)) → ZFSet.{u} := by
  letI := M.smallFunctionOrder X Y ZFSet.omega
  exact fun H => ZFSet.sep (fun z => ∃ p, H.mem p ∧ z ∈ SetMembers.raw p) (ZFSet.prod X Y)

theorem mem_countableGenericGraph (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ (H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega))) (z : ZFSet.{u}),
      z ∈ M.countableGenericGraph X Y H ↔ ∃ p, H.mem p ∧ z ∈ SetMembers.raw p := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro H z
  rw [countableGenericGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨p, hp, hz⟩
    exact ⟨(M.smallFunction_raw_properties X Y ZFSet.omega p).2.1.shape hz, p, hp, hz⟩

theorem countableGenericGraph_extends (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ (H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega))) p,
      H.mem p → SetMembers.raw p ⊆ M.countableGenericGraph X Y H := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro H p hp z hz
  exact (M.mem_countableGenericGraph X Y H z).2 ⟨p, hp, hz⟩

theorem countableGenericGraph_partial (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)),
      PartialFunctionCode X Y (M.countableGenericGraph X Y H) := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro H
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x y z hy hz
  obtain ⟨p, hp, py⟩ := (M.mem_countableGenericGraph X Y H _).1 hy
  obtain ⟨q, hq, qz⟩ := (M.mem_countableGenericGraph X Y H _).1 hz
  obtain ⟨r, _, rp, rq⟩ := H.directed hp hq
  have code := (M.smallFunction_raw_properties X Y ZFSet.omega r).2.1
  exact code.unique x y z
    ((M.smallFunction_le_iff X Y ZFSet.omega r p).1 rp py)
    ((M.smallFunction_le_iff X Y ZFSet.omega r q).1 rq qz)

theorem countableGenericGraph_isFunc
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (values : Y.Nonempty) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)),
      H.GenericFor (M.codedFamily (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega))) →
      ZFSet.IsFunc X Y (M.countableGenericGraph X Y H) := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro H generic
  have code := M.countableGenericGraph_partial X Y H
  refine ⟨code.shape, ?_⟩
  intro x hx
  obtain ⟨p, hp, y, _, rel⟩ :=
    M.generic_meets_coordinate pairing unions powers separation infinite hX hY values hx H generic
  have entry := M.countableGenericGraph_extends X Y H p hp rel
  exact ⟨y, entry, fun z hz => code.unique x z y hz entry⟩

theorem exists_total_countableFunction_generic
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (values : Y.Nonempty)
    (p : SetMembers (M.smallPartialFunctions X Y ZFSet.omega)) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)), H.mem p ∧
      H.GenericFor (M.codedFamily (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega))) ∧
      H.GenericFor (formulaFamily (M.nameDomain
        (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)))) ∧
      ZFSet.IsFunc X Y (M.countableGenericGraph X Y H) := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  obtain ⟨H, hp, ground, ordinary⟩ :=
    M.exists_countableFunction_generic small pairing unions powers separation infinite hX hY p
  exact ⟨H, hp, ground, ordinary,
    M.countableGenericGraph_isFunc pairing unions powers separation infinite hX hY values H ground⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def rowDistinguishingFormula {n} (p i j c y : Fin n) : BoundedFormula n :=
  exMem c (exMem y.succ (exMem y.succ.succ
    (.conj (.neg (.equal 1 0))
      (.conj (tripleMembershipFormula i.succ.succ.succ 2 1 p.succ.succ.succ)
        (tripleMembershipFormula j.succ.succ.succ 2 0 p.succ.succ.succ)))))

theorem truth_rowDistinguishingFormula {n} (p i j c y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rowDistinguishingFormula p i j c y) env ↔
      ∃ k ∈ env c, ∃ a ∈ env y, ∃ b ∈ env y, a ≠ b ∧
        ZFSet.pair (ZFSet.pair (env i) k) a ∈ env p ∧
        ZFSet.pair (ZFSet.pair (env j) k) b ∈ env p := by
  simp only [rowDistinguishingFormula, truth_exMem, Truth, truth_tripleMembershipFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem rowDistinguishing_code_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C Y i j : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hi : i ∈ I) (hj : j ∈ I) :
    (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)).subset
      (M.rowDistinguishing I C Y i j) ∈ M.sets := by
  let s := SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)
  let params := extend i (extend j (extend C (extend Y Fin.elim0)))
  have members : ∀ k, params k ∈ M.sets :=
    Fin.cases (M.transitive hI hi) (Fin.cases (M.transitive hI hj)
      (Fin.cases hC (Fin.cases hY (fun k => Fin.elim0 k))))
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) hY
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.rowDistinguishingFormula 0 1 2 3 4) params members carrier
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.rowDistinguishingFormula 0 1 2 3 4) (extend z params))
      (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega) =
        s.subset (M.rowDistinguishing I C Y i j) := by
    apply ZFSet.ext
    intro z
    erw [ZFSet.mem_sep, s.mem_subset]
    constructor
    · rintro ⟨hz, rel⟩
      obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 hz
      exact ⟨p, (BoundedFormula.truth_rowDistinguishingFormula 0 1 2 3 4 _).1 rel, rfl⟩
    · rintro ⟨p, distinguishing, rfl⟩
      exact ⟨s.encode_mem p,
        (BoundedFormula.truth_rowDistinguishingFormula 0 1 2 3 4 _).2 distinguishing⟩
  exact eq ▸ selected

theorem generic_meets_rowDistinguishing
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
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)),
      H.GenericFor (M.codedFamily
        (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega))) →
      H.Meets (M.rowDistinguishing I C Y i j) := by
  let := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
  intro H generic
  exact M.generic_meets_coded_dense _ H generic
    (M.rowDistinguishing_code_mem pairing unions powers separation infinite hI hC hY hi hj)
    (M.rowDistinguishing_dense pairing unions powers separation infinite choice
      hI hC hY hi hj distinct values uncountable)

theorem countableGenericGraph_rows_separated
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
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)),
      H.GenericFor (M.codedFamily
        (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega))) →
      ∃ c ∈ C, ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧
        ZFSet.pair (ZFSet.pair i c) a ∈ M.countableGenericGraph (ZFSet.prod I C) Y H ∧
        ZFSet.pair (ZFSet.pair j c) b ∈ M.countableGenericGraph (ZFSet.prod I C) Y H ∧
        ZFSet.pair (ZFSet.pair j c) a ∉ M.countableGenericGraph (ZFSet.prod I C) Y H := by
  let := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
  intro H generic
  obtain ⟨p, hp, c, hc, a, ha, b, hb, ne, first, second⟩ :=
    M.generic_meets_rowDistinguishing pairing unions powers separation infinite choice
      hI hC hY hi hj distinct values uncountable H generic
  have includes := M.countableGenericGraph_extends (ZFSet.prod I C) Y H p hp
  have firstEntry := includes first
  have secondEntry := includes second
  refine ⟨c, hc, a, ha, b, hb, ne, firstEntry, secondEntry, ?_⟩
  intro sameValue
  exact ne ((M.countableGenericGraph_partial (ZFSet.prod I C) Y H).unique
    (ZFSet.pair j c) a b sameValue secondEntry)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
