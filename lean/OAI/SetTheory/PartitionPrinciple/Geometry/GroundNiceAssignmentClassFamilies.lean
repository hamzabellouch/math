import OAI.SetTheory.PartitionPrinciple.Definability.GroundPackedRefinementFormulaData

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "data" => M.refinementLevelFormulaData a s b d level T T2 valid

noncomputable def niceAssignmentClassGraphs (A : ZFSet.{u}) (side : Fin 2) : ZFSet.{u} :=
  M.assignmentClassGraph side A (data (Fin.cases 5 (fun _ => 4) side))
    T s.carrier s.conditionOrder (s.encode ⊤)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (members : ∀ j : Fin 15, (M.refinementLevelFormulaData a s b d level T T2 valid) j ∈ M.sets)
include pairing unions powers separation collection members

theorem niceAssignmentClassGraphs_entry {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (idx : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (u w : Name s) (hu : u.val ∈ T) (hw : w.val ∈ T)
    (member : stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val ∈ A) (side : Fin 2) (y : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val) y ∈ M.niceAssignmentClassGraphs a s b d level T T2 valid A side ↔
      y = (Name.refinementClass T valid
        (Fin.cases (motive := fun _ => Name s) Rc.val (fun _ => Rf.val) side)
        (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side)).val := by
  have hT : T ∈ M.sets := members 6
  have carrier : s.carrier ∈ M.sets := members 7
  have order : s.conditionOrder ∈ M.sets := members 8
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT (members 9) valid
  obtain ⟨_, _, hf, hc, _⟩ := (M.niceRefinementIndex_mem_iff a s b d pairing unions powers
    separation collection carrier order level T T2 valid family C E U Rf Rc).1 idx
  have fine := M.niceNameCandidates_subset a s T2 (d.principalFix C) hf
  have coarse := M.niceNameCandidates_subset a s T2 (d.principalFix C) hc
  have lookup (j : Fin 6) (R : Name s) (bound : R.val ∈ M.groundRelations T2 s.carrier)
      (value : (![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val] j) = R.val) :
      ∀ z, ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) z ∈
        refinementIndexFieldGraph I (M.groundRelations T2 s.carrier) j ↔ z = R.val := by
    intro z
    rw [refinementIndexCode, refinementIndexFieldGraph_entry, value]
    exact ⟨fun h => h.2.2, fun eq => ⟨idx, eq.symm ▸ bound, eq⟩⟩
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) side
  · dsimp only [niceAssignmentClassGraphs, Fin.cases_zero]
    exact M.assignmentClassGraph_entry s 0 pairing unions powers separation collection carrier order
      hA (members 5) hT valid Rc.val u w Rc.property (M.transitive hT hu) (M.transitive hT hw)
      member (lookup 5 Rc.val coarse rfl) y
  · dsimp only [niceAssignmentClassGraphs, Fin.cases_succ]
    exact M.assignmentClassGraph_entry s 1 pairing unions powers separation collection carrier order
      hA (members 4) hT valid Rf.val u w Rf.property (M.transitive hT hu) (M.transitive hT hw)
      member (lookup 4 Rf.val fine rfl) y

theorem niceAssignmentClassRequests
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (valid2 : ∀ z ∈ T2, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (children : ∀ z : Name s, z.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) z)
    (secondChildren : ∀ z : Name s, z.val ∈ T2 →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) z)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (shape : A ⊆ stageOneAssignments I T)
    (small : M.groundEmbeddable A ZFSet.omega) :
    let graphs := M.niceAssignmentClassGraphs a s b d level T T2 valid A
    let bound := M.groundRelations T s.carrier
    let J := relationImage A bound (graphs 0) ∪ relationImage A bound (graphs 1)
    (∀ side, graphs side ∈ M.sets ∧ ZFSet.IsFunc A bound (graphs side)) ∧
    J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
    (∀ z ∈ J, IsName s z) ∧
    ∀ z : Name s, z.val ∈ J →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
      ∀ H : ConditionFilter P, Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := by
  let graphs := M.niceAssignmentClassGraphs a s b d level T T2 valid A
  let bound := M.groundRelations T s.carrier
  have hT : T ∈ M.sets := members 6
  have carrier : s.carrier ∈ M.sets := members 7
  have order : s.conditionOrder ∈ M.sets := members 8
  have hb := M.groundRelations_mem pairing unions powers separation hT carrier
  have hOmega := M.omega_mem separation infinite
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT (members 9) valid
  have request (side : Fin 2) (x : ZFSet.{u}) (hx : x ∈ A) :
      ∃ z : Name s, z.val ∈ bound ∧
        HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
        z.val ⊆ ZFSet.prod T s.carrier ∧
        ∀ y, ZFSet.pair x y ∈ graphs side ↔ y = z.val := by
    obtain ⟨i, hi, rawU, hu, rawW, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 (shape hx)
    obtain ⟨C, E, U, Rf, Rc, rfl⟩ := M.exists_niceRefinementIndex_fields a s b d level T T2 valid valid2 hi
    let u : Name s := ⟨rawU, valid rawU hu⟩
    let w : Name s := ⟨rawW, valid rawW hw⟩
    obtain ⟨_, _, hf, hc, _⟩ := (M.niceRefinementIndex_mem_iff a s b d pairing unions powers
      separation collection carrier order level T T2 valid family C E U Rf Rc).1 hi
    have fineHS := niceNameCode_principal_hs a s d base C directed secondChildren
      ((M.mem_niceNameCandidates a s T2 (d.principalFix C) Rf.val.val).1 hf).2
    have coarseHS := niceNameCode_principal_hs a s d base C directed secondChildren
      ((M.mem_niceNameCandidates a s T2 (d.principalFix C) Rc.val.val).1 hc).2
    have result (R : (M.nameDomain s).names) (z : Name s) (hz : z.val ∈ T)
        (hs : HereditarilySymmetric a s (d.principalSupportFamily base directed) R.val) :
        (Name.refinementClass T valid R.val z).val ∈ bound ∧
        HereditarilySymmetric a s (d.principalSupportFamily base directed)
          (Name.refinementClass T valid R.val z) ∧
        (Name.refinementClass T valid R.val z).val ⊆ ZFSet.prod T s.carrier :=
      ⟨(M.mem_groundRelations T s.carrier _).2
          ⟨M.refinementClass_mem s pairing unions powers separation collection carrier order
            hT valid R.val z R.property (M.transitive hT hz), Name.refinementClass_subset T valid R.val z⟩,
        Name.refinementClass_hs_of_hs a T valid closed _ children R.val z hs (children z hz),
        Name.refinementClass_subset T valid R.val z⟩
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) side
    · exact ⟨Name.refinementClass T valid Rc.val u, (result Rc u hu coarseHS).1,
        (result Rc u hu coarseHS).2.1, (result Rc u hu coarseHS).2.2,
        M.niceAssignmentClassGraphs_entry a s b d level T T2 valid pairing unions powers separation
          collection members hA C E U Rf Rc hi u w hu hw hx 0⟩
    · exact ⟨Name.refinementClass T valid Rf.val w, (result Rf w hw fineHS).1,
        (result Rf w hw fineHS).2.1, (result Rf w hw fineHS).2.2,
        M.niceAssignmentClassGraphs_entry a s b d level T T2 valid pairing unions powers separation
          collection members hA C E U Rf Rc hi u w hu hw hx 1⟩
  have grounds (side : Fin 2) : graphs side ∈ M.sets :=
    M.assignmentClassGraph_mem side pairing unions powers separation hA
      (members (Fin.cases 5 (fun _ => 4) side)) hT carrier order (members 9)
  have functions (side : Fin 2) : ZFSet.IsFunc A bound (graphs side) := by
    refine ⟨?_, ?_⟩
    · intro x h
      unfold graphs niceAssignmentClassGraphs assignmentClassGraph at h
      exact (ZFSet.mem_sep.1 h).1
    · intro x hx
      obtain ⟨z, _, _, _, entries⟩ := request side x hx
      exact ⟨z.val, (entries _).2 rfl, fun y h => (entries y).1 h⟩
  have imageGround (side : Fin 2) := M.relationImage_mem separation hA hb (grounds side)
  have imageSmall (side : Fin 2) := M.groundEmbeddable_function_image pairing unions powers
    separation choice hA hb hOmega (grounds side) (functions side) small
  have imageFacts (side : Fin 2) (y : ZFSet.{u})
      (member : y ∈ relationImage A bound (graphs side)) :
      ∃ z : Name s, y = z.val ∧ HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
        z.val ⊆ ZFSet.prod T s.carrier := by
    obtain ⟨_, x, hx, edge⟩ := (mem_relationImage A bound (graphs side) y).1 member
    obtain ⟨z, _, symmetric, subset, entries⟩ := request side x hx
    exact ⟨z, (entries y).1 edge, symmetric, subset⟩
  have allFacts (y : ZFSet.{u}) (member : y ∈ relationImage A bound (graphs 0) ∪
      relationImage A bound (graphs 1)) :
      ∃ z : Name s, y = z.val ∧ HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
        z.val ⊆ ZFSet.prod T s.carrier :=
    (ZFSet.mem_union.1 member).elim (imageFacts 0 y) (imageFacts 1 y)
  refine ⟨fun side => ⟨grounds side, functions side⟩,
    M.binary_union_mem pairing unions (imageGround 0) (imageGround 1),
    M.groundCountable_binary_union pairing unions powers separation infinite choice
      (imageGround 0) (imageGround 1) (imageSmall 0) (imageSmall 1), ?_, ?_⟩
  · intro y member
    obtain ⟨z, rfl, _, _⟩ := allFacts y member
    exact z.property
  · intro z member
    obtain ⟨w, equal, symmetric, subset⟩ := allFacts z.val member
    have same : z = w := Subtype.ext equal
    subst w
    exact ⟨symmetric, fun H => Name.eval_subset_familySet_of_code_subset H T valid z subset⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
