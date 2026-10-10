import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNormalizedRefinementOutputs
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementCoarseVisibility

namespace OAI


namespace PartitionPilot.Forcing
universe u

def RefinementIndexLevelCode (I level : ZFSet.{u}) : Prop :=
  ∀ z ∈ I, ∃ fields : Fin 6 → ZFSet.{u},
    z = nonemptyTupleCode 5 fields ∧ fields 0 = level

namespace RefinementIndexLevelCode
variable {I J level next : ZFSet.{u}}

theorem disjoint (first : RefinementIndexLevelCode I level)
    (second : RefinementIndexLevelCode J next) (different : level ≠ next) :
    ∀ z, ¬ (z ∈ I ∧ z ∈ J) := by
  rintro z ⟨hi, hj⟩
  obtain ⟨v, eqv, hv⟩ := first z hi
  obtain ⟨w, eqw, hw⟩ := second z hj
  have equal := nonemptyTupleCode_injective 5 (eqv.symm.trans eqw)
  exact different (hv.symm.trans ((congrFun equal 0).trans hw))

theorem union_level_graph (first : RefinementIndexLevelCode I level)
    (second : RefinementIndexLevelCode J next) :
    refinementIndexFieldGraph (I ∪ J) {level, next} 0 =
      ZFSet.prod I {level} ∪ ZFSet.prod J {next} := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 ((ZFSet.mem_sep.1 hz).1)
    obtain ⟨hx, _, v, eqv, hy⟩ :=
      (pair_mem_refinementIndexFieldGraph (I ∪ J) {level, next} x y 0).1 hz
    rcases ZFSet.mem_union.1 hx with hi | hj
    · obtain ⟨w, eqw, hw⟩ := first x hi
      have equal := nonemptyTupleCode_injective 5 (eqv.symm.trans eqw)
      exact ZFSet.mem_union.2 (Or.inl (ZFSet.pair_mem_prod.2
        ⟨hi, ZFSet.mem_singleton.2 (hy.trans ((congrFun equal 0).trans hw))⟩))
    · obtain ⟨w, eqw, hw⟩ := second x hj
      have equal := nonemptyTupleCode_injective 5 (eqv.symm.trans eqw)
      exact ZFSet.mem_union.2 (Or.inr (ZFSet.pair_mem_prod.2
        ⟨hj, ZFSet.mem_singleton.2 (hy.trans ((congrFun equal 0).trans hw))⟩))
  · intro hz
    rcases ZFSet.mem_union.1 hz with hi | hj
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hi
      obtain ⟨v, eqv, hv⟩ := first x hx
      have yl := ZFSet.mem_singleton.1 hy
      have bound : y ∈ ({level, next} : ZFSet.{u}) := by
        simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
        exact Or.inl yl
      exact (pair_mem_refinementIndexFieldGraph (I ∪ J) {level, next} x y 0).2
        ⟨ZFSet.mem_union.2 (Or.inl hx), bound, v, eqv, yl.trans hv.symm⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hj
      obtain ⟨v, eqv, hv⟩ := second x hx
      have yn := ZFSet.mem_singleton.1 hy
      have bound : y ∈ ({level, next} : ZFSet.{u}) := by
        simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
        exact Or.inr yn
      exact (pair_mem_refinementIndexFieldGraph (I ∪ J) {level, next} x y 0).2
        ⟨ZFSet.mem_union.2 (Or.inr hx), bound, v, eqv, yn.trans hv.symm⟩

theorem union_level_function (first : RefinementIndexLevelCode I level)
    (second : RefinementIndexLevelCode J next) :
    ZFSet.IsFunc (I ∪ J) {level, next}
      (refinementIndexFieldGraph (I ∪ J) {level, next} 0) := by
  apply refinementIndexFieldGraph_function
  intro z hz
  rcases ZFSet.mem_union.1 hz with hi | hj
  · obtain ⟨v, eqv, hv⟩ := first z hi
    exact ⟨v, eqv, by simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton]; exact Or.inl hv⟩
  · obtain ⟨v, eqv, hv⟩ := second z hj
    exact ⟨v, eqv, by simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton]; exact Or.inr hv⟩

theorem union_level_entry (first : RefinementIndexLevelCode I level)
    (second : RefinementIndexLevelCode J next) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ refinementIndexFieldGraph (I ∪ J) {level, next} 0 ↔
      (x ∈ I ∧ y = level) ∨ (x ∈ J ∧ y = next) := by
  rw [first.union_level_graph second]
  simp only [ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

end RefinementIndexLevelCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def RefinementIndexSelectionCode (M : TransitiveGround.{u})
    (level r candidates relations T P order top z : ZFSet.{u}) : Prop :=
  ∃ C E U Rf Rc N V,
    z = refinementIndexCode level C E U Rf Rc ∧ ZFSet.pair C E ∈ r ∧ C ≠ E ∧
    ZFSet.pair C N ∈ candidates ∧ U ∈ N ∧ ZFSet.pair C V ∈ relations ∧
    Rf ∈ V ∧ Rc ∈ V ∧
    Realize M.sets (refinementValidityForcingFormula 0 1 2 3 4 5 6)
      ![U, Rf, Rc, T, P, order, top]

namespace SetFormula

def refinementIndexSelectionRawFormula {n} (z level r candidates relations T P order top : Fin n)
    (w : Fin 7 → Fin n) : SetFormula n :=
  .conj (BoundedFormula.refinementIndexFormula z level (w 0) (w 1) (w 2) (w 3) (w 4)).toFormula
  (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 1) r).toFormula
  (.conj (.neg (.equal (w 0) (w 1)))
  (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 5) candidates).toFormula
  (.conj (.mem (w 2) (w 5))
  (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 6) relations).toFormula
  (.conj (.mem (w 3) (w 6)) (.conj (.mem (w 4) (w 6))
    (reindex ![w 2, w 3, w 4, T, P, order, top]
      (refinementValidityForcingFormula 0 1 2 3 4 5 6)))))))))

def refinementIndexSelectionFormula {n} (z level r candidates relations T P order top : Fin n) : SetFormula n :=
  let old := suffixIndex n 7
  exBlock 7 (refinementIndexSelectionRawFormula (old z) (old level) (old r)
    (old candidates) (old relations) (old T) (old P) (old order) (old top) (prefixIndex n 7))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_refinementIndexSelectionRawFormula {n}
    (z level r candidates relations T P order top : Fin n) (w : Fin 7 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementIndexSelectionRawFormula z level r candidates relations T P order top w) env ↔
      env z = refinementIndexCode (env level) (env (w 0)) (env (w 1)) (env (w 2)) (env (w 3)) (env (w 4)) ∧
      ZFSet.pair (env (w 0)) (env (w 1)) ∈ env r ∧ env (w 0) ≠ env (w 1) ∧
      ZFSet.pair (env (w 0)) (env (w 5)) ∈ env candidates ∧ env (w 2) ∈ env (w 5) ∧
      ZFSet.pair (env (w 0)) (env (w 6)) ∈ env relations ∧
      env (w 3) ∈ env (w 6) ∧ env (w 4) ∈ env (w 6) ∧
      Realize M.sets (refinementValidityForcingFormula 0 1 2 3 4 5 6)
        ![env (w 2), env (w 3), env (w 4), env T, env P, env order, env top] := by
  have mapped : (fun j : Fin 7 => env (![w 2, w 3, w 4, T, P, order, top] j)) =
      ![env (w 2), env (w 3), env (w 4), env T, env P, env order, env top] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  simp only [refinementIndexSelectionRawFormula, Realize,
    BoundedFormula.realize_toFormula M _ env members,
    BoundedFormula.truth_refinementIndexFormula, BoundedFormula.truth_pairMembershipFormula,
    SetFormula.realize_reindex, mapped]

theorem realize_refinementIndexSelectionFormula {n}
    (z level r candidates relations T P order top : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementIndexSelectionFormula z level r candidates relations T P order top) env ↔
      RefinementIndexSelectionCode M (env level) (env r) (env candidates) (env relations)
        (env T) (env P) (env order) (env top) (env z) := by
  rw [refinementIndexSelectionFormula, realize_exBlock]
  have actual (w : Fin 7 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :=
    M.realize_refinementIndexSelectionRawFormula (suffixIndex n 7 z) (suffixIndex n 7 level)
      (suffixIndex n 7 r) (suffixIndex n 7 candidates) (suffixIndex n 7 relations)
      (suffixIndex n 7 T) (suffixIndex n 7 P) (suffixIndex n 7 order) (suffixIndex n 7 top)
      (prefixIndex n 7) (extendMany 7 w env) (extendMany_members 7 w env ground members)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨w, ground, selected⟩
    exact ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, (actual w ground).1 selected⟩
  · rintro ⟨C, E, U, Rf, Rc, N, V, equal, edge, strict, first, hU, second, hf, hc, forced⟩
    have fields := M.refinementIndexCode_fields_mem (equal ▸ members z)
    have hN := M.pair_right (M.transitive (members candidates) first)
    have hV := M.pair_right (M.transitive (members relations) second)
    let w : Fin 7 → ZFSet.{u} := ![C, E, U, Rf, Rc, N, V]
    have ground : ∀ j, w j ∈ M.sets :=
      Fin.cases fields.2.1 (Fin.cases fields.2.2.1 (Fin.cases fields.2.2.2.1
        (Fin.cases fields.2.2.2.2.1 (Fin.cases fields.2.2.2.2.2
          (Fin.cases hN (Fin.cases hV (fun j => Fin.elim0 j)))))))
    exact ⟨w, ground, (actual w ground).2 ⟨equal, edge, strict, first, hU, second, hf, hc, forced⟩⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def refinementIndices
    (level nodes r candidates relations T1 T2 T P order top : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (RefinementIndexSelectionCode M level r candidates relations T P order top)
    (refinementIndexBound {level} nodes (M.groundRelations T1 P) (M.groundRelations T2 P))

theorem mem_refinementIndices
    (level nodes r candidates relations T1 T2 T P order top z : ZFSet.{u}) :
    z ∈ M.refinementIndices level nodes r candidates relations T1 T2 T P order top ↔
      z ∈ refinementIndexBound {level} nodes (M.groundRelations T1 P) (M.groundRelations T2 P) ∧
        RefinementIndexSelectionCode M level r candidates relations T P order top z :=
  ZFSet.mem_sep

theorem refinementIndexCode_mem_indices
    (level nodes r candidates relations T1 T2 T P order top C E U Rf Rc : ZFSet.{u}) :
    refinementIndexCode level C E U Rf Rc ∈
      M.refinementIndices level nodes r candidates relations T1 T2 T P order top ↔
    C ∈ nodes ∧ E ∈ nodes ∧ U ∈ M.groundRelations T1 P ∧
    Rf ∈ M.groundRelations T2 P ∧ Rc ∈ M.groundRelations T2 P ∧
    ZFSet.pair C E ∈ r ∧ C ≠ E ∧
    ∃ N V, ZFSet.pair C N ∈ candidates ∧ U ∈ N ∧
      ZFSet.pair C V ∈ relations ∧ Rf ∈ V ∧ Rc ∈ V ∧
      Realize M.sets (refinementValidityForcingFormula 0 1 2 3 4 5 6)
        ![U, Rf, Rc, T, P, order, top] := by
  rw [M.mem_refinementIndices, refinementIndexCode_mem_bound]
  constructor
  · rintro ⟨⟨_, hC, hE, hU, hf, hc⟩, c, e, a, f, t, N, V, equal, edge, strict, first, ha, second, hff, hcc, forced⟩
    obtain ⟨_, rfl, rfl, rfl, rfl, rfl⟩ := (refinementIndexCode_eq_iff _ _ _ _ _ _ _ _ _ _ _ _).1 equal
    exact ⟨hC, hE, hU, hf, hc, edge, strict, N, V, first, ha, second, hff, hcc, forced⟩
  · rintro ⟨hC, hE, hU, hf, hc, edge, strict, N, V, first, ha, second, hff, hcc, forced⟩
    exact ⟨⟨ZFSet.mem_singleton.2 rfl, hC, hE, hU, hf, hc⟩,
      C, E, U, Rf, Rc, N, V, rfl, edge, strict, first, ha, second, hff, hcc, forced⟩

theorem refinementIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {level nodes r candidates relations T1 T2 T P order top : ZFSet.{u}}
    (hl : level ∈ M.sets) (hn : nodes ∈ M.sets) (hr : r ∈ M.sets)
    (hc : candidates ∈ M.sets) (hrel : relations ∈ M.sets)
    (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets) (hT : T ∈ M.sets)
    (hP : P ∈ M.sets) (ho : order ∈ M.sets) (ht : top ∈ M.sets) :
    M.refinementIndices level nodes r candidates relations T1 T2 T P order top ∈ M.sets := by
  let B := refinementIndexBound {level} nodes (M.groundRelations T1 P) (M.groundRelations T2 P)
  have hB := M.refinementIndexBound_mem pairing unions powers separation
    (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hl hl) hn
    (M.groundRelations_mem pairing unions powers separation hT1 hP)
    (M.groundRelations_mem pairing unions powers separation hT2 hP)
  let params : Fin 8 → ZFSet.{u} := ![level, r, candidates, relations, T, P, order, top]
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hl (Fin.cases hr (Fin.cases hc (Fin.cases hrel (Fin.cases hT
      (Fin.cases hP (Fin.cases ho (Fin.cases ht (fun j => Fin.elim0 j))))))))
  let φ : SetFormula 9 := refinementIndexSelectionFormula 0 1 2 3 4 5 6 7 8
  have ground := M.separation_mem separation φ params members hB
  have equal : ZFSet.sep (fun z => Realize M.sets φ (extend z params)) B =
      M.refinementIndices level nodes r candidates relations T1 T2 T P order top := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_refinementIndices]
    apply and_congr_right
    intro hz
    exact M.realize_refinementIndexSelectionFormula 0 1 2 3 4 5 6 7 8
      (extend z params) (Fin.cases (M.transitive hB hz) members)
  exact equal ▸ ground

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

noncomputable def niceRefinementIndices (level T1 T2 : ZFSet.{u})
    (valid : ∀ z ∈ T1, IsName s z) : ZFSet.{u} :=
  M.refinementIndices level b.carrier b.conditionOrder
    (M.niceNameCandidateGraph a s b T1 d.principalFix)
    (M.niceNameCandidateGraph a s b T2 d.principalFix) T1 T2
    (Name.familySet ⊤ T1 valid).val s.carrier s.conditionOrder (s.encode ⊤)

theorem niceRefinementIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {level T1 T2 : ZFSet.{u}} (valid : ∀ z ∈ T1, IsName s z)
    (hl : level ∈ M.sets) (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (first : M.niceNameCandidateGraph a s b T1 d.principalFix ∈ M.sets)
    (second : M.niceNameCandidateGraph a s b T2 d.principalFix ∈ M.sets) :
    M.niceRefinementIndices a s b d level T1 T2 valid ∈ M.sets := by
  have top := M.transitive carrier (s.encode_mem ⊤)
  exact M.refinementIndices_mem pairing unions powers separation hl nodes nodeOrder first second
    hT1 hT2 (M.familySet_mem s ⊤ pairing unions powers separation hT1 top valid) carrier order top

theorem niceRefinementIndex_mem_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (level T1 T2 : ZFSet.{u}) (valid : ∀ z ∈ T1, IsName s z)
    (familyGround : (Name.familySet ⊤ T1 valid).val ∈ M.sets)
    (C E : L) (U Rf Rc : (M.nameDomain s).names) :
    refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid ↔
    C < E ∧ U.val.val ∈ M.niceNameCandidates a s T1 (d.principalFix C) ∧
      Rf.val.val ∈ M.niceNameCandidates a s T2 (d.principalFix C) ∧
      Rc.val.val ∈ M.niceNameCandidates a s T2 (d.principalFix C) ∧
      Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula
        (extend U (extend Rf (extend Rc (extend ⟨Name.familySet ⊤ T1 valid, familyGround⟩ Fin.elim0)))) ⊤ := by
  let T : (M.nameDomain s).names := ⟨Name.familySet ⊤ T1 valid, familyGround⟩
  let names := extend U (extend Rf (extend Rc (extend T Fin.elim0)))
  have forcing := M.realize_refinementValidityForcing s pairing unions powers separation collection carrier order
    0 1 2 3 4 5 6 ![U.val.val, Rf.val.val, Rc.val.val, T.val.val, s.carrier, s.conditionOrder, s.encode ⊤]
    names ⊤ rfl rfl rfl rfl rfl rfl rfl
  rw [niceRefinementIndices, M.refinementIndexCode_mem_indices]
  constructor
  · rintro ⟨_, _, _, _, _, edge, strict, N, V, first, hU, second, hf, hc, forced⟩
    have nEq := (M.pair_mem_niceNameCandidateGraph a s b T1 d.principalFix C N).1 first
    have vEq := (M.pair_mem_niceNameCandidateGraph a s b T2 d.principalFix C V).1 second
    subst N
    subst V
    have lower := (b.pair_mem_conditionOrder C E).1 edge
    have different : C ≠ E := fun eq => strict (congrArg b.encode eq)
    exact ⟨lt_of_le_of_ne lower different, hU, hf, hc, forcing.1 forced⟩
  · rintro ⟨strict, hU, hf, hc, forced⟩
    refine ⟨b.encode_mem C, b.encode_mem E, M.niceNameCandidates_subset a s T1 _ hU,
      M.niceNameCandidates_subset a s T2 _ hf, M.niceNameCandidates_subset a s T2 _ hc,
      (b.pair_mem_conditionOrder C E).2 strict.le,
      (fun eq => strict.ne (b.injective eq)), M.niceNameCandidates a s T1 (d.principalFix C),
      M.niceNameCandidates a s T2 (d.principalFix C), ?_, hU, ?_, hf, hc, forcing.2 forced⟩
    · exact (M.pair_mem_niceNameCandidateGraph a s b T1 d.principalFix C _).2 rfl
    · exact (M.pair_mem_niceNameCandidateGraph a s b T2 d.principalFix C _).2 rfl

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (level nodes r candidates relations T1 T2 T P order top : ZFSet.{u})
local notation "I" => M.refinementIndices level nodes r candidates relations T1 T2 T P order top
local notation "bounds" => (![Singleton.singleton level, nodes, nodes, M.groundRelations T1 P,
  M.groundRelations T2 P, M.groundRelations T2 P])

theorem refinementIndices_fields {z : ZFSet.{u}} (hz : z ∈ I) :
    ∃ fields : Fin 6 → ZFSet.{u}, z = nonemptyTupleCode 5 fields ∧ ∀ j, fields j ∈ bounds j := by
  obtain ⟨l, hl, C, hC, E, hE, U, hU, Rf, hf, Rc, hc, eq⟩ :=
    (mem_refinementIndexBound _ _ _ _ z).1 ((M.mem_refinementIndices _ _ _ _ _ _ _ _ _ _ _ _).1 hz).1
  refine ⟨![l, C, E, U, Rf, Rc], eq, ?_⟩
  exact Fin.cases hl (Fin.cases hC (Fin.cases hE (Fin.cases hU
    (Fin.cases hf (Fin.cases hc (fun j => Fin.elim0 j))))))

theorem refinementIndices_field_function (j : Fin 6) :
    ZFSet.IsFunc I (bounds j) (refinementIndexFieldGraph I (bounds j) j) := by
  apply refinementIndexFieldGraph_function
  intro z hz
  obtain ⟨v, equal, bound⟩ := M.refinementIndices_fields _ _ _ _ _ _ _ _ _ _ _ hz
  exact ⟨v, equal, bound j⟩

theorem refinementIndices_fields_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hl : level ∈ M.sets) (hn : nodes ∈ M.sets) (hr : r ∈ M.sets)
    (hc : candidates ∈ M.sets) (hrel : relations ∈ M.sets)
    (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets) (hT : T ∈ M.sets)
    (hP : P ∈ M.sets) (ho : order ∈ M.sets) (ht : top ∈ M.sets) :
    ∀ j : Fin 6, refinementIndexFieldGraph I (bounds j) j ∈ M.sets := by
  have hI := M.refinementIndices_mem pairing unions powers separation
    hl hn hr hc hrel hT1 hT2 hT hP ho ht
  have hV := M.groundRelations_mem pairing unions powers separation hT1 hP
  have hW := M.groundRelations_mem pairing unions powers separation hT2 hP
  have hs : ({level} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hl hl
  have ground : ∀ j : Fin 6, bounds j ∈ M.sets :=
    Fin.cases hs (Fin.cases hn (Fin.cases hn (Fin.cases hV
      (Fin.cases hW (Fin.cases hW (fun j => Fin.elim0 j))))))
  exact fun j => M.refinementIndexFieldGraph_mem pairing unions powers separation hI (ground j) j

theorem refinementIndices_level_graph :
    refinementIndexFieldGraph I {level} 0 = ZFSet.prod I {level} := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (ZFSet.mem_sep.1 hz).1
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    obtain ⟨v, equal, bound⟩ := M.refinementIndices_fields _ _ _ _ _ _ _ _ _ _ _ hx
    have same : y = v 0 := (ZFSet.mem_singleton.1 hy).trans (ZFSet.mem_singleton.1 (bound 0)).symm
    exact (pair_mem_refinementIndexFieldGraph I {level} x y 0).2 ⟨hx, hy, v, equal, same⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

theorem exists_niceRefinementIndex_fields (level T1 T2 : ZFSet.{u})
    (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
    {z : ZFSet.{u}} (member : z ∈ M.niceRefinementIndices a s b d level T1 T2 valid1) :
    ∃ C E : L, ∃ U Rf Rc : (M.nameDomain s).names,
      z = refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val := by
  have bound := ((M.mem_refinementIndices _ _ _ _ _ _ _ _ _ _ _ z).1 member).1
  obtain ⟨l, hl, C, hC, E, hE, U, hU, Rf, hf, Rc, hc, equal⟩ :=
    (mem_refinementIndexBound _ _ _ _ z).1 bound
  have same : l = level := ZFSet.mem_singleton.1 hl
  subst l
  obtain ⟨c, rfl⟩ := (b.mem_carrier C).1 hC
  obtain ⟨e, rfl⟩ := (b.mem_carrier E).1 hE
  have domain := (M.mem_groundRelations T1 s.carrier U).1 hU
  have fine := (M.mem_groundRelations T2 s.carrier Rf).1 hf
  have coarse := (M.mem_groundRelations T2 s.carrier Rc).1 hc
  exact ⟨c, e, ⟨Name.ofSubset valid1 domain.2, domain.1⟩,
    ⟨Name.ofSubset valid2 fine.2, fine.1⟩, ⟨Name.ofSubset valid2 coarse.2, coarse.1⟩, equal⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u

theorem normalizedRefinementIndex_mem
    (M : TransitiveGround.{u})
    {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
    (a : PosetAction G P) (s : Presentation P)
    (b : Presentation L) (d : PosetAction G L)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (level T1 T2 : ZFSet.{u}) (valid : ∀ z ∈ T1, IsName s z)
    (C E : L) (normalized : Assignment (M.nameDomain s) 4)
    (last : (normalized 3).val = Name.familySet ⊤ T1 valid)
    (strict : C < E)
    (niceU : NiceNameCode a s T1 (d.principalFix C) (normalized 0).val.val)
    (niceRf : NiceNameCode a s T2 (d.principalFix C) (normalized 1).val.val)
    (niceRc : NiceNameCode a s T2 (d.principalFix C) (normalized 2).val.val)
    (forced : Forces (M.nameDomain s)
      BoundedFormula.refinementValidityFormula.toFormula normalized ⊤) :
    refinementIndexCode level (b.encode C) (b.encode E)
      (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
        M.niceRefinementIndices a s b d level T1 T2 valid := by
  have familyGround : (Name.familySet ⊤ T1 valid).val ∈ M.sets := by
    rw [← last]
    exact (normalized 3).property
  have lastName : normalized 3 = ⟨Name.familySet ⊤ T1 valid, familyGround⟩ :=
    Subtype.ext last
  have normalizedEq : normalized =
      extend (normalized 0) (extend (normalized 1) (extend (normalized 2)
        (extend ⟨Name.familySet ⊤ T1 valid, familyGround⟩ Fin.elim0))) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases lastName (fun j => Fin.elim0 j)))) i
  apply (M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation
    collection carrier order level T1 T2 valid familyGround C E
      (normalized 0) (normalized 1) (normalized 2)).2
  refine ⟨strict, ?_, ?_, ?_, normalizedEq ▸ forced⟩
  · exact (M.mem_niceNameCandidates a s T1 (d.principalFix C) _).2
      ⟨(normalized 0).property, niceU⟩
  · exact (M.mem_niceNameCandidates a s T2 (d.principalFix C) _).2
      ⟨(normalized 1).property, niceRf⟩
  · exact (M.mem_niceNameCandidates a s T2 (d.principalFix C) _).2
      ⟨(normalized 2).property, niceRc⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

namespace TransitiveGround
noncomputable def niceRefinementIndexBounds (M : TransitiveGround.{u})
    (s : Presentation P) (b : Presentation L) (level T1 T2 : ZFSet.{u}) : Fin 6 → ZFSet.{u} :=
  ![{level}, b.carrier, b.carrier, M.groundRelations T1 s.carrier,
    M.groundRelations T2 s.carrier, M.groundRelations T2 s.carrier]

end TransitiveGround

structure NiceRefinementIndexSystem (M : TransitiveGround.{u})
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (level T1 T2 : ZFSet.{u}) (valid1 : ∀ z ∈ T1, IsName s z)
    (valid2 : ∀ z ∈ T2, IsName s z) : Prop where
  index_ground : M.niceRefinementIndices a s b d level T1 T2 valid1 ∈ M.sets
  family_ground : (Name.familySet ⊤ T1 valid1).val ∈ M.sets
  first_candidates_ground : M.niceNameCandidateGraph a s b T1 d.principalFix ∈ M.sets
  second_candidates_ground : M.niceNameCandidateGraph a s b T2 d.principalFix ∈ M.sets
  field_ground : ∀ j, refinementIndexFieldGraph (M.niceRefinementIndices a s b d level T1 T2 valid1)
    (M.niceRefinementIndexBounds s b level T1 T2 j) j ∈ M.sets
  field_function : ∀ j, ZFSet.IsFunc (M.niceRefinementIndices a s b d level T1 T2 valid1)
    (M.niceRefinementIndexBounds s b level T1 T2 j)
    (refinementIndexFieldGraph (M.niceRefinementIndices a s b d level T1 T2 valid1)
      (M.niceRefinementIndexBounds s b level T1 T2 j) j)
  level_graph : refinementIndexFieldGraph (M.niceRefinementIndices a s b d level T1 T2 valid1)
      {level} 0 = ZFSet.prod (M.niceRefinementIndices a s b d level T1 T2 valid1) {level}
  typed_entries : ∀ C E (U Rf Rc : (M.nameDomain s).names),
    refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1 ↔
    C < E ∧ U.val.val ∈ M.niceNameCandidates a s T1 (d.principalFix C) ∧
      Rf.val.val ∈ M.niceNameCandidates a s T2 (d.principalFix C) ∧
      Rc.val.val ∈ M.niceNameCandidates a s T2 (d.principalFix C) ∧
      Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula
        (extend U (extend Rf (extend Rc (extend ⟨Name.familySet ⊤ T1 valid1, family_ground⟩ Fin.elim0)))) ⊤
  decoded : ∀ z ∈ M.niceRefinementIndices a s b d level T1 T2 valid1,
    ∃ C E : L, ∃ U Rf Rc : (M.nameDomain s).names,
      z = refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val

namespace TransitiveGround
variable (M : TransitiveGround.{u}) (a : PosetAction G P) (s : Presentation P)
variable (b : Presentation L) (d : PosetAction G L)

theorem niceRefinementIndexSystem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {level T1 T2 : ZFSet.{u}} {valid1 : ∀ z ∈ T1, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
    (hl : level ∈ M.sets) (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
    (first : NiceNameSystem M a s b d base directed T1 valid1)
    (second : NiceNameSystem M a s b d base directed T2 valid2) :
    NiceRefinementIndexSystem M a s b d level T1 T2 valid1 valid2 := by
  have top := M.transitive carrier (s.encode_mem ⊤)
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT1 top valid1
  refine ⟨M.niceRefinementIndices_mem a s b d pairing unions powers separation valid1 hl hT1 hT2
    carrier order nodes nodeOrder first.candidate_graph_ground second.candidate_graph_ground,
    family, first.candidate_graph_ground, second.candidate_graph_ground, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.refinementIndices_fields_ground _ _ _ _ _ _ _ _ _ _ _ pairing unions powers separation
      hl nodes nodeOrder first.candidate_graph_ground second.candidate_graph_ground hT1 hT2 family carrier order top
  · exact M.refinementIndices_field_function _ _ _ _ _ _ _ _ _ _ _
  · exact M.refinementIndices_level_graph _ _ _ _ _ _ _ _ _ _ _
  · exact M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
      carrier order level T1 T2 valid1 family
  · exact fun _ hz => M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 hz

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.NiceRefinementIndexSystem
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {G P Q L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder Q] [OrderTop Q]
variable [PartialOrder L]
variable {a : PosetAction G P} {e : PosetAction G Q}
variable {s : Presentation P} {t : Presentation Q} {b : Presentation L} {d : PosetAction G L}
variable {level next T T2 U U2 : ZFSet.{u}}
variable {valid : ∀ z ∈ T, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
variable {upperValid : ∀ z ∈ U, IsName t z} {upperValid2 : ∀ z ∈ U2, IsName t z}
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "J" => M.niceRefinementIndices e t b d next U U2 upperValid

theorem levelCode (first : NiceRefinementIndexSystem M a s b d level T T2 valid valid2) :
    RefinementIndexLevelCode I level := by
  intro z hz
  obtain ⟨C, E, X, Rf, Rc, equal⟩ := first.decoded z hz
  exact ⟨![level, b.encode C, b.encode E, X.val.val, Rf.val.val, Rc.val.val], equal, rfl⟩

theorem different_levels_disjoint
    (first : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
    (second : NiceRefinementIndexSystem M e t b d next U U2 upperValid upperValid2)
    (different : level ≠ next) : ∀ z, ¬ (z ∈ I ∧ z ∈ J) :=
  first.levelCode.disjoint second.levelCode different

theorem union_level_data
    (first : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
    (second : NiceRefinementIndexSystem M e t b d next U U2 upperValid upperValid2)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hLevel : level ∈ M.sets) (hNext : next ∈ M.sets) :
    I ∪ J ∈ M.sets ∧
      refinementIndexFieldGraph (I ∪ J) {level, next} 0 ∈ M.sets ∧
      ZFSet.IsFunc (I ∪ J) {level, next} (refinementIndexFieldGraph (I ∪ J) {level, next} 0) ∧
      refinementIndexFieldGraph (I ∪ J) {level, next} 0 =
        ZFSet.prod I {level} ∪ ZFSet.prod J {next} := by
  have ground := M.binary_union_mem pairing unions first.index_ground second.index_ground
  exact ⟨ground, M.refinementIndexFieldGraph_mem pairing unions powers separation
    ground (M.unorderedPair_mem pairing hLevel hNext) 0,
    first.levelCode.union_level_function second.levelCode,
    first.levelCode.union_level_graph second.levelCode⟩

end PartitionPilot.Forcing.NiceRefinementIndexSystem



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure RefinementObjectSystem (M : TransitiveGround.{u}) (a : PosetAction G P)
    (s : Presentation P) (F : NormalSubgroupFamily G) (K : Subgroup G)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s) : Prop where
  ground : (Name.refinementQuotient T valid U Rf).val ∈ M.sets ∧
    (Name.refinementQuotient T valid U Rc).val ∈ M.sets ∧
    (Name.refinementNaturalMap T valid U Rf Rc).val ∈ M.sets
  support : K ≤ a.stabilizer s (Name.refinementQuotient T valid U Rf) ∧
    K ≤ a.stabilizer s (Name.refinementQuotient T valid U Rc) ∧
    K ≤ a.stabilizer s (Name.refinementNaturalMap T valid U Rf Rc)
  hs : HereditarilySymmetric a s F (Name.refinementQuotient T valid U Rf) ∧
    HereditarilySymmetric a s F (Name.refinementQuotient T valid U Rc) ∧
    HereditarilySymmetric a s F (Name.refinementNaturalMap T valid U Rf Rc)
  classes : ∀ w : Name s, w.val ∈ T →
    (Name.refinementClass T valid Rf w).val ∈ M.sets ∧
    (Name.refinementClass T valid Rc w).val ∈ M.sets ∧
    HereditarilySymmetric a s F (Name.refinementClass T valid Rf w) ∧
    HereditarilySymmetric a s F (Name.refinementClass T valid Rc w)
  class_graphs : Name.refinementClassGraph T valid Rf T valid ∈ M.sets ∧
    Name.refinementClassGraph T valid Rc T valid ∈ M.sets ∧
    Name.refinementPairClassGraph T valid Rf Rc T valid ∈ M.sets
  values : ∀ (H : ConditionFilter P), H.GenericFor (formulaFamily (M.nameDomain s)) →
    RefinementObjectValues {p | H.mem p} T valid U Rf Rc

namespace TransitiveGround
variable (M : TransitiveGround.{u}) (a : PosetAction G P) (s : Presentation P)
variable (b : Presentation L) (d : PosetAction G L) (base : L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem niceRefinementObjects
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {level T1 T2 : ZFSet.{u}} {valid1 : ∀ z ∈ T1, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
    (hl : level ∈ M.sets) (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (closed : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
    (children : ∀ w : Name s, w.val ∈ T1 →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) w)
    (first : NiceNameSystem M a s b d base directed T1 valid1)
    (second : NiceNameSystem M a s b d base directed T2 valid2) :
    NiceRefinementIndexSystem M a s b d level T1 T2 valid1 valid2 ∧
      ∀ C E (U Rf Rc : (M.nameDomain s).names),
        refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
          M.niceRefinementIndices a s b d level T1 T2 valid1 →
        RefinementObjectSystem M a s (d.principalSupportFamily base directed) (d.principalFix C)
          T1 valid1 U.val Rf.val Rc.val := by
  have indices := M.niceRefinementIndexSystem a s b d pairing unions powers separation collection
    hl hT1 hT2 carrier order nodes nodeOrder first second
  refine ⟨indices, ?_⟩
  intro C E U Rf Rc entry
  obtain ⟨_, hU, hRf, hRc, forced⟩ := (indices.typed_entries C E U Rf Rc).1 entry
  have supportedU := ((M.name_mem_niceNameCandidates a s T1 (d.principalFix C) U.val).1 hU).2.2
  have supportedRf := ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rf.val).1 hRf).2.2
  have supportedRc := ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rc.val).1 hRc).2.2
  have hsU := first.candidate_hs C U.val hU
  have hsRf := second.candidate_hs C Rf.val hRf
  have hsRc := second.candidate_hs C Rc.val hRc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨M.refinementQuotient_mem s pairing unions powers separation collection carrier order
        hT1 valid1 U.val Rf.val U.property Rf.property,
      M.refinementQuotient_mem s pairing unions powers separation collection carrier order
        hT1 valid1 U.val Rc.val U.property Rc.property,
      M.refinementNaturalMap_mem s pairing unions powers separation collection carrier order
        hT1 valid1 U.val Rf.val Rc.val U.property Rf.property Rc.property⟩
  · exact ⟨Name.refinementQuotient_support a T1 valid1 closed U.val Rf.val _ supportedU supportedRf,
      Name.refinementQuotient_support a T1 valid1 closed U.val Rc.val _ supportedU supportedRc,
      Name.refinementNaturalMap_support a T1 valid1 closed U.val Rf.val Rc.val _ supportedU supportedRf supportedRc⟩
  · exact ⟨Name.refinementQuotient_hs a T1 valid1 closed _ children U.val Rf.val hsU hsRf,
      Name.refinementQuotient_hs a T1 valid1 closed _ children U.val Rc.val hsU hsRc,
      Name.refinementNaturalMap_hs a T1 valid1 closed _ children U.val Rf.val Rc.val hsU hsRf hsRc⟩
  · intro w hw
    exact ⟨M.refinementClass_mem s pairing unions powers separation collection carrier order
        hT1 valid1 Rf.val w Rf.property (M.transitive hT1 hw),
      M.refinementClass_mem s pairing unions powers separation collection carrier order
        hT1 valid1 Rc.val w Rc.property (M.transitive hT1 hw),
      Name.refinementClass_hs_of_hs a T1 valid1 closed _ children Rf.val w hsRf (children w hw),
      Name.refinementClass_hs_of_hs a T1 valid1 closed _ children Rc.val w hsRc (children w hw)⟩
  · exact ⟨M.refinementClassGraph_mem s pairing unions powers separation collection carrier order
        hT1 hT1 valid1 valid1 Rf.val Rf.property,
      M.refinementClassGraph_mem s pairing unions powers separation collection carrier order
        hT1 hT1 valid1 valid1 Rc.val Rc.property,
      M.refinementPairClassGraph_mem s pairing unions powers separation collection carrier order
        hT1 hT1 valid1 valid1 Rf.val Rc.val Rf.property Rc.property⟩
  · intro H generic
    exact M.refinementObjects_eval s pairing carrier hT1 valid1 indices.family_ground
      U Rf Rc H generic H.top_mem forced

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

theorem niceRefinementIndex_preserves_visibility
    (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (a : PosetAction G P) (t : Presentation G) (maps : a.conditionMapFamily s t ∈ M.sets)
    (b : Presentation L) (d : PosetAction G L) (base : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    {level T1 T2 : ZFSet.{u}} (hT1 : T1 ∈ M.sets)
    {valid1 : ∀ z ∈ T1, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
    (terms : ∀ g (z : Name s), z.val ∈ T1 → (a.act s g z).val ∈ T1)
    (system : NiceNameSystem M a s b d base directed T1 valid1)
    (indices : NiceRefinementIndexSystem M a s b d level T1 T2 valid1 valid2)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1)
    {v : L} (lower : C ≤ v)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {fineClass coarseClass : ZFSet.{u}}
    (visible : fineClass ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T1 (d.principalFix v)))
    (entry : ZFSet.pair fineClass coarseClass ∈
      Name.eval {p | H.mem p} (Name.refinementNaturalMap T1 valid1 U.val Rf.val Rc.val)) :
    coarseClass ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T1 (d.principalFix v)) := by
  obtain ⟨_, hU, _, hRc, forced⟩ := (indices.typed_entries C E U Rf Rc).1 member
  have domain := ((M.name_mem_niceNameCandidates a s T1 (d.principalFix C) U.val).1 hU).2.2
  have relation := ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rc.val).1 hRc).2.2
  have values := M.refinementObjects_eval s pairing carrier hT1 valid1 indices.family_ground
    U Rf Rc H generic H.top_mem forced
  rw [values.natural_map] at entry
  exact M.refinementQuotientMap_preserves_visibility s pairing unions powers separation collection
    carrier order a t maps b d base directed hT1 valid1 terms system U Rf Rc lower domain relation
    H generic values.validity visible entry

end PartitionPilot.Forcing.TransitiveGround

end OAI
