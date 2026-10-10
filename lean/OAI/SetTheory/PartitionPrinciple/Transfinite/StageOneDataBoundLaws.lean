import OAI.SetTheory.PartitionPrinciple.Geometry.RowPositionBounds

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

noncomputable def stageOneAssignment (t u w : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair t (ZFSet.pair u w)

noncomputable def stageOneAssignments (I T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod I (ZFSet.prod T T)

theorem stageOneAssignment_eq_iff (t u w t' u' w' : ZFSet.{u}) :
    stageOneAssignment t u w = stageOneAssignment t' u' w' ↔
      t = t' ∧ u = u' ∧ w = w' := by
  simp only [stageOneAssignment, ZFSet.pair_inj]

theorem stageOneAssignment_mem_assignments (I T t u w : ZFSet.{u}) :
    stageOneAssignment t u w ∈ stageOneAssignments I T ↔
      t ∈ I ∧ u ∈ T ∧ w ∈ T := by
  simp only [stageOneAssignment, stageOneAssignments, ZFSet.pair_mem_prod]

theorem mem_stageOneAssignments (I T z : ZFSet.{u}) :
    z ∈ stageOneAssignments I T ↔
      ∃ t ∈ I, ∃ u ∈ T, ∃ w ∈ T, z = stageOneAssignment t u w := by
  constructor
  · intro member
    obtain ⟨t, ht, rest, hr, rfl⟩ := ZFSet.mem_prod.1 member
    obtain ⟨u, hu, w, hw, rfl⟩ := ZFSet.mem_prod.1 hr
    exact ⟨t, ht, u, hu, w, hw, rfl⟩
  · rintro ⟨t, ht, u, hu, w, hw, rfl⟩
    exact (stageOneAssignment_mem_assignments I T t u w).2 ⟨ht, hu, hw⟩

noncomputable def stageOneAssignmentLevels (I T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (stageOneAssignments I T) {∅}

theorem pair_mem_stageOneAssignmentLevels (I T z level : ZFSet.{u}) :
    ZFSet.pair z level ∈ stageOneAssignmentLevels I T ↔
      z ∈ stageOneAssignments I T ∧ level = ∅ := by
  simp only [stageOneAssignmentLevels, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

theorem stageOneAssignmentLevels_function (I T : ZFSet.{u}) :
    ZFSet.IsFunc (stageOneAssignments I T) {∅} (stageOneAssignmentLevels I T) := by
  refine ⟨fun _ hz => hz, ?_⟩
  intro z hz
  exact ⟨∅, (pair_mem_stageOneAssignmentLevels I T z ∅).2 ⟨hz, rfl⟩,
    fun level entry => ((pair_mem_stageOneAssignmentLevels I T z level).1 entry).2⟩

theorem stageOneAssignmentCut_zero (I T A : ZFSet.{u}) :
    assignmentCut (stageOneAssignmentLevels I T) (natSetCode 0) A = ∅ := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut, natSetCode_zero]
  constructor
  · rintro ⟨_, xi, hxi, _⟩
    exact False.elim (ZFSet.notMem_empty xi hxi)
  · intro hz
    exact False.elim (ZFSet.notMem_empty z hz)

theorem stageOneAssignmentCut_one (I T : ZFSet.{u}) {A : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments I T) :
    assignmentCut (stageOneAssignmentLevels I T) (natSetCode 1) A = A := by
  apply assignmentCut_eq_of_lower
  intro z hz
  exact ⟨∅, ZFSet.mem_insert ∅ ∅,
    (pair_mem_stageOneAssignmentLevels I T z ∅).2 ⟨subset hz, rfl⟩⟩

namespace BoundedFormula

def stageOneAssignmentFormula {n : Nat} (z t u w : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 2 z ![t, u, w]

theorem truth_stageOneAssignmentFormula {n : Nat} (z t u w : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (stageOneAssignmentFormula z t u w) env ↔
      env z = stageOneAssignment (env t) (env u) (env w) :=
  truth_nonemptyTupleFormula 2 z ![t, u, w] env

end BoundedFormula

end

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def groundSmallSubsets (B N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun D => M.groundEmbeddable D N) (M.groundPower B)

theorem mem_groundSmallSubsets (B N D : ZFSet.{u}) :
    D ∈ M.groundSmallSubsets B N ↔ D ∈ M.sets ∧ D ⊆ B ∧ M.groundEmbeddable D N := by
  rw [groundSmallSubsets, ZFSet.mem_sep, M.mem_groundPower]
  exact and_assoc

theorem groundSmallSubsets_mem (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets)
    {B N : ZFSet.{u}} (hB : B ∈ M.sets) (hN : N ∈ M.sets) :
    M.groundSmallSubsets B N ∈ M.sets := by
  have hW := M.groundPower_mem powers hB
  have selected := M.separation_mem separation (hasInjectionFormula 0 1)
    (extend N Fin.elim0) (Fin.cases hN (fun i => Fin.elim0 i)) hW
  have eq : ZFSet.sep (fun D => Realize M.sets (hasInjectionFormula 0 1)
      (extend D (extend N Fin.elim0))) (M.groundPower B) = M.groundSmallSubsets B N := by
    apply ZFSet.ext
    intro D
    rw [ZFSet.mem_sep, groundSmallSubsets, ZFSet.mem_sep]
    apply and_congr_right
    intro hD
    exact M.realize_hasInjectionFormula 0 1 _
      (Fin.cases (M.transitive hW hD) (Fin.cases hN (fun i => Fin.elim0 i)))
  exact eq ▸ selected

theorem stageOneAssignment_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {t u w : ZFSet.{u}} (ht : t ∈ M.sets) (hu : u ∈ M.sets) (hw : w ∈ M.sets) :
    stageOneAssignment t u w ∈ M.sets :=
  M.orderedPair_mem pairing ht (M.orderedPair_mem pairing hu hw)

theorem stageOneAssignment_fields_mem {t u w : ZFSet.{u}}
    (ground : stageOneAssignment t u w ∈ M.sets) :
    t ∈ M.sets ∧ u ∈ M.sets ∧ w ∈ M.sets :=
  ⟨M.pair_left ground, M.pair_left (M.pair_right ground), M.pair_right (M.pair_right ground)⟩

theorem stageOneAssignments_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I T : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets) :
    stageOneAssignments I T ∈ M.sets :=
  M.prod_mem pairing unions powers separation hI (M.prod_mem pairing unions powers separation hT hT)

theorem stageOneAssignmentLevels_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I T : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets) :
    stageOneAssignmentLevels I T ∈ M.sets := by
  have hz := M.empty_mem ⟨I, hI⟩
  have one : ({∅} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hz hz
  exact M.prod_mem pairing unions powers separation
    (M.stageOneAssignments_mem pairing unions powers separation hI hT) one

noncomputable def stageOneCandidateBound (rawRowCarrier I T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod rawRowCarrier (M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega)

theorem pair_mem_stageOneCandidateBound (rawRowCarrier I T p A : ZFSet.{u}) :
    ZFSet.pair p A ∈ M.stageOneCandidateBound rawRowCarrier I T ↔
      p ∈ rawRowCarrier ∧ A ∈ M.sets ∧ A ⊆ stageOneAssignments I T ∧
        M.groundEmbeddable A ZFSet.omega := by
  rw [stageOneCandidateBound, ZFSet.pair_mem_prod, M.mem_groundSmallSubsets]

theorem mem_stageOneCandidateBound (rawRowCarrier I T z : ZFSet.{u}) :
    z ∈ M.stageOneCandidateBound rawRowCarrier I T ↔
      ∃ p ∈ rawRowCarrier, ∃ A ∈ M.sets, A ⊆ stageOneAssignments I T ∧
        M.groundEmbeddable A ZFSet.omega ∧ z = ZFSet.pair p A := by
  constructor
  · intro member
    obtain ⟨p, hp, A, hA, equal⟩ := ZFSet.mem_prod.1 member
    obtain ⟨ground, subset, small⟩ := (M.mem_groundSmallSubsets (stageOneAssignments I T) ZFSet.omega A).1 hA
    exact ⟨p, hp, A, ground, subset, small, equal⟩
  · rintro ⟨p, hp, A, ground, subset, small, rfl⟩
    exact (M.pair_mem_stageOneCandidateBound rawRowCarrier I T p A).2 ⟨hp, ground, subset, small⟩

theorem stageOneCandidateBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rawRowCarrier I T : ZFSet.{u}} (hRow : rawRowCarrier ∈ M.sets)
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.stageOneCandidateBound rawRowCarrier I T ∈ M.sets :=
  M.prod_mem pairing unions powers separation hRow (M.groundSmallSubsets_mem powers separation
    (M.stageOneAssignments_mem pairing unions powers separation hI hT) omega)

theorem stageOneCandidateBound_empty {rawRowCarrier I T p : ZFSet.{u}}
    (hRow : rawRowCarrier ∈ M.sets) (hp : p ∈ rawRowCarrier) :
    ZFSet.pair p ∅ ∈ M.stageOneCandidateBound rawRowCarrier I T :=
  (M.pair_mem_stageOneCandidateBound rawRowCarrier I T p ∅).2
    ⟨hp, M.empty_mem ⟨rawRowCarrier, hRow⟩,
      fun z hz => False.elim (ZFSet.notMem_empty z hz),
      M.empty_groundEmbeddable ZFSet.omega ⟨rawRowCarrier, hRow⟩⟩

end TransitiveGround

section
open SetRealization SetFormula
universe u

noncomputable def stageOneDataBounds (A I T S L mu X r anchors tuples : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ A, ∃ D ∈ L, ∃ i ∈ I, ∃ u ∈ T, ∃ w ∈ T, ∃ E ∈ L,
    ∃ fu ∈ S, ∃ fw ∈ S, z = ZFSet.pair v D ∧ v = stageOneAssignment i u w ∧
      ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
      ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
      RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D)
    (ZFSet.prod A L)

theorem mem_stageOneDataBounds (A I T S L mu X r anchors tuples z : ZFSet.{u}) :
    z ∈ stageOneDataBounds A I T S L mu X r anchors tuples ↔
      ∃ v ∈ A, ∃ D ∈ L, ∃ i ∈ I, ∃ u ∈ T, ∃ w ∈ T, ∃ E ∈ L,
        ∃ fu ∈ S, ∃ fw ∈ S, z = ZFSet.pair v D ∧ v = stageOneAssignment i u w ∧
          ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
          ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
          RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D := by
  rw [stageOneDataBounds, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨v,hv,D,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨hv,hD⟩,
      v,hv,D,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩

theorem pair_mem_stageOneDataBounds (A I T S L mu X r anchors tuples v D : ZFSet.{u}) :
    ZFSet.pair v D ∈ stageOneDataBounds A I T S L mu X r anchors tuples ↔
      v ∈ A ∧ D ∈ L ∧ ∃ i ∈ I, ∃ u ∈ T, ∃ w ∈ T, ∃ E ∈ L, ∃ fu ∈ S, ∃ fw ∈ S,
        v = stageOneAssignment i u w ∧ ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
        ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
        RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D := by
  rw [mem_stageOneDataBounds]
  constructor
  · rintro ⟨v',hv,D',hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective equal
    exact ⟨hv,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rest⟩
  · rintro ⟨hv,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rest⟩
    exact ⟨v,hv,D,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rfl,rest⟩

namespace BoundedFormula

def stageOneDataBoundEntryFormula {n} (z A I T S L mu X r anchors tuples : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ.succ.succ.succ.succ
  exMem A (exMem L.succ (exMem I.succ.succ (exMem T.succ.succ.succ
    (exMem T.succ.succ.succ.succ (exMem L.succ.succ.succ.succ.succ
      (exMem S.succ.succ.succ.succ.succ.succ (exMem S.succ.succ.succ.succ.succ.succ.succ
        (.conj (orderedPairFormula (lift z) 7 6)
          (.conj (stageOneAssignmentFormula 7 5 4 3)
            (.conj (pairMembershipFormula 5 2 (lift anchors))
              (.conj (pairMembershipFormula 2 6 (lift r))
                (.conj (pairMembershipFormula 1 4 (lift tuples))
                  (.conj (pairMembershipFormula 0 3 (lift tuples))
                    (.conj (rowPositionBoundFormula (lift mu) (lift X) (lift r) 1 6)
                      (rowPositionBoundFormula (lift mu) (lift X) (lift r) 0 6)))))))))))))))

theorem truth_stageOneDataBoundEntryFormula {n} (z A I T S L mu X r anchors tuples : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (stageOneDataBoundEntryFormula z A I T S L mu X r anchors tuples) env ↔
      ∃ v ∈ env A, ∃ D ∈ env L, ∃ i ∈ env I, ∃ u ∈ env T, ∃ w ∈ env T, ∃ E ∈ env L,
        ∃ fu ∈ env S, ∃ fw ∈ env S, env z = ZFSet.pair v D ∧ v = stageOneAssignment i u w ∧
          ZFSet.pair i E ∈ env anchors ∧ ZFSet.pair E D ∈ env r ∧
          ZFSet.pair fu u ∈ env tuples ∧ ZFSet.pair fw w ∈ env tuples ∧
          RowPositionBound (env mu) (env X) (env r) fu D ∧
          RowPositionBound (env mu) (env X) (env r) fw D := by
  simp only [stageOneDataBoundEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_stageOneAssignmentFormula, truth_pairMembershipFormula, truth_rowPositionBoundFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem stageOneDataBounds_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A I T S L mu X r anchors tuples : ZFSet.{u}}
    (hA : A ∈ M.sets) (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hS : S ∈ M.sets)
    (hL : L ∈ M.sets) (hmu : mu ∈ M.sets) (hX : X ∈ M.sets) (hr : r ∈ M.sets)
    (hAnchors : anchors ∈ M.sets) (hTuples : tuples ∈ M.sets) :
    stageOneDataBounds A I T S L mu X r anchors tuples ∈ M.sets := by
  let params : Fin 10 → ZFSet.{u} := ![A,I,T,S,L,mu,X,r,anchors,tuples]
  have members : ∀ j, params j ∈ M.sets := Fin.cases hA (Fin.cases hI (Fin.cases hT
    (Fin.cases hS (Fin.cases hL (Fin.cases hmu (Fin.cases hX (Fin.cases hr
      (Fin.cases hAnchors (Fin.cases hTuples (fun j => Fin.elim0 j))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.stageOneDataBoundEntryFormula 0 1 2 3 4 5 6 7 8 9 10) params members
    (M.prod_mem pairing unions powers separation hA hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.stageOneDataBoundEntryFormula 0 1 2 3 4 5 6 7 8 9 10) (extend z params))
      (ZFSet.prod A L) = stageOneDataBounds A I T S L mu X r anchors tuples := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, stageOneDataBounds, ZFSet.mem_sep,
      BoundedFormula.truth_stageOneDataBoundEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

end

open SetRealization
universe u

theorem stageOneDataBounds_assignment_entry (A I T S L mu X r anchors tuples i u w D : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) D ∈ stageOneDataBounds A I T S L mu X r anchors tuples ↔
      stageOneAssignment i u w ∈ A ∧ D ∈ L ∧ i ∈ I ∧ u ∈ T ∧ w ∈ T ∧
      ∃ E ∈ L, ∃ fu ∈ S, ∃ fw ∈ S,
        ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
        ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
        RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D := by
  rw [pair_mem_stageOneDataBounds]
  constructor
  · rintro ⟨member,hD,i',hi,u',hu,w',hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩
    obtain ⟨rfl,rfl,rfl⟩ := (stageOneAssignment_eq_iff i u w i' u' w').1 equal
    exact ⟨member,hD,hi,hu,hw,E,hE,fu,hfu,fw,hfw,rest⟩
  · rintro ⟨member,hD,hi,hu,hw,E,hE,fu,hfu,fw,hfw,rest⟩
    exact ⟨member,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rfl,rest⟩

theorem stageOneDataBounds_mono {L : Type u} [Preorder L] (b : Presentation L)
    {A I T S mu X anchors tuples v : ZFSet.{u}} {D E : L}
    (member : ZFSet.pair v (b.encode D) ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples) (le : D ≤ E) :
    ZFSet.pair v (b.encode E) ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples := by
  obtain ⟨hv,_,i,hi,u,hu,w,hw,anchor,hAnchor,fu,hfu,fw,hfw,equal,edge,below,tupleU,tupleW,boundU,boundW⟩ :=
    (pair_mem_stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples v (b.encode D)).1 member
  obtain ⟨anchor,rfl⟩ := (b.mem_carrier anchor).1 hAnchor
  exact (pair_mem_stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples v (b.encode E)).2
    ⟨hv,b.encode_mem E,i,hi,u,hu,w,hw,b.encode anchor,b.encode_mem anchor,fu,hfu,fw,hfw,equal,edge,
      (b.pair_mem_conditionOrder anchor E).2 (le_trans ((b.pair_mem_conditionOrder anchor D).1 below) le),
      tupleU,tupleW,boundU.mono b le,boundW.mono b le⟩

theorem stageOneDataBounds_total {L : Type u} [Preorder L] (b : Presentation L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    {A I T S mu X anchors tuples : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments I T) (anchorFunction : ZFSet.IsFunc I b.carrier anchors)
    (provenance : ∀ u ∈ T, ∃ f ∈ S, ZFSet.pair f u ∈ tuples)
    (positionBounds : ∀ f ∈ S, ∃ D : L, RowPositionBound mu X b.conditionOrder f (b.encode D)) :
    ∀ v ∈ A, ∃ D ∈ b.carrier, ZFSet.pair v D ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples := by
  intro v hv
  obtain ⟨i,hi,u,hu,w,hw,rfl⟩ := (mem_stageOneAssignments I T v).1 (subset hv)
  obtain ⟨anchor,edge,_⟩ := anchorFunction.2 i hi
  have hAnchor := (ZFSet.pair_mem_prod.1 (anchorFunction.1 edge)).2
  obtain ⟨anchor,rfl⟩ := (b.mem_carrier anchor).1 hAnchor
  obtain ⟨fu,hfu,tupleU⟩ := provenance u hu
  obtain ⟨fw,hfw,tupleW⟩ := provenance w hw
  obtain ⟨Du,boundU⟩ := positionBounds fu hfu
  obtain ⟨Dw,boundW⟩ := positionBounds fw hfw
  obtain ⟨middle,anchorBelow,uBelow⟩ := directed anchor Du
  obtain ⟨D,middleBelow,wBelow⟩ := directed middle Dw
  refine ⟨b.encode D,b.encode_mem D,?_⟩
  exact (stageOneDataBounds_assignment_entry A I T S b.carrier mu X b.conditionOrder anchors tuples
    i u w (b.encode D)).2
    ⟨hv,b.encode_mem D,hi,hu,hw,b.encode anchor,b.encode_mem anchor,fu,hfu,fw,hfw,edge,
      (b.pair_mem_conditionOrder anchor D).2 (le_trans anchorBelow middleBelow),tupleU,tupleW,
      boundU.mono b (le_trans uBelow middleBelow),boundW.mono b wBelow⟩

end PartitionPilot.Forcing

end OAI
