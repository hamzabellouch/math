import OAI.SetTheory.PartitionPrinciple.Definability.CompressionExternalStepRealization
import OAI.SetTheory.PartitionPrinciple.Definability.IntervalHeightFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIndexedSubstructures

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u
namespace BoundedFormula
open SetFormula

def intervalHeightCandidateFormula {n}
    (Ps rs D rD lo hi i f boundPs boundRs : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ
  exMem boundPs (exMem boundRs.succ
    (.conj (pairMembershipFormula (lift i) 1 (lift Ps))
      (.conj (pairMembershipFormula (lift i) 0 (lift rs))
        (intervalHeightFormula 1 0 (lift D) (lift rD) (lift lo) (lift hi) (lift f)))))

theorem truth_intervalHeightCandidateFormula {n}
    (Ps rs D rD lo hi i f boundPs boundRs : Fin n) (env : Fin n → ZFSet.{u})
    (sourceBound : env boundPs = ⋃₀ ⋃₀ env Ps)
    (orderBound : env boundRs = ⋃₀ ⋃₀ env rs) :
    Truth (intervalHeightCandidateFormula Ps rs D rD lo hi i f boundPs boundRs) env ↔
      intervalHeightCandidate (env Ps) (env rs) (env D) (env rD)
        (env lo) (env hi) (env i) (env f) := by
  simp only [intervalHeightCandidateFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_intervalHeightFormula]
  change (∃ P ∈ env boundPs, ∃ r ∈ env boundRs,
    ZFSet.pair (env i) P ∈ env Ps ∧ ZFSet.pair (env i) r ∈ env rs ∧
      IntervalHeightCode P r (env D) (env rD) (env lo) (env hi) (env f)) ↔ _
  rw [sourceBound, orderBound]
  rfl

def intervalHeightRelationEntryFormula {n}
    (z I W Ps rs D rD lo hi boundPs boundRs : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (intervalHeightCandidateFormula Ps.succ.succ rs.succ.succ D.succ.succ
        rD.succ.succ lo.succ.succ hi.succ.succ 1 0 boundPs.succ.succ boundRs.succ.succ)))

theorem truth_intervalHeightRelationEntryFormula {n}
    (z I W Ps rs D rD lo hi boundPs boundRs : Fin n) (env : Fin n → ZFSet.{u})
    (sourceBound : env boundPs = ⋃₀ ⋃₀ env Ps)
    (orderBound : env boundRs = ⋃₀ ⋃₀ env rs) :
    Truth (intervalHeightRelationEntryFormula z I W Ps rs D rD lo hi boundPs boundRs) env ↔
      ∃ i ∈ env I, ∃ f ∈ env W, env z = ZFSet.pair i f ∧
        intervalHeightCandidate (env Ps) (env rs) (env D) (env rD) (env lo) (env hi) i f := by
  simp only [intervalHeightRelationEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply exists_congr
  intro f
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_intervalHeightCandidateFormula Ps.succ.succ rs.succ.succ
    D.succ.succ rD.succ.succ lo.succ.succ hi.succ.succ 1 0 boundPs.succ.succ boundRs.succ.succ
    (extend f (extend i env)) sourceBound orderBound)

end BoundedFormula

namespace TransitiveGround
open SetFormula

theorem intervalHeightRelation_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W Ps rs D rD lo hi : ZFSet.{u}}
    (hI : I ∈ M.sets) (hW : W ∈ M.sets) (hPs : Ps ∈ M.sets) (hrs : rs ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hlo : lo ∈ M.sets) (hhi : hi ∈ M.sets) :
    intervalHeightRelation I W Ps rs D rD lo hi ∈ M.sets := by
  have sourceBound := M.union_mem unions (M.union_mem unions hPs)
  have orderBound := M.union_mem unions (M.union_mem unions hrs)
  let params := extend I (extend W (extend Ps (extend rs (extend D (extend rD
    (extend lo (extend hi (extend (⋃₀ ⋃₀ Ps) (extend (⋃₀ ⋃₀ rs) Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.intervalHeightRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hPs (Fin.cases hrs (Fin.cases hD
      (Fin.cases hrD (Fin.cases hlo (Fin.cases hhi (Fin.cases sourceBound
        (Fin.cases orderBound (fun j => Fin.elim0 j)))))))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.intervalHeightRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10)
      (extend z params)) (ZFSet.prod I W) = intervalHeightRelation I W Ps rs D rD lo hi := by
    apply ZFSet.ext
    intro z
    rw [intervalHeightRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_intervalHeightRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10
        (extend z params) rfl rfl)
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u

theorem exists_intervalHeight_family (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I B Ps rs D rD c lo hi : ZFSet.{u}}
    (sources : FunctionGraphOn I Ps) (orders : FunctionGraphOn I rs)
    (sourceBound : ∀ i, sources.value i ⊆ B)
    (hI : I ∈ M.sets) (hB : B ∈ M.sets) (hPs : Ps ∈ M.sets) (hrs : rs ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (hlo : lo ∈ M.sets) (hhi : hi ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (injection : InjectionCode D ZFSet.omega c)
    (witnesses : ∀ i, ∃ f ∈ M.sets, IntervalHeightCode (sources.value i) (orders.value i) D rD lo hi f) :
    ∃ family ∈ M.sets, ZFSet.IsFunc I (M.groundRelations B D) family ∧
      ∀ (i : {i : ZFSet.{u} // i ∈ I}) f, ZFSet.pair i.val f ∈ family →
        f ∈ M.sets ∧ IntervalHeightCode (sources.value i) (orders.value i) D rD lo hi f ∧
        relationImage (sources.value i) D f ∈ M.sets ∧
        M.groundEmbeddable (relationImage (sources.value i) D f) ZFSet.omega := by
  let W := M.groundRelations B D
  have hW : W ∈ M.sets := M.groundRelations_mem pairing unions powers separation hB hD
  have hRelation := M.intervalHeightRelation_mem pairing unions powers separation
    hI hW hPs hrs hD hrD hlo hhi
  have total : ∀ i ∈ I, ∃ f ∈ W,
      ZFSet.pair i f ∈ intervalHeightRelation I W Ps rs D rD lo hi := by
    intro i memI
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, memI⟩
    obtain ⟨f, ground, code⟩ := witnesses j
    have bound : f ⊆ ZFSet.prod B D := by
      intro z hz
      obtain ⟨x, hx, a, ha, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨sourceBound j hx, ha⟩
    have fW : f ∈ W := (M.mem_groundRelations B D f).2 ⟨ground, bound⟩
    exact ⟨f, fW, (pair_mem_intervalHeightRelation I W Ps rs D rD lo hi i f).2
      ⟨memI, fW, (intervalHeightCandidate_iff sources orders j f).2 code⟩⟩
  obtain ⟨family, ground, function, selected⟩ := M.uniformize_relation
    pairing unions powers separation choice hI hW hRelation total
  refine ⟨family, ground, function, ?_⟩
  intro i f entry
  have candidate := (pair_mem_intervalHeightRelation I W Ps rs D rD lo hi i.val f).1 (selected entry)
  have fGround := ((M.mem_groundRelations B D f).1 candidate.2.1).1
  have code := (intervalHeightCandidate_iff sources orders i f).1 candidate.2.2
  have rangeGround := M.relationImage_mem separation (sources.value_mem M hPs i) hD fGround
  exact ⟨fGround, code, rangeGround, M.groundEmbeddable_restrict separation rangeGround hOmega
    (fun _ hz => ((mem_relationImage _ _ _ _).1 hz).1) ⟨c, hc, injection⟩⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalPointOrder (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  flatCopyOrderGraph (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (completion.externalPointClassifier P r μ A) (completion.algebra.union.fields 1)

noncomputable def externalPointMeet (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  canonicalMeetGraph (completion.externalPointCarrier P r μ A) (completion.externalPointOrder P r μ A)

noncomputable def externalPointAction (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  let S := externalChildLetters I P (externalRectangles P G r μ A)
  flatCopyActionGraph (M.externalGroupCarrier G S m one) (completion.algebra.union.fields 0)
    (completion.externalPointCarrier P r μ A) (completion.externalPointClassifier P r μ A)
    (M.externalGroupMultiplication G S m one)

noncomputable def externalCopyGraph (P r μ A w : ZFSet.{u}) : ZFSet.{u} :=
  flatCopyEmbeddingGraph (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (completion.externalPointClassifier P r μ A) w

end GroundCompressionCompletion

structure GroundExternalGeometryData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P r μ A : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) : Prop where
  carrier_ground : completion.externalPointCarrier P r μ A ∈ M.sets
  classifier_ground : completion.externalPointClassifier P r μ A ∈ M.sets
  order_ground : completion.externalPointOrder P r μ A ∈ M.sets
  meet_ground : completion.externalPointMeet P r μ A ∈ M.sets
  action_ground : completion.externalPointAction P r μ A ∈ M.sets
  meet : MeetOrderCode (completion.externalPointCarrier P r μ A)
    (completion.externalPointOrder P r μ A) (completion.externalPointMeet P r μ A)
  action : PosetActionCode
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.externalPointCarrier P r μ A)
    (M.externalGroupMultiplication G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.externalPointOrder P r μ A) (completion.externalPointAction P r μ A)
  copies_ground : ∀ w ∈ M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one,
    completion.externalCopyGraph P r μ A w ∈ M.sets
  copies : ∀ w ∈ M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one,
    MeetEmbeddingCode (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
      (completion.algebra.union.fields 1) (completion.externalPointOrder P r μ A)
      (completion.algebra.union.fields 2) (completion.externalPointMeet P r μ A)
      (completion.externalCopyGraph P r μ A w)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "U" => completion.algebra.union.fields 0
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground

noncomputable def externalPointPresentation :
    letI := group.toGroup
    Presentation ((family).Node (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet)) := by
  letI := group.toGroup
  have hE : (sGroup).carrier ∈ M.sets := by
    rw [completion.externalFamilyGroupPresentation_carrier]
    exact data.group.carrier_mem
  exact M.flatCopyPresentation pairing unions powers separation infinite (family)
    (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet)
    (sGroup) (SetMembers.presentation U)
    (completion.externalFlatSteps_iff group oldAction data.original pairing unions powers separation infinite
      hG data.words.letters_ground) hE (completion.algebra.union.ground 0)

theorem externalPointPresentation_carrier :
    letI := group.toGroup
    (data.externalPointPresentation group oldAction pairing unions powers separation infinite hG).carrier =
      completion.externalPointCarrier P0 r0 μ0 A0 := by
  let := group.toGroup
  change equivalenceClasses (ZFSet.prod (sGroup).carrier U)
    (M.finitePathClosure (ZFSet.prod (sGroup).carrier U) (completion.externalFlatSteps P0 r0 μ0 A0)) = _
  rw [completion.externalFamilyGroupPresentation_carrier]
  rfl

theorem externalPointClassifier_entry_iff :
    letI := group.toGroup
    let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
    let q := data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
    ∀ (w : External (SetMembers G) (family).Letters) (x : SetMembers U) (z : (family).Node a),
      ZFSet.pair (ZFSet.pair ((sGroup).encode w) (SetMembers.raw x)) (q.encode z) ∈
        completion.externalPointClassifier P0 r0 μ0 A0 ↔ ((family).copy a w).toFun x = z := by
  let := group.toGroup
  dsimp only
  have hE : (sGroup).carrier ∈ M.sets := by
    rw [completion.externalFamilyGroupPresentation_carrier]
    exact data.group.carrier_mem
  have entries := M.flatCopyClassifier_entry_iff pairing unions powers separation infinite (family)
    (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet)
    (sGroup) (SetMembers.presentation U)
    (completion.externalFlatSteps_iff group oldAction data.original pairing unions powers separation infinite
      hG data.words.letters_ground) hE (completion.algebra.union.ground 0)
  intro w x z
  have entry := entries w x z
  change ZFSet.pair (ZFSet.pair ((sGroup).encode w) (SetMembers.raw x))
    ((data.externalPointPresentation group oldAction pairing unions powers separation infinite hG).encode z) ∈
    equivalenceClassifier (ZFSet.prod (sGroup).carrier U)
      (M.finitePathClosure (ZFSet.prod (sGroup).carrier U) (completion.externalFlatSteps P0 r0 μ0 A0)) ↔ _ at entry
  rw [completion.externalFamilyGroupPresentation_carrier] at entry
  exact entry

theorem externalGeometry_entries :
    letI := group.toGroup
    let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
    let q := data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
    (∀ x y, ZFSet.pair (q.encode x) (q.encode y) ∈ completion.externalPointOrder P0 r0 μ0 A0 ↔
      ((family).gluedOrder a).le x y) ∧
    (∀ x y z, ZFSet.pair (ZFSet.pair (q.encode x) (q.encode y)) (q.encode z) ∈
      completion.externalPointMeet P0 r0 μ0 A0 ↔ ((family).gluedOrder a).meet x y = z) ∧
    (∀ w x y, ZFSet.pair (ZFSet.pair ((sGroup).encode w) (q.encode x)) (q.encode y) ∈
      completion.externalPointAction P0 r0 μ0 A0 ↔ (family).translate a w x = y) ∧
    (∀ w x y, ZFSet.pair (SetMembers.raw x) (q.encode y) ∈
      completion.externalCopyGraph P0 r0 μ0 A0 ((sGroup).encode w) ↔ ((family).copy a w).toFun x = y) := by
  let := group.toGroup
  dsimp only
  let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
  let q := data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
  let s := sGroup
  let t := SetMembers.presentation U
  have classed := data.externalPointClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  have sCarrier := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qCarrier := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have multiplication := completion.externalFamilyGroupPresentation_multiplication group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  change s.carrier = M.externalGroupCarrier G
    (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one at sCarrier
  change q.carrier = completion.externalPointCarrier P0 r0 μ0 A0 at qCarrier
  change M.externalGroupMultiplication G
    (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one =
      (s.product s).graph s (fun p => p.1 * p.2) at multiplication
  have tCarrier : t.carrier = U := rfl
  have related : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ completion.algebra.union.fields 1 ↔
      completion.algebra.union.meet.toSmallMeetOrder.le x y := fun _ _ => Iff.rfl
  have order := flatCopy_order_iff (family) a s t q classed related
  have meet := q.canonicalMeetGraph_iff ((family).gluedOrder a) order
  have action := flatCopy_action_iff (family) a s t q classed
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [sCarrier, tCarrier, qCarrier, GroundCompressionCompletion.externalPointOrder] using order
  · simpa only [sCarrier, tCarrier, qCarrier, GroundCompressionCompletion.externalPointOrder,
      GroundCompressionCompletion.externalPointMeet] using meet
  · simpa only [sCarrier, tCarrier, qCarrier, ← multiplication,
      GroundCompressionCompletion.externalPointAction] using action
  · intro w x y
    change ZFSet.pair (t.encode x) (q.encode y) ∈ flatCopyEmbeddingGraph U
      (completion.externalPointCarrier P0 r0 μ0 A0) (completion.externalPointClassifier P0 r0 μ0 A0) (s.encode w) ↔ _
    rw [pair_mem_flatCopyEmbeddingGraph]
    exact ⟨fun entry => (classed w x y).1 entry.2.2,
      fun equal => ⟨SetMembers.raw_mem x, qCarrier ▸ q.encode_mem y, (classed w x y).2 equal⟩⟩

include data group oldAction pairing unions powers separation infinite hG in
theorem externalGeometryData (hP : P0 ∈ M.sets) :
    GroundExternalGeometryData M initial I Sources Reps G m one T τ P0 r0 μ0 A0 completion := by
  let := group.toGroup
  let a := completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
  let s := sGroup
  let t := SetMembers.presentation U
  let q := data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
  have classed := data.externalPointClassifier_entry_iff group oldAction pairing unions powers separation infinite hG
  have sCarrier := completion.externalFamilyGroupPresentation_carrier group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  have qCarrier := data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG
  have multiplication := completion.externalFamilyGroupPresentation_multiplication group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  change s.carrier = M.externalGroupCarrier G
    (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one at sCarrier
  change q.carrier = completion.externalPointCarrier P0 r0 μ0 A0 at qCarrier
  change M.externalGroupMultiplication G
    (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one =
      (s.product s).graph s (fun p => p.1 * p.2) at multiplication
  have tCarrier : t.carrier = U := rfl
  have identity := completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground
  change M.externalGroupIdentity G
    (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one = s.encode 1 at identity
  have quot := data.point_quotient_ground pairing unions powers separation infinite hP hG
  have hQ := quot.2.2.1
  have hClassifier := quot.2.2.2.1
  have hOrder := M.flatCopyOrderGraph_mem pairing unions powers separation data.group.carrier_mem
    (completion.algebra.union.ground 0) hQ hClassifier (completion.algebra.union.ground 1)
  have related : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ completion.algebra.union.fields 1 ↔
      completion.algebra.union.meet.toSmallMeetOrder.le x y := fun _ _ => Iff.rfl
  refine ⟨hQ, hClassifier, hOrder, M.canonicalMeetGraph_mem pairing unions powers separation hQ hOrder,
    M.flatCopyActionGraph_mem pairing unions powers separation data.group.carrier_mem
      (completion.algebra.union.ground 0) hQ hClassifier data.group.multiplication_mem, ?_, ?_, ?_, ?_⟩
  · have code := flatCopy_meetOrder (family) a s t q classed related
    simpa only [sCarrier, tCarrier, qCarrier, GroundCompressionCompletion.externalPointOrder,
      GroundCompressionCompletion.externalPointMeet] using code
  · have code := flatCopy_actionCode (family) a s t q classed related
    simpa only [sCarrier, tCarrier, qCarrier, ← multiplication, ← identity,
      GroundCompressionCompletion.externalPointOrder, GroundCompressionCompletion.externalPointAction] using code
  · intro w hw
    exact M.flatCopyEmbeddingGraph_mem pairing unions powers separation (completion.algebra.union.ground 0)
      hQ hClassifier (M.transitive data.group.carrier_mem hw)
  · intro w hw
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 (sCarrier.symm ▸ hw)
    have code := flatCopyEmbeddingGraph_code (family) a s t q classed related
      (fun x y z => (completion.algebra.union.meet.toSmallMeetOrder_meet_eq_iff x y z).symm) w
    simpa only [sCarrier, tCarrier, qCarrier, GroundCompressionCompletion.externalPointOrder,
      GroundCompressionCompletion.externalPointMeet, GroundCompressionCompletion.externalCopyGraph] using code

end PartitionPilot.Forcing.GroundExternalGeometryInputs



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialExternalGeometry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalGeometryInputs M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data⟩ :=
    M.exists_groundInitialExternalGeometryInputs pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels hm hInv group action meet hτ top hC hD hrD hc hOriginal
      originalCode columns target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data,
    data.externalGeometryData group action pairing unions powers separation infinite hG hP⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

def vertexImageDomains (Requests N U Q V images : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ r ∈ Requests, ∃ y ∈ Q, ∃ j ∈ N, ∃ x ∈ U, ∃ v ∈ V,
    z = ZFSet.pair r y ∧ v = ZFSet.pair (ZFSet.pair r j) x ∧ ZFSet.pair v y ∈ images)
    (ZFSet.prod Requests Q)

theorem pair_mem_vertexImageDomains (Requests N U Q V images r y : ZFSet.{u}) :
    ZFSet.pair r y ∈ vertexImageDomains Requests N U Q V images ↔
      r ∈ Requests ∧ y ∈ Q ∧ ∃ j ∈ N, ∃ x ∈ U,
        ZFSet.pair (ZFSet.pair r j) x ∈ V ∧
          ZFSet.pair (ZFSet.pair (ZFSet.pair r j) x) y ∈ images := by
  rw [vertexImageDomains, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, r', hr, y', hy, j, hj, x, hx, v, hv, equal, rfl, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hr, hy, j, hj, x, hx, hv, entry⟩
  · rintro ⟨hr, hy, j, hj, x, hx, hv, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hr, hy⟩, r, hr, y, hy, j, hj, x, hx,
      ZFSet.pair (ZFSet.pair r j) x, hv, rfl, rfl, entry⟩

namespace BoundedFormula
def vertexImageDomainsEntryFormula {n} (z Requests N U Q V images : Fin n) : BoundedFormula n :=
  exMem Requests (exMem Q.succ (exMem N.succ.succ (exMem U.succ.succ.succ (exMem V.succ.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ.succ 4 3)
      (.conj (orderedTripleFormula 0 4 2 1)
        (pairMembershipFormula 0 3 images.succ.succ.succ.succ.succ)))))))

theorem truth_vertexImageDomainsEntryFormula {n} (z Requests N U Q V images : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (vertexImageDomainsEntryFormula z Requests N U Q V images) env ↔
      env z ∈ vertexImageDomains (env Requests) (env N) (env U) (env Q) (env V) (env images) := by
  simp only [vertexImageDomainsEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_orderedTripleFormula, truth_pairMembershipFormula, vertexImageDomains, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨r, hr, y, hy, _, _, _, _, _, _, equal, _⟩ := h
  change env z = ZFSet.pair r y at equal
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hr, hy⟩
end BoundedFormula

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (P r μ A : ZFSet.{u})
local notation "Requests" => externalRequestCarrier I P (externalRectangles P G r μ A)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "V" => completion.externalVertices P r μ A
local notation "E" => M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one

noncomputable def localTileVertexImages : ZFSet.{u} :=
  relationCompose V (ZFSet.prod E U) Q
    (indexedRelationSection V (ZFSet.prod E U) (completion.externalPlacements P r μ A)
      (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one))
    (completion.externalPointClassifier P r μ A)

noncomputable def localTilePoints : ZFSet.{u} :=
  vertexImageDomains Requests (natSetCode 3) U Q V (completion.localTileVertexImages P r μ A)

noncomputable def localTileCarrier (request : ZFSet.{u}) : ZFSet.{u} :=
  relationFiber Q (completion.localTilePoints P r μ A) request

noncomputable def localTileOrder (request : ZFSet.{u}) : ZFSet.{u} :=
  relationFiber (completion.externalPointOrder P r μ A)
    (indexedSuborderGraph Requests Q (completion.externalPointOrder P r μ A)
      (completion.localTilePoints P r μ A)) request

noncomputable def localTileMeet (request : ZFSet.{u}) : ZFSet.{u} :=
  relationFiber (completion.externalPointMeet P r μ A)
    (indexedSubmeetGraph Requests Q (completion.externalPointMeet P r μ A)
      (completion.localTilePoints P r μ A)) request

noncomputable def localTileCarriers : ZFSet.{u} :=
  M.relationFiberFamily Requests Q (completion.localTilePoints P r μ A)

noncomputable def localTileOrders : ZFSet.{u} :=
  M.relationFiberFamily Requests (completion.externalPointOrder P r μ A)
    (indexedSuborderGraph Requests Q (completion.externalPointOrder P r μ A)
      (completion.localTilePoints P r μ A))

noncomputable def localTileMeets : ZFSet.{u} :=
  M.relationFiberFamily Requests (completion.externalPointMeet P r μ A)
    (indexedSubmeetGraph Requests Q (completion.externalPointMeet P r μ A)
      (completion.localTilePoints P r μ A))

noncomputable def localTileVertexGraphs : ZFSet.{u} :=
  M.indexedRelationSections (ZFSet.prod Requests (natSetCode 3)) U Q
    (completion.localTileVertexImages P r μ A)

theorem localTileCarrier_subset (request : ZFSet.{u}) : completion.localTileCarrier P r μ A request ⊆ Q :=
  fun _ hz => (mem_relationFiber _ _ _ _).1 hz |>.1

end GroundCompressionCompletion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure GroundExternalLocalHeightData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 r0 μ0 A0 D rD lo hi : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) where
  family : ZFSet.{u}
  family_ground : family ∈ M.sets
  function : ZFSet.IsFunc (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0))
    (M.groundRelations (completion.externalPointCarrier P0 r0 μ0 A0) D) family
  values : ∀ i h, ZFSet.pair i h ∈ family → h ∈ M.sets ∧
    IntervalHeightCode (completion.localTileCarrier P0 r0 μ0 A0 i)
      (completion.localTileOrder P0 r0 μ0 A0 i) D rD lo hi h ∧
    relationImage (completion.localTileCarrier P0 r0 μ0 A0 i) D h ∈ M.sets ∧
    M.groundEmbeddable (relationImage (completion.localTileCarrier P0 r0 μ0 A0 i) D h) ZFSet.omega

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
theorem vertexImageDomains_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Requests N U Q V images : ZFSet.{u}}
    (hRequests : Requests ∈ M.sets) (hN : N ∈ M.sets) (hU : U ∈ M.sets)
    (hQ : Q ∈ M.sets) (hV : V ∈ M.sets) (hImages : images ∈ M.sets) :
    vertexImageDomains Requests N U Q V images ∈ M.sets := by
  let params := extend Requests (extend N (extend U (extend Q (extend V (extend images Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.vertexImageDomainsEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hRequests (Fin.cases hN (Fin.cases hU (Fin.cases hQ
      (Fin.cases hV (Fin.cases hImages (fun j => Fin.elim0 j)))))))
    (M.prod_mem pairing unions powers separation hRequests hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.vertexImageDomainsEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod Requests Q) = vertexImageDomains Requests N U Q V images := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_vertexImageDomainsEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected
end TransitiveGround

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "Requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "R" => completion.externalPointOrder P0 r0 μ0 A0
local notation "μ" => completion.externalPointMeet P0 r0 μ0 A0
local notation "V" => completion.externalVertices P0 r0 μ0 A0
local notation "U" => completion.algebra.union.fields 0
local notation "images" => completion.localTileVertexImages P0 r0 μ0 A0
local notation "domains" => completion.localTilePoints P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG hP0

theorem localTileGroundInputs :
    Q ∈ M.sets ∧ R ∈ M.sets ∧ μ ∈ M.sets ∧ images ∈ M.sets ∧ domains ∈ M.sets := by
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP0
  have flat := data.flat_relations_ground pairing unions powers separation hP0 hG
  have product := M.prod_mem pairing unions powers separation data.group.carrier_mem (completion.algebra.union.ground 0)
  have sectionGround := M.indexedRelationSection_mem pairing unions powers separation flat.1 product
    flat.2.2.1 data.group.identity_mem
  have imageGround : images ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    flat.1 product geometry.carrier_ground sectionGround geometry.classifier_ground
  have domainGround : domains ∈ M.sets := M.vertexImageDomains_mem pairing unions powers separation
    data.words.requests_ground (M.natSetCode_mem separation infinite 3) (completion.algebra.union.ground 0)
    geometry.carrier_ground flat.1 imageGround
  exact ⟨geometry.carrier_ground, geometry.order_ground, geometry.meet_ground, imageGround, domainGround⟩

theorem localTileCarriers_spec :
    completion.localTileCarriers P0 r0 μ0 A0 ∈ M.sets ∧
      FunctionGraphOn Requests (completion.localTileCarriers P0 r0 μ0 A0) ∧
      ∀ i f, ZFSet.pair i f ∈ completion.localTileCarriers P0 r0 μ0 A0 ↔
        i ∈ Requests ∧ f = completion.localTileCarrier P0 r0 μ0 A0 i := by
  have ground := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  exact ⟨M.relationFiberFamily_mem pairing unions powers separation data.words.requests_ground ground.1 ground.2.2.2.2,
    ⟨_, M.relationFiberFamily_function separation data.words.requests_ground ground.1 ground.2.2.2.2⟩,
    M.relationFiberFamily_entries separation data.words.requests_ground ground.1 ground.2.2.2.2⟩

theorem localTileOrders_spec :
    completion.localTileOrders P0 r0 μ0 A0 ∈ M.sets ∧
      FunctionGraphOn Requests (completion.localTileOrders P0 r0 μ0 A0) ∧
      ∀ i f, ZFSet.pair i f ∈ completion.localTileOrders P0 r0 μ0 A0 ↔
        i ∈ Requests ∧ f = completion.localTileOrder P0 r0 μ0 A0 i := by
  have ground := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  have indexed := M.indexedSuborderGraph_mem pairing unions powers separation data.words.requests_ground
    ground.1 ground.2.1 ground.2.2.2.2
  exact ⟨M.relationFiberFamily_mem pairing unions powers separation data.words.requests_ground ground.2.1 indexed,
    ⟨_, M.relationFiberFamily_function separation data.words.requests_ground ground.2.1 indexed⟩,
    M.relationFiberFamily_entries separation data.words.requests_ground ground.2.1 indexed⟩

theorem localTileMeets_spec :
    completion.localTileMeets P0 r0 μ0 A0 ∈ M.sets ∧
      FunctionGraphOn Requests (completion.localTileMeets P0 r0 μ0 A0) ∧
      ∀ i f, ZFSet.pair i f ∈ completion.localTileMeets P0 r0 μ0 A0 ↔
        i ∈ Requests ∧ f = completion.localTileMeet P0 r0 μ0 A0 i := by
  have ground := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  have indexed := M.indexedSubmeetGraph_mem pairing unions powers separation data.words.requests_ground
    ground.1 ground.2.2.1 ground.2.2.2.2
  exact ⟨M.relationFiberFamily_mem pairing unions powers separation data.words.requests_ground ground.2.2.1 indexed,
    ⟨_, M.relationFiberFamily_function separation data.words.requests_ground ground.2.2.1 indexed⟩,
    M.relationFiberFamily_entries separation data.words.requests_ground ground.2.2.1 indexed⟩

theorem localTileVertexGraphs_spec :
    completion.localTileVertexGraphs P0 r0 μ0 A0 ∈ M.sets ∧
      FunctionGraphOn (ZFSet.prod Requests (natSetCode 3)) (completion.localTileVertexGraphs P0 r0 μ0 A0) ∧
      ∀ i f, ZFSet.pair i f ∈ completion.localTileVertexGraphs P0 r0 μ0 A0 ↔
        i ∈ ZFSet.prod Requests (natSetCode 3) ∧ f = indexedRelationSection U Q images i := by
  have ground := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  have spec := M.indexedRelationSections_spec pairing unions powers separation
    (M.prod_mem pairing unions powers separation data.words.requests_ground (M.natSetCode_mem separation infinite 3))
    (completion.algebra.union.ground 0) ground.1 ground.2.2.2.1
  exact ⟨spec.1, ⟨_, spec.2.1⟩, spec.2.2⟩

end GroundExternalGeometryInputs

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 D rD c lo hi : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "Requests" => externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite choice hG hP0

theorem localHeightFamily_of_witnesses
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (hlo : lo ∈ M.sets) (hhi : hi ∈ M.sets) (injection : InjectionCode D ZFSet.omega c)
    (witnesses : ∀ i ∈ Requests, ∃ h ∈ M.sets,
      IntervalHeightCode (completion.localTileCarrier P0 r0 μ0 A0 i)
        (completion.localTileOrder P0 r0 μ0 A0 i) D rD lo hi h) :
    Nonempty (GroundExternalLocalHeightData M initial I Sources Reps G m one T τ
      P0 r0 μ0 A0 D rD lo hi completion) := by
  have carriers := data.localTileCarriers_spec group oldAction pairing unions powers separation infinite hG hP0
  have orders := data.localTileOrders_spec group oldAction pairing unions powers separation infinite hG hP0
  have ground := data.localTileGroundInputs group oldAction pairing unions powers separation infinite hG hP0
  have carrierValue (i : {i : ZFSet.{u} // i ∈ Requests}) :
      carriers.2.1.value i = completion.localTileCarrier P0 r0 μ0 A0 i.val :=
    ((carriers.2.2 _ _).1 (carriers.2.1.value_entry i)).2
  have orderValue (i : {i : ZFSet.{u} // i ∈ Requests}) :
      orders.2.1.value i = completion.localTileOrder P0 r0 μ0 A0 i.val :=
    ((orders.2.2 _ _).1 (orders.2.1.value_entry i)).2
  have bound (i : {i : ZFSet.{u} // i ∈ Requests}) : carriers.2.1.value i ⊆ Q := by
    rw [carrierValue]
    exact completion.localTileCarrier_subset P0 r0 μ0 A0 i.val
  have localExists (i : {i : ZFSet.{u} // i ∈ Requests}) :
      ∃ h ∈ M.sets, IntervalHeightCode (carriers.2.1.value i) (orders.2.1.value i) D rD lo hi h := by
    rw [carrierValue, orderValue]
    exact witnesses i.val i.property
  obtain ⟨family, member, function, values⟩ := M.exists_intervalHeight_family
    pairing unions powers separation choice carriers.2.1 orders.2.1 bound data.words.requests_ground ground.1
    carriers.1 orders.1 hD hrD hc hlo hhi (M.omega_mem separation infinite) injection localExists
  refine ⟨⟨family, member, function, ?_⟩⟩
  intro i h entry
  have hi := (ZFSet.pair_mem_prod.1 (function.1 entry)).1
  have value := values ⟨i, hi⟩ h entry
  rw [carrierValue, orderValue] at value
  exact value

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end OAI
