import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStoredStructuralRequestActions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCertificateProfileImageFamilies

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def certificateUsedSupports (nodes k : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => ∃ z F B f,
    ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ v ∈ B) nodes

theorem mem_certificateUsedSupports (nodes k v : ZFSet.{u}) :
    v ∈ certificateUsedSupports nodes k ↔ v ∈ nodes ∧
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ v ∈ B :=
  ZFSet.mem_sep

noncomputable def preparationEventUsedSupports (nodes event : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => ∃ alpha r k enumerations,
    event = ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations)) ∧
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ v ∈ B) nodes

theorem preparationEventUsedSupports_active (nodes alpha r k enumerations : ZFSet.{u}) :
    preparationEventUsedSupports nodes (ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations))) =
      certificateUsedSupports nodes k := by
  apply ZFSet.ext
  intro v
  rw [preparationEventUsedSupports, ZFSet.mem_sep, mem_certificateUsedSupports]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨alpha', r', k', e', equal, data⟩
    have middle := (ZFSet.pair_inj.1 equal).2
    have last := (ZFSet.pair_inj.1 middle).2
    have same := (ZFSet.pair_inj.1 last).1
    exact same.symm ▸ data
  · intro data
    exact ⟨alpha, r, k, enumerations, rfl, data⟩

theorem preparationEventUsedSupports_idle (nodes : ZFSet.{u}) :
    preparationEventUsedSupports nodes ∅ = ∅ := by
  apply ZFSet.ext
  intro v
  rw [preparationEventUsedSupports, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, alpha, r, k, enumerations, equal, _⟩
    have member : ({alpha} : ZFSet.{u}) ∈
        ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations)) := by
      exact ZFSet.mem_insert _ _
    rw [← equal] at member
    exact False.elim (ZFSet.notMem_empty _ member)
  · intro member
    exact False.elim (ZFSet.notMem_empty _ member)

namespace BoundedFormula

def certificateBasisMemberFormula {n} (v k : Fin n) : BoundedFormula n :=
  exGraphFields k (exPairFields 0 (exPairFields 0 (.mem v.succ.succ.succ.succ.succ.succ 1)))

theorem truth_certificateBasisMemberFormula {n} (v k : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (certificateBasisMemberFormula v k) env ↔
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ env k ∧ env v ∈ B := by
  simp only [certificateBasisMemberFormula, truth_exGraphFields, truth_exPairFields, Truth]
  change (∃ z c, ZFSet.pair z c ∈ env k ∧ ∃ F tail, c = ZFSet.pair F tail ∧
    ∃ B f, tail = ZFSet.pair B f ∧ env v ∈ B) ↔ _
  constructor
  · rintro ⟨z, c, edge, F, tail, rfl, B, f, rfl, member⟩
    exact ⟨z, F, B, f, edge, member⟩
  · rintro ⟨z, F, B, f, edge, member⟩
    exact ⟨z, _, edge, F, _, rfl, B, f, rfl, member⟩

def preparationEventSupportFormula {n} (v event : Fin n) : BoundedFormula n :=
  exPairFields event (exPairFields 0 (exPairFields 0
    (certificateBasisMemberFormula v.succ.succ.succ.succ.succ.succ 1)))

theorem truth_preparationEventSupportFormula {n} (v event : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (preparationEventSupportFormula v event) env ↔
      ∃ alpha r k enumerations,
        env event = ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations)) ∧
          ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ env v ∈ B := by
  simp only [preparationEventSupportFormula, truth_exPairFields, truth_certificateBasisMemberFormula]
  change (∃ alpha output, env event = ZFSet.pair alpha output ∧ ∃ r tail,
    output = ZFSet.pair r tail ∧ ∃ k enumerations, tail = ZFSet.pair k enumerations ∧
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ env v ∈ B) ↔ _
  constructor
  · rintro ⟨alpha, output, equal, r, tail, rfl, k, enumerations, rfl, data⟩
    exact ⟨alpha, r, k, enumerations, equal, data⟩
  · rintro ⟨alpha, r, k, enumerations, equal, data⟩
    exact ⟨alpha, _, equal, r, _, rfl, k, enumerations, rfl, data⟩

end BoundedFormula






def preparationTupleCode (F B f e names : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (ZFSet.pair F (ZFSet.pair B f)) (ZFSet.pair e names)

private noncomputable def tupleImageWithOmega
    (omega nodes N nodeMap nameMap F B f e names : ZFSet.{u}) : ZFSet.{u} :=
  preparationTupleCode (relationImage F nodes nodeMap) (relationImage B nodes nodeMap)
    (relationCompose nodes B N (relationConverse B nodes nodeMap)
      (relationCompose B N N f nameMap))
    (relationCompose omega B nodes e nodeMap) (relationCompose omega N N names nameMap)

noncomputable def preparationTupleImage
    (nodes N nodeMap nameMap F B f e names : ZFSet.{u}) : ZFSet.{u} :=
  tupleImageWithOmega ZFSet.omega nodes N nodeMap nameMap F B f e names

noncomputable def preparationTupleActionGraph
    (C E nodes N nodeMap nameMap : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ F B f e names, z = ZFSet.pair (preparationTupleCode F B f e names)
    (preparationTupleImage nodes N nodeMap nameMap F B f e names))
    (ZFSet.prod (ZFSet.prod C E) (ZFSet.prod C E))

theorem pair_mem_preparationTupleActionGraph (C E nodes N nodeMap nameMap F B f e names y : ZFSet.{u}) :
    ZFSet.pair (preparationTupleCode F B f e names) y ∈
      preparationTupleActionGraph C E nodes N nodeMap nameMap ↔
    preparationTupleCode F B f e names ∈ ZFSet.prod C E ∧ y ∈ ZFSet.prod C E ∧
      y = preparationTupleImage nodes N nodeMap nameMap F B f e names := by
  rw [preparationTupleActionGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨bounds, F', B', f', e', names', equal⟩
    obtain ⟨keys, values⟩ := ZFSet.pair_inj.1 equal
    have fields : F = F' ∧ B = B' ∧ f = f' ∧ e = e' ∧ names = names' := by
      simpa only [preparationTupleCode, ZFSet.pair_inj, and_assoc] using keys
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fields
    exact ⟨bounds.1, bounds.2, values⟩
  · rintro ⟨hx, hy, rfl⟩
    exact ⟨⟨hx, hy⟩, F, B, f, e, names, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

private noncomputable def pairDefinition :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => ZFSet.pair (env 0) (env 1)) where
  formula := orderedPairFormula 0 1 2
  closed := fun _ h => M.orderedPair_mem pairing (h 0) (h 1)
  correct := fun _ h _ hz => M.realize_orderedPairFormula pairing 0 1 2 _ hz (h 0) (h 1)

private noncomputable def imageDefinition :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => relationImage (env 0) (env 1) (env 2)) where
  formula := (BoundedFormula.relationImageEqualityFormula 0 1 2 3).toFormula
  closed := fun _ h => M.relationImage_mem separation (h 0) (h 1) (h 2)
  correct := by
    intro env h z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz h),
      BoundedFormula.truth_relationImageEqualityFormula]
    rfl

private noncomputable def converseDefinition :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => relationConverse (env 0) (env 1) (env 2)) where
  formula := exactSetFormula 0 (BoundedFormula.converseEntryFormula 0 2 3 4).toFormula
  closed := fun _ h => M.relationConverse_mem pairing unions powers separation (h 0) (h 1) (h 2)
  correct := by
    intro env h z hz
    apply M.realize_exactSetFormula 0 _ _ hz
      (fun w hw => M.transitive
        (M.relationConverse_mem pairing unions powers separation (h 0) (h 1) (h 2)) hw)
    intro w hw
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz h)),
      BoundedFormula.truth_converseEntryFormula, mem_relationConverse]
    rfl

private noncomputable def composeDefinition :
    GroundDefinableFunction M (fun env : Fin 5 → ZFSet.{u} =>
      relationCompose (env 0) (env 1) (env 2) (env 3) (env 4)) where
  formula := exactSetFormula 0 (BoundedFormula.composeEntryFormula 0 2 3 4 5 6).toFormula
  closed := fun _ h => M.relationCompose_mem pairing unions powers separation (h 0) (h 1) (h 2) (h 3) (h 4)
  correct := by
    intro env h z hz
    apply M.realize_exactSetFormula 0 _ _ hz
      (fun w hw => M.transitive
        (M.relationCompose_mem pairing unions powers separation (h 0) (h 1) (h 2) (h 3) (h 4)) hw)
    intro w hw
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz h)),
      BoundedFormula.truth_composeEntryFormula, mem_relationCompose]
    rfl

private noncomputable def actionPairDefinition :
    GroundDefinableFunction M (fun env : Fin 10 → ZFSet.{u} =>
      ZFSet.pair (preparationTupleCode (env 0) (env 1) (env 2) (env 3) (env 4))
        (tupleImageWithOmega (env 9) (env 5) (env 6) (env 7) (env 8)
          (env 0) (env 1) (env 2) (env 3) (env 4))) := by
  let v := GroundSetTerm.var M (n := 10)
  let pair (x y : GroundSetTerm M 10) := GroundSetTerm.app (pairDefinition M pairing) ![x,y]
  let image (x : GroundSetTerm M 10) := GroundSetTerm.app (imageDefinition M separation) ![x,v 5,v 7]
  let compose (x y z r f : GroundSetTerm M 10) :=
    GroundSetTerm.app (composeDefinition M pairing unions powers separation) ![x,y,z,r,f]
  let inverse := GroundSetTerm.app (converseDefinition M pairing unions powers separation) ![v 1,v 5,v 7]
  let movedF := compose (v 5) (v 1) (v 6) inverse (compose (v 1) (v 6) (v 6) (v 2) (v 8))
  let movedE := compose (v 9) (v 1) (v 5) (v 3) (v 7)
  let movedNames := compose (v 9) (v 6) (v 6) (v 4) (v 8)
  exact (pair (pair (pair (v 0) (pair (v 1) (v 2))) (pair (v 3) (v 4)))
    (pair (pair (image (v 0)) (pair (image (v 1)) movedF)) (pair movedE movedNames))).definition

include pairing unions powers separation in
theorem preparationTupleActionGraph_mem
    {C E nodes N nodeMap nameMap : ZFSet.{u}}
    (hC : C ∈ M.sets) (hE : E ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hN : N ∈ M.sets) (hNodeMap : nodeMap ∈ M.sets) (hNameMap : nameMap ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    preparationTupleActionGraph C E nodes N nodeMap nameMap ∈ M.sets := by
  let defined := actionPairDefinition M pairing unions powers separation
  let slots : Fin 11 → Fin 11 := ![5,0,1,2,3,4,6,7,8,9,10]
  let formula := exBlock 5 (SetFormula.reindex slots defined.formula)
  let params : Fin 5 → ZFSet.{u} := ![nodes,N,nodeMap,nameMap,ZFSet.omega]
  have paramsGround : ∀ j, params j ∈ M.sets := by
    intro j
    exact Fin.cases hNodes (Fin.cases hN (Fin.cases hNodeMap
      (Fin.cases hNameMap (Fin.cases omega (fun k => Fin.elim0 k))))) j
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hC hE)
    (M.prod_mem pairing unions powers separation hC hE)
  have selected := M.separation_mem separation formula params paramsGround bound
  have same : ZFSet.sep (fun z => Realize M.sets formula (extend z params))
      (ZFSet.prod (ZFSet.prod C E) (ZFSet.prod C E)) =
      preparationTupleActionGraph C E nodes N nodeMap nameMap := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, preparationTupleActionGraph, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    have zGround := M.transitive bound hz
    rw [show formula = exBlock 5 (SetFormula.reindex slots defined.formula) from rfl,
      realize_exBlock]
    constructor
    · rintro ⟨fields, grounds, meaning⟩
      rw [realize_reindex] at meaning
      have values : (fun j => extendMany 5 fields (extend z params) (slots j)) =
          extend z (extendMany 5 fields params) := by
        funext j
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))))) j
      rw [values] at meaning
      have equal := (defined.correct (extendMany 5 fields params)
        (extendMany_members 5 fields params grounds paramsGround) z zGround).1 meaning
      exact ⟨fields 0, fields 1, fields 2, fields 3, fields 4, equal⟩
    · rintro ⟨F,B,f,e,names,equal⟩
      have inputGround : preparationTupleCode F B f e names ∈ M.sets :=
        M.pair_left (equal ▸ zGround)
      have hF := M.pair_left (M.pair_left inputGround)
      have hB := M.pair_left (M.pair_right (M.pair_left inputGround))
      have hf := M.pair_right (M.pair_right (M.pair_left inputGround))
      have he := M.pair_left (M.pair_right inputGround)
      have hNames := M.pair_right (M.pair_right inputGround)
      let fields : Fin 5 → ZFSet.{u} := ![F,B,f,e,names]
      have grounds : ∀ j, fields j ∈ M.sets := by
        intro j
        exact Fin.cases hF (Fin.cases hB (Fin.cases hf
          (Fin.cases he (Fin.cases hNames (fun k => Fin.elim0 k))))) j
      refine ⟨fields,grounds,?_⟩
      rw [realize_reindex]
      have values : (fun j => extendMany 5 fields (extend z params) (slots j)) =
          extend z (extendMany 5 fields params) := by
        funext j
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))))) j
      rw [values]
      exact (defined.correct (extendMany 5 fields params)
        (extendMany_members 5 fields params grounds paramsGround) z zGround).2 equal
  exact same ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem preparationTupleImage_mem_bound
    {nodes N W nodeMap nameMap F B f e names : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (hNodeMap : nodeMap ∈ M.sets) (hNameMap : nameMap ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (localBound : N ⊆ W)
    (nodeInjection : InjectionCode nodes nodes nodeMap)
    (member : preparationTupleCode F B f e names ∈ ZFSet.prod
      (M.supportedEqualityCertificateBound nodes W) (M.synchronizedEnumerationBound nodes W)) :
    preparationTupleImage nodes N nodeMap nameMap F B f e names ∈ ZFSet.prod
      (M.supportedEqualityCertificateBound nodes W) (M.synchronizedEnumerationBound nodes W) := by
  have parts := ZFSet.pair_mem_prod.1 member
  obtain ⟨⟨hF,_⟩,⟨hB,Bsub,small⟩,hf,_⟩ :=
    (M.mem_supportedEqualityCertificateBound nodes W F B f).1 parts.1
  have enumParts := ZFSet.pair_mem_prod.1 parts.2
  have he := ((M.mem_groundRelations ZFSet.omega nodes e).1 enumParts.1).1
  have hNames := ((M.mem_groundRelations ZFSet.omega W names).1 enumParts.2).1
  have hImageF := M.relationImage_mem separation hF hNodes hNodeMap
  have hImageB := M.relationImage_mem separation hB hNodes hNodeMap
  have hMovedF := M.relationCompose_mem pairing unions powers separation hNodes hB hN
    (M.relationConverse_mem pairing unions powers separation hB hNodes hNodeMap)
    (M.relationCompose_mem pairing unions powers separation hB hN hN hf hNameMap)
  have hMovedE := M.relationCompose_mem pairing unions powers separation omega hB hNodes he hNodeMap
  have hMovedNames := M.relationCompose_mem pairing unions powers separation omega hN hN hNames hNameMap
  change ZFSet.pair
      (ZFSet.pair (relationImage F nodes nodeMap) (ZFSet.pair (relationImage B nodes nodeMap)
        (relationCompose nodes B N (relationConverse B nodes nodeMap) (relationCompose B N N f nameMap))))
      (ZFSet.pair (relationCompose ZFSet.omega B nodes e nodeMap)
        (relationCompose ZFSet.omega N N names nameMap)) ∈ _
  apply ZFSet.pair_mem_prod.2
  constructor
  · apply (M.mem_supportedEqualityCertificateBound nodes W _ _ _).2
    refine ⟨⟨hImageF, fun _ h => ((mem_relationImage _ _ _ _).1 h).1⟩,
      ⟨hImageB, fun _ h => ((mem_relationImage _ _ _ _).1 h).1,
        M.groundEmbeddable_image pairing unions powers separation hB hNodes omega hNodeMap
          nodeInjection Bsub small⟩, hMovedF, ?_⟩
    intro z hz
    obtain ⟨v,hv,tau,ht,rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    exact ZFSet.pair_mem_prod.2 ⟨hv,localBound ht⟩
  · apply ZFSet.pair_mem_prod.2
    refine ⟨(M.mem_groundRelations ZFSet.omega nodes _).2
      ⟨hMovedE, fun _ h => (ZFSet.mem_sep.1 h).1⟩,
      (M.mem_groundRelations ZFSet.omega W _).2 ⟨hMovedNames,?_⟩⟩
    intro z hz
    obtain ⟨n,hn,tau,ht,rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    exact ZFSet.pair_mem_prod.2 ⟨hn,localBound ht⟩

theorem preparationTupleActionGraph_function
    {nodes N W nodeMap nameMap : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (hNodeMap : nodeMap ∈ M.sets) (hNameMap : nameMap ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (localBound : N ⊆ W)
    (nodeInjection : InjectionCode nodes nodes nodeMap) :
    let D := ZFSet.prod (M.supportedEqualityCertificateBound nodes W)
      (M.synchronizedEnumerationBound nodes W)
    ZFSet.IsFunc D D (preparationTupleActionGraph
      (M.supportedEqualityCertificateBound nodes W) (M.synchronizedEnumerationBound nodes W)
      nodes N nodeMap nameMap) := by
  dsimp only
  refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
  intro x hx
  obtain ⟨cert,hcert,enm,henm,rfl⟩ := ZFSet.mem_prod.1 hx
  obtain ⟨F,hF,rest,hrest,rfl⟩ := ZFSet.mem_prod.1 hcert
  obtain ⟨B,hB,f,hf,rfl⟩ := ZFSet.mem_prod.1 hrest
  obtain ⟨e,he,names,hnames,rfl⟩ := ZFSet.mem_prod.1 henm
  have input : preparationTupleCode F B f e names ∈ ZFSet.prod
      (M.supportedEqualityCertificateBound nodes W) (M.synchronizedEnumerationBound nodes W) :=
    ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hF,ZFSet.pair_mem_prod.2 ⟨hB,hf⟩⟩,
      ZFSet.pair_mem_prod.2 ⟨he,hnames⟩⟩
  have output := M.preparationTupleImage_mem_bound pairing unions powers separation
    hNodes hN hNodeMap hNameMap omega localBound nodeInjection input
  refine ⟨preparationTupleImage nodes N nodeMap nameMap F B f e names,
    (pair_mem_preparationTupleActionGraph _ _ _ _ _ _ _ _ _ _ _ _).2 ⟨input,output,rfl⟩, ?_⟩
  intro y hy
  exact ((pair_mem_preparationTupleActionGraph _ _ _ _ _ _ _ _ _ _ _ _).1 hy).2.2

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing
universe u
variable (M : TransitiveGround.{u})
variable {nodes N W nodeMap nameMap J k enums : ZFSet.{u}}
local notation "C" => M.supportedEqualityCertificateBound nodes W
local notation "E" => M.synchronizedEnumerationBound nodes W
local notation "tuples" => preparationTupleActionGraph C E nodes N nodeMap nameMap
local notation "movedK" => preparationFamilyFirst J N C E nameMap tuples k enums
variable (nodeBound : nodeMap ⊆ ZFSet.prod nodes nodes)
variable (keys : InjectionCode N N nameMap) (sourceKeys : J ⊆ N)
variable (tupleFunction : ZFSet.IsFunc
  (ZFSet.prod (M.supportedEqualityCertificateBound nodes W) (M.synchronizedEnumerationBound nodes W))
  (ZFSet.prod (M.supportedEqualityCertificateBound nodes W) (M.synchronizedEnumerationBound nodes W))
  (preparationTupleActionGraph (M.supportedEqualityCertificateBound nodes W)
    (M.synchronizedEnumerationBound nodes W) nodes N nodeMap nameMap))
variable (first : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
variable (second : ZFSet.IsFunc J (M.synchronizedEnumerationBound nodes W) enums)
include nodeBound keys sourceKeys tupleFunction first second

theorem preparationFamilyFirst_usedSupports_image :
    certificateUsedSupports nodes movedK =
      relationImage (certificateUsedSupports nodes k) nodes nodeMap := by
  have functions := preparationFamilyImages_function keys tupleFunction first second
  apply ZFSet.ext
  intro v
  constructor
  · intro member
    obtain ⟨hv, z, Fg, Bg, fg, cert, basis⟩ := (mem_certificateUsedSupports nodes movedK v).1 member
    have hz := (ZFSet.pair_mem_prod.1 (functions.1.1 cert)).1
    obtain ⟨enm, enum, _⟩ := functions.2.2 z hz
    obtain ⟨eg, _, namesg, _, rfl⟩ := ZFSet.mem_prod.1
      (ZFSet.pair_mem_prod.1 (functions.2.1 enum)).2
    obtain ⟨oldZ, oldC, oldE, oldCert, oldEnum, _key, tuple⟩ :=
      (preparationFamilyImages_entry keys tupleFunction first second z _ _).1 ⟨cert, enum⟩
    obtain ⟨F, _, tail, hTail, rfl⟩ := ZFSet.mem_prod.1
      (ZFSet.pair_mem_prod.1 (first.1 oldCert)).2
    obtain ⟨B, _, f, _, rfl⟩ := ZFSet.mem_prod.1 hTail
    obtain ⟨e, _, names, _, rfl⟩ := ZFSet.mem_prod.1
      (ZFSet.pair_mem_prod.1 (second.1 oldEnum)).2
    have equal := ((pair_mem_preparationTupleActionGraph C E nodes N nodeMap nameMap
      F B f e names _).1 tuple).2.2
    have basisEq : Bg = relationImage B nodes nodeMap :=
      (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).1).2).1
    obtain ⟨_, w, hw, edge⟩ := (mem_relationImage B nodes nodeMap v).1 (basisEq ▸ basis)
    have hwNodes := (ZFSet.pair_mem_prod.1 (nodeBound edge)).1
    exact (mem_relationImage _ nodes nodeMap v).2
      ⟨hv, w, (mem_certificateUsedSupports nodes k w).2
        ⟨hwNodes, oldZ, F, B, f, oldCert, hw⟩, edge⟩
  · intro member
    obtain ⟨hv, w, hw, edge⟩ := (mem_relationImage _ nodes nodeMap v).1 member
    obtain ⟨_, z, F, B, f, cert, basis⟩ := (mem_certificateUsedSupports nodes k w).1 hw
    have bounds := ZFSet.pair_mem_prod.1 (first.1 cert)
    obtain ⟨enm, enum, _⟩ := second.2 z bounds.1
    have enumBound := (ZFSet.pair_mem_prod.1 (second.1 enum)).2
    obtain ⟨e, he, names, hn, rfl⟩ := ZFSet.mem_prod.1 enumBound
    obtain ⟨zg, key, _⟩ := keys.function.2 z (sourceKeys bounds.1)
    have input : preparationTupleCode F B f e names ∈ ZFSet.prod C E :=
      ZFSet.pair_mem_prod.2 ⟨bounds.2, ZFSet.pair_mem_prod.2 ⟨he, hn⟩⟩
    obtain ⟨value, tuple, _⟩ := tupleFunction.2 _ input
    have equal := ((pair_mem_preparationTupleActionGraph C E nodes N nodeMap nameMap
      F B f e names value).1 tuple).2.2
    rw [equal] at tuple
    have moved := (preparationFamilyImages_entry keys tupleFunction first second zg
      (ZFSet.pair (relationImage F nodes nodeMap)
        (ZFSet.pair (relationImage B nodes nodeMap)
          (relationCompose nodes B N (relationConverse B nodes nodeMap)
            (relationCompose B N N f nameMap))))
      (ZFSet.pair (relationCompose ZFSet.omega B nodes e nodeMap)
        (relationCompose ZFSet.omega N N names nameMap))).2
      ⟨z, _, _, cert, enum, key, tuple⟩
    exact (mem_certificateUsedSupports nodes movedK v).2
      ⟨hv, zg, _, _, _, moved.1,
        (mem_relationImage B nodes nodeMap v).2 ⟨hv, w, basis, edge⟩⟩

theorem preparationFamilyFirst_usedSupports_subset {S : ZFSet.{u}}
    (bound : certificateUsedSupports nodes k ⊆ S) :
    certificateUsedSupports nodes movedK ⊆ relationImage S nodes nodeMap := by
  rw [preparationFamilyFirst_usedSupports_image M nodeBound keys sourceKeys tupleFunction first second]
  intro v member
  obtain ⟨hv, w, hw, edge⟩ := (mem_relationImage _ nodes nodeMap v).1 member
  exact (mem_relationImage S nodes nodeMap v).2 ⟨hv, w, bound hw, edge⟩

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (omega : ZFSet.omega ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
include pairing unions powers separation collection carrier order group nodes supports maps nodeMaps omega hT valid closed

theorem preparedCertificateFamily_act
    (meetGraph : ZFSet.{u}) (meet : MeetOrderCode b.carrier b.conditionOrder meetGraph)
    {J W k enums : ZFSet.{u}} (hJ : J ∈ M.sets) (hW : W ∈ M.sets)
    (hk : k ∈ M.sets) (hEnums : enums ∈ M.sets)
    (requestBound : J ⊆ M.groundRelations T s.carrier)
    (localBound : M.groundRelations T s.carrier ⊆ W) (p : P) (g : G)
    (family : PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier b.conditionOrder meetGraph (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤) ZFSet.omega J
      (M.supportedEqualityCertificateBound b.carrier W) (M.synchronizedEnumerationBound b.carrier W) k enums) :
    let N := M.groundRelations T s.carrier
    let validN : ∀ z ∈ N, IsName s z := fun z hz =>
      Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
    let C := M.supportedEqualityCertificateBound b.carrier W
    let E := M.synchronizedEnumerationBound b.carrier W
    let keyMap := Name.renameFamilyGraph s (a.iso g) N validN
    let nodeMap := b.graph b (d.iso g)
    let tupleMap := preparationTupleActionGraph C E b.carrier N nodeMap keyMap
    let movedK := preparationFamilyFirst J N C E keyMap tupleMap k enums
    let movedEnums := preparationFamilySecond J N C E keyMap tupleMap k enums
    movedK ∈ M.sets ∧ movedEnums ∈ M.sets ∧
      PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode (a.iso g p))
        b.carrier b.conditionOrder meetGraph N (M.niceVisibilityGraph a s b T d.principalFix)
        (s.encode ⊤) ZFSet.omega (relationImage J N keyMap) C E movedK movedEnums := by
  let N := M.groundRelations T s.carrier
  let validN : ∀ z ∈ N, IsName s z := fun z hz =>
    Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
  let C := M.supportedEqualityCertificateBound b.carrier W
  let E := M.synchronizedEnumerationBound b.carrier W
  let keyMap := Name.renameFamilyGraph s (a.iso g) N validN
  let nodeMap := b.graph b (d.iso g)
  let tupleMap := preparationTupleActionGraph C E b.carrier N nodeMap keyMap
  have hN := M.groundRelations_mem pairing unions powers separation hT carrier
  have hC := M.supportedEqualityCertificateBound_mem pairing unions powers separation nodes hW omega
  have hE := M.synchronizedEnumerationBound_mem pairing unions powers separation nodes hW omega
  have keyGround := (M.groundRelations_nameAction_ground_function a s t pairing unions powers
    separation collection carrier maps T closed hT valid g).1
  have keyInjection : InjectionCode N N keyMap := stageOneTermAction_injection a s N validN
    (M.groundRelations_act_mem a s t pairing unions powers separation collection carrier maps T closed) g
  have nodeGround := M.conditionMap_graph_mem d b t nodeMaps g
  have nodeInjection := b.graph_injection b (d.iso g) (d.iso g).injective
  have tupleGround := M.preparationTupleActionGraph_mem pairing unions powers separation hC hE nodes hN nodeGround keyGround omega
  have tupleFunction := M.preparationTupleActionGraph_function pairing unions powers separation
    nodes hN nodeGround keyGround omega localBound nodeInjection
  have ground := M.preparationFamilyImages_mem pairing unions powers separation
    hJ hN hC hE keyGround tupleGround hk hEnums
  have functions := preparationFamilyImages_function keyInjection tupleFunction family.1 family.2.1
  dsimp only
  refine ⟨ground.2.1, ground.2.2, functions.1, functions.2, ?_⟩
  intro x F' B' f' e' names' stored enumerated
  obtain ⟨z, c, enm, oldK, oldE, keyEdge, tupleEdge⟩ :=
    (preparationFamilyImages_entry keyInjection tupleFunction family.1 family.2.1
      x (ZFSet.pair F' (ZFSet.pair B' f')) (ZFSet.pair e' names')).1 ⟨stored, enumerated⟩
  have zInJ := (ZFSet.pair_mem_prod.1 (family.1.1 oldK)).1
  have cBound := (ZFSet.pair_mem_prod.1 (family.1.1 oldK)).2
  have eBound := (ZFSet.pair_mem_prod.1 (family.2.1.1 oldE)).2
  obtain ⟨F, _, rest, restBound, rfl⟩ := ZFSet.mem_prod.1 cBound
  obtain ⟨B, _, f, _, rfl⟩ := ZFSet.mem_prod.1 restBound
  obtain ⟨e, _, names, _, rfl⟩ := ZFSet.mem_prod.1 eBound
  let oldName : Name s := ⟨z, validN z (requestBound zInJ)⟩
  let old : (M.nameDomain s).names := ⟨oldName, ((M.mem_groundRelations T s.carrier z).1 (requestBound zInJ)).1⟩
  have keyEqual := ((Name.pair_mem_renameFamilyGraph s (a.iso g) N validN oldName x).1 keyEdge).2
  have moved := M.preparedCertificateCode_act a s t b d pairing unions powers separation collection
    carrier order group nodes supports maps hT valid closed meetGraph meet old F B f e names p g
    (family.2.2 z F B f e names oldK oldE)
  have tupleEqual := ((pair_mem_preparationTupleActionGraph C E b.carrier N nodeMap keyMap
    F B f e names (preparationTupleCode F' B' f' e' names')).1 tupleEdge).2.2
  have fields : F' = relationImage F b.carrier nodeMap ∧
      B' = relationImage B b.carrier nodeMap ∧
      f' = Name.actedRepresentativeGraph a s b d N validN g B f ∧
      e' = relationCompose ZFSet.omega B b.carrier e nodeMap ∧
      names' = Name.actedEnumerationGraph a s N validN g ZFSet.omega names := by
    change ZFSet.pair (ZFSet.pair F' (ZFSet.pair B' f')) (ZFSet.pair e' names') =
      ZFSet.pair (ZFSet.pair (relationImage F b.carrier nodeMap)
        (ZFSet.pair (relationImage B b.carrier nodeMap) (Name.actedRepresentativeGraph a s b d N validN g B f)))
        (ZFSet.pair (relationCompose ZFSet.omega B b.carrier e nodeMap)
          (Name.actedEnumerationGraph a s N validN g ZFSet.omega names)) at tupleEqual
    simpa only [ZFSet.pair_inj, and_assoc] using tupleEqual
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fields
  rw [keyEqual]
  exact moved

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (omega : ZFSet.omega ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
include pairing unions powers separation collection carrier order group nodes supports maps nodeMaps omega hT valid closed

theorem preparedCertificateFamily_act_support
    (meetGraph : ZFSet.{u}) (meet : MeetOrderCode b.carrier b.conditionOrder meetGraph)
    {J W k enums S : ZFSet.{u}} (hJ : J ∈ M.sets) (hW : W ∈ M.sets)
    (hk : k ∈ M.sets) (hEnums : enums ∈ M.sets) (hS : S ∈ M.sets)
    (requestBound : J ⊆ M.groundRelations T s.carrier)
    (localBound : M.groundRelations T s.carrier ⊆ W)
    (supportNodes : S ⊆ b.carrier) (small : M.groundEmbeddable S ZFSet.omega)
    (p : P) (g : G)
    (family : PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier b.conditionOrder meetGraph (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤) ZFSet.omega J
      (M.supportedEqualityCertificateBound b.carrier W) (M.synchronizedEnumerationBound b.carrier W) k enums)
    (supportBound : certificateUsedSupports b.carrier k ⊆ S) :
    let N := M.groundRelations T s.carrier
    let validN : ∀ z ∈ N, IsName s z := fun z hz =>
      Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
    let C := M.supportedEqualityCertificateBound b.carrier W
    let E := M.synchronizedEnumerationBound b.carrier W
    let keyMap := Name.renameFamilyGraph s (a.iso g) N validN
    let nodeMap := b.graph b (d.iso g)
    let tupleMap := preparationTupleActionGraph C E b.carrier N nodeMap keyMap
    let movedK := preparationFamilyFirst J N C E keyMap tupleMap k enums
    let movedEnums := preparationFamilySecond J N C E keyMap tupleMap k enums
    let movedS := relationImage S b.carrier nodeMap
    movedK ∈ M.sets ∧ movedEnums ∈ M.sets ∧ movedS ∈ M.sets ∧
      movedS ⊆ b.carrier ∧ M.groundEmbeddable movedS ZFSet.omega ∧
      PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode (a.iso g p))
        b.carrier b.conditionOrder meetGraph N (M.niceVisibilityGraph a s b T d.principalFix)
        (s.encode ⊤) ZFSet.omega (relationImage J N keyMap) C E movedK movedEnums ∧
      certificateUsedSupports b.carrier movedK =
        relationImage (certificateUsedSupports b.carrier k) b.carrier nodeMap ∧
      certificateUsedSupports b.carrier movedK ⊆ movedS := by
  let N := M.groundRelations T s.carrier
  let validN : ∀ z ∈ N, IsName s z := fun z hz =>
    Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
  let keyMap := Name.renameFamilyGraph s (a.iso g) N validN
  have prepared := M.preparedCertificateFamily_act a s t b d pairing unions powers separation
    collection carrier order group nodes supports maps nodeMaps omega hT valid closed
    meetGraph meet hJ hW hk hEnums requestBound localBound p g family
  have hN := M.groundRelations_mem pairing unions powers separation hT carrier
  have keyGround := (M.groundRelations_nameAction_ground_function a s t pairing unions powers
    separation collection carrier maps T closed hT valid g).1
  have keyInjection : InjectionCode N N keyMap := stageOneTermAction_injection a s N validN
    (M.groundRelations_act_mem a s t pairing unions powers separation collection carrier maps T closed) g
  have nodeGround := M.conditionMap_graph_mem d b t nodeMaps g
  have nodeInjection := b.graph_injection b (d.iso g) (d.iso g).injective
  have tupleFunction := M.preparationTupleActionGraph_function pairing unions powers separation
    nodes hN nodeGround keyGround omega localBound nodeInjection
  dsimp only
  exact ⟨prepared.1, prepared.2.1, M.relationImage_mem separation hS nodes nodeGround,
    fun v hv => ((mem_relationImage S b.carrier (b.graph b (d.iso g)) v).1 hv).1,
    M.groundEmbeddable_image pairing unions powers separation hS nodes omega nodeGround
      nodeInjection supportNodes small, prepared.2.2,
    preparationFamilyFirst_usedSupports_image M nodeInjection.function.1 keyInjection requestBound
      tupleFunction family.1 family.2.1,
    preparationFamilyFirst_usedSupports_subset M nodeInjection.function.1 keyInjection requestBound
      tupleFunction family.1 family.2.1 supportBound⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (members : ∀ j : Fin 15, (M.refinementLevelFormulaData a s b d level T T2 valid) j ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (group : t.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (omega : ZFSet.omega ∈ M.sets)
variable (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
variable (closed2 : ∀ g (z : Name s), z.val ∈ T2 → (a.act s g z).val ∈ T2)
include pairing unions powers separation collection members maps nodeMaps group supports omega closed closed2 valid2

theorem storedPreparationFamily_structural_act_support
    (hLevel : level ∈ M.sets) (hT2 : T2 ∈ M.sets) {stages history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level
      (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)) ∈ history)
    (meetGraph : ZFSet.{u}) (meet : MeetOrderCode b.carrier b.conditionOrder meetGraph)
    {A W k enums S : ZFSet.{u}} (hA : A ∈ M.sets) (hW : W ∈ M.sets)
    (hk : k ∈ M.sets) (hEnums : enums ∈ M.sets) (hS : S ∈ M.sets)
    (localBound : M.groundRelations T s.carrier ⊆ W)
    (supportNodes : S ⊆ b.carrier) (small : M.groundEmbeddable S ZFSet.omega)
    (p : P) (g : G)
    (family : PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier b.conditionOrder meetGraph (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤) ZFSet.omega
      (M.storedPreparationRequests A (M.refinementLevelFormulaData a s b d level T T2 valid))
      (M.supportedEqualityCertificateBound b.carrier W) (M.synchronizedEnumerationBound b.carrier W) k enums)
    (supportBound : certificateUsedSupports b.carrier k ⊆ S) :
    let N := M.groundRelations T s.carrier
    let validN : ∀ z ∈ N, IsName s z := fun z hz =>
      Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
    let J := M.storedPreparationRequests A (M.refinementLevelFormulaData a s b d level T T2 valid)
    let C := M.supportedEqualityCertificateBound b.carrier W
    let E := M.synchronizedEnumerationBound b.carrier W
    let keyMap := Name.renameFamilyGraph s (a.iso g) N validN
    let nodeMap := b.graph b (d.iso g)
    let tupleMap := preparationTupleActionGraph C E b.carrier N nodeMap keyMap
    let movedK := preparationFamilyFirst J N C E keyMap tupleMap k enums
    let movedEnums := preparationFamilySecond J N C E keyMap tupleMap k enums
    let movedS := relationImage S b.carrier nodeMap
    let movedA := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A
    movedK ∈ M.sets ∧ movedEnums ∈ M.sets ∧ movedS ∈ M.sets ∧
      movedS ⊆ b.carrier ∧ M.groundEmbeddable movedS ZFSet.omega ∧
      PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode (a.iso g p))
        b.carrier b.conditionOrder meetGraph N (M.niceVisibilityGraph a s b T d.principalFix)
        (s.encode ⊤) ZFSet.omega
        (M.storedPreparationRequests movedA (M.refinementLevelFormulaData a s b d level T T2 valid))
        C E movedK movedEnums ∧
      certificateUsedSupports b.carrier movedK =
        relationImage (certificateUsedSupports b.carrier k) b.carrier nodeMap ∧
      certificateUsedSupports b.carrier movedK ⊆ movedS := by
  let N := M.groundRelations T s.carrier
  let validN : ∀ z ∈ N, IsName s z := fun z hz =>
    Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
  let J := M.storedPreparationRequests A (M.refinementLevelFormulaData a s b d level T T2 valid)
  let C := M.supportedEqualityCertificateBound b.carrier W
  let E := M.synchronizedEnumerationBound b.carrier W
  let keyMap := Name.renameFamilyGraph s (a.iso g) N validN
  let nodeMap := b.graph b (d.iso g)
  let tupleMap := preparationTupleActionGraph C E b.carrier N nodeMap keyMap
  let movedK := preparationFamilyFirst J N C E keyMap tupleMap k enums
  let movedEnums := preparationFamilySecond J N C E keyMap tupleMap k enums
  have hJ := M.storedPreparationRequests_mem pairing unions powers separation hA _ members
  have requestBound : J ⊆ N := by
    intro z hz
    change z ∈ relationImage _ N _ ∪ relationImage _ N _ at hz
    rcases ZFSet.mem_union.1 hz with left | right
    · exact ((mem_relationImage _ N _ z).1 left).1
    · exact ((mem_relationImage _ N _ z).1 right).1
  have moved := M.preparedCertificateFamily_act_support a s t b d pairing unions powers separation
    collection (members 7) (members 8) group (members 10) supports maps nodeMaps omega (members 6) valid closed
    meetGraph meet hJ hW hk hEnums hS requestBound localBound supportNodes small p g family supportBound
  have requests := M.storedPreparationRequests_structural_act a s b d level T T2 valid valid2 t
    pairing unions powers separation collection members maps nodeMaps group (members 10) supports closed closed2
    hLevel hT2 function stored hA g
  dsimp only at moved requests ⊢
  refine ⟨moved.1, moved.2.1, moved.2.2.1, moved.2.2.2.1, moved.2.2.2.2.1,
    ?_, moved.2.2.2.2.2.2⟩
  exact (congrArg (fun domain => PreparedCertificateFamilyCode M s.carrier s.conditionOrder
    (s.encode (a.iso g p)) b.carrier b.conditionOrder meetGraph N
    (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤) ZFSet.omega domain C E movedK movedEnums)
    requests).mp moved.2.2.2.2.2.1

end PartitionPilot.Forcing.TransitiveGround

end OAI
