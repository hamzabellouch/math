import OAI.SetTheory.PartitionPrinciple.Definability.TileStarIncidenceRealization
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialExternalGroup

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def externalCosetRelation (E G inclusion multiplication : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ w ∈ E, ∃ v ∈ E, z = ZFSet.pair w v ∧
    ∃ j ∈ G, ∃ k ∈ E, ZFSet.pair j k ∈ inclusion ∧
      ZFSet.pair (ZFSet.pair w k) v ∈ multiplication) (ZFSet.prod E E)

theorem externalCosetRelation_subset (E G inclusion multiplication : ZFSet.{u}) :
    externalCosetRelation E G inclusion multiplication ⊆ ZFSet.prod E E :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem pair_mem_externalCosetRelation (E G inclusion multiplication w v : ZFSet.{u}) :
    ZFSet.pair w v ∈ externalCosetRelation E G inclusion multiplication ↔
      w ∈ E ∧ v ∈ E ∧ ∃ j ∈ G, ∃ k ∈ E, ZFSet.pair j k ∈ inclusion ∧
        ZFSet.pair (ZFSet.pair w k) v ∈ multiplication := by
  rw [externalCosetRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, w', hw, v', hv, equal, witnesses⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hw, hv, witnesses⟩
  · rintro ⟨hw, hv, witnesses⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hw, hv⟩, w, hw, v, hv, rfl, witnesses⟩

namespace BoundedFormula

def externalCosetEntryFormula {n} (z E G inclusion multiplication : Fin n) : BoundedFormula n :=
  exMem E (exMem E.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (exMem G.succ.succ (exMem E.succ.succ.succ
      (.conj (pairMembershipFormula 1 0 inclusion.succ.succ.succ.succ)
        (tripleMembershipFormula 3 0 2 multiplication.succ.succ.succ.succ))))))

theorem truth_externalCosetEntryFormula {n} (z E G inclusion multiplication : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalCosetEntryFormula z E G inclusion multiplication) env ↔
      ∃ w ∈ env E, ∃ v ∈ env E, env z = ZFSet.pair w v ∧
        ∃ j ∈ env G, ∃ k ∈ env E, ZFSet.pair j k ∈ env inclusion ∧
          ZFSet.pair (ZFSet.pair w k) v ∈ env multiplication := by
  simp only [externalCosetEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalCosetRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {E G inclusion multiplication : ZFSet.{u}}
    (hE : E ∈ M.sets) (hG : G ∈ M.sets) (hInclusion : inclusion ∈ M.sets)
    (hMultiplication : multiplication ∈ M.sets) :
    externalCosetRelation E G inclusion multiplication ∈ M.sets := by
  let params := extend E (extend G (extend inclusion (extend multiplication Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalCosetEntryFormula 0 1 2 3 4) params
    (Fin.cases hE (Fin.cases hG (Fin.cases hInclusion (Fin.cases hMultiplication (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hE hE)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalCosetEntryFormula 0 1 2 3 4) (extend z params)) (ZFSet.prod E E) =
      externalCosetRelation E G inclusion multiplication := by
    apply ZFSet.ext
    intro z
    rw [externalCosetRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalCosetEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps.CosetGeometry
universe u
variable {J S : Type u} [Group J]
variable (s : Presentation (External J S)) (g : Presentation J)
variable {inclusion multiplication : ZFSet.{u}}
variable (oldEntries : ∀ j k, ZFSet.pair (g.encode j) (s.encode k) ∈ inclusion ↔ old J S j = k)
variable (mulEntries : ∀ w k v,
  ZFSet.pair (ZFSet.pair (s.encode w) (s.encode k)) (s.encode v) ∈ multiplication ↔ w * k = v)

include oldEntries mulEntries in
theorem externalCosetRelation_iff (w v : External J S) :
    ZFSet.pair (s.encode w) (s.encode v) ∈ externalCosetRelation s.carrier g.carrier inclusion multiplication ↔
      point J S w = point J S v := by
  rw [pair_mem_externalCosetRelation, point_eq]
  constructor
  · rintro ⟨_, _, j, hj, k, hk, oldEntry, mulEntry⟩
    obtain ⟨j, rfl⟩ := (g.mem_carrier j).1 hj
    obtain ⟨k, rfl⟩ := (s.mem_carrier k).1 hk
    exact ⟨j, (oldEntries j k).1 oldEntry ▸ (mulEntries w k v).1 mulEntry⟩
  · rintro ⟨j, equal⟩
    exact ⟨s.encode_mem w, s.encode_mem v, g.encode j, g.encode_mem j,
      s.encode (old J S j), s.encode_mem _, (oldEntries j _).2 rfl,
      (mulEntries w _ v).2 equal⟩

include oldEntries mulEntries in
theorem externalCosetRelation_equivalence :
    EquivalenceRelationCode s.carrier (externalCosetRelation s.carrier g.carrier inclusion multiplication) := by
  have entries := externalCosetRelation_iff s g oldEntries mulEntries
  refine ⟨externalCosetRelation_subset _ _ _ _, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    exact (entries w w).2 rfl
  · intro w v related
    obtain ⟨hw, hv, _⟩ := (pair_mem_externalCosetRelation _ _ _ _ _ _).1 related
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    obtain ⟨v, rfl⟩ := (s.mem_carrier v).1 hv
    exact (entries v w).2 ((entries w v).1 related).symm
  · intro w v z first second
    obtain ⟨hw, hv, _⟩ := (pair_mem_externalCosetRelation _ _ _ _ _ _).1 first
    obtain ⟨_, hz, _⟩ := (pair_mem_externalCosetRelation _ _ _ _ _ _).1 second
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    obtain ⟨v, rfl⟩ := (s.mem_carrier v).1 hv
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    exact (entries w z).2 (((entries w v).1 first).trans ((entries v z).1 second))

include oldEntries mulEntries in
theorem externalCosetRelation_related (w v : External J S) :
    ZFSet.pair (s.encode w) (s.encode v) ∈ externalCosetRelation s.carrier g.carrier inclusion multiplication ↔
      (cosetSetoid J S).r w v :=
  (externalCosetRelation_iff s g oldEntries mulEntries w v).trans (point_eq J S w v)

noncomputable def externalCosetPresentation : Presentation (Vertex J S) :=
  s.quotientPresentation (cosetSetoid J S)
    (externalCosetRelation_equivalence s g oldEntries mulEntries)
    (externalCosetRelation_related s g oldEntries mulEntries)

theorem externalCosetPresentation_carrier :
    (externalCosetPresentation s g oldEntries mulEntries).carrier =
      equivalenceClasses s.carrier (externalCosetRelation s.carrier g.carrier inclusion multiplication) := rfl

theorem externalCosetPresentation_encode_point (w : External J S) :
    (externalCosetPresentation s g oldEntries mulEntries).encode (point J S w) =
      equivalenceClass s.carrier (externalCosetRelation s.carrier g.carrier inclusion multiplication) (s.encode w) := rfl

theorem externalCosetClassifier_entry_iff (w : External J S) (q : Vertex J S) :
    ZFSet.pair (s.encode w) ((externalCosetPresentation s g oldEntries mulEntries).encode q) ∈
      equivalenceClassifier s.carrier (externalCosetRelation s.carrier g.carrier inclusion multiplication) ↔
        point J S w = q :=
  s.quotientPresentation_classifier_entry_iff (cosetSetoid J S)
    (externalCosetRelation_equivalence s g oldEntries mulEntries)
    (externalCosetRelation_related s g oldEntries mulEntries) w q

theorem externalCosetClassifier_eq_graph :
    equivalenceClassifier s.carrier (externalCosetRelation s.carrier g.carrier inclusion multiplication) =
      s.graph (externalCosetPresentation s g oldEntries mulEntries) (point J S) :=
  s.quotientClassifier_eq_graph (cosetSetoid J S)
    (externalCosetRelation_equivalence s g oldEntries mulEntries)
    (externalCosetRelation_related s g oldEntries mulEntries)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hG : G ∈ M.sets) (hLetters : externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0) ∈ M.sets)

noncomputable def externalFamilyGroupPresentation :
    letI := group.toGroup
    Presentation (External (SetMembers G) (completion.externalFamily group oldAction compression).Letters) := by
  letI := group.toGroup
  exact M.externalGroupPresentation pairing unions powers separation infinite (SetMembers.presentation G)
    (completion.externalFamilyLetterPresentation group oldAction compression) hG hLetters

theorem externalFamilyGroupPresentation_carrier :
    letI := group.toGroup
    (completion.externalFamilyGroupPresentation group oldAction compression pairing unions powers separation infinite hG hLetters).carrier =
      M.externalGroupCarrier G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one := by
  let := group.toGroup
  change M.externalGroupCarrier G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0))
    (((SetMembers.presentation G).product (SetMembers.presentation G)).graph (SetMembers.presentation G) (fun p => p.1 * p.2))
    ((SetMembers.presentation G).encode 1) = _
  rw [group.multiplication_graph_eq, group.identity_code_eq]

theorem externalFamilyGroupPresentation_multiplication :
    letI := group.toGroup
    let s := completion.externalFamilyGroupPresentation group oldAction compression pairing unions powers separation infinite hG hLetters
    M.externalGroupMultiplication G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one =
      (s.product s).graph s (fun p => p.1 * p.2) := by
  let := group.toGroup
  have equal := M.externalGroupMultiplication_eq_graph pairing unions powers separation infinite
    (SetMembers.presentation G) (completion.externalFamilyLetterPresentation group oldAction compression) hG hLetters
  rw [group.multiplication_graph_eq, group.identity_code_eq] at equal
  exact equal

theorem externalFamilyGroupPresentation_old :
    letI := group.toGroup
    let s := completion.externalFamilyGroupPresentation group oldAction compression pairing unions powers separation infinite hG hLetters
    M.externalOldInclusion G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one =
      (SetMembers.presentation G).graph s (old (SetMembers G) (completion.externalFamily group oldAction compression).Letters) := by
  let := group.toGroup
  have equal := M.externalOldInclusion_eq_graph pairing unions powers separation infinite
    (SetMembers.presentation G) (completion.externalFamilyLetterPresentation group oldAction compression) hG hLetters
  rw [group.multiplication_graph_eq, group.identity_code_eq] at equal
  exact equal

theorem externalFamilyGroupPresentation_generators :
    letI := group.toGroup
    let s := completion.externalFamilyGroupPresentation group oldAction compression pairing unions powers separation infinite hG hLetters
    M.externalChildGenerators G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one =
      (completion.externalFamilyLetterPresentation group oldAction compression).graph s
        (generator (SetMembers G) (completion.externalFamily group oldAction compression).Letters) := by
  let := group.toGroup
  have equal := M.externalChildGenerators_eq_graph pairing unions powers separation infinite
    (SetMembers.presentation G) (completion.externalFamilyLetterPresentation group oldAction compression) hG hLetters
  rw [group.multiplication_graph_eq, group.identity_code_eq] at equal
  exact equal

theorem externalFamilyGroupPresentation_identity :
    letI := group.toGroup
    let s := completion.externalFamilyGroupPresentation group oldAction compression pairing unions powers separation infinite hG hLetters
    M.externalGroupIdentity G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one = s.encode 1 := by
  let := group.toGroup
  have equal := M.externalGroupIdentity_eq_encode pairing unions powers separation infinite
    (SetMembers.presentation G) (completion.externalFamilyLetterPresentation group oldAction compression) hG hLetters
  rw [group.multiplication_graph_eq, group.identity_code_eq] at equal
  exact equal

end PartitionPilot.Forcing.GroundCompressionCompletion



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure GroundExternalGeometryInputs (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m inv one T τ P r μ A : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) : Prop where
  words : GroundExternalWordData M initial I Sources Reps G m one T τ P r μ A completion
  group : GroundExternalGroupData M G (externalChildLetters I P (externalRectangles P G r μ A)) m inv one
  old_inclusion_ground : M.externalOldInclusion G
    (externalChildLetters I P (externalRectangles P G r μ A)) m one ∈ M.sets
  old_inclusion_injection : InjectionCode G
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (M.externalOldInclusion G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
  generators_ground : M.externalChildGenerators G
    (externalChildLetters I P (externalRectangles P G r μ A)) m one ∈ M.sets
  generators_injection : InjectionCode (externalChildLetters I P (externalRectangles P G r μ A))
    (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (M.externalChildGenerators G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
  original : CompressionOriginalData P r μ A G (completion.algebra.union.fields 0)
    (completion.algebra.union.fields 1) (completion.algebra.union.fields 2) (completion.algebra.union.fields 12)

namespace GroundCompressionOrigin
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P r μ A τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P r μ A τ I Sources Reps G m inv one T Filters)

include origin in
theorem externalGeometryInputs
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv one) (hm : m ∈ M.sets) (hInv : inv ∈ M.sets) :
    GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion := by
  have words := completion.externalWordData pairing unions powers separation infinite hI hP hG hr hμ hA
  have generators := M.externalGeneratorGraphs_ground_injections pairing unions powers separation infinite
    group hG words.letters_ground hm
  exact ⟨words, M.externalGroupData pairing unions powers separation infinite group hG words.letters_ground hm hInv,
    generators.1, generators.2.1, generators.2.2.1, generators.2.2.2,
    origin.union_original_data completion.algebra.union pairing unions powers separation hI hSources hReps hG hT⟩

end GroundCompressionOrigin

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalCosetEquivalence (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  externalCosetRelation (M.externalGroupCarrier G S m one) G
    (M.externalOldInclusion G S m one) (M.externalGroupMultiplication G S m one)
noncomputable def externalCosetCarrier (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClasses (M.externalGroupCarrier G S m one) (M.externalCosetEquivalence G S m one)
noncomputable def externalCosetClassifier (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClassifier (M.externalGroupCarrier G S m one) (M.externalCosetEquivalence G S m one)

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
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground

theorem externalCoset_old_entries :
    letI := group.toGroup
    ∀ j k, ZFSet.pair ((SetMembers.presentation G).encode j) ((sGroup).encode k) ∈
      M.externalOldInclusion G letters m one ↔ old (SetMembers G) (family).Letters j = k := by
  let := group.toGroup
  intro j k
  rw [completion.externalFamilyGroupPresentation_old group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground]
  exact Presentation.pair_mem_graph _ _ _ _ _

theorem externalCoset_mul_entries :
    letI := group.toGroup
    ∀ (w k v : External (SetMembers G) (family).Letters), ZFSet.pair (ZFSet.pair ((sGroup).encode w) ((sGroup).encode k)) ((sGroup).encode v) ∈
      M.externalGroupMultiplication G letters m one ↔ w * k = v := by
  let := group.toGroup
  intro w k v
  rw [completion.externalFamilyGroupPresentation_multiplication group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground]
  exact Presentation.pair_mem_graph ((sGroup).product (sGroup)) (sGroup) (fun p => p.1 * p.2) (w, k) v

noncomputable def externalCosetPresentation :
    letI := group.toGroup
    Presentation (Vertex (SetMembers G) (family).Letters) := by
  letI := group.toGroup
  exact Forcing.externalCosetPresentation (sGroup) (SetMembers.presentation G)
    (data.externalCoset_old_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG)

theorem externalCosetPresentation_carrier :
    letI := group.toGroup
    (data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG).carrier =
      M.externalCosetCarrier G letters m one := by
  let := group.toGroup
  change equivalenceClasses (sGroup).carrier (externalCosetRelation (sGroup).carrier G
    (M.externalOldInclusion G letters m one) (M.externalGroupMultiplication G letters m one)) = _
  rw [completion.externalFamilyGroupPresentation_carrier]
  rfl

theorem externalCosetEquivalence_iff :
    letI := group.toGroup
    ∀ w v, ZFSet.pair ((sGroup).encode w) ((sGroup).encode v) ∈ M.externalCosetEquivalence G letters m one ↔
      point (SetMembers G) (family).Letters w = point (SetMembers G) (family).Letters v := by
  let := group.toGroup
  have entries := Forcing.externalCosetRelation_iff (sGroup) (SetMembers.presentation G)
    (data.externalCoset_old_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG)
  rw [completion.externalFamilyGroupPresentation_carrier] at entries
  exact entries

theorem externalCosetClassifier_entry_iff :
    letI := group.toGroup
    let q := data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG
    ∀ w v, ZFSet.pair ((sGroup).encode w) (q.encode v) ∈ M.externalCosetClassifier G letters m one ↔
      point (SetMembers G) (family).Letters w = v := by
  let := group.toGroup
  dsimp only
  have entries := Forcing.externalCosetClassifier_entry_iff (sGroup) (SetMembers.presentation G)
    (data.externalCoset_old_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG)
  rw [completion.externalFamilyGroupPresentation_carrier] at entries
  exact entries

theorem externalCosetClassifier_graph :
    letI := group.toGroup
    M.externalCosetClassifier G letters m one = (sGroup).graph
      (data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG)
      (point (SetMembers G) (family).Letters) := by
  let := group.toGroup
  have equal := Forcing.externalCosetClassifier_eq_graph (sGroup) (SetMembers.presentation G)
    (data.externalCoset_old_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG)
  rw [completion.externalFamilyGroupPresentation_carrier] at equal
  exact equal

include data pairing unions powers separation hG in
theorem externalCosets_ground :
    M.externalCosetEquivalence G letters m one ∈ M.sets ∧
      M.externalCosetCarrier G letters m one ∈ M.sets ∧ M.externalCosetClassifier G letters m one ∈ M.sets := by
  have relation := M.externalCosetRelation_mem pairing unions powers separation data.group.carrier_mem hG
    data.old_inclusion_ground data.group.multiplication_mem
  exact ⟨relation, M.equivalenceClasses_mem powers separation data.group.carrier_mem relation,
    M.equivalenceClassifier_mem pairing unions powers separation data.group.carrier_mem relation⟩

include data group oldAction pairing unions powers separation infinite hG in
theorem externalCosets_spec :
    let E := M.externalGroupCarrier G letters m one
    let Q := M.externalCosetCarrier G letters m one
    let C := M.externalCosetClassifier G letters m one
    EquivalenceRelationCode E (M.externalCosetEquivalence G letters m one) ∧ ZFSet.IsFunc E Q C ∧
      (∀ q ∈ Q, ∃ w ∈ E, ZFSet.pair w q ∈ C) ∧
      (∀ w v q t, ZFSet.pair w q ∈ C → ZFSet.pair v t ∈ C →
        (q = t ↔ ZFSet.pair w v ∈ M.externalCosetEquivalence G letters m one)) := by
  let := group.toGroup
  have code := Forcing.externalCosetRelation_equivalence (sGroup) (SetMembers.presentation G)
    (data.externalCoset_old_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG)
  rw [completion.externalFamilyGroupPresentation_carrier] at code
  exact ⟨code, equivalenceClassifier_function _ _, fun _ hq => equivalenceClassifier_onto hq,
    fun _ _ _ _ first second => code.classifier_kernel first second⟩

end GroundExternalGeometryInputs




namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarVertices (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarVertexCarrier (M.externalCosetCarrier G S m one) (M.externalGroupCarrier G S m one) R
noncomputable def externalStarEdges (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarEdgeCarrier (M.externalGroupCarrier G S m one) R S
noncomputable def externalStarDarts (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarDartCarrier (M.externalGroupCarrier G S m one) R S

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
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "family" => completion.externalFamily group oldAction data.original
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "sLetter" => completion.externalFamilyLetterPresentation group oldAction data.original
local notation "sRequest" => externalRequestPresentation I P0 rectangles
local notation "sCoset" => data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG

noncomputable def externalStarVertexPresentation :
    letI := group.toGroup
    Presentation (TileStars.Vertex (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)) := by
  letI := group.toGroup
  exact tileStarVertexPresentation (sGroup) (sRequest) (sCoset)

noncomputable def externalStarEdgePresentation :
    letI := group.toGroup
    Presentation (TileStars.Edge (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)) := by
  letI := group.toGroup
  exact tileStarEdgePresentation (sGroup) (sLetter) (sRequest)

noncomputable def externalStarDartPresentation :
    letI := group.toGroup
    Presentation (TileStars.Dart (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)) := by
  letI := group.toGroup
  exact tileStarDartPresentation (sGroup) (sLetter) (sRequest)

theorem externalStarPresentations_carriers :
    letI := group.toGroup
    (data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG).carrier =
      M.externalStarVertices G letters requests m one ∧
    (data.externalStarEdgePresentation group oldAction pairing unions powers separation infinite hG).carrier =
      M.externalStarEdges G letters requests m one ∧
    (data.externalStarDartPresentation group oldAction pairing unions powers separation infinite hG).carrier =
      M.externalStarDarts G letters requests m one := by
  let := group.toGroup
  change tileStarVertexCarrier (sCoset).carrier (sGroup).carrier requests = _ ∧
    tileStarEdgeCarrier (sGroup).carrier requests (sLetter).carrier = _ ∧
    tileStarDartCarrier (sGroup).carrier requests (sLetter).carrier = _
  rw [data.externalCosetPresentation_carrier, completion.externalFamilyGroupPresentation_carrier,
    completion.externalFamilyLetterPresentation_carrier]
  exact ⟨rfl, rfl, rfl⟩

include data pairing unions powers separation hG in
theorem externalStarCarriers_ground :
    M.externalStarVertices G letters requests m one ∈ M.sets ∧
      M.externalStarEdges G letters requests m one ∈ M.sets ∧
      M.externalStarDarts G letters requests m one ∈ M.sets := by
  exact M.tileStarCarriers_mem pairing unions powers separation
    (data.externalCosets_ground pairing unions powers separation hG).2.1
    data.group.carrier_mem data.words.requests_ground data.words.letters_ground

end GroundExternalGeometryInputs
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def tileStarRequestGraph (R S : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction S (productFirst R (natSetCode 2))

theorem pair_mem_tileStarRequestGraph {R S a c b : ZFSet.{u}}
    (ha : a ∈ R) (hc : c ∈ natSetCode 2) (hs : ZFSet.pair a c ∈ S) :
    ZFSet.pair (ZFSet.pair a c) b ∈ tileStarRequestGraph R S ↔ a = b := by
  rw [tileStarRequestGraph, pair_mem_graphRestriction, mem_productFirst]
  constructor
  · rintro ⟨⟨x, _, y, _, equal⟩, _⟩
    have eq := ZFSet.pair_inj.1 equal
    exact ((ZFSet.pair_inj.1 eq.1).1).trans eq.2.symm
  · rintro rfl
    exact ⟨⟨a, ha, c, hc, rfl⟩, hs⟩

theorem externalRequestChildCode_mem {I P R : ZFSet.{u}}
    (r : ExternalRequestIndex I P R) (c : ExternalRequestChild r) :
    externalRequestChildCode r c ∈ natSetCode 2 := by
  rcases r with i | (x | r)
  · exact (mem_natTwo_iff_externalSignCode _).2 ⟨false, rfl⟩
  · exact (mem_natTwo_iff_externalSignCode _).2 ⟨false, rfl⟩
  · exact (mem_natTwo_iff_externalSignCode _).2 ⟨c.down, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem tileStarRequestGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R S : ZFSet.{u}} (hR : R ∈ M.sets) (hS : S ∈ M.sets) : tileStarRequestGraph R S ∈ M.sets := by
  have hz : natSetCode 0 ∈ M.sets := M.empty_mem ⟨R, hR⟩
  have ho : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hz hz
  have ht : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions ho ho
  exact M.graphRestriction_mem unions separation hS (M.productFirst_mem pairing unions powers separation hR ht)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialExternalGeometryInputs
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
            I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, ⟨compression⟩⟩ :=
    M.exists_groundInitialCompressionOrigin pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels group action meet hτ top hC hD hrD hc hOriginal
      originalCode columns target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression,
    origin.externalGeometryInputs compression.born.profiled.heighted.completion
      pairing unions powers separation infinite hI hSources hReps hG hT hP hr hμ hA group hm hInv⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarSource (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarSourceGraph (M.externalGroupCarrier G S m one) R S (M.externalCosetCarrier G S m one)
    (M.externalCosetClassifier G S m one) (tileStarRequestGraph R S)
    (M.externalChildGenerators G S m one) (M.externalGroupMultiplication G S m one)
noncomputable def externalStarTarget (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarTargetGraph (M.externalGroupCarrier G S m one) R S (M.externalCosetCarrier G S m one)
    (M.externalCosetClassifier G S m one) (tileStarRequestGraph R S)
    (M.externalChildGenerators G S m one) (M.externalGroupMultiplication G S m one)
noncomputable def externalStarReverse (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarReverseGraph (M.externalGroupCarrier G S m one) R S
noncomputable def externalStarIncidence (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  dartIncidenceGraph (M.externalStarSource G S R m one) (M.externalStarTarget G S R m one)
noncomputable def externalStarAdjacency (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  dartAdjacencyGraph (M.externalStarDarts G S R m one) (M.externalStarVertices G S R m one)
    (M.externalStarSource G S R m one) (M.externalStarTarget G S R m one)

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
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "rectangles" => externalRectangles P0 G r0 μ0 A0
local notation "letters" => externalChildLetters I P0 rectangles
local notation "requests" => externalRequestCarrier I P0 rectangles
local notation "family" => completion.externalFamily group oldAction data.original
local notation "sGroup" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "sLetter" => completion.externalFamilyLetterPresentation group oldAction data.original
local notation "sRequest" => externalRequestPresentation I P0 rectangles
local notation "sCoset" => data.externalCosetPresentation group oldAction pairing unions powers separation infinite hG
local notation "sVertex" => data.externalStarVertexPresentation group oldAction pairing unions powers separation infinite hG
local notation "sDart" => data.externalStarDartPresentation group oldAction pairing unions powers separation infinite hG

theorem externalStar_request_entries :
    ∀ (a : (family).Letters) b, ZFSet.pair ((sLetter).encode a) ((sRequest).encode b) ∈
      tileStarRequestGraph requests letters ↔ a.1 = b := by
  intro a b
  let child := externalRequestChildCode a.1 (cast (completion.externalFamily_child group oldAction data.original a.1) a.2)
  have shape : (sLetter).encode a = ZFSet.pair ((sRequest).encode a.1) child := rfl
  have member := (sLetter).encode_mem a
  rw [shape] at member ⊢
  exact (pair_mem_tileStarRequestGraph ((sRequest).encode_mem a.1)
    (externalRequestChildCode_mem _ _) member).trans
    ⟨fun h => (sRequest).injective h, congrArg (sRequest).encode⟩

theorem externalStar_generator_entries :
    letI := group.toGroup
    ∀ a b, ZFSet.pair ((sLetter).encode a) ((sGroup).encode b) ∈ M.externalChildGenerators G letters m one ↔
      generator (SetMembers G) (family).Letters a = b := by
  let := group.toGroup
  intro a b
  rw [completion.externalFamilyGroupPresentation_generators group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground]
  exact Presentation.pair_mem_graph (sLetter) (sGroup) _ a b

theorem externalStarSource_iff :
    letI := group.toGroup
    ∀ (d : TileStars.Dart (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles))
      (v : TileStars.Vertex (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)),
      ZFSet.pair ((sDart).encode d) ((sVertex).encode v) ∈ M.externalStarSource G letters requests m one ↔
        TileStars.source (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) d = v := by
  let := group.toGroup
  intro d v
  have entries := tileStar_source_iff (sGroup) (sLetter) (sRequest) (sCoset) (fun a => a.1)
    (data.externalCosetClassifier_entry_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStar_request_entries group oldAction)
    (data.externalStar_generator_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG) d v
  rw [completion.externalFamilyGroupPresentation_carrier, completion.externalFamilyLetterPresentation_carrier,
    data.externalCosetPresentation_carrier] at entries
  exact entries

theorem externalStarTarget_iff :
    letI := group.toGroup
    ∀ (d : TileStars.Dart (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles))
      (v : TileStars.Vertex (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)),
      ZFSet.pair ((sDart).encode d) ((sVertex).encode v) ∈ M.externalStarTarget G letters requests m one ↔
        TileStars.target (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) d = v := by
  let := group.toGroup
  intro d v
  have entries := tileStar_target_iff (sGroup) (sLetter) (sRequest) (sCoset) (fun a => a.1)
    (data.externalCosetClassifier_entry_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStar_request_entries group oldAction)
    (data.externalStar_generator_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG) d v
  rw [completion.externalFamilyGroupPresentation_carrier, completion.externalFamilyLetterPresentation_carrier,
    data.externalCosetPresentation_carrier] at entries
  exact entries

theorem externalStarReverse_iff :
    letI := group.toGroup
    ∀ (d v : TileStars.Dart (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)),
      ZFSet.pair ((sDart).encode d) ((sDart).encode v) ∈ M.externalStarReverse G letters requests m one ↔
        TileStars.reverse (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) d = v := by
  let := group.toGroup
  intro d v
  have entries := tileStar_reverse_iff (sGroup) (sLetter) (sRequest) d v
  rw [completion.externalFamilyGroupPresentation_carrier, completion.externalFamilyLetterPresentation_carrier] at entries
  exact entries

theorem externalStarIncidence_iff :
    letI := group.toGroup
    ∀ (d : TileStars.Dart (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles))
      (v : TileStars.Vertex (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)), ZFSet.pair ((sDart).encode d) ((sVertex).encode v) ∈ M.externalStarIncidence G letters requests m one ↔
      TileStars.source (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) d = v ∨
        TileStars.target (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) d = v := by
  let := group.toGroup
  intro d v
  have entries := tileStar_incidence_iff (sGroup) (sLetter) (sRequest) (sCoset) (fun a => a.1)
    (data.externalCosetClassifier_entry_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStar_request_entries group oldAction)
    (data.externalStar_generator_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG) d v
  rw [completion.externalFamilyGroupPresentation_carrier, completion.externalFamilyLetterPresentation_carrier,
    data.externalCosetPresentation_carrier] at entries
  exact entries

theorem externalStarAdjacency_iff :
    letI := group.toGroup
    ∀ (x y : TileStars.Vertex (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles)), ZFSet.pair ((sVertex).encode x) ((sVertex).encode y) ∈ M.externalStarAdjacency G letters requests m one ↔
      ∃ d : TileStars.Dart (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles),
        TileStars.source (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) d = x ∧
        TileStars.target (SetMembers G) (family).Letters (ExternalRequestIndex I P0 rectangles) (fun a => a.1) d = y := by
  let := group.toGroup
  intro x y
  have entries := tileStar_adjacency_iff (sGroup) (sLetter) (sRequest) (sCoset) (fun a => a.1)
    (data.externalCosetClassifier_entry_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStar_request_entries group oldAction)
    (data.externalStar_generator_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG) x y
  rw [completion.externalFamilyGroupPresentation_carrier, completion.externalFamilyLetterPresentation_carrier,
    data.externalCosetPresentation_carrier] at entries
  exact entries

include data group oldAction pairing unions powers separation infinite hG in
theorem externalStarEndpoint_functions :
    ZFSet.IsFunc (M.externalStarDarts G letters requests m one) (M.externalStarVertices G letters requests m one)
      (M.externalStarSource G letters requests m one) ∧
    ZFSet.IsFunc (M.externalStarDarts G letters requests m one) (M.externalStarVertices G letters requests m one)
      (M.externalStarTarget G letters requests m one) ∧
    ZFSet.IsFunc (M.externalStarDarts G letters requests m one) (M.externalStarDarts G letters requests m one)
      (M.externalStarReverse G letters requests m one) := by
  let := group.toGroup
  have functions := tileStar_endpoint_functions (sGroup) (sLetter) (sRequest) (sCoset) (fun a => a.1)
    (data.externalCosetClassifier_entry_iff group oldAction pairing unions powers separation infinite hG)
    (data.externalStar_request_entries group oldAction)
    (data.externalStar_generator_entries group oldAction pairing unions powers separation infinite hG)
    (data.externalCoset_mul_entries group oldAction pairing unions powers separation infinite hG)
  rw [completion.externalFamilyGroupPresentation_carrier, completion.externalFamilyLetterPresentation_carrier,
    data.externalCosetPresentation_carrier] at functions
  exact functions

include data pairing unions powers separation hG in
theorem externalStarIncidence_ground :
    tileStarRequestGraph requests letters ∈ M.sets ∧
    M.externalStarSource G letters requests m one ∈ M.sets ∧
    M.externalStarTarget G letters requests m one ∈ M.sets ∧
    M.externalStarReverse G letters requests m one ∈ M.sets ∧
    M.externalStarIncidence G letters requests m one ∈ M.sets ∧
    M.externalStarAdjacency G letters requests m one ∈ M.sets := by
  have req := M.tileStarRequestGraph_mem pairing unions powers separation data.words.requests_ground data.words.letters_ground
  have cosets := data.externalCosets_ground pairing unions powers separation hG
  have carriers := data.externalStarCarriers_ground pairing unions powers separation hG
  have src := M.tileStarSourceGraph_mem pairing unions powers separation data.group.carrier_mem
    data.words.requests_ground data.words.letters_ground cosets.2.1 cosets.2.2 req
    data.generators_ground data.group.multiplication_mem
  have tgt := M.tileStarTargetGraph_mem pairing unions powers separation data.group.carrier_mem
    data.words.requests_ground data.words.letters_ground cosets.2.1 cosets.2.2 req
    data.generators_ground data.group.multiplication_mem
  have rev := M.tileStarReverseGraph_mem pairing unions powers separation data.group.carrier_mem
    data.words.requests_ground data.words.letters_ground
  exact ⟨req, src, tgt, rev, M.dartIncidenceGraph_mem pairing unions src tgt,
    M.dartAdjacencyGraph_mem pairing unions powers separation carriers.2.2 carriers.1 src tgt⟩

end GroundExternalGeometryInputs
end PartitionPilot.Forcing

end OAI
