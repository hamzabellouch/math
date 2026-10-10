import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCompressionBirthData

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def birthRestrictionFamilyEntryFormula {k} (z omega domainsBound relations t domains birth : Fin k) :
    BoundedFormula k :=
  exMem omega (exMem domainsBound.succ (exMem relations.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 0)
      (.conj (pairMembershipFormula 2 1 domains.succ.succ.succ)
        (graphRestrictionFormula 0 1 t.succ.succ.succ birth.succ.succ.succ)))))

theorem truth_birthRestrictionFamilyEntryFormula {k}
    (z omega domainsBound relations t domains birth : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (birthRestrictionFamilyEntryFormula z omega domainsBound relations t domains birth) env ↔
      ∃ n ∈ env omega, ∃ P ∈ env domainsBound, ∃ b ∈ env relations,
        env z = ZFSet.pair n b ∧ ZFSet.pair n P ∈ env domains ∧
          b = ZFSet.sep (fun w => w ∈ ZFSet.prod P (env t)) (env birth) := by
  simp only [birthRestrictionFamilyEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_graphRestrictionFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def birthRestrictionFamily (U T Ps birth : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ P ∈ ⋃₀ ⋃₀ Ps,
    ∃ b ∈ M.groundRelations U T,
      z = ZFSet.pair n b ∧ ZFSet.pair n P ∈ Ps ∧ b = graphRestriction P birth)
    (ZFSet.prod ZFSet.omega (M.groundRelations U T))

theorem birthRestrictionFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U T Ps birth : ZFSet.{u}} (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    (hU : U ∈ M.sets) (hT : T ∈ M.sets) (hPs : Ps ∈ M.sets) (hBirth : birth ∈ M.sets)
    (born : ZFSet.IsFunc U T birth) : M.birthRestrictionFamily U T Ps birth ∈ M.sets := by
  have hBound := M.union_mem unions (M.union_mem unions hPs)
  have hRelations := M.groundRelations_mem pairing unions powers separation hU hT
  let params := extend ZFSet.omega (extend (⋃₀ ⋃₀ Ps) (extend (M.groundRelations U T)
    (extend T (extend Ps (extend birth Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.birthRestrictionFamilyEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hω (Fin.cases hBound (Fin.cases hRelations (Fin.cases hT
      (Fin.cases hPs (Fin.cases hBirth (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hω hRelations)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.birthRestrictionFamilyEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod ZFSet.omega (M.groundRelations U T)) = M.birthRestrictionFamily U T Ps birth := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, birthRestrictionFamily, ZFSet.mem_sep,
      BoundedFormula.truth_birthRestrictionFamilyEntryFormula]
    change (_ ∧ ∃ n ∈ ZFSet.omega, ∃ P ∈ ⋃₀ ⋃₀ Ps, ∃ b ∈ M.groundRelations U T,
      z = ZFSet.pair n b ∧ ZFSet.pair n P ∈ Ps ∧
        b = ZFSet.sep (fun w => w ∈ ZFSet.prod P T) birth) ↔ _
    simp only [graphRestriction_eq_sep born]
  exact equal ▸ selected

theorem birthRestrictionFamily_entries
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {U T Ps birth : ZFSet.{u}} (hPs : Ps ∈ M.sets) (hBirth : birth ∈ M.sets)
    (P : Nat → ZFSet.{u})
    (domains : ∀ n D, ZFSet.pair (natSetCode n) D ∈ Ps ↔ D = P n)
    (born : ZFSet.IsFunc U T birth) (n : Nat) (b : ZFSet.{u}) :
    ZFSet.pair (natSetCode n) b ∈ M.birthRestrictionFamily U T Ps birth ↔
      b = graphRestriction (P n) birth := by
  constructor
  · intro member
    obtain ⟨_, k, _, D, _, c, _, equal, entry, restriction⟩ := ZFSet.mem_sep.1 member
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact (domains n D).1 entry ▸ restriction
  · intro equal
    have entry := (domains n (P n)).2 rfl
    have hP := M.pair_right (M.transitive hPs entry)
    have hRestriction := M.graphRestriction_mem unions separation hP hBirth
    have relation : b ∈ M.groundRelations U T := (M.mem_groundRelations U T b).2 ⟨
      equal.symm ▸ hRestriction, fun z hz => born.1
        (graphRestriction_subset (P n) birth (equal ▸ hz))⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, relation⟩,
      natSetCode n, natSetCode_mem_omega n, P n, pair_second_mem_doubleUnion entry,
      b, relation, rfl, entry, equal⟩

theorem exists_groundBirthRestrictionFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U T Ps birth : ZFSet.{u}} (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    (hU : U ∈ M.sets) (hT : T ∈ M.sets) (hPs : Ps ∈ M.sets) (hBirth : birth ∈ M.sets)
    (P : Nat → ZFSet.{u})
    (domains : ∀ n D, ZFSet.pair (natSetCode n) D ∈ Ps ↔ D = P n)
    (born : ZFSet.IsFunc U T birth) :
    ∃ family ∈ M.sets, FunctionGraphOn ZFSet.omega family ∧
      ∀ n b, ZFSet.pair (natSetCode n) b ∈ family ↔ b = graphRestriction (P n) birth := by
  have entries := M.birthRestrictionFamily_entries unions separation hPs hBirth P domains born
  refine ⟨M.birthRestrictionFamily U T Ps birth,
    M.birthRestrictionFamily_mem pairing unions powers separation hω hU hT hPs hBirth born,
    ⟨M.groundRelations U T, ?_, ?_⟩, entries⟩
  · exact fun z hz => (ZFSet.mem_sep.1 hz).1
  · intro n hn
    obtain ⟨j, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    exact ⟨graphRestriction (P j) birth, (entries j _).2 rfl,
      fun b hb => (entries j b).1 hb⟩

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundBirthData
    (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {base old : ZFSet.{u}} (hBase : base ∈ M.sets) (hOld : old ∈ M.sets)
    (ordinal : ordinalSetProperty base) (oldFunction : FunctionGraphOn state.data.D old)
    (oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base)
    (oldMeet : OldMeetCode state.data.rD state.data.μD old) :
    Nonempty (GroundCompressionBirthData M state.data I Sources Reps G m one T data base old) := by
  obtain ⟨stamps, hStamps, limit, hLimit, _, times⟩ := M.exists_groundCompressionStamps
    pairing unions separation collection infinite hBase ordinal
  have born : ZFSet.IsFunc state.data.D limit old := by
    refine ⟨?_, oldFunction.to_isFunc.2⟩
    intro z hz
    obtain ⟨x, hx, t, rfl⟩ := oldFunction.shape z hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, times.union.subset 0
      (compressionStamp_old_mem (oldBound x t hz) 0)⟩
  have hω := M.omega_mem separation infinite
  let stages := state.data.iterate M I Sources Reps G T
  obtain ⟨history, hHistory, _, entries, _, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  obtain ⟨domains, hDomains, _, domainEntries⟩ := M.exists_groundStateFieldFamily
    pairing separation collection hω hHistory stages entries 0
  obtain ⟨birth, hBirth, _, extension⟩ := M.exists_groundFirstAppearanceBirth
    pairing unions powers separation hω (data.ground 0) hLimit hDomains hStamps hOld
    (fun n => (stages n).D) (compressionStamp base) domainEntries times.entries
    (data.fieldUnion 0) born times.stamp_mem_limit
  have mono : ∀ n k, n ≤ k → (stages n).D ⊆ (stages k).D :=
    fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).1
  have function := extension.function (data.fieldUnion 0) mono born times.stamp_mem_limit
  obtain ⟨family, hFamily, familyFunction, familyEntries⟩ := M.exists_groundBirthRestrictionFamily
    pairing unions powers separation hω (data.ground 0) hLimit hDomains hBirth
    (fun n => (stages n).D) domainEntries function
  have finite := state.canonical_birth_oldMeet data pairing unions powers separation
    hI hSources hReps hG hT extension born times oldBound oldMeet
  have unionBirth := extension.restriction_union (data.fieldUnion 0) born
  have unionOldMeet := (data.fieldUnion 1).oldMeet (data.fieldUnion 2) unionBirth finite
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).2.2.1)
    (fun _ _ h => NatBirthExtensionCode.restriction_mono mono h)
  refine ⟨⟨stamps, hStamps, limit, hLimit, times, birth, hBirth, extension,
    family, hFamily, familyFunction, familyEntries, born, oldBound, function,
    extension.restriction_zero mono born, finite, unionOldMeet, ?_⟩⟩
  intro x entry
  exact ZFSet.mem_irrefl limit (ZFSet.pair_mem_prod.1 (function.1 entry)).2

end PartitionPilot.Forcing.GroundCompressionState

end

end OAI
