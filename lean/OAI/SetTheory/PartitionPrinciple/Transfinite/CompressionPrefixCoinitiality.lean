import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundChronologyFieldAppend

namespace OAI


namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def incoming_birth_layer_of_constancy
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {base birth bound stamp : ZFSet.{u}}
    (born : ZFSet.IsFunc state.data.D bound birth)
    (old : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (before : base ∈ stamp)
    (space : Space base = P0) (order : sourceOrder base = r0) (meet : sourceMeet base = μ0) :
    CodedGrowthLayer M Space sourceOrder sourceMeet state.data.currentCarrier
      state.data.currentOrder state.data.currentMeet (state.batch.batchBirth birth stamp) stamp := by
  apply state.batch.batchBirth_incoming_layer pairing unions powers separation
    state.ground.carrier state.ground.indices state.ground.spaces state.ground.relations
    state.ground.anchors state.ground.embeddings born old (fun _ => base) (fun _ => before)
  · intro i
    exact space.trans ((constant.space_entry_iff _ _).1
      (state.batch.space_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩)).2.symm
  · intro i
    exact order.trans ((constant.relation_entry_iff _ _).1
      (state.batch.rel_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩)).2.symm
  · intro i
    exact meet.trans ((constant.meet_entry_iff _ _).1
      (state.batch.meet_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩)).2.symm

variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include hI hSources hReps hG hT

noncomputable def canonical_incoming_birth_layer
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {base stamps limit old birth : ZFSet.{u}}
    (code : NatBirthExtensionCode (fun n => (state.data.iterate M I Sources Reps G T n).D)
      (compressionStamp base) old birth)
    (born : ZFSet.IsFunc state.data.D limit old)
    (times : CompressionStampCode base stamps limit)
    (oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base)
    (space : Space base = P0) (order : sourceOrder base = r0) (meet : sourceMeet base = μ0)
    (n : Nat) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T n).currentCarrier
      (state.data.iterate M I Sources Reps G T n).currentOrder
      (state.data.iterate M I Sources Reps G T n).currentMeet
      (graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D birth)
      (compressionStamp base n) := by
  let current := state.iterate pairing unions powers separation hI hSources hReps hG hT n
  have equal : current.data = state.data.iterate M I Sources Reps G T n :=
    state.iterate_data pairing unions powers separation hI hSources hReps hG hT n
  have currentConstant : RecursiveTemplateConstancy P0 r0 μ0 current.data := by
    simpa only [equal] using constant.iterate M I Sources Reps G T n
  have finite : ZFSet.IsFunc current.data.D limit
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) := by
    simpa only [equal] using state.canonical_birth_function data pairing unions powers separation
      hI hSources hReps hG hT code born times n
  have earlier : ∀ x t, ZFSet.pair x t ∈
      graphRestriction (state.data.iterate M I Sources Reps G T n).D birth → t ∈ compressionStamp base n :=
    fun _ _ entry => state.canonical_birth_before_stamp pairing unions powers separation
      hI hSources hReps hG hT code oldBound n entry
  have result := current.incoming_birth_layer_of_constancy pairing unions powers separation
    currentConstant finite earlier (compressionStamp_base_mem base n) space order meet
  change CodedGrowthLayer M Space sourceOrder sourceMeet current.data.currentCarrier
    current.data.currentOrder current.data.currentMeet
    (taggedBirth current.data.D current.data.fresh
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth)
      (compressionStamp base n)) (compressionStamp base n) at result
  rw [state.canonical_birth_step pairing unions powers separation hI hSources hReps hG hT code born n]
  simpa only [equal] using result

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

noncomputable def ground_birth_incoming_layer
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    (space : Space base = P0) (order : sourceOrder base = r0) (meet : sourceMeet base = μ0)
    (n : Nat) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (data.fields 0) (data.fields 1)
      (data.fields 2) births.birth (compressionStamp base n) :=
  state.canonical_birth_layer_to_union data pairing unions powers separation
    hI hSources hReps hG hT births.extension births.initial_function (n + 1)
    ((compressionStamp_mem_iff base n (n + 1)).2 (Nat.lt_succ_self n))
    (state.canonical_incoming_birth_layer pairing unions powers separation data
      hI hSources hReps hG hT constant births.extension births.initial_function births.times
      births.initial_bound space order meet n)

noncomputable def ground_birth_prior_layer {t : ZFSet.{u}} (priorTime : t ∈ base ∨ t = base)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet state.data.D state.data.rD state.data.μD old t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (data.fields 0) (data.fields 1)
      (data.fields 2) births.birth t :=
  state.prior_birth_layer_to_union data pairing unions powers separation
    hI hSources hReps hG hT births.extension births.initial_function priorTime layer

omit pairing unions powers separation hI hSources hReps hG hT in
def ground_birth_limit_layer :
    CodedGrowthLayer M Space sourceOrder sourceMeet (data.fields 0) (data.fields 1)
      (data.fields 2) births.birth births.limit :=
  .empty_of_no_birth ⟨data.fields 0, data.ground 0⟩ (fun x _ => births.no_limit_birth x)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
include pairing unions powers separation hI hSources hReps hG hT

section Transfer
variable {base limit old birth : ZFSet.{u}}
variable (code : NatBirthExtensionCode (fun n => (state.data.iterate M I Sources Reps G T n).D)
    (compressionStamp base) old birth)
variable (born : ZFSet.IsFunc state.data.D limit old)
include code born

noncomputable def canonical_birth_layer_to_finite (n k : Nat) (before : n ≤ k)
    {t : ZFSet.{u}} (earlier : t ∈ compressionStamp base n)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T n).D
      (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T k).D
      (state.data.iterate M I Sources Reps G T k).rD
      (state.data.iterate M I Sources Reps G T k).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T k).D birth) t := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have growth := state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT before
  have ground : (state.data.iterate M I Sources Reps G T n).D ∈ M.sets := by
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    rw [← equal]
    exact current.ground.carrier
  exact layer.of_literal_extension separation ground growth.1 growth.2.1 growth.2.2.1
    (NatBirthExtensionCode.restriction_mono mono before)
    (fun _ _ entry => code.earlier_fiber mono born
      (fun _ _ h => compressionStamp_subset base h) n earlier
      (pair_mem_graphRestriction.1 entry).1)

noncomputable def prior_birth_layer_to_finite (k : Nat) {t : ZFSet.{u}}
    (priorTime : t ∈ base ∨ t = base)
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet
      state.data.D state.data.rD state.data.μD old t) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T k).D
      (state.data.iterate M I Sources Reps G T k).rD
      (state.data.iterate M I Sources Reps G T k).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T k).D birth) t := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have zero := code.restriction_zero mono born
  apply state.canonical_birth_layer_to_finite pairing unions powers separation
    hI hSources hReps hG hT code born 0 k (Nat.zero_le k) (compressionStamp_old_mem priorTime 0)
  rw [zero]
  simpa only [RecursiveStateData.iterate_zero] using layer
end Transfer

noncomputable def ground_birth_finite_all_layers
    (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
    {base old : ZFSet.{u}}
    (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    (space : Space base = P0) (order : sourceOrder base = r0) (meet : sourceMeet base = μ0)
    (prior : ∀ t, t ∈ base ∨ t = base →
      CodedGrowthLayer M Space sourceOrder sourceMeet state.data.D state.data.rD state.data.μD old t)
    (n : Nat) (t : ZFSet.{u}) (bound : t ∈ compressionStamp base n ∨ t = compressionStamp base n) :
    CodedGrowthLayer M Space sourceOrder sourceMeet
      (state.data.iterate M I Sources Reps G T (n + 1)).D
      (state.data.iterate M I Sources Reps G T (n + 1)).rD
      (state.data.iterate M I Sources Reps G T (n + 1)).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth) t := by
  have cases : t ∈ base ∨ t = base ∨ ∃ j, j ≤ n ∧ t = compressionStamp base j := by
    rcases bound with before | equal
    · rcases (mem_compressionStamp_iff base t n).1 before with old | equal | ⟨j, before, equal⟩
      · exact Or.inl old
      · exact Or.inr (Or.inl equal)
      · exact Or.inr (Or.inr ⟨j, Nat.le_of_lt before, equal⟩)
    · exact Or.inr (Or.inr ⟨n, Nat.le_refl n, equal⟩)
  apply Classical.choice
  rcases cases with old | equal | ⟨j, before, rfl⟩
  · exact ⟨state.prior_birth_layer_to_finite pairing unions powers separation
      hI hSources hReps hG hT births.extension births.initial_function (n + 1)
      (Or.inl old) (prior t (Or.inl old))⟩
  · exact ⟨state.prior_birth_layer_to_finite pairing unions powers separation
      hI hSources hReps hG hT births.extension births.initial_function (n + 1)
      (Or.inr equal) (prior t (Or.inr equal))⟩
  · exact ⟨state.canonical_birth_layer_to_finite pairing unions powers separation
      hI hSources hReps hG hT births.extension births.initial_function (j + 1) (n + 1)
      (Nat.add_le_add_right before 1)
      ((compressionStamp_mem_iff base j (j + 1)).2 (Nat.lt_succ_self j))
      (state.canonical_incoming_birth_layer pairing unions powers separation data
        hI hSources hReps hG hT constant births.extension births.initial_function births.times
        births.initial_bound space order meet j)⟩

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)

noncomputable def ground_birth_all_layers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    (space : Space base = P0) (order : sourceOrder base = r0) (meet : sourceMeet base = μ0)
    (prior : ∀ t, t ∈ base ∨ t = base →
      CodedGrowthLayer M Space sourceOrder sourceMeet state.data.D state.data.rD state.data.μD old t)
    (t : ZFSet.{u}) (bound : t ∈ births.limit ∨ t = births.limit) :
    CodedGrowthLayer M Space sourceOrder sourceMeet (data.fields 0) (data.fields 1)
      (data.fields 2) births.birth t := by
  apply Classical.choice
  rcases bound with before | rfl
  · rcases (births.times.mem_limit_iff t).1 before with original | same | ⟨n, rfl⟩
    · exact ⟨state.ground_birth_prior_layer data births pairing unions powers separation
        hI hSources hReps hG hT (Or.inl original) (prior t (Or.inl original))⟩
    · exact ⟨state.ground_birth_prior_layer data births pairing unions powers separation
        hI hSources hReps hG hT (Or.inr same) (prior t (Or.inr same))⟩
    · exact ⟨state.ground_birth_incoming_layer data births pairing unions powers separation
        hI hSources hReps hG hT constant space order meet n⟩
  · exact ⟨state.ground_birth_limit_layer data births⟩

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T
    data P0 C Q qlt original)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)

theorem prefix_sources_eq_below {t s : ZFSet.{u}} (oldTime : t ∈ base ∨ t = base)
    (before : s ∈ t) :
    (state.prefixFields data births heights prior).space s = prior.space s ∧ (state.prefixFields data births heights prior).order s = prior.order s ∧
      (state.prefixFields data births heights prior).meetGraph s = prior.meetGraph s := by
  dsimp only [prefixFields]
  exact ⟨compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before,
    compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before,
    compressionPrefixValue_eq_prior_below _ _ _ births.times oldTime before⟩

variable (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
include ordinal hBase

noncomputable def prefix_old_layer {cutoff t : ZFSet.{u}}
    (oldCutoff : cutoff ∈ base ∨ cutoff = base) (bound : t = cutoff ∨ t ∈ cutoff) :
    CodedGrowthLayer M (state.prefixFields data births heights prior).space (state.prefixFields data births heights prior).order (state.prefixFields data births heights prior).meetGraph
      ((state.prefixFields data births heights prior).space cutoff) ((state.prefixFields data births heights prior).order cutoff) ((state.prefixFields data births heights prior).meetGraph cutoff) ((state.prefixFields data births heights prior).birth cutoff) t := by
  have hc : cutoff ∈ T0 := oldCutoff.elim
    (fun member => ordinal.1 base hBase cutoff member) (fun equal => equal.symm ▸ hBase)
  have ht : t ∈ T0 := bound.elim (fun equal => equal.symm ▸ hc)
    (fun before => ordinal.1 cutoff hc t before)
  have oldTime : t ∈ base ∨ t = base := by
    rcases bound with equal | before
    · exact equal.symm ▸ oldCutoff
    · apply Or.inl
      rcases oldCutoff with member | equal
      · exact ordinal.2 base hBase cutoff member t before
      · exact equal ▸ before
  have layer := (prior.layer cutoff hc t ht bound).congr_sources_below
    (fun s hs => (state.prefix_sources_eq_below data births heights prior oldTime hs).1.symm)
    (fun s hs => (state.prefix_sources_eq_below data births heights prior oldTime hs).2.1.symm)
    (fun s hs => (state.prefix_sources_eq_below data births heights prior oldTime hs).2.2.symm)
  have values := state.prefixFields_old data births heights prior oldCutoff
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1] using layer

variable (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
variable (initialMeet : state.data.μD = μ0)
variable (priorSpace : prior.space base = P0) (priorOrder : prior.order base = r0)
variable (priorMeet : prior.meetGraph base = μ0) (priorBirth : prior.birth base = old)
include initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth

noncomputable def prefix_base_layers (t : ZFSet.{u}) (before : t ∈ base ∨ t = base) :
    CodedGrowthLayer M (state.prefixFields data births heights prior).space (state.prefixFields data births heights prior).order (state.prefixFields data births heights prior).meetGraph
      state.data.D state.data.rD state.data.μD old t := by
  have layer := state.prefix_old_layer data births heights prior ordinal hBase
    (Or.inr rfl : base ∈ base ∨ base = base) before.symm
  have values := state.prefixFields_old data births heights prior (Or.inr rfl : base ∈ base ∨ base = base)
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1,
    priorSpace, priorOrder, priorMeet, priorBirth, initialDomain, initialOrder, initialMeet] using layer

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
include pairing unions powers separation hI hSources hReps hG hT constant

noncomputable def prefix_finite_layers (n : Nat) (t : ZFSet.{u})
    (bound : t = compressionStamp base n ∨ t ∈ compressionStamp base n) :
    CodedGrowthLayer M (state.prefixFields data births heights prior).space (state.prefixFields data births heights prior).order (state.prefixFields data births heights prior).meetGraph
      ((state.prefixFields data births heights prior).space (compressionStamp base n)) ((state.prefixFields data births heights prior).order (compressionStamp base n))
      ((state.prefixFields data births heights prior).meetGraph (compressionStamp base n)) ((state.prefixFields data births heights prior).birth (compressionStamp base n)) t := by
  have atBase := state.prefixFields_old data births heights prior (Or.inr rfl : base ∈ base ∨ base = base)
  have layer := state.ground_birth_finite_all_layers pairing unions powers separation
    hI hSources hReps hG hT data births constant
    (atBase.1.trans priorSpace) (atBase.2.1.trans priorOrder) (atBase.2.2.1.trans priorMeet)
    (state.prefix_base_layers data births heights prior ordinal hBase initialDomain initialOrder
      initialMeet priorSpace priorOrder priorMeet priorBirth) n t bound.symm
  have values := state.prefixFields_stamp data births heights prior n
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1] using layer

noncomputable def prefix_union_layers (t : ZFSet.{u})
    (bound : t = births.limit ∨ t ∈ births.limit) :
    CodedGrowthLayer M (state.prefixFields data births heights prior).space (state.prefixFields data births heights prior).order (state.prefixFields data births heights prior).meetGraph
      ((state.prefixFields data births heights prior).space births.limit) ((state.prefixFields data births heights prior).order births.limit)
      ((state.prefixFields data births heights prior).meetGraph births.limit) ((state.prefixFields data births heights prior).birth births.limit) t := by
  have atBase := state.prefixFields_old data births heights prior (Or.inr rfl : base ∈ base ∨ base = base)
  have layer := state.ground_birth_all_layers data births pairing unions powers separation
    hI hSources hReps hG hT constant
    (atBase.1.trans priorSpace) (atBase.2.1.trans priorOrder) (atBase.2.2.1.trans priorMeet)
    (state.prefix_base_layers data births heights prior ordinal hBase initialDomain initialOrder
      initialMeet priorSpace priorOrder priorMeet priorBirth) t bound.symm
  have values := state.prefixFields_limit data births heights prior
  simpa only [values.1, values.2.1, values.2.2.1, values.2.2.2.1] using layer

noncomputable def prefix_all_layers :
    ∀ cutoff ∈ insert births.limit births.limit, ∀ t ∈ insert births.limit births.limit,
      t = cutoff ∨ t ∈ cutoff → CodedGrowthLayer M (state.prefixFields data births heights prior).space (state.prefixFields data births heights prior).order (state.prefixFields data births heights prior).meetGraph
        ((state.prefixFields data births heights prior).space cutoff) ((state.prefixFields data births heights prior).order cutoff) ((state.prefixFields data births heights prior).meetGraph cutoff) ((state.prefixFields data births heights prior).birth cutoff) t := by
  intro cutoff hc t _ bound
  apply Classical.choice
  rcases ZFSet.mem_insert_iff.1 hc with equal | before
  · subst cutoff
    exact ⟨state.prefix_union_layers data births heights prior ordinal hBase initialDomain initialOrder
      initialMeet priorSpace priorOrder priorMeet priorBirth pairing unions powers separation
      hI hSources hReps hG hT constant t bound⟩
  · rcases (births.times.mem_limit_iff cutoff).1 before with oldTime | same | ⟨n, rfl⟩
    · exact ⟨state.prefix_old_layer data births heights prior ordinal hBase (Or.inl oldTime) bound⟩
    · exact ⟨state.prefix_old_layer data births heights prior ordinal hBase (Or.inr same) bound⟩
    · exact ⟨state.prefix_finite_layers data births heights prior ordinal hBase initialDomain initialOrder
        initialMeet priorSpace priorOrder priorMeet priorBirth pairing unions powers separation
        hI hSources hReps hG hT constant n t bound⟩

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
variable (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
variable (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
variable (initialMeet : state.data.μD = μ0)
variable (priorSpace : prior.space base = P0) (priorOrder : prior.order base = r0)
variable (priorMeet : prior.meetGraph base = μ0) (priorBirth : prior.birth base = old)

noncomputable def prefixHistory :
    GroundChronologicalHistory M (insert births.limit births.limit) C Q qlt where
  space := (state.prefixFields data births heights prior).space
  order := (state.prefixFields data births heights prior).order
  meetGraph := (state.prefixFields data births heights prior).meetGraph
  birth := (state.prefixFields data births heights prior).birth
  height := (state.prefixFields data births heights prior).height
  space_mem := fun _ hs => (state.prefixFields_ground data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).1
  order_mem := fun _ hs => (state.prefixFields_ground data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.1
  meet_mem := fun _ hs => (state.prefixFields_ground data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.1
  birth_mem := fun _ hs => (state.prefixFields_ground data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.2.1
  height_mem := fun _ hs => (state.prefixFields_ground data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.2.2
  meet_order := fun _ hs => (state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).1
  birth_function := fun _ hs => (state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.1
  birth_bound := fun _ hs => (state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.1
  old_meet := fun _ hs => (state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.2.1
  strict_height := fun _ hs => (state.prefixFields_stage_laws data births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal hBase hs).2.2.2.2
  layer := state.prefix_all_layers data births heights prior ordinal hBase initialDomain initialOrder
    initialMeet priorSpace priorOrder priorMeet priorBirth pairing unions powers separation
    hI hSources hReps hG hT constant

local notation "history" => state.prefixHistory data births heights prior pairing unions powers separation
  hI hSources hReps hG hT ordinal hBase constant initialDomain initialOrder initialMeet
  priorSpace priorOrder priorMeet priorBirth

theorem prefixHistory_old {s : ZFSet.{u}} (before : s ∈ base ∨ s = base) :
    (history).space s = prior.space s ∧ (history).order s = prior.order s ∧
    (history).meetGraph s = prior.meetGraph s ∧ (history).birth s = prior.birth s ∧
    (history).height s = prior.height s :=
  state.prefixFields_old data births heights prior before

theorem prefixHistory_stamp (n : Nat) :
    (history).space (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).D ∧
    (history).order (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).rD ∧
    (history).meetGraph (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).μD ∧
    (history).birth (compressionStamp base n) =
      graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth ∧
    (history).height (compressionStamp base n) = heights.function.natValue (n + 1) :=
  state.prefixFields_stamp data births heights prior n

theorem prefixHistory_limit :
    (history).space births.limit = data.fields 0 ∧ (history).order births.limit = data.fields 1 ∧
    (history).meetGraph births.limit = data.fields 2 ∧ (history).birth births.limit = births.birth ∧
    (history).height births.limit = heights.height :=
  state.prefixFields_limit data births heights prior

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M N : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T
    data P0 C Q qlt original)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
variable (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
variable (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
variable (initialMeet : state.data.μD = μ0)
variable (priorSpace : prior.space base = P0) (priorOrder : prior.order base = r0)
variable (priorMeet : prior.meetGraph base = μ0) (priorBirth : prior.birth base = old)

include state data births heights prior pairing unions powers separation
  hI hSources hReps hG hT ordinal hBase constant initialDomain initialOrder initialMeet
  priorSpace priorOrder priorMeet priorBirth

theorem prefix_exists_extension_basis
    (includes : M.sets ⊆ N.sets)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets SetFormula.infinity Fin.elim0)
    (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (data.fields 0) (data.fields 1) (data.fields 2) F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ data.fields 1 := by
  let history := state.prefixHistory data births heights prior pairing unions powers separation
    hI hSources hReps hG hT ordinal hBase constant initialDomain initialOrder initialMeet
    priorSpace priorOrder priorMeet priorBirth
  have atLimit := state.prefixHistory_limit data births heights prior pairing unions powers separation
    hI hSources hReps hG hT ordinal hBase constant initialDomain initialOrder initialMeet
    priorSpace priorOrder priorMeet priorBirth
  change history.space births.limit = data.fields 0 ∧ history.order births.limit = data.fields 1 ∧
    history.meetGraph births.limit = data.fields 2 ∧ history.birth births.limit = births.birth ∧
    history.height births.limit = heights.height at atLimit
  have filterAtLimit : MeetFilterCode (history.space births.limit) (history.order births.limit)
      (history.meetGraph births.limit) F := by
    simpa only [atLimit.1, atLimit.2.1, atLimit.2.2.1] using filter
  have basis := history.exists_extension_basis includes pairingN unionsN powersN separationN
    infiniteN choiceN (M.insert_mem pairing unions births.limit_ground births.limit_ground)
    hC hQ (ordinalSetProperty_succ births.times.ordinal) smallQ irreflexive
    (ZFSet.mem_insert births.limit births.limit) hF filterAtLimit
  simpa only [atLimit.2.1] using basis

end PartitionPilot.Forcing.GroundCompressionState

end OAI
