import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialCompressionPrefix

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem finiteWords_subset_powerset (A : ZFSet.{u}) :
    M.finiteWords A ⊆ ZFSet.powerset (ZFSet.prod ZFSet.omega A) := by
  intro f hf
  have relation := (ZFSet.mem_sep.1 hf).1
  exact ZFSet.mem_powerset.2 ((M.mem_groundRelations ZFSet.omega A f).1 relation).2

theorem finiteWords_rank_le (A : ZFSet.{u}) :
    ZFSet.rank (M.finiteWords A) ≤ Order.succ (ZFSet.rank (ZFSet.prod ZFSet.omega A)) := by
  have bound := ZFSet.rank_mono (M.finiteWords_subset_powerset A)
  rwa [ZFSet.rank_powerset] at bound

theorem finiteWords_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) {A : ZFSet.{u}}
    (omega : ZFSet.rank ZFSet.omega < o) (alphabet : ZFSet.rank A < o) :
    ZFSet.rank (M.finiteWords A) < o :=
  (M.finiteWords_rank_le A).trans_lt (limit.succ_lt (rank_product_lt limit omega alphabet))

end TransitiveGround

section
open SetFormula
universe u

noncomputable def externalRequestAlphabet (I P G r μ A : ZFSet.{u}) : ZFSet.{u} :=
  externalGeneratorAlphabet G (externalChildLetters I P (externalRectangles P G r μ A))

structure GroundExternalWordData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P r μ A : ZFSet.{u})
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ) : Prop where
  rectangles_ground : externalRectangles P G r μ A ∈ M.sets
  requests_ground : externalRequestCarrier I P (externalRectangles P G r μ A) ∈ M.sets
  letters_ground : externalChildLetters I P (externalRectangles P G r μ A) ∈ M.sets
  kinds_ground : externalRequestKinds I P (externalRectangles P G r μ A) ∈ M.sets
  payloads_ground : externalRequestPayloads I P (externalRectangles P G r μ A) ∈ M.sets
  kinds_function : FunctionGraphOn (externalRequestCarrier I P (externalRectangles P G r μ A))
    (externalRequestKinds I P (externalRectangles P G r μ A))
  payloads_function : FunctionGraphOn (externalRequestCarrier I P (externalRectangles P G r μ A))
    (externalRequestPayloads I P (externalRectangles P G r μ A))
  maps_ground : completion.externalMaps ∈ M.sets
  caps_ground : completion.externalCaps ∈ M.sets
  maps_function : FunctionGraphOn (ZFSet.prod {natSetCode 0} I) completion.externalMaps
  caps_function : ZFSet.IsFunc (ZFSet.prod {natSetCode 0} I)
    (completion.algebra.union.fields 0) completion.externalCaps
  alphabet_ground : externalRequestAlphabet I P G r μ A ∈ M.sets
  words_ground : M.finiteWords (externalRequestAlphabet I P G r μ A) ∈ M.sets
  append_ground : M.finiteWordAppendGraph (externalRequestAlphabet I P G r μ A) ∈ M.sets
  reverse_ground : M.finiteWordReverseGraph (externalRequestAlphabet I P G r μ A) ∈ M.sets
  length_ground : M.finiteWordLengthGraph (externalRequestAlphabet I P G r μ A) ∈ M.sets
  append_function : ZFSet.IsFunc
    (ZFSet.prod (M.finiteWords (externalRequestAlphabet I P G r μ A))
      (M.finiteWords (externalRequestAlphabet I P G r μ A)))
    (M.finiteWords (externalRequestAlphabet I P G r μ A))
    (M.finiteWordAppendGraph (externalRequestAlphabet I P G r μ A))
  reverse_function : ZFSet.IsFunc (M.finiteWords (externalRequestAlphabet I P G r μ A))
    (M.finiteWords (externalRequestAlphabet I P G r μ A))
    (M.finiteWordReverseGraph (externalRequestAlphabet I P G r μ A))
  length_function : ZFSet.IsFunc (M.finiteWords (externalRequestAlphabet I P G r μ A)) ZFSet.omega
    (M.finiteWordLengthGraph (externalRequestAlphabet I P G r μ A))

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P r μ A : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

theorem externalWordData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) :
    GroundExternalWordData M initial I Sources Reps G m one T τ P r μ A completion := by
  obtain ⟨rectangles, requests, letters, kinds, payloads, kindFunction, payloadFunction⟩ :=
    M.groundExternalRequestData pairing unions powers separation hI hP hG hr hμ hA
  obtain ⟨maps, caps, mapFunction, capFunction⟩ :=
    completion.external_fields_ground pairing unions powers separation hI
  have alphabet : externalRequestAlphabet I P G r μ A ∈ M.sets :=
    M.externalGeneratorAlphabet_mem pairing unions powers separation hG letters
  exact {
    rectangles_ground := rectangles
    requests_ground := requests
    letters_ground := letters
    kinds_ground := kinds
    payloads_ground := payloads
    kinds_function := kindFunction
    payloads_function := payloadFunction
    maps_ground := maps
    caps_ground := caps
    maps_function := mapFunction
    caps_function := capFunction
    alphabet_ground := alphabet
    words_ground := M.finiteWords_mem pairing unions powers separation infinite alphabet
    append_ground := M.finiteWordAppendGraph_mem pairing unions powers separation infinite alphabet
    reverse_ground := M.finiteWordReverseGraph_mem pairing unions powers separation infinite alphabet
    length_ground := M.finiteWordLengthGraph_mem pairing unions powers separation infinite alphabet
    append_function := M.finiteWordAppendGraph_function pairing unions separation infinite alphabet
    reverse_function := M.finiteWordReverseGraph_function pairing unions separation infinite alphabet
    length_function := M.finiteWordLengthGraph_function _ }

end GroundCompressionCompletion

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialExternalWordData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
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
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalWordData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, compression⟩ :=
    M.exists_groundInitialCompressionPrefix pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels group action meet hτ top hC hD hrD hc hOriginal
      originalCode columns target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  obtain ⟨compression⟩ := compression
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, compression,
    compression.born.profiled.heighted.completion.externalWordData
      pairing unions powers separation infinite hI hP hG hr hμ hA⟩

theorem exists_groundInitialExternalGroup
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
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalWordData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalGroupData M G (externalChildLetters I P (externalRectangles P G r μ A))
            m inv one := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, compression, words⟩ :=
    M.exists_groundInitialExternalWordData pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels group action meet hτ top hC hD hrD hc hOriginal
      originalCode columns target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, compression, words,
    M.externalGroupData pairing unions powers separation infinite group hG words.letters_ground hm hInv⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
