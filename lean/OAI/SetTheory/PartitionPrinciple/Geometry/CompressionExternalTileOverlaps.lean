import OAI.SetTheory.PartitionPrinciple.Definability.CodedRangeCompletion
import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionUnionBaseFilling
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalRequestOverlaps
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCompressionBirthData
import OAI.SetTheory.PartitionPrinciple.Transfinite.SmallTileHeightInputs

namespace OAI


namespace PartitionPilot.Forcing
universe u

structure GroundCompressionCompletion (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ : ZFSet.{u}) where
  algebra : GroundCompressionAlgebra M initial I Sources Reps G m one T
  bases_ground : algebra.bases ∈ M.sets
  caps_ground : algebra.caps τ ∈ M.sets
  bases_function : ZFSet.IsFunc I (algebra.union.fields 0) algebra.bases
  caps_function : ZFSet.IsFunc I (algebra.union.fields 0) (algebra.caps τ)
  top_mem : τ ∈ algebra.union.fields 0
  top : ∀ x ∈ algebra.union.fields 0, ZFSet.pair x τ ∈ algebra.union.fields 1
  range : ∀ i f k x, ZFSet.pair i f ∈ algebra.maps → ZFSet.pair i k ∈ algebra.caps τ →
    ((∃ y ∈ algebra.union.fields 0, ZFSet.pair y x ∈ f) ↔
      x ∈ algebra.union.fields 0 ∧ ZFSet.pair x k ∈ algebra.union.fields 1)
  equivariant : ∀ g i j f h x y z,
    ZFSet.pair (ZFSet.pair g i) j ∈ T →
    ZFSet.pair i f ∈ algebra.maps → ZFSet.pair j h ∈ algebra.maps →
    ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ h →
      ZFSet.pair (ZFSet.pair g y) z ∈ algebra.union.fields 12
  source_agreement : ∀ i f a g x y,
    ZFSet.pair i f ∈ algebra.maps → ZFSet.pair i a ∈ Sources → ZFSet.pair i g ∈ Reps →
    ZFSet.pair x a ∈ algebra.union.fields 1 →
      (ZFSet.pair x y ∈ f ↔ ZFSet.pair (ZFSet.pair g x) y ∈ algebra.union.fields 12)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}

namespace GroundCompressionUnionData

theorem fields_unique
    (first second : GroundCompressionUnionData M initial I Sources Reps G m one T) :
    first.fields = second.fields := by
  funext j
  apply ZFSet.ext
  intro z
  exact (first.fieldUnion j z).trans (second.fieldUnion j z).symm

theorem unique
    (first second : GroundCompressionUnionData M initial I Sources Reps G m one T) :
    first = second := by
  have equal := first.fields_unique second
  cases first
  cases second
  cases equal
  rfl

end GroundCompressionUnionData

namespace GroundCompressionAlgebra

theorem unique
    (first second : GroundCompressionAlgebra M initial I Sources Reps G m one T) :
    first = second := by
  have sameUnion := first.union.unique second.union
  have sameMaps : first.maps = second.maps := by
    rw [first.maps_eq_sections, second.maps_eq_sections, sameUnion]
  cases first
  cases second
  cases sameUnion
  cases sameMaps
  rfl

end GroundCompressionAlgebra

namespace GroundCompressionCompletion

theorem unique
    (first second : GroundCompressionCompletion M initial I Sources Reps G m one T τ) :
    first = second := by
  have equal := first.algebra.unique second.algebra
  cases first
  cases second
  cases equal
  rfl

end GroundCompressionCompletion
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization Compression Compression.RecursiveMaps
universe u

private theorem externalRectangleParameters_exists {P G r μ A : ZFSet.{u}}
    (z : SetMembers (externalRectangles P G r μ A)) :
    ∃ v : ZFSet.{u} × ZFSet.{u} × ZFSet.{u} × ZFSet.{u} × ZFSet.{u},
    SetMembers.raw z = externalRectangleCode v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 ∧
      ExternalRectangleCode P G r μ A v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 := by
  obtain ⟨c, b, d, g, h, equal, code⟩ :=
    (mem_externalRectangles P G r μ A _).1 (SetMembers.raw_mem z)
  exact ⟨(c, b, d, g, h), equal, code⟩

noncomputable def externalRectangleParameters {P G r μ A : ZFSet.{u}}
    (z : SetMembers (externalRectangles P G r μ A)) :
    ZFSet.{u} × ZFSet.{u} × ZFSet.{u} × ZFSet.{u} × ZFSet.{u} :=
  Classical.choose (externalRectangleParameters_exists z)

theorem externalRectangleParameters_spec {P G r μ A : ZFSet.{u}}
    (z : SetMembers (externalRectangles P G r μ A)) :
    let v := externalRectangleParameters z
    SetMembers.raw z = externalRectangleCode v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 ∧
      ExternalRectangleCode P G r μ A v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 :=
  Classical.choose_spec (externalRectangleParameters_exists z)

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalMap (i : SetMembers I) : ZFSet.{u} :=
  completion.algebra.function.value ⟨SetMembers.raw i, SetMembers.raw_mem i⟩

theorem externalMap_entry (i : SetMembers I) :
    ZFSet.pair (SetMembers.raw i) (completion.externalMap i) ∈ completion.algebra.maps :=
  completion.algebra.function.value_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩

noncomputable def externalCap (i : SetMembers I) : SetMembers (completion.algebra.union.fields 0) :=
  (SetMembers.presentation I).decodeFunction (SetMembers.presentation (completion.algebra.union.fields 0))
    (completion.algebra.caps τ) completion.caps_function i

theorem externalCap_entry (i : SetMembers I) :
    ZFSet.pair (SetMembers.raw i) (SetMembers.raw (completion.externalCap i)) ∈ completion.algebra.caps τ :=
  (SetMembers.presentation I).decodeFunction_mem (SetMembers.presentation (completion.algebra.union.fields 0))
    (completion.algebra.caps τ) completion.caps_function i

noncomputable def externalCopy (i : SetMembers I) :
    MeetIso completion.algebra.union.meet.toSmallMeetOrder
      (Attachment.idealOrder completion.algebra.union.meet.toSmallMeetOrder (completion.externalCap i)) :=
  smallCompressionTileIso completion.algebra.union.meet
    (completion.algebra.embedding _ _ (completion.externalMap_entry i)) (completion.externalCap i)
    (fun x => completion.range _ _ _ x (completion.externalMap_entry i) (completion.externalCap_entry i))

theorem externalCopy_entry (i : SetMembers I) (x : SetMembers (completion.algebra.union.fields 0)) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw ((completion.externalCopy i).toFun x).val) ∈
      completion.externalMap i :=
  smallCompressionTileIso_entry _ _ _ _ x

variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

noncomputable def externalRectangle
    (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) :
    ActionRectangle completion.algebra.union.meet.toSmallMeetOrder
      (completion.algebra.union.action.toSmallMeetIso group completion.algebra.union.meet) :=
  (((externalRectangleParameters_spec z).2).lift_compression compression oldAction).toSmallActionRectangle
    group completion.algebra.union.action completion.algebra.union.meet

theorem externalRectangle_fields (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) :
    let rectangle := completion.externalRectangle group oldAction compression z
    externalRectangleCode (SetMembers.raw rectangle.C) (SetMembers.raw rectangle.B)
      (SetMembers.raw rectangle.D) (SetMembers.raw rectangle.first) (SetMembers.raw rectangle.second) =
        SetMembers.raw z := by
  have fields := (((externalRectangleParameters_spec z).2).lift_compression compression oldAction).toSmallActionRectangle_fields
    group completion.algebra.union.action completion.algebra.union.meet
  change externalRectangleCode _ _ _ _ _ = _
  dsimp only [externalRectangle]
  rw [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2]
  exact (externalRectangleParameters_spec z).1.symm

noncomputable def externalRequest :
    ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0) →
      TileRequests.Request completion.algebra.union.meet.toSmallMeetOrder
  | .inl i => .compression (completion.externalCap i) (completion.externalCopy i)
  | .inr (.inl x) => .separation (SetMembers.ofMem (SetMembers.raw x)
      (compression.subset (SetMembers.raw_mem x)))
  | .inr (.inr z) => .rectangle ((completion.externalRectangle group oldAction compression z).toInput
      (SetMembers.ofMem τ completion.top_mem) (fun x => by
        simpa only [MeetOrderCode.toSmallMeetOrder, SetMembers.raw_ofMem] using
          completion.top _ (SetMembers.raw_mem x)))

noncomputable def externalFamily : TileRequests.Family completion.algebra.union.meet.toSmallMeetOrder
    (ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) where
  top := SetMembers.ofMem τ completion.top_mem
  greatest x := by
    simpa only [MeetOrderCode.toSmallMeetOrder, SetMembers.raw_ofMem] using
      completion.top _ (SetMembers.raw_mem x)
  request := completion.externalRequest group oldAction compression

theorem externalFamily_child (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) :
    (completion.externalFamily group oldAction compression).Child r = ExternalRequestChild r := by
  rcases r with i | (x | z) <;> rfl

noncomputable def externalFamilyLetterEquiv :
    (completion.externalFamily group oldAction compression).Letters ≃
      Sigma (@ExternalRequestChild I P0 (externalRectangles P0 G r0 μ0 A0)) where
  toFun x := ⟨x.1, cast (completion.externalFamily_child group oldAction compression x.1) x.2⟩
  invFun x := ⟨x.1, cast (completion.externalFamily_child group oldAction compression x.1).symm x.2⟩
  left_inv x := by cases x; simp; rfl
  right_inv x := by cases x; simp

noncomputable def externalFamilyLetterPresentation :
    Presentation (completion.externalFamily group oldAction compression).Letters where
  carrier := externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
  encode x := externalRequestLetterCode (completion.externalFamilyLetterEquiv group oldAction compression x)
  injective := (externalRequestLetterCode_injective _ _ _).comp
    (completion.externalFamilyLetterEquiv group oldAction compression).injective
  mem_carrier z := by
    have member : z ∈ externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0) ↔
        ∃ x : Sigma (@ExternalRequestChild I P0 (externalRectangles P0 G r0 μ0 A0)),
          externalRequestLetterCode x = z :=
      (externalRequestLetterPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).mem_carrier z
    rw [member]
    exact ⟨fun ⟨x, hx⟩ => ⟨(completion.externalFamilyLetterEquiv group oldAction compression).symm x, by
      simpa only [Equiv.apply_symm_apply] using hx⟩, fun ⟨x, hx⟩ =>
      ⟨completion.externalFamilyLetterEquiv group oldAction compression x, hx⟩⟩

theorem externalFamilyLetterPresentation_carrier :
    (completion.externalFamilyLetterPresentation group oldAction compression).carrier =
      externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0) := rfl

end GroundCompressionCompletion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def externalCompressionField (I V F : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (ZFSet.prod {natSetCode 0} I) I V (productSecond {natSetCode 0} I) F

private theorem compressionProjection_entry_iff (I i j : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 0) i) j ∈ productSecond {natSetCode 0} I ↔
      i ∈ I ∧ j = i := by
  rw [mem_productSecond]
  constructor
  · rintro ⟨t, ht, x, hx, equal⟩
    have sameI := (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 equal).1).2
    exact ⟨sameI.symm ▸ hx, (ZFSet.pair_inj.1 equal).2.trans sameI.symm⟩
  · rintro ⟨hi, equal⟩
    subst j
    exact ⟨natSetCode 0, ZFSet.mem_singleton.2 rfl, i, hi, rfl⟩

theorem externalCompressionField_entry_iff {I V F i y : ZFSet.{u}}
    (function : ZFSet.IsFunc I V F) :
    ZFSet.pair (ZFSet.pair (natSetCode 0) i) y ∈ externalCompressionField I V F ↔
      ZFSet.pair i y ∈ F := by
  rw [externalCompressionField, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, j, _, projection, entry⟩
    have same := (compressionProjection_entry_iff I i j).1 projection
    exact same.2 ▸ entry
  · intro entry
    have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, bounds.1⟩, bounds.2,
      i, bounds.1, (compressionProjection_entry_iff I i i).2 ⟨bounds.1, rfl⟩, entry⟩

theorem externalCompressionField_function {I V F : ZFSet.{u}}
    (function : ZFSet.IsFunc I V F) :
    ZFSet.IsFunc (ZFSet.prod {natSetCode 0} I) V (externalCompressionField I V F) :=
  relationCompose_function_of_subset (productSecond_function {natSetCode 0} I) function (fun _ h => h)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalCompressionField_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I V F : ZFSet.{u}} (hI : I ∈ M.sets) (hV : V ∈ M.sets) (hF : F ∈ M.sets) :
    externalCompressionField I V F ∈ M.sets := by
  have zero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨I, hI⟩
  have single : ({natSetCode 0} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing zero zero
  exact M.relationCompose_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation single hI) hI hV
    (M.productSecond_mem pairing unions powers separation single hI) hF

end TransitiveGround

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalMaps : ZFSet.{u} :=
  externalCompressionField I completion.algebra.maps.sUnion.sUnion completion.algebra.maps

noncomputable def externalCaps : ZFSet.{u} :=
  externalCompressionField I (completion.algebra.union.fields 0) (completion.algebra.caps τ)

theorem external_fields_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) :
    completion.externalMaps ∈ M.sets ∧ completion.externalCaps ∈ M.sets ∧
      FunctionGraphOn (ZFSet.prod {natSetCode 0} I) completion.externalMaps ∧
      ZFSet.IsFunc (ZFSet.prod {natSetCode 0} I) (completion.algebra.union.fields 0) completion.externalCaps :=
  ⟨M.externalCompressionField_mem pairing unions powers separation hI
      (M.union_mem unions (M.union_mem unions completion.algebra.ground)) completion.algebra.ground,
    M.externalCompressionField_mem pairing unions powers separation hI
      (completion.algebra.union.ground 0) completion.caps_ground,
    ⟨_, externalCompressionField_function completion.algebra.function.to_isFunc⟩,
    externalCompressionField_function completion.caps_function⟩

theorem external_fields_entries (i f k : ZFSet.{u}) :
    (ZFSet.pair (ZFSet.pair (natSetCode 0) i) f ∈ completion.externalMaps ↔
      ZFSet.pair i f ∈ completion.algebra.maps) ∧
    (ZFSet.pair (ZFSet.pair (natSetCode 0) i) k ∈ completion.externalCaps ↔
      ZFSet.pair i k ∈ completion.algebra.caps τ) :=
  ⟨externalCompressionField_entry_iff completion.algebra.function.to_isFunc,
    externalCompressionField_entry_iff completion.caps_function⟩

theorem external_fields_range {i f k : ZFSet.{u}}
    (map : ZFSet.pair (ZFSet.pair (natSetCode 0) i) f ∈ completion.externalMaps)
    (cap : ZFSet.pair (ZFSet.pair (natSetCode 0) i) k ∈ completion.externalCaps) :
    MeetEmbeddingCode (completion.algebra.union.fields 0) (completion.algebra.union.fields 0)
      (completion.algebra.union.fields 1) (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 2) (completion.algebra.union.fields 2) f ∧
      ∀ x, ((∃ y ∈ completion.algebra.union.fields 0, ZFSet.pair y x ∈ f) ↔
        x ∈ completion.algebra.union.fields 0 ∧ ZFSet.pair x k ∈ completion.algebra.union.fields 1) := by
  have originalMap := ((completion.external_fields_entries i f k).1).1 map
  have originalCap := ((completion.external_fields_entries i f k).2).1 cap
  exact ⟨completion.algebra.embedding i f originalMap,
    fun x => completion.range i f k x originalMap originalCap⟩

end GroundCompressionCompletion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)

theorem completion_of_accounting
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (accounting : CompressionRangeAccounting P0 I (algebra.union.fields 0)
      (algebra.union.fields 1) (algebra.union.fields 2) algebra.maps algebra.bases (algebra.caps τ)) :
    Nonempty (GroundCompressionCompletion M state.data I Sources Reps G m one T τ) := by
  obtain ⟨basesGround, capsGround⟩ := state.union_markings_ground algebra
    pairing unions powers separation hI hSources
  refine ⟨{
    algebra := algebra
    bases_ground := basesGround
    caps_ground := capsGround
    bases_function := state.union_bases_function algebra
    caps_function := state.union_caps_function algebra
    top_mem := state.union_original_subset algebra.union seed.top_mem
    top := fun _ hx => state.union_top algebra pairing unions powers separation
      hI hSources hReps hG hT hx
    range := ?_
    equivariant := ?_
    source_agreement := ?_
  }⟩
  · intro i f k x indexed capped
    apply accounting.range_iff algebra.union.meet algebra.function algebra.embedding
      (state.union_bases_function algebra) (state.union_caps_function algebra) ?_
      (algebra.function.pair_source indexed) indexed capped
    intro j _ graph cap map capEntry y z image
    exact state.union_map_range_below_cap algebra pairing unions powers separation
      hI hSources hReps hG hT map ((state.union_cap_entry_iff algebra map).1 capEntry) image
  · intro g i j f h x y z transport firstMap secondMap first second
    exact state.union_map_equivariant algebra pairing unions powers separation
      hI hSources hReps hG hT transport firstMap secondMap first second
  · intro i f a g x y map source representative below
    exact state.union_map_agrees_on_source algebra pairing unions powers separation
      hI hSources hReps hG hT map source representative below

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
universe u

structure GroundHeightedCompression (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 C D rD original : ZFSet.{u}) where
  completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ
  heights : GroundCompressionHeightData M initial I Sources Reps G m one T
    completion.algebra.union P0 C D rD original

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

theorem externalFamily_compression_letter (i : SetMembers I) :
    (completion.externalFamilyLetterPresentation group oldAction compression).encode ⟨.inl i, ⟨()⟩⟩ =
      ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0) := rfl

theorem externalFamily_separation_letter (x : SetMembers P0) :
    (completion.externalFamilyLetterPresentation group oldAction compression).encode ⟨.inr (.inl x), ⟨()⟩⟩ =
      ZFSet.pair (ZFSet.pair (natSetCode 1) (SetMembers.raw x)) (natSetCode 0) := rfl

theorem externalFamily_rectangle_letter (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (b : Bool) :
    (completion.externalFamilyLetterPresentation group oldAction compression).encode ⟨.inr (.inr z), ⟨b⟩⟩ =
      ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (externalSignCode b) := rfl

noncomputable def externalFamilyVertexCode
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) :
    Option ((completion.externalFamily group oldAction compression).Child r) → ZFSet.{u}
  | none => natSetCode 0
  | some child => insert
      (externalRequestChildCode r (cast (completion.externalFamily_child group oldAction compression r) child))
      (externalRequestChildCode r (cast (completion.externalFamily_child group oldAction compression r) child))

theorem externalFamilyVertexCode_root
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) :
    completion.externalFamilyVertexCode group oldAction compression r none = natSetCode 0 := rfl

theorem externalFamilyVertexCode_compression (i : SetMembers I) :
    completion.externalFamilyVertexCode group oldAction compression (.inl i) (some ⟨()⟩) = natSetCode 1 := rfl

theorem externalFamilyVertexCode_separation (x : SetMembers P0) :
    completion.externalFamilyVertexCode group oldAction compression (.inr (.inl x)) (some ⟨()⟩) = natSetCode 1 := rfl

theorem externalFamilyVertexCode_rectangle (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (b : Bool) :
    completion.externalFamilyVertexCode group oldAction compression (.inr (.inr z)) (some ⟨b⟩) =
      natSetCode (if b then 2 else 1) := by cases b <;> rfl

end PartitionPilot.Forcing.GroundCompressionCompletion



namespace PartitionPilot.Forcing
universe u

structure GroundProfiledCompression (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 C D rD original Targets Separators Filters : ZFSet.{u}) where
  heighted : GroundHeightedCompression M initial I Sources Reps G m one T τ P0 C D rD original
  profiles : CodedCompressionProfiles
    (heighted.completion.algebra.union.fields 0) (heighted.completion.algebra.union.fields 1)
    (heighted.completion.algebra.union.fields 2) (heighted.completion.algebra.caps τ)
    Targets Separators Filters

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

theorem externalMaps_compression_iff (i : SetMembers I) (f : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) f ∈ completion.externalMaps ↔
      f = completion.externalMap i := by
  rw [(completion.external_fields_entries (SetMembers.raw i) f ∅).1]
  exact ⟨fun entry => (completion.algebra.function.unique entry (completion.externalMap_entry i)),
    fun equal => equal.symm ▸ completion.externalMap_entry i⟩

theorem externalMaps_tag {tag x f : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair tag x) f ∈ completion.externalMaps) : tag = natSetCode 0 := by
  have function := externalCompressionField_function completion.algebra.function.to_isFunc
  have domain := (ZFSet.pair_mem_prod.1 (function.1 entry)).1
  exact ZFSet.mem_singleton.1 (ZFSet.pair_mem_prod.1 domain).1

theorem externalMap_external_bound (i : SetMembers I) : completion.externalMap i ∈ completion.externalMaps.sUnion.sUnion :=
  pair_second_mem_doubleUnion ((completion.externalMaps_compression_iff i _).2 rfl)

theorem externalOverlapForward_compression {P Rectangles r A : ZFSet.{u}}
    (task : SetMembers I) (i x j y : ZFSet.{u}) :
    ExternalRequestOverlapForward P G Rectangles completion.externalMaps completion.externalMaps.sUnion.sUnion r A
      (natSetCode 0) (natSetCode 1) (natSetCode 2)
      (ZFSet.pair (natSetCode 0) (SetMembers.raw task)) i x j y ↔
      i = natSetCode 0 ∧ j = natSetCode 1 ∧ ZFSet.pair y x ∈ completion.externalMap task := by
  simp only [ExternalRequestOverlapForward, ZFSet.pair_inj, natSetCode_injective.eq_iff,
    completion.externalMaps_compression_iff]
  simp
  intro _ _ _
  simpa only [ZFSet.mem_sUnion] using completion.externalMap_external_bound task

theorem externalOverlapForward_separation {P Rectangles r A : ZFSet.{u}}
    (point : SetMembers P) (i x j y : ZFSet.{u}) :
    ExternalRequestOverlapForward P G Rectangles completion.externalMaps completion.externalMaps.sUnion.sUnion r A
      (natSetCode 0) (natSetCode 1) (natSetCode 2)
      (ZFSet.pair (natSetCode 1) (SetMembers.raw point)) i x j y ↔
      i = natSetCode 0 ∧ j = natSetCode 1 ∧ x = y ∧ ZFSet.pair x (SetMembers.raw point) ∈ r := by
  have empty : ∀ f, ZFSet.pair (ZFSet.pair (natSetCode 1) (SetMembers.raw point)) f ∉ completion.externalMaps := by
    intro f entry
    have equal := natSetCode_injective (completion.externalMaps_tag entry)
    exact Nat.noConfusion equal
  simp only [ExternalRequestOverlapForward, ZFSet.pair_inj, natSetCode_injective.eq_iff]
  simp [empty, SetMembers.raw_mem point]

theorem externalOverlapForward_rectangle {P r0 μ0 A0 r A : ZFSet.{u}}
    (z : SetMembers (externalRectangles P G r0 μ0 A0)) (i x j y : ZFSet.{u}) :
    let v := externalRectangleParameters z
    ExternalRequestOverlapForward P G (externalRectangles P G r0 μ0 A0)
      completion.externalMaps completion.externalMaps.sUnion.sUnion r A
      (natSetCode 0) (natSetCode 1) (natSetCode 2)
      (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) i x j y ↔
      (i = natSetCode 0 ∧ j = natSetCode 1 ∧ ZFSet.pair y v.1 ∈ r ∧ ZFSet.pair (ZFSet.pair v.2.2.2.1 y) x ∈ A) ∨
      (i = natSetCode 0 ∧ j = natSetCode 2 ∧ ZFSet.pair y v.1 ∈ r ∧ ZFSet.pair (ZFSet.pair v.2.2.2.2 y) x ∈ A) ∨
      (i = natSetCode 1 ∧ j = natSetCode 2 ∧ x = y ∧ ZFSet.pair x v.2.1 ∈ r) := by
  have empty : ∀ f, ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) f ∉ completion.externalMaps := by
    intro f entry
    have equal := natSetCode_injective (completion.externalMaps_tag entry)
    exact Nat.noConfusion equal
  dsimp only
  rw [ExternalRequestOverlapForward]
  constructor
  · rintro (⟨_, _, f, _, entry, _⟩ | ⟨_, _, w, _, equal, _⟩ | rect)
    · exact False.elim (empty f entry)
    · exact False.elim (by have eq := natSetCode_injective (ZFSet.pair_inj.1 equal).1; omega)
    · obtain ⟨t, _, c, _, b, _, d, _, g, _, h, _, qt, tuple, overlap⟩ := rect
      have equalT := (ZFSet.pair_inj.1 qt).2
      have coords := externalRectangleCode_inj.1
        (tuple.symm.trans (equalT.symm.trans (externalRectangleParameters_spec z).1))
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := coords
      exact overlap
  · intro overlap
    have params := externalRectangleParameters_spec z
    exact Or.inr (Or.inr ⟨SetMembers.raw z, SetMembers.raw_mem z,
      _, params.2.1, _, params.2.2.1, _, params.2.2.2.1, _, params.2.2.2.2.1, _, params.2.2.2.2.2.1,
      rfl, params.1, overlap⟩)

end GroundCompressionCompletion
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure GroundBornCompression (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 C D rD original Targets Separators Filters base old : ZFSet.{u}) where
  profiled : GroundProfiledCompression M initial I Sources Reps G m one T τ P0 C D rD original
    Targets Separators Filters
  births : GroundCompressionBirthData M initial I Sources Reps G m one T
    profiled.heighted.completion.algebra.union base old

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization Compression Compression.RecursiveMaps
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

local notation "p" => completion.algebra.union.meet.toSmallMeetOrder
local notation "f" => completion.externalFamily group oldAction compression
local notation "U" => completion.algebra.union.fields 0
local notation "ru" => completion.algebra.union.fields 1
local notation "au" => completion.algebra.union.fields 12

theorem externalFamily_diagonal_iff
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
    (i : Option ((f).Child r)) (x y : SetMembers U) :
    ((f).flatVertex r i).toFun x = ((f).flatVertex r i).toFun y ↔ SetMembers.raw x = SetMembers.raw y :=
  ⟨fun same => congrArg SetMembers.raw (embedding_injective ((f).flatVertex r i).toMeetEmbedding same),
    fun same => congrArg ((f).flatVertex r i).toFun (SetMembers.raw_injective U same)⟩

theorem externalFamily_compression_overlap (task : SetMembers I) (x y : SetMembers U) :
    ((f).flatVertex (.inl task) none).toFun x = ((f).flatVertex (.inl task) (some ⟨()⟩)).toFun y ↔
      ZFSet.pair (SetMembers.raw y) (SetMembers.raw x) ∈ completion.externalMap task := by
  change (BinaryTiles.compression p (f).top (completion.externalCap task) (f).greatest
    (completion.externalCopy task)).left.toFun x =
    (BinaryTiles.compression p (f).top (completion.externalCap task) (f).greatest
      (completion.externalCopy task)).right.toFun y ↔ _
  rw [BinaryTiles.compression_identification]
  change Sum.inl x = Sum.inl ((completion.externalCopy task).toFun y).val ↔ _
  rw [Sum.inl.injEq, eq_comm]
  exact (completion.algebra.embedding _ _ (completion.externalMap_entry task)).smallValue_eq_iff y x

theorem externalFamily_separation_overlap (point : SetMembers P0) (x y : SetMembers U) :
    ((f).flatVertex (.inr (.inl point)) none).toFun x =
      ((f).flatVertex (.inr (.inl point)) (some ⟨()⟩)).toFun y ↔
      SetMembers.raw x = SetMembers.raw y ∧ ZFSet.pair (SetMembers.raw x) (SetMembers.raw point) ∈ ru := by
  let W := SetMembers.ofMem (SetMembers.raw point) (compression.subset (SetMembers.raw_mem point))
  change (BinaryTiles.separation p W).left.toFun x = (BinaryTiles.separation p W).right.toFun y ↔ _
  rw [eq_comm, (BinaryTiles.separation p W).overlap_exact]
  change (∃ _ : ZFSet.pair (SetMembers.raw y) (SetMembers.raw W) ∈ ru, y = x) ↔ _
  simp only [W, SetMembers.raw_ofMem]
  constructor
  · rintro ⟨lower, rfl⟩
    exact ⟨rfl, lower⟩
  · rintro ⟨same, lower⟩
    have equal := SetMembers.raw_injective U same
    exact ⟨by simpa only [← equal] using lower, equal.symm⟩

theorem externalFamily_rectangle_first_overlap
    (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (x y : SetMembers U) :
    let v := externalRectangleParameters z
    ((f).flatVertex (.inr (.inr z)) none).toFun x =
      ((f).flatVertex (.inr (.inr z)) (some ⟨false⟩)).toFun y ↔
      ZFSet.pair (SetMembers.raw y) v.1 ∈ ru ∧
        ZFSet.pair (ZFSet.pair v.2.2.2.1 (SetMembers.raw y)) (SetMembers.raw x) ∈ au := by
  let rect := completion.externalRectangle group oldAction compression z
  let tile := rect.toInput (f).top (f).greatest
  change tile.root.toFun x = tile.first.toFun y ↔ _
  rw [eq_comm, tile.first_root_intersection]
  have fields := (((externalRectangleParameters_spec z).2).lift_compression compression oldAction).toSmallActionRectangle_fields
    group completion.algebra.union.action completion.algebra.union.meet
  have code : (p).le y tile.C ↔ ZFSet.pair (SetMembers.raw y) (externalRectangleParameters z).1 ∈ ru := by
    change ZFSet.pair (SetMembers.raw y) (SetMembers.raw rect.C) ∈ ru ↔ _
    rw [show SetMembers.raw rect.C = _ from fields.1]
  have actor : tile.g1.toFun y = x ↔
      ZFSet.pair (ZFSet.pair (externalRectangleParameters z).2.2.2.1 (SetMembers.raw y)) (SetMembers.raw x) ∈ au := by
    change completion.algebra.union.action.act rect.first y = x ↔ _
    rw [completion.algebra.union.action.act_eq_iff]
    rw [show SetMembers.raw rect.first = _ from fields.2.2.2.1]
  exact and_congr code actor

theorem externalFamily_rectangle_second_overlap
    (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (x y : SetMembers U) :
    let v := externalRectangleParameters z
    ((f).flatVertex (.inr (.inr z)) none).toFun x =
      ((f).flatVertex (.inr (.inr z)) (some ⟨true⟩)).toFun y ↔
      ZFSet.pair (SetMembers.raw y) v.1 ∈ ru ∧
        ZFSet.pair (ZFSet.pair v.2.2.2.2 (SetMembers.raw y)) (SetMembers.raw x) ∈ au := by
  let rect := completion.externalRectangle group oldAction compression z
  let tile := rect.toInput (f).top (f).greatest
  change tile.root.toFun x = tile.second.toFun y ↔ _
  rw [eq_comm, tile.second_root_intersection]
  have fields := (((externalRectangleParameters_spec z).2).lift_compression compression oldAction).toSmallActionRectangle_fields
    group completion.algebra.union.action completion.algebra.union.meet
  have code : (p).le y tile.C ↔ ZFSet.pair (SetMembers.raw y) (externalRectangleParameters z).1 ∈ ru := by
    change ZFSet.pair (SetMembers.raw y) (SetMembers.raw rect.C) ∈ ru ↔ _
    rw [show SetMembers.raw rect.C = _ from fields.1]
  have actor : tile.g2.toFun y = x ↔
      ZFSet.pair (ZFSet.pair (externalRectangleParameters z).2.2.2.2 (SetMembers.raw y)) (SetMembers.raw x) ∈ au := by
    change completion.algebra.union.action.act rect.second y = x ↔ _
    rw [completion.algebra.union.action.act_eq_iff]
    rw [show SetMembers.raw rect.second = _ from fields.2.2.2.2]
  exact and_congr code actor

theorem externalFamily_rectangle_children_overlap
    (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (x y : SetMembers U) :
    let v := externalRectangleParameters z
    ((f).flatVertex (.inr (.inr z)) (some ⟨false⟩)).toFun x =
      ((f).flatVertex (.inr (.inr z)) (some ⟨true⟩)).toFun y ↔
      SetMembers.raw x = SetMembers.raw y ∧ ZFSet.pair (SetMembers.raw x) v.2.1 ∈ ru := by
  let rect := completion.externalRectangle group oldAction compression z
  let tile := rect.toInput (f).top (f).greatest
  change tile.first.toFun x = tile.second.toFun y ↔ _
  rw [tile.children_intersection]
  have fields := (((externalRectangleParameters_spec z).2).lift_compression compression oldAction).toSmallActionRectangle_fields
    group completion.algebra.union.action completion.algebra.union.meet
  change (ZFSet.pair (SetMembers.raw x) (SetMembers.raw rect.B) ∈ ru ∧ x = y) ↔ _
  rw [show SetMembers.raw rect.B = _ from fields.2.1]
  rw [← (SetMembers.raw_injective U).eq_iff, and_comm]

end PartitionPilot.Forcing.GroundCompressionCompletion

end OAI
