import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionExternalTileOverlaps

namespace OAI

section

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

theorem externalFamilyVertexCode_injective
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) :
    Function.Injective (completion.externalFamilyVertexCode group oldAction compression r) := by
  rcases r with i | (x | z)
  all_goals
    intro v w equal
    cases v with
    | none =>
      cases w with
      | none => rfl
      | some w =>
        cases w with | up w =>
          cases w <;> simp only [externalFamilyVertexCode_root, externalFamilyVertexCode_compression,
            externalFamilyVertexCode_separation, externalFamilyVertexCode_rectangle,
            natSetCode_injective.eq_iff] at equal <;> contradiction
    | some v =>
      cases w with
      | none =>
        cases v with | up v =>
          cases v <;> simp only [externalFamilyVertexCode_root, externalFamilyVertexCode_compression,
            externalFamilyVertexCode_separation, externalFamilyVertexCode_rectangle,
            natSetCode_injective.eq_iff] at equal <;> contradiction
      | some w =>
        cases v with | up v =>
          cases w with | up w =>
            cases v <;> cases w <;> simp_all only [externalFamilyVertexCode_compression,
              externalFamilyVertexCode_separation, externalFamilyVertexCode_rectangle,
              natSetCode_injective.eq_iff, Bool.false_eq_true] <;> simp_all

theorem externalFamilyVertexCode_range
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0)) (v : ZFSet.{u}) :
    (v = natSetCode 0 ∨ v = natSetCode 1 ∨
      (externalRequestIndexCode r ∈ ZFSet.prod {natSetCode 2} (externalRectangles P0 G r0 μ0 A0) ∧
        v = natSetCode 2)) ↔
    ∃ i, completion.externalFamilyVertexCode group oldAction compression r i = v := by
  rcases r with j | (x | z)
  · simp only [externalRequestIndexCode, ZFSet.pair_mem_prod, ZFSet.mem_singleton,
      natSetCode_injective.eq_iff, show ¬ (0 : Nat) = 2 by decide, false_and, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨()⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inl rfl
      | some i => exact Or.inr rfl
  · simp only [externalRequestIndexCode, ZFSet.pair_mem_prod, ZFSet.mem_singleton,
      natSetCode_injective.eq_iff, show ¬ (1 : Nat) = 2 by decide, false_and, or_false]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨()⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inl rfl
      | some i => exact Or.inr rfl
  · simp only [externalRequestIndexCode, ZFSet.pair_mem_prod, ZFSet.mem_singleton,
      SetMembers.raw_mem, and_self, true_and]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨false⟩, rfl⟩
      · exact ⟨some ⟨true⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i with
      | none => exact Or.inl rfl
      | some i =>
        cases i with | up b =>
          cases b
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)

noncomputable def externalFamilyTileVertexPresentation :
    Presentation (Sigma fun r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0) =>
      Option ((completion.externalFamily group oldAction compression).Child r) ×
        SetMembers (completion.algebra.union.fields 0)) where
  carrier := externalTileVertices (externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0))
    (externalRectangles P0 G r0 μ0 A0) (completion.algebra.union.fields 0)
  encode v := ZFSet.pair (ZFSet.pair (externalRequestIndexCode v.1)
    (completion.externalFamilyVertexCode group oldAction compression v.1 v.2.1)) (SetMembers.raw v.2.2)
  injective := by
    rintro ⟨r, i, x⟩ ⟨s, j, y⟩ equal
    have outer := ZFSet.pair_inj.1 equal
    have inner := ZFSet.pair_inj.1 outer.1
    have same := externalRequestIndexCode_injective I P0 (externalRectangles P0 G r0 μ0 A0) inner.1
    cases same
    have vertex := completion.externalFamilyVertexCode_injective group oldAction compression r inner.2
    have point := SetMembers.raw_injective _ outer.2
    cases vertex
    cases point
    rfl
  mem_carrier z := by
    constructor
    · intro hz
      have shape : ∃ q i x, z = ZFSet.pair (ZFSet.pair q i) x := by
        rcases ZFSet.mem_union.1 hz with h | h
        all_goals
          obtain ⟨qi, hqi, x, _, rfl⟩ := ZFSet.mem_prod.1 h
          obtain ⟨q, _, i, _, rfl⟩ := ZFSet.mem_prod.1 hqi
          exact ⟨q, i, x, rfl⟩
      obtain ⟨q, i, x, rfl⟩ := shape
      obtain ⟨hqi, hx⟩ := (triple_mem_externalTileVertices _ _ _ _ _ _).1 hz
      have hq : q ∈ externalRequestCarrier I P0 (externalRectangles P0 G r0 μ0 A0) := by
        rcases hqi with ⟨hq, _⟩ | ⟨hq, _⟩
        · exact hq
        · exact ZFSet.mem_union.2 (Or.inr hq)
      obtain ⟨r, rfl⟩ := ((externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).mem_carrier q).1 hq
      have hv : i = natSetCode 0 ∨ i = natSetCode 1 ∨
          (externalRequestIndexCode r ∈ ZFSet.prod {natSetCode 2} (externalRectangles P0 G r0 μ0 A0) ∧
            i = natSetCode 2) := by tauto
      obtain ⟨v, rfl⟩ := (completion.externalFamilyVertexCode_range group oldAction compression r i).1 hv
      exact ⟨⟨r, v, SetMembers.ofMem x hx⟩, by simp only [SetMembers.raw_ofMem]; rfl⟩
    · rintro ⟨⟨r, i, x⟩, rfl⟩
      apply (triple_mem_externalTileVertices _ _ _ _ _ _).2
      refine ⟨?_, SetMembers.raw_mem x⟩
      have hv := (completion.externalFamilyVertexCode_range group oldAction compression r _).2 ⟨i, rfl⟩
      have hq := (externalRequestPresentation I P0 (externalRectangles P0 G r0 μ0 A0)).encode_mem r
      tauto

theorem externalFamilyTileVertexPresentation_encode
    (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
    (i : Option ((completion.externalFamily group oldAction compression).Child r))
    (x : SetMembers (completion.algebra.union.fields 0)) :
    (completion.externalFamilyTileVertexPresentation group oldAction compression).encode ⟨r, i, x⟩ =
      ZFSet.pair (ZFSet.pair (externalRequestIndexCode r)
        (completion.externalFamilyVertexCode group oldAction compression r i)) (SetMembers.raw x) := rfl

end PartitionPilot.Forcing.GroundCompressionCompletion

end

end OAI
