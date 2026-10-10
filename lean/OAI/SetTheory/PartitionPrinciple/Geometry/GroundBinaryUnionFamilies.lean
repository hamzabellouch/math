import OAI.SetTheory.PartitionPrinciple.Definability.GroundRefinementPairClassGraphs

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u
namespace BoundedFormula

def binaryUnionSetFormula {n} (output first second : Fin n) : BoundedFormula n :=
  .conj (.allMem output (.disj (.mem 0 first.succ) (.mem 0 second.succ)))
    (.conj (.allMem first (.mem 0 output.succ)) (.allMem second (.mem 0 output.succ)))

theorem truth_binaryUnionSetFormula {n} (output first second : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (binaryUnionSetFormula output first second) env ↔
      env output = env first ∪ env second := by
  simp only [binaryUnionSetFormula, Truth, truth_disj, extend, Fin.cases_zero, Fin.cases_succ]
  constructor
  · rintro ⟨forward, left, right⟩
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => ZFSet.mem_union.2 (forward z hz),
      fun hz => (ZFSet.mem_union.1 hz).elim (left z) (right z)⟩
  · intro equal
    refine ⟨fun z hz => ZFSet.mem_union.1 (equal ▸ hz), ?_, ?_⟩
    · intro z hz
      exact equal.symm ▸ ZFSet.mem_union.2 (Or.inl hz)
    · intro z hz
      exact equal.symm ▸ ZFSet.mem_union.2 (Or.inr hz)

def binaryUnionFamilyEntryFormula : BoundedFormula 7 :=
  exMem 1 (exMem 3 (exMem 7 (exMem 9
    (.conj (orderedPairFormula 4 3 2) (.conj (pairMembershipFormula 3 1 7)
      (.conj (pairMembershipFormula 3 0 8) (binaryUnionSetFormula 2 1 0)))))))

theorem truth_binaryUnionFamilyEntryFormula (z I W F H RF RH : ZFSet.{u}) :
    Truth binaryUnionFamilyEntryFormula ![z,I,W,F,H,RF,RH] ↔
      ∃ x ∈ I, ∃ out ∈ W, ∃ f ∈ RF, ∃ h ∈ RH,
        z = ZFSet.pair x out ∧ ZFSet.pair x f ∈ F ∧ ZFSet.pair x h ∈ H ∧ out = f ∪ h := by
  simp only [binaryUnionFamilyEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_binaryUnionSetFormula]
  rfl

end BoundedFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem familyCodeGraph_binaryUnions_mem {G : Type u} (t : Presentation G) (f h : G → ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (group : t.carrier ∈ M.sets)
    (wholeF : familyCodeGraph t.encode f ∈ M.sets)
    (wholeH : familyCodeGraph t.encode h ∈ M.sets) :
    familyCodeGraph t.encode (fun g => f g ∪ h g) ∈ M.sets := by
  let F := familyCodeGraph t.encode f
  let H := familyCodeGraph t.encode h
  let RF := ⋃₀ ⋃₀ F
  let RH := ⋃₀ ⋃₀ H
  let V := (⋃₀ RF) ∪ (⋃₀ RH)
  let W := M.groundPower V
  let result := familyCodeGraph t.encode (fun g => f g ∪ h g)
  have hRF : RF ∈ M.sets := M.union_mem unions (M.union_mem unions wholeF)
  have hRH : RH ∈ M.sets := M.union_mem unions (M.union_mem unions wholeH)
  have hV : V ∈ M.sets := M.binary_union_mem pairing unions
    (M.union_mem unions hRF) (M.union_mem unions hRH)
  have hW : W ∈ M.sets := M.groundPower_mem powers hV
  have fEntry (g : G) := (pair_mem_familyCodeGraph t.encode f t.injective g (f g)).2 rfl
  have hEntry (g : G) := (pair_mem_familyCodeGraph t.encode h t.injective g (h g)).2 rfl
  have fiber (g : G) : f g ∪ h g ∈ W := by
    apply (M.mem_groundPower V _).2
    refine ⟨M.binary_union_mem pairing unions
      (M.transitive hRF (pair_second_mem_doubleUnion (fEntry g)))
      (M.transitive hRH (pair_second_mem_doubleUnion (hEntry g))), ?_⟩
    intro z hz
    rcases ZFSet.mem_union.1 hz with left | right
    · exact ZFSet.mem_union.2 (Or.inl (ZFSet.mem_sUnion.2
        ⟨f g, pair_second_mem_doubleUnion (fEntry g), left⟩))
    · exact ZFSet.mem_union.2 (Or.inr (ZFSet.mem_sUnion.2
        ⟨h g, pair_second_mem_doubleUnion (hEntry g), right⟩))
  let params : Fin 6 → ZFSet.{u} := ![t.carrier,W,F,H,RF,RH]
  have members : ∀ j, params j ∈ M.sets := Fin.cases group (Fin.cases hW
    (Fin.cases wholeF (Fin.cases wholeH (Fin.cases hRF (Fin.cases hRH (fun j => Fin.elim0 j))))))
  have meaning (z : ZFSet.{u}) :
      BoundedFormula.Truth BoundedFormula.binaryUnionFamilyEntryFormula (extend z params) ↔ z ∈ result := by
    change BoundedFormula.Truth BoundedFormula.binaryUnionFamilyEntryFormula ![z,t.carrier,W,F,H,RF,RH] ↔ z ∈ result
    rw [BoundedFormula.truth_binaryUnionFamilyEntryFormula]
    constructor
    · rintro ⟨x,hx,out,_,first,_,second,_,equal,fe,he,union⟩
      obtain ⟨g,rfl⟩ := (t.mem_carrier x).1 hx
      have ef := (pair_mem_familyCodeGraph t.encode f t.injective g first).1 fe
      have eh := (pair_mem_familyCodeGraph t.encode h t.injective g second).1 he
      exact (mem_familyCodeGraph _ _ z).2 ⟨g, by simpa only [ef,eh,union] using equal.symm⟩
    · intro member
      obtain ⟨g,rfl⟩ := (mem_familyCodeGraph _ _ z).1 member
      exact ⟨t.encode g,t.encode_mem g,_,fiber g,f g,pair_second_mem_doubleUnion (fEntry g),
        h g,pair_second_mem_doubleUnion (hEntry g),rfl,fEntry g,hEntry g,rfl⟩
  have bound : result ⊆ ZFSet.prod t.carrier W := by
    intro z hz
    obtain ⟨g,rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨t.encode_mem g,fiber g⟩
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.binaryUnionFamilyEntryFormula
      (extend z params)) (ZFSet.prod t.carrier W) = result := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, meaning]
    exact ⟨And.right, fun hz => ⟨bound hz,hz⟩⟩
  change result ∈ M.sets
  rw [← equal]
  exact M.bounded_separation_mem separation BoundedFormula.binaryUnionFamilyEntryFormula
    params members (M.prod_mem pairing unions powers separation group hW)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
