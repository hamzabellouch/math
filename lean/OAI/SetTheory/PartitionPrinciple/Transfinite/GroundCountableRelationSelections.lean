import OAI.SetTheory.PartitionPrinciple.Definability.GroundBelowFunctionGraphs

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def binaryUnionEnumeration (A B : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair (natSetCode 0) A)
    (ZFSet.prod (ZFSet.sep (fun n => n ≠ natSetCode 0) ZFSet.omega) {B})

theorem pair_mem_binaryUnionEnumeration (A B n p : ZFSet.{u}) :
    ZFSet.pair n p ∈ binaryUnionEnumeration A B ↔
      (n = natSetCode 0 ∧ p = A) ∨
      (n ∈ ZFSet.omega ∧ n ≠ natSetCode 0 ∧ p = B) := by
  simp only [binaryUnionEnumeration, ZFSet.mem_insert_iff, ZFSet.pair_inj,
    ZFSet.pair_mem_prod, ZFSet.mem_sep, ZFSet.mem_singleton, and_assoc]

theorem binaryUnionEnumeration_isFunc (A B : ZFSet.{u}) :
    ZFSet.IsFunc ZFSet.omega {A, B} (binaryUnionEnumeration A B) := by
  classical
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | hz
    · exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega 0, ZFSet.mem_pair.2 (Or.inl rfl)⟩
    · obtain ⟨n, hn, p, hp, rfl⟩ := ZFSet.mem_prod.1 hz
      exact ZFSet.pair_mem_prod.2
        ⟨(ZFSet.mem_sep.1 hn).1, ZFSet.mem_pair.2 (Or.inr (ZFSet.mem_singleton.1 hp))⟩
  · intro n hn
    by_cases zero : n = natSetCode 0
    · refine ⟨A, (pair_mem_binaryUnionEnumeration A B n A).2 (Or.inl ⟨zero, rfl⟩), ?_⟩
      intro p hp
      rcases (pair_mem_binaryUnionEnumeration A B n p).1 hp with h | h
      · exact h.2
      · exact False.elim (h.2.1 zero)
    · refine ⟨B, (pair_mem_binaryUnionEnumeration A B n B).2 (Or.inr ⟨hn, zero, rfl⟩), ?_⟩
      intro p hp
      rcases (pair_mem_binaryUnionEnumeration A B n p).1 hp with h | h
      · exact False.elim (zero h.1)
      · exact h.2.2

theorem binaryUnionEnumeration_onto (A B : ZFSet.{u}) :
    ∀ p ∈ ({A, B} : ZFSet.{u}),
      ∃ n ∈ ZFSet.omega, ZFSet.pair n p ∈ binaryUnionEnumeration A B := by
  intro p hp
  rcases ZFSet.mem_pair.1 hp with hp | hp
  · subst p
    exact ⟨natSetCode 0, natSetCode_mem_omega 0,
      (pair_mem_binaryUnionEnumeration A B _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
  · subst p
    exact ⟨natSetCode 1, natSetCode_mem_omega 1,
      (pair_mem_binaryUnionEnumeration A B _ _).2
        (Or.inr ⟨natSetCode_mem_omega 1, fun eq => Nat.one_ne_zero (natSetCode_injective eq), rfl⟩)⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem binaryUnionEnumeration_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    binaryUnionEnumeration A B ∈ M.sets := by
  have hzero := M.natSetCode_mem separation infinite 0
  have nonzero : ZFSet.sep (fun n => n ≠ natSetCode 0) ZFSet.omega ∈ M.sets :=
    M.bounded_separation_mem separation (.neg (.equal 0 1))
      (extend (natSetCode 0) Fin.elim0) (Fin.cases hzero (fun j => Fin.elim0 j))
      (M.omega_mem separation infinite)
  have singleton : ({B} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hB hB
  exact M.insert_mem pairing unions (M.orderedPair_mem pairing hzero hA)
    (M.prod_mem pairing unions powers separation nonzero singleton)

theorem groundCountable_binary_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (countA : M.groundEmbeddable A ZFSet.omega)
    (countB : M.groundEmbeddable B ZFSet.omega) :
    M.groundEmbeddable (A ∪ B) ZFSet.omega := by
  have result := M.countable_enumerated_union pairing unions powers separation infinite choice
    (M.unorderedPair_mem pairing hA hB) (M.binary_union_mem pairing unions hA hB)
    (M.binaryUnionEnumeration_mem pairing unions powers separation infinite hA hB)
    (binaryUnionEnumeration_isFunc A B) (binaryUnionEnumeration_onto A B)
    (fun p hp => (ZFSet.mem_pair.1 hp).elim
      (fun eq => eq ▸ fun _ hz => ZFSet.mem_union.2 (Or.inl hz))
      (fun eq => eq ▸ fun _ hz => ZFSet.mem_union.2 (Or.inr hz)))
    (fun p hp => (ZFSet.mem_pair.1 hp).elim (fun eq => eq ▸ countA) (fun eq => eq ▸ countB))
  simpa only [ZFSet.sUnion_pair] using result

theorem countablePartialFunctions_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y p q : ZFSet.{u}}
    (hp : p ∈ M.smallPartialFunctions X Y ZFSet.omega)
    (hq : q ∈ M.smallPartialFunctions X Y ZFSet.omega)
    (agree : ∀ x y z, ZFSet.pair x y ∈ p → ZFSet.pair x z ∈ q → y = z) :
    p ∪ q ∈ M.smallPartialFunctions X Y ZFSet.omega := by
  obtain ⟨hpM, hpCode, hpSmall⟩ := (M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp
  obtain ⟨hqM, hqCode, hqSmall⟩ := (M.mem_smallPartialFunctions X Y ZFSet.omega q).1 hq
  exact (M.mem_smallPartialFunctions X Y ZFSet.omega _).2
    ⟨M.binary_union_mem pairing unions hpM hqM, hpCode.union hqCode agree,
      M.groundCountable_binary_union pairing unions powers separation infinite choice hpM hqM hpSmall hqSmall⟩

theorem countableFunction_common_extension
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ p q : SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      (∀ x y z, ZFSet.pair x y ∈ SetMembers.raw p → ZFSet.pair x z ∈ SetMembers.raw q → y = z) →
      ∃ r, SetMembers.raw r = SetMembers.raw p ∪ SetMembers.raw q ∧ r ≤ p ∧ r ≤ q := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro p q agree
  have member := M.countablePartialFunctions_union pairing unions powers separation infinite choice
    (SetMembers.raw_mem p) (SetMembers.raw_mem q) agree
  let r := SetMembers.ofMem (SetMembers.raw p ∪ SetMembers.raw q) member
  have raw : SetMembers.raw r = SetMembers.raw p ∪ SetMembers.raw q := SetMembers.raw_ofMem _ _
  refine ⟨r, raw, (M.smallFunction_le_iff X Y ZFSet.omega r p).2 ?_,
    (M.smallFunction_le_iff X Y ZFSet.omega r q).2 ?_⟩
  · rw [raw]
    exact fun _ hz => ZFSet.mem_union.2 (Or.inl hz)
  · rw [raw]
    exact fun _ hz => ZFSet.mem_union.2 (Or.inr hz)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation infinite choice

theorem exists_countableRelationSelection {A L R : ZFSet.{u}}
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (hR : R ∈ M.sets)
    (smallA : M.groundEmbeddable A ZFSet.omega)
    (total : ∀ x ∈ A, ∃ y ∈ L, ZFSet.pair x y ∈ R) :
    ∃ f ∈ M.sets, ZFSet.IsFunc A L f ∧ f ⊆ R ∧
      relationImage A L f ∈ M.sets ∧ M.groundEmbeddable (relationImage A L f) ZFSet.omega := by
  obtain ⟨f,hf,function,selected⟩ := M.uniformize_relation pairing unions powers separation choice hA hL hR total
  exact ⟨f,hf,function,selected,M.relationImage_mem separation hA hL hf,
    M.groundEmbeddable_function_image pairing unions powers separation choice hA hL
      (M.omega_mem separation infinite) hf function smallA⟩

theorem exists_countableNodeSelection {A L R used extra : ZFSet.{u}}
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (hR : R ∈ M.sets)
    (smallA : M.groundEmbeddable A ZFSet.omega)
    (total : ∀ x ∈ A, ∃ y ∈ L, ZFSet.pair x y ∈ R)
    (hUsed : used ∈ M.sets) (hExtra : extra ∈ M.sets)
    (usedSubset : used ⊆ L) (extraSubset : extra ⊆ L)
    (smallUsed : M.groundEmbeddable used ZFSet.omega)
    (smallExtra : M.groundEmbeddable extra ZFSet.omega) :
    ∃ f ∈ M.sets, ∃ W ∈ M.sets,
      ZFSet.IsFunc A L f ∧ f ⊆ R ∧
      W = (relationImage A L f ∪ used) ∪ extra ∧
      W ⊆ L ∧ M.groundEmbeddable W ZFSet.omega ∧
      (∀ x y, ZFSet.pair x y ∈ f → y ∈ W) ∧ used ⊆ W ∧ extra ⊆ W := by
  obtain ⟨f,hf,function,selected,hImage,smallImage⟩ :=
    M.exists_countableRelationSelection pairing unions powers separation infinite choice hA hL hR smallA total
  have hBoth := M.binary_union_mem pairing unions hImage hUsed
  have smallBoth := M.groundCountable_binary_union pairing unions powers separation infinite choice
    hImage hUsed smallImage smallUsed
  let W := (relationImage A L f ∪ used) ∪ extra
  have hW : W ∈ M.sets := M.binary_union_mem pairing unions hBoth hExtra
  have smallW : M.groundEmbeddable W ZFSet.omega :=
    M.groundCountable_binary_union pairing unions powers separation infinite choice hBoth hExtra smallBoth smallExtra
  refine ⟨f,hf,W,hW,function,selected,rfl,?_,smallW,?_,?_,?_⟩
  · intro y hy
    rcases ZFSet.mem_union.1 hy with both | additional
    · rcases ZFSet.mem_union.1 both with image | old
      · exact ((mem_relationImage A L f y).1 image).1
      · exact usedSubset old
    · exact extraSubset additional
  · intro x y entry
    have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact ZFSet.mem_union.2 (Or.inl (ZFSet.mem_union.2 (Or.inl
      ((mem_relationImage A L f y).2 ⟨bounds.2,x,bounds.1,entry⟩))))
  · intro y hy
    exact ZFSet.mem_union.2 (Or.inl (ZFSet.mem_union.2 (Or.inr hy)))
  · intro y hy
    exact ZFSet.mem_union.2 (Or.inr hy)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
