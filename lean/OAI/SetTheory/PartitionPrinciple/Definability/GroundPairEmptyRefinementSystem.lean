import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNiceRefinementVisibility

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

theorem pairEmpty_refinementSystem (a : PosetAction G P) (s : Presentation P)
    (t : Presentation G) (b : Presentation L) (d : PosetAction G L) (base : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (action : a.actionGraph s t ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
    (children : ∀ w : Name s, w.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) w) :
    let lifted := Name.renamedFamily s.pairEmpty id T valid
    let squared := orderedPairNameFamily (s.pairEmpty.encode ⊤) lifted lifted
    let graph := Name.renameFamilyGraph s.pairEmpty id T valid
    lifted ∈ M.sets ∧ squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
      ∃ valid1 : ∀ z ∈ lifted, IsName s.pairEmpty z,
      ∃ valid2 : ∀ z ∈ squared, IsName s.pairEmpty z,
        NiceNameSystem M a s.pairEmpty b d base directed lifted valid1 ∧
        NiceNameSystem M a s.pairEmpty b d base directed squared valid2 ∧
        NiceRefinementIndexSystem M a s.pairEmpty b d ∅ lifted squared valid1 valid2 ∧
        (∀ C E (U Rf Rc : (M.nameDomain s.pairEmpty).names),
          refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
            M.niceRefinementIndices a s.pairEmpty b d ∅ lifted squared valid1 →
          RefinementObjectSystem M a s.pairEmpty (d.principalSupportFamily base directed)
            (d.principalFix C) lifted valid1 U.val Rf.val Rc.val) ∧
        ∀ n : Nat, Name.renamedFamily s.pairEmpty id (iteratedPairNameFamily (s.encode ⊤) T n)
            (iteratedPairNameFamily_valid ⊤ valid n) =
          iteratedPairNameFamily (s.pairEmpty.encode ⊤) lifted n := by
  obtain ⟨hLifted, hGraph, injection, valid1, hs1, closed1, _⟩ :=
    M.pairEmpty_nameFamily a s (d.principalSupportFamily base directed)
      pairing unions powers separation collection carrier T hT valid closed children
  let lifted := Name.renamedFamily s.pairEmpty id T valid
  let squared := orderedPairNameFamily (s.pairEmpty.encode ⊤) lifted lifted
  have pairedCarrier := M.pairEmpty_carrier_mem pairing unions powers separation s carrier
  have pairedOrder := M.pairEmpty_order_mem pairing unions powers separation s carrier order
  have pairedMaps := M.pairEmpty_conditionMapFamily_mem pairing unions powers separation s a t
    collection carrier group action
  have hTop := M.transitive pairedCarrier (s.pairEmpty.encode_mem ⊤)
  have hSquared : squared ∈ M.sets :=
    M.orderedPairNameFamily_mem pairing unions powers separation hTop hLifted hLifted
  have valid2 : ∀ z ∈ squared, IsName s.pairEmpty z := orderedPairNameFamily_valid ⊤ valid1 valid1
  have closed2 := orderedPairNameFamily_closed a valid1 valid1 closed1 closed1
  have hs2 := orderedPairNameFamily_hs a (d.principalSupportFamily base directed) valid1 valid1 hs1 hs1
  have first := M.niceNameSystem a s.pairEmpty t pairing unions powers separation collection
    pairedCarrier pairedOrder pairedMaps hLifted valid1 closed1 b d base directed group nodes supports hs1
  have second := M.niceNameSystem a s.pairEmpty t pairing unions powers separation collection
    pairedCarrier pairedOrder pairedMaps hSquared valid2 closed2 b d base directed group nodes supports hs2
  obtain ⟨indices, objects⟩ := M.niceRefinementObjects a s.pairEmpty b d base directed
    pairing unions powers separation collection (M.empty_mem ⟨s.carrier, carrier⟩) hLifted hSquared
    pairedCarrier pairedOrder nodes nodeOrder closed1 hs1 first second
  exact ⟨hLifted, hSquared, hGraph, injection, valid1, valid2, first, second, indices, objects,
    fun n => Name.renamedFamily_iteratedPairNameFamily s.pairEmpty id ⊤ T valid n⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
