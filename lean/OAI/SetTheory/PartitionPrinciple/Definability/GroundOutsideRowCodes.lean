import OAI.SetTheory.PartitionPrinciple.Forcing.GroundBinaryRowNameCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundOutsideRowNames

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_binaryRowSubsetEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C J : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (hJ : J ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets binaryRowSetEntryFormula (extend z (extend J (extend C (extend
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
        (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))))) ↔
      z ∈ (M.binaryRowSubsetName I C one J).val := by
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hone := M.transitive hQ (SetMembers.raw_mem one)
  rw [binaryRowSetEntryFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, rest⟩
    obtain ⟨w, hwM, hi, code, shape⟩ := (realize_ex M.sets _ _).1 rest
    rw [realize_binaryApplication, map_extend, map_extend, map_extend, map_extend, map_empty] at code
    have eq := (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
      hI hC one i w hiM hwM).1 code
    have pair := (M.realize_orderedPairFormula pairing 2 0 6 _ hz hwM hone).1 shape
    exact (M.mem_binaryRowSubsetName_code I C one J z).2
      ⟨i, hi, pair.trans (congrArg (fun v => ZFSet.pair v (SetMembers.raw one)) eq)⟩
  · intro member
    obtain ⟨i, hi, shape⟩ := (M.mem_binaryRowSubsetName_code I C one J z).1 member
    have hiM := M.transitive hJ hi
    have hname := M.binaryRowName_mem pairing unions powers separation collection infinite hI hC one i hiM
    refine ⟨i, hiM, ?_⟩
    rw [realize_ex]
    refine ⟨(M.binaryRowName I C one i).val, hname, hi, ?_, ?_⟩
    · rw [realize_binaryApplication, map_extend, map_extend, map_extend, map_extend, map_empty]
      exact (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
        hI hC one i _ hiM hname).2 rfl
    · exact (M.realize_orderedPairFormula pairing 2 0 6 _ hz hname hone).2 shape

theorem binaryRowSubsetName_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C J : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (hJ : J ∈ M.sets) (subset : J ⊆ I) :
    (M.binaryRowSubsetName I C one J).val ∈ M.sets := by
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hone := M.transitive hQ (SetMembers.raw_mem one)
  obtain ⟨W, hW, inW⟩ := M.exists_binaryRowName_bound pairing unions powers separation collection infinite
    hI hC one
  obtain ⟨D, hD, pairBound⟩ := M.exists_pair_bound pairing unions powers hW
    (M.unorderedPair_mem pairing hone hone)
  have bound : (M.binaryRowSubsetName I C one J).val ⊆ D := by
    intro z hz
    obtain ⟨i, hi, eq⟩ := (M.mem_binaryRowSubsetName_code I C one J z).1 hz
    exact eq.symm ▸ pairBound _ (inW i (subset hi)) _ (ZFSet.mem_pair.2 (Or.inl rfl))
  let params := extend J (extend C (extend
    (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
      (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0))))
  have selected := M.separation_mem separation binaryRowSetEntryFormula params
    (Fin.cases hJ (Fin.cases hC (Fin.cases hQ (Fin.cases hone
      (Fin.cases (M.natSetCode_mem separation infinite 1) (fun j => Fin.elim0 j)))))) hD
  have eq : ZFSet.sep (fun z => Realize M.sets binaryRowSetEntryFormula
      (extend z params)) D = (M.binaryRowSubsetName I C one J).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_binaryRowSubsetEntryFormula pairing unions powers separation collection infinite
        hI hC one hJ z (M.transitive hD hz)).1 rel
    · intro hz
      exact ⟨bound hz, (M.realize_binaryRowSubsetEntryFormula pairing unions powers separation collection infinite
        hI hC one hJ z (M.transitive hD (bound hz))).2 hz⟩
  exact eq ▸ selected

theorem outsideRowIndices_mem {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (B : L) (separation : SeparationSchema M.sets)
    (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) :
    outsideRowIndices s B ∈ M.sets := by
  have hB := M.transitive hL (s.encode_mem B)
  let params := extend (s.encode B) (extend s.conditionOrder Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (.neg (BoundedFormula.pairMembershipFormula 0 1 2)) params
    (Fin.cases hB (Fin.cases order (fun j => Fin.elim0 j)))
    (M.nonbottom_carrier_mem s separation hL)
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (.neg (BoundedFormula.pairMembershipFormula 0 1 2)) (extend x params))
      s.nonbottom.carrier = outsideRowIndices s B := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, outsideRowIndices, ZFSet.mem_sep]
    exact and_congr Iff.rfl (not_congr (BoundedFormula.truth_pairMembershipFormula 0 1 2 _))
  exact eq ▸ selected

theorem internalOutsideRowsName_mem {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets)
    (order : s.conditionOrder ∈ M.sets) (B : L) :
    (M.internalOutsideRowsName s C hL B).val ∈ M.sets := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowSubsetName_mem pairing unions powers separation collection infinite
    (M.nonbottom_carrier_mem s separation hL) hC ⊤
    (M.outsideRowIndices_mem s B separation hL order) (outsideRowIndices_subset s B)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
