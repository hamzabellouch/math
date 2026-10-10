import OAI.SetTheory.PartitionPrinciple.Definability.GroundSelectedSupportTupleFamilies

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (s : Presentation L) (C : ZFSet.{u}) (hL : s.carrier ∈ M.sets)

theorem internalRowTupleName_eval_function (δ : ZFSet.{u})
    (positions : δ.toSet → {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      ZFSet.IsFunc δ (ZFSet.range (fun i : δ => M.binaryGenericRow s.nonbottom.carrier C H
        (s.encode (positions i).val)))
        (Name.eval {p | H.mem p} (M.internalRowTupleName s C hL δ positions)) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H
  have eq (i : δ.toSet) : Name.eval {p | H.mem p} (M.internalRowName s C hL (positions i)) =
      M.binaryGenericRow s.nonbottom.carrier C H (s.encode (positions i).val) :=
    M.eval_binaryRowName s.nonbottom.carrier C ⊤ H H.top_mem _
  have result := Name.eval_indexedTuple_function {p | H.mem p} ⊤ H.top_mem δ
    (fun i => M.internalRowName s C hL (positions i))
  simpa only [eq, internalRowTupleName] using result

theorem internalRowTupleName_eval_domain_eq {δ ε : ZFSet.{u}}
    (positions : δ.toSet → {i : L // i ≠ ⊥}) (other : ε.toSet → {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      Name.eval {p | H.mem p} (M.internalRowTupleName s C hL δ positions) =
        Name.eval {p | H.mem p} (M.internalRowTupleName s C hL ε other) → δ = ε := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H eq
  exact Name.eval_indexedTuple_domain_eq {p | H.mem p} ⊤ H.top_mem
    (fun i => M.internalRowName s C hL (positions i))
    (fun i => M.internalRowName s C hL (other i)) eq

theorem internalRowTupleName_eval_eq_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (hC : C ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (δ : ZFSet.{u}) (positions other : δ.toSet → {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      H.GenericFor (M.codedFamily (SetMembers.presentation (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) →
      (Name.eval {p | H.mem p} (M.internalRowTupleName s C hL δ positions) =
        Name.eval {p | H.mem p} (M.internalRowTupleName s C hL δ other) ↔ positions = other) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H generic
  constructor
  · intro eq
    have values := (Name.eval_indexedTuple_eq_iff {p | H.mem p} ⊤ H.top_mem δ
      (fun i => M.internalRowName s C hL (positions i))
      (fun i => M.internalRowName s C hL (other i))).1 eq
    funext i
    apply Subtype.ext
    apply s.injective
    by_contra distinct
    have separated := M.binaryGenericRow_ne pairing unions powers separation infinite choice
      (M.nonbottom_carrier_mem s separation hL) hC
      (s.nonbottom.encode_mem (positions i)) (s.nonbottom.encode_mem (other i))
      distinct uncountable H generic
    apply separated
    have ev := values i
    change Name.eval {p | H.mem p} (M.binaryRowName s.nonbottom.carrier C ⊤
      (s.encode (positions i).val)) = Name.eval {p | H.mem p}
      (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode (other i).val)) at ev
    simpa only [M.eval_binaryRowName s.nonbottom.carrier C ⊤ H H.top_mem,
      Presentation.nonbottom_encode] using ev
  · rintro rfl
    rfl

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
