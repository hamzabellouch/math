import OAI.SetTheory.PartitionPrinciple.Definability.GroundPrincipalNiceSupportCodes

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

private theorem codeFunction (N : ZFSet.{u}) : FunctionGraphOn N (identityFunctionGraph N) :=
  ⟨N, (identityFunctionGraph_injection N).function⟩

private theorem codeValue (N : ZFSet.{u}) (i : N.toSet) :
    (codeFunction N).value i = i.val :=
  (codeFunction N).value_eq_of_entry i
    ((pair_mem_identityFunctionGraph N i.val i.val).2 ⟨rfl, i.property⟩)

private theorem codeIsName (i : (M.niceSupportNameCodes a s T K).toSet) :
    IsName s ((codeFunction (M.niceSupportNameCodes a s T K)).value i) := by
  rw [codeValue]
  exact M.niceSupportNameCodes_valid a s T K i.val i.property

variable [OrderTop P]

noncomputable def niceSupportEvaluationName : Name s :=
  Name.indexedGraphName ⊤ (codeFunction (M.niceSupportNameCodes a s T K))
    (codeIsName M a s T K)

theorem niceSupportEvaluationName_entry (tau : Name s)
    (member : tau.val ∈ M.niceSupportNameCodes a s T K)
    (H : ConditionFilter P) (x : ZFSet.{u}) :
    ZFSet.pair tau.val x ∈ Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K) ↔
      Name.eval {p | H.mem p} tau = x := by
  let i : (M.niceSupportNameCodes a s T K).toSet := ⟨tau.val, member⟩
  have same : (⟨(codeFunction (M.niceSupportNameCodes a s T K)).value i,
      codeIsName M a s T K i⟩ : Name s) = tau := Subtype.ext (codeValue _ i)
  exact (Name.pair_mem_eval_indexedGraphName {p | H.mem p} ⊤ H.top_mem
    (codeFunction (M.niceSupportNameCodes a s T K)) (codeIsName M a s T K) i x).trans
      (by rw [same])

theorem niceSupportEvaluationName_mem (t : Presentation G) (b : Presentation I)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) :
    (M.niceSupportEvaluationName a s T K).val ∈ M.sets := by
  have hN := M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  exact M.indexedGraphName_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) hN
    (M.identityFunctionGraph_mem pairing unions powers separation hN)
    (codeFunction (M.niceSupportNameCodes a s T K)) (codeIsName M a s T K)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
