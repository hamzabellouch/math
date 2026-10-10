import OAI.SetTheory.PartitionPrinciple.Definability.MainLimitCoverageFormulas

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_supportedCertificateFormula {n}
    (nodes N order R niceEval visibilityEval value F B f : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (BoundedFormula.supportedCertificateFormula
      nodes N order R niceEval visibilityEval value F B f).toFormula env ↔
      SupportedEqualityCertificate (env nodes) (env N) (env order) (env R)
        (env niceEval) (env visibilityEval) (env value) (env F) (env B) (env f) :=
  (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_supportedCertificateFormula
      nodes N order R niceEval visibilityEval value F B f env)

theorem realize_supportedCertificateEntryFormula {n}
    (entry J PF PB WF nodes N order R inputEval niceEval visibilityEval : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (BoundedFormula.supportedCertificateEntryFormula
      entry J PF PB WF nodes N order R inputEval niceEval visibilityEval).toFormula env ↔
      ∃ j ∈ env J, ∃ F ∈ env PF, ∃ B ∈ env PB, ∃ f ∈ env WF,
        env entry = ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∧
        ∃ value, ZFSet.pair j value ∈ env inputEval ∧
          SupportedEqualityCertificate (env nodes) (env N) (env order) (env R)
            (env niceEval) (env visibilityEval) value F B f :=
  (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_supportedCertificateEntryFormula
      entry J PF PB WF nodes N order R inputEval niceEval visibilityEval env)

theorem supportedCertificateRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {J PF PB WF nodes N order R inputEval niceEval visibilityEval : ZFSet.{u}}
    (hJ : J ∈ M.sets) (hPF : PF ∈ M.sets) (hPB : PB ∈ M.sets) (hWF : WF ∈ M.sets)
    (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets) (hOrder : order ∈ M.sets)
    (hR : R ∈ M.sets) (hInput : inputEval ∈ M.sets) (hNice : niceEval ∈ M.sets)
    (hVisibility : visibilityEval ∈ M.sets) :
    supportedCertificateRelation J PF PB WF nodes N order R inputEval niceEval visibilityEval ∈ M.sets := by
  let params : Fin 11 → ZFSet.{u} := ![J, PF, PB, WF, nodes, N, order, R,
    inputEval, niceEval, visibilityEval]
  have members : ∀ i, params i ∈ M.sets := by
    exact (Fin.cases hJ (Fin.cases hPF (Fin.cases hPB (Fin.cases hWF (Fin.cases hNodes (Fin.cases hN (Fin.cases hOrder (Fin.cases hR (Fin.cases hInput (Fin.cases hNice (Fin.cases hVisibility (fun i => Fin.elim0 i))))))))))))
  have bound := M.prod_mem pairing unions powers separation hJ
    (M.prod_mem pairing unions powers separation hPF
      (M.prod_mem pairing unions powers separation hPB hWF))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.supportedCertificateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11)
    params members bound
  have equal : ZFSet.sep (fun entry => BoundedFormula.Truth
      (BoundedFormula.supportedCertificateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11)
      (extend entry params)) (ZFSet.prod J (ZFSet.prod PF (ZFSet.prod PB WF))) =
      supportedCertificateRelation J PF PB WF nodes N order R inputEval niceEval visibilityEval := by
    apply ZFSet.ext
    intro entry
    rw [ZFSet.mem_sep, supportedCertificateRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_supportedCertificateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 _)
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

def supportedCertificateFamilyFormula : SetFormula 12 :=
  (BoundedFormula.allMem 0
    (BoundedFormula.supportedCertificateEntryFormula 0 2 3 4 5 6 7 8 9 10 11 12)).toFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_supportedCertificateFamilyFormula (env : Fin 12 → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets supportedCertificateFamilyFormula env ↔
      env 0 ⊆ supportedCertificateRelation (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) (env 11) := by
  rw [supportedCertificateFamilyFormula, BoundedFormula.realize_toFormula M _ env members]
  change (∀ entry ∈ env 0, BoundedFormula.Truth
    (BoundedFormula.supportedCertificateEntryFormula 0 2 3 4 5 6 7 8 9 10 11 12)
      (extend entry env)) ↔ _
  constructor
  · intro allEntries entry member
    obtain ⟨j, hj, F, hF, B, hB, f, hf, equal, value, evaluated, certificate⟩ :=
      (BoundedFormula.truth_supportedCertificateEntryFormula 0 2 3 4 5 6 7 8 9 10 11 12 _).1
        (allEntries entry member)
    change entry = ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) at equal
    rw [equal]
    exact (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2
      ⟨hj, hF, hB, hf, value, evaluated, certificate⟩
  · intro selected entry member
    obtain ⟨_, witness⟩ := ZFSet.mem_sep.1 (selected member)
    exact (BoundedFormula.truth_supportedCertificateEntryFormula 0 2 3 4 5 6 7 8 9 10 11 12 _).2 witness

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
