import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundBinaryRowStageOneRefinement

namespace OAI

section

namespace PartitionPilot.Forcing.RefinementStageSystem
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable {a : PosetAction G P} {s : Presentation P} {t : Presentation G}
variable {b : Presentation L} {d : PosetAction G L} {base : L}
variable {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {level T T2 : ZFSet.{u}}

theorem finitePower_system (system : RefinementStageSystem M a s t b d base directed level T T2)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets) (hT : T ∈ M.sets) (n : Nat) :
    let X := iteratedPairNameFamily (s.encode ⊤) T n
    ∃ valid : ∀ z ∈ X, IsName s z,
      X ∈ M.sets ∧
      (∀ g (tau : Name s), tau.val ∈ X → (a.act s g tau).val ∈ X) ∧
      (∀ tau : Name s, tau.val ∈ X →
        HereditarilySymmetric a s (d.principalSupportFamily base directed) tau) ∧
      NiceNameSystem M a s b d base directed X valid := by
  let valid := iteratedPairNameFamily_valid ⊤ system.valid1 n
  have ground := M.iteratedPairNameFamily_mem pairing unions powers separation
    (M.transitive carrier (s.encode_mem ⊤)) hT n
  have closed := iteratedPairNameFamily_closed a system.valid1 system.inputs.terms_closed n
  have symmetric := iteratedPairNameFamily_hs a (d.principalSupportFamily base directed)
    system.valid1 system.terms_hs n
  exact ⟨valid, ground, closed, symmetric,
    M.niceNameSystem a s t pairing unions powers separation collection carrier order
      system.inputs.condition_maps ground valid closed b d base directed group nodes supports symmetric⟩

end PartitionPilot.Forcing.RefinementStageSystem

end

end OAI
