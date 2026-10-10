import OAI.SetTheory.PartitionPrinciple.Forcing.NameRenameSteps

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u

def rawCandidateDensity (M : TransitiveGround.{u}) {n : Nat}
    (phi : SetFormula (n + 1)) (Q order W base : ZFSet.{u})
    (env : Fin n → ZFSet.{u}) : Prop :=
  ∀ p ∈ Q, ZFSet.pair p base ∈ order →
    ∃ q ∈ Q, ZFSet.pair q p ∈ order ∧
      Realize M.sets (candidateForcingFormula phi)
        (extend q (extend W (extend Q (extend order env))))

theorem rawCandidateDensity_iff (M : TransitiveGround.{u})
    {P : Type u} [Preorder P] (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (phi : SetFormula (n + 1)) (env : Assignment (M.nameDomain s) n)
    (W : ZFSet.{u}) (valid : ∀ z ∈ W, IsName s z) (base : P) :
    M.rawCandidateDensity phi s.carrier s.conditionOrder W (s.encode base)
      (fun i => (env i).val.val) ↔
      DenseBelow base {q | ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
        Forces (M.nameDomain s) phi (extend tau env) q} := by
  constructor
  · intro dense p below
    obtain ⟨rawQ, member, relation, truth⟩ := dense (s.encode p) (s.encode_mem p)
      ((s.pair_mem_conditionOrder p base).2 below)
    obtain ⟨q, rfl⟩ := (s.mem_carrier rawQ).1 member
    exact ⟨q, (s.pair_mem_conditionOrder q p).1 relation,
      (M.realize_candidateForcingFormula s pairing unions powers separation collection
        carrier order phi env W valid q).1 truth⟩
  · intro dense rawP member relation
    obtain ⟨p, rfl⟩ := (s.mem_carrier rawP).1 member
    obtain ⟨q, below, forced⟩ := dense p ((s.pair_mem_conditionOrder p base).1 relation)
    exact ⟨s.encode q, s.encode_mem q, (s.pair_mem_conditionOrder q p).2 below,
      (M.realize_candidateForcingFormula s pairing unions powers separation collection
        carrier order phi env W valid q).2 forced⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
