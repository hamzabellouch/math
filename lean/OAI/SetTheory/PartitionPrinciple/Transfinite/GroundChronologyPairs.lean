import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def chronologyPairs (T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ s ∈ T, ∃ t ∈ T,
    z = ZFSet.pair s t ∧ (t = s ∨ t ∈ s)) (ZFSet.prod T T)

theorem mem_chronologyPairs (T z : ZFSet.{u}) :
    z ∈ chronologyPairs T ↔ ∃ s ∈ T, ∃ t ∈ T,
      z = ZFSet.pair s t ∧ (t = s ∨ t ∈ s) := by
  rw [chronologyPairs, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨s, hs, t, ht, equal, before⟩
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨hs, ht⟩, s, hs, t, ht, equal, before⟩

theorem pair_mem_chronologyPairs (T s t : ZFSet.{u}) :
    ZFSet.pair s t ∈ chronologyPairs T ↔ s ∈ T ∧ t ∈ T ∧ (t = s ∨ t ∈ s) := by
  rw [mem_chronologyPairs]
  constructor
  · rintro ⟨a, ha, b, hb, equal, before⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, before⟩
  · rintro ⟨hs, ht, before⟩
    exact ⟨s, hs, t, ht, rfl, before⟩

theorem chronologyPairs_subset (T : ZFSet.{u}) : chronologyPairs T ⊆ ZFSet.prod T T :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem chronologyPairs_mono {S T : ZFSet.{u}} (subset : S ⊆ T) :
    chronologyPairs S ⊆ chronologyPairs T := by
  intro z hz
  obtain ⟨s, hs, t, ht, rfl, before⟩ := (mem_chronologyPairs S z).1 hz
  exact (pair_mem_chronologyPairs T s t).2 ⟨subset hs, subset ht, before⟩

theorem chronologyPairs_restrict {S T : ZFSet.{u}}
    (subset : S ⊆ T) (transitive : setTransitive S) :
    chronologyPairs S = graphRestriction S (chronologyPairs T) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨s, hs, t, ht, rfl, before⟩ := (mem_chronologyPairs S z).1 hz
    exact pair_mem_graphRestriction.2
      ⟨(pair_mem_chronologyPairs T s t).2 ⟨subset hs, subset ht, before⟩, hs⟩
  · intro hz
    obtain ⟨s, hs, t, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨_, _, before⟩ := (pair_mem_chronologyPairs T s t).1 entry
    have ht : t ∈ S := before.elim (fun equal => equal.symm ▸ hs)
      (fun earlier => transitive s hs t earlier)
    exact (pair_mem_chronologyPairs S s t).2 ⟨hs, ht, before⟩

namespace BoundedFormula

def chronologyPairFormula {n} (z T : Fin n) : BoundedFormula n :=
  exMem T (exMem T.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (disj (.equal 0 1) (.mem 0 1))))

theorem truth_chronologyPairFormula {n} (z T : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologyPairFormula z T) env ↔ env z ∈ chronologyPairs (env T) := by
  simp only [chronologyPairFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_disj, mem_chronologyPairs]
  rfl

def chronologyPairsEquationFormula {n} (J T : Fin n) : BoundedFormula n :=
  .conj (.allMem J (chronologyPairFormula 0 T.succ))
    (.allMem T (.allMem T.succ (imp (disj (.equal 0 1) (.mem 0 1))
      (pairMembershipFormula 1 0 J.succ.succ))))

theorem truth_chronologyPairsEquationFormula {n} (J T : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologyPairsEquationFormula J T) env ↔ env J = chronologyPairs (env T) := by
  simp only [chronologyPairsEquationFormula, Truth, truth_chronologyPairFormula,
    truth_imp, truth_disj, truth_pairMembershipFormula]
  change ((∀ z ∈ env J, z ∈ chronologyPairs (env T)) ∧
    ∀ s ∈ env T, ∀ t ∈ env T, (t = s ∨ t ∈ s) → ZFSet.pair s t ∈ env J) ↔ _
  constructor
  · rintro ⟨subset, cover⟩
    apply ZFSet.ext
    intro z
    refine ⟨subset z, ?_⟩
    intro hz
    obtain ⟨s, hs, t, ht, rfl, before⟩ := (mem_chronologyPairs (env T) z).1 hz
    exact cover s hs t ht before
  · intro equal
    rw [equal]
    exact ⟨fun _ hz => hz, fun s hs t ht before =>
      (pair_mem_chronologyPairs (env T) s t).2 ⟨hs, ht, before⟩⟩

theorem realize_chronologyPairFormula (M : TransitiveGround.{u}) {n}
    (z T : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyPairFormula z T).toFormula env ↔ env z ∈ chronologyPairs (env T) :=
  (realize_toFormula M _ env members).trans (truth_chronologyPairFormula z T env)

theorem realize_chronologyPairsEquationFormula (M : TransitiveGround.{u}) {n}
    (J T : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyPairsEquationFormula J T).toFormula env ↔ env J = chronologyPairs (env T) :=
  (realize_toFormula M _ env members).trans (truth_chronologyPairsEquationFormula J T env)

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem chronologyPairs_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) : chronologyPairs T ∈ M.sets := by
  let params := extend T Fin.elim0
  have ground := M.bounded_separation_mem separation (BoundedFormula.chronologyPairFormula 0 1)
    params (Fin.cases hT (fun i => Fin.elim0 i)) (M.prod_mem pairing unions powers separation hT hT)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.chronologyPairFormula 0 1)
      (extend z params)) (ZFSet.prod T T) = chronologyPairs T := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_chronologyPairFormula]
    exact ⟨And.right, fun hz => ⟨chronologyPairs_subset T hz, hz⟩⟩
  exact equal ▸ ground

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
