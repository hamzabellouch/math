import OAI.SetTheory.PartitionPrinciple.Models.GroundSuccessorInjections

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

def RowPositionSequenceAt (L r I delta f : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc delta I f ∧ ∃ D ∈ L, ∀ a x, ZFSet.pair a x ∈ f → ZFSet.pair x D ∈ r

def RowPositionSequenceCode (L r I mu f : ZFSet.{u}) : Prop :=
  ∃ delta ∈ insert mu mu, RowPositionSequenceAt L r I delta f

theorem rowPositionSequence_length {mu delta : ZFSet.{u}}
    (ordinal : ordinalSetProperty mu) (length : delta ∈ insert mu mu) :
    ordinalSetProperty delta ∧ delta ⊆ mu := by
  rcases ZFSet.mem_insert_iff.1 length with rfl | member
  · exact ⟨ordinal, fun _ hx => hx⟩
  · exact ⟨ordinalSetProperty_member ordinal member, fun a ha => ordinal.1 delta member a ha⟩

theorem RowPositionSequenceCode.shape {L r I mu f : ZFSet.{u}}
    (code : RowPositionSequenceCode L r I mu f) (ordinal : ordinalSetProperty mu) :
    f ⊆ ZFSet.prod mu I := by
  obtain ⟨delta, length, function, _⟩ := code
  intro z hz
  obtain ⟨a, ha, x, hx, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨(rowPositionSequence_length ordinal length).2 ha, hx⟩

theorem RowPositionSequenceAt.domain_unique {L r I delta eta f : ZFSet.{u}}
    (first : RowPositionSequenceAt L r I delta f) (second : RowPositionSequenceAt L r I eta f) :
    delta = eta := by
  apply ZFSet.ext
  intro a
  constructor
  · intro ha
    obtain ⟨x, entry, _⟩ := first.1.2 a ha
    exact (ZFSet.pair_mem_prod.1 (second.1.1 entry)).1
  · intro ha
    obtain ⟨x, entry, _⟩ := second.1.2 a ha
    exact (ZFSet.pair_mem_prod.1 (first.1.1 entry)).1

namespace BoundedFormula

def rowPositionSequenceAtFormula {n} (L r I delta f : Fin n) : BoundedFormula n :=
  .conj (functionFormula delta I f)
    (exMem L (.allMem delta.succ (.allMem I.succ.succ
      (imp (pairMembershipFormula 1 0 f.succ.succ.succ)
        (pairMembershipFormula 0 2 r.succ.succ.succ)))))

theorem truth_rowPositionSequenceAtFormula {n} (L r I delta f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rowPositionSequenceAtFormula L r I delta f) env ↔
      RowPositionSequenceAt (env L) (env r) (env I) (env delta) (env f) := by
  simp only [rowPositionSequenceAtFormula, Truth, truth_functionFormula,
    truth_exMem, truth_imp, truth_pairMembershipFormula]
  change (ZFSet.IsFunc (env delta) (env I) (env f) ∧
    ∃ D ∈ env L, ∀ a ∈ env delta, ∀ x ∈ env I,
      ZFSet.pair a x ∈ env f → ZFSet.pair x D ∈ env r) ↔ _
  constructor
  · rintro ⟨function, D, hD, bounds⟩
    refine ⟨function, D, hD, ?_⟩
    intro a x entry
    have shape := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact bounds a shape.1 x shape.2 entry
  · rintro ⟨function, D, hD, bounds⟩
    exact ⟨function, D, hD, fun a _ x _ entry => bounds a x entry⟩

def rowPositionSequenceFormula {n} (L r I mu f : Fin n) : BoundedFormula n :=
  disj (rowPositionSequenceAtFormula L r I mu f)
    (exMem mu (rowPositionSequenceAtFormula L.succ r.succ I.succ 0 f.succ))

theorem truth_rowPositionSequenceFormula {n} (L r I mu f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rowPositionSequenceFormula L r I mu f) env ↔
      RowPositionSequenceCode (env L) (env r) (env I) (env mu) (env f) := by
  simp only [rowPositionSequenceFormula, truth_disj, truth_exMem, truth_rowPositionSequenceAtFormula]
  change (RowPositionSequenceAt (env L) (env r) (env I) (env mu) (env f) ∨
    ∃ delta ∈ env mu, RowPositionSequenceAt (env L) (env r) (env I) delta (env f)) ↔ _
  constructor
  · rintro (whole | ⟨delta, hdelta, code⟩)
    · exact ⟨env mu, ZFSet.mem_insert _ _, whole⟩
    · exact ⟨delta, ZFSet.mem_insert_of_mem _ hdelta, code⟩
  · rintro ⟨delta, hdelta, code⟩
    rcases ZFSet.mem_insert_iff.1 hdelta with equal | hdelta
    · exact Or.inl (equal ▸ code)
    · exact Or.inr ⟨delta, hdelta, code⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def rowPositionSequences (L r I mu : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (RowPositionSequenceCode L r I mu) (M.groundRelations mu I)

theorem mem_rowPositionSequences {L r I mu f : ZFSet.{u}} (ordinal : ordinalSetProperty mu) :
    f ∈ M.rowPositionSequences L r I mu ↔ f ∈ M.sets ∧ RowPositionSequenceCode L r I mu f := by
  rw [rowPositionSequences, ZFSet.mem_sep, M.mem_groundRelations]
  exact ⟨fun ⟨ground, code⟩ => ⟨ground.1, code⟩,
    fun ⟨ground, code⟩ => ⟨⟨ground, code.shape ordinal⟩, code⟩⟩

theorem rowPositionSequences_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {L r I mu : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hmu : mu ∈ M.sets) : M.rowPositionSequences L r I mu ∈ M.sets := by
  let formula : BoundedFormula 5 := BoundedFormula.rowPositionSequenceFormula 1 2 3 4 0
  let params := extend L (extend r (extend I (extend mu Fin.elim0)))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hL (Fin.cases hr (Fin.cases hI (Fin.cases hmu (fun i => Fin.elim0 i))))
  have ground := M.bounded_separation_mem separation formula params members
    (M.groundRelations_mem pairing unions powers separation hmu hI)
  have equal : ZFSet.sep (fun f => BoundedFormula.Truth formula (extend f params))
      (M.groundRelations mu I) = M.rowPositionSequences L r I mu := by
    apply ZFSet.ext
    intro f
    rw [ZFSet.mem_sep, rowPositionSequences, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_rowPositionSequenceFormula 1 2 3 4 0 _)
  exact equal ▸ ground

theorem rowPositionSequence_data {L r I mu f : ZFSet.{u}}
    (hL : L ∈ M.sets) (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu)
    (member : f ∈ M.rowPositionSequences L r I mu) :
    f ∈ M.sets ∧ ∃ delta ∈ M.sets, ordinalSetProperty delta ∧ delta ⊆ mu ∧
      ZFSet.IsFunc delta I f ∧ ∃ D ∈ L, D ∈ M.sets ∧
        ∀ a x, ZFSet.pair a x ∈ f → ZFSet.pair x D ∈ r := by
  obtain ⟨ground, delta, length, function, D, hD, bounds⟩ :=
    (M.mem_rowPositionSequences ordinal).1 member
  have hdelta : delta ∈ M.sets := (ZFSet.mem_insert_iff.1 length).elim
    (fun equal => equal ▸ hmu) (M.transitive hmu)
  have ordBound := rowPositionSequence_length ordinal length
  exact ⟨ground, delta, hdelta, ordBound.1, ordBound.2, function,
    D, hD, M.transitive hL hD, bounds⟩

theorem empty_mem_rowPositionSequences {L r I mu : ZFSet.{u}}
    (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu) (inhabited : L.Nonempty) :
    (∅ : ZFSet.{u}) ∈ M.rowPositionSequences L r I mu := by
  obtain ⟨D, hD⟩ := inhabited
  have length : (∅ : ZFSet.{u}) ∈ insert mu mu := by
    obtain ⟨o, rfl⟩ := (ordinalSetProperty_iff mu).1 ordinal
    rw [← ordinalCode_succ, ← ordinalCode_zero]
    exact (mem_ordinalCode_iff _ _).2 (Order.lt_succ_iff.2 zero_le)
  exact (M.mem_rowPositionSequences ordinal).2
    ⟨M.empty_mem ⟨mu, hmu⟩, ∅, length,
      ⟨ZFSet.empty_subset _, fun a ha => False.elim (ZFSet.notMem_empty a ha)⟩,
      D, hD, fun a x entry => False.elim (ZFSet.notMem_empty (ZFSet.pair a x) entry)⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def RowPositionBound (mu I r f D : ZFSet.{u}) : Prop :=
  f ⊆ ZFSet.prod mu I ∧ ∀ a x, ZFSet.pair a x ∈ f → ZFSet.pair x D ∈ r

namespace BoundedFormula

def rowPositionBoundFormula {n} (mu I r f D : Fin n) : BoundedFormula n :=
  .conj (relationBetweenFormula mu I f)
    (.allMem mu (.allMem I.succ
      (imp (pairMembershipFormula 1 0 f.succ.succ) (pairMembershipFormula 0 D.succ.succ r.succ.succ))))

theorem truth_rowPositionBoundFormula {n} (mu I r f D : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (rowPositionBoundFormula mu I r f D) env ↔
      RowPositionBound (env mu) (env I) (env r) (env f) (env D) := by
  simp only [rowPositionBoundFormula, Truth, truth_relationBetweenFormula, truth_imp,
    truth_pairMembershipFormula]
  change (env f ⊆ ZFSet.prod (env mu) (env I) ∧ ∀ a ∈ env mu, ∀ x ∈ env I,
    ZFSet.pair a x ∈ env f → ZFSet.pair x (env D) ∈ env r) ↔ _
  constructor
  · rintro ⟨shape,bound⟩
    refine ⟨shape,fun a x entry => ?_⟩
    have fields := ZFSet.pair_mem_prod.1 (shape entry)
    exact bound a fields.1 x fields.2 entry
  · rintro ⟨shape,bound⟩
    exact ⟨shape,fun a _ x _ entry => bound a x entry⟩

end BoundedFormula

theorem RowPositionBound.mono {L : Type u} [Preorder L] (s : Presentation L)
    {mu I f : ZFSet.{u}} {D E : L}
    (bound : RowPositionBound mu I s.conditionOrder f (s.encode D)) (le : D ≤ E) :
    RowPositionBound mu I s.conditionOrder f (s.encode E) := by
  refine ⟨bound.1,fun a x entry => ?_⟩
  have lower := bound.2 a x entry
  have hx : x ∈ s.carrier :=
    (ZFSet.pair_mem_prod.1 ((s.product s).subset_carrier (fun z => z.1 ≤ z.2) lower)).1
  obtain ⟨x,rfl⟩ := (s.mem_carrier x).1 hx
  exact (s.pair_mem_conditionOrder x E).2 (le_trans ((s.pair_mem_conditionOrder x D).1 lower) le)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowPositionSequence_bound {L r I mu f : ZFSet.{u}}
    (member : f ∈ M.rowPositionSequences L r I mu) :
    ∃ D ∈ L, RowPositionBound mu I r f D := by
  have data := ZFSet.mem_sep.1 member
  have shape := ((M.mem_groundRelations mu I f).1 data.1).2
  obtain ⟨delta,_,_,D,hD,bound⟩ := data.2
  exact ⟨D,hD,shape,bound⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
