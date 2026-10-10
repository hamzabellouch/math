import Mathlib
import OAI.SetTheory.PartitionConsistency.Construction.BlockTowers
import OAI.SetTheory.PartitionConsistency.Models.CodeCardinals
import OAI.SetTheory.PartitionConsistency.Models.GermSelectors

namespace OAI

/-! ## CellDescent -/

namespace PartitionConsistency.ConservativeMonoids
universe u
open DiagramOrder
noncomputable section

namespace Cell
variable {M : Object.{u}} (d : Cell M)

/-- The old-input gate rule for the literal cells. A merger has no new old
divisors; a probe's first-letter gate consumes all letters on an old input. -/
theorem descent_gate (w : d.extension) (hw : ∀ x, d.inclusion x ≠ w)
    (hb : ∃ y, w ∣ d.inclusion y) :
    ∃ g : M, w ∣ d.inclusion g ∧ (∀ y, w ∣ d.inclusion y → g ∣ y) ∧
      ∀ x, d.inclusion g ∣ w * d.inclusion x → ∃ y, w * d.inclusion x = d.inclusion y := by
  cases d with
  | inl d =>
    let A := d.path.alphabet d.e_ne_one
    change ProbeAlgebra.Word A d.b at w
    change ∀ x, ProbeAlgebra.Word.old A d.b x ≠ w at hw
    change ∃ y, w ∣ ProbeAlgebra.Word.old A d.b y at hb
    change ∃ g : M, w ∣ ProbeAlgebra.Word.old A d.b g ∧
      (∀ y, w ∣ ProbeAlgebra.Word.old A d.b y → g ∣ y) ∧
      ∀ x, ProbeAlgebra.Word.old A d.b g ∣ w * ProbeAlgebra.Word.old A d.b x →
        ∃ y, w * ProbeAlgebra.Word.old A d.b x = ProbeAlgebra.Word.old A d.b y
    obtain ⟨y,hy⟩ := hb
    cases hs : ProbeAlgebra.Word.head A d.b w with
    | none =>
      obtain ⟨x,hx⟩ := (ProbeAlgebra.Word.head_eq_none_iff A d.b w).mp hs
      exact (hw x hx.symm).elim
    | some s =>
      obtain ⟨g,hg⟩ := ProbeAlgebra.Word.exists_gate_of_exit A d.b
        (d.path.oldIntersections d.e_ne_one d.b M.joins) w hs hy (by intro h; cases h)
      exact ⟨g,ProbeAlgebra.Word.Gate.dvd A d.b hg,
        fun y hy => (ProbeAlgebra.Word.Gate.dvd_old_iff A d.b hg y).mp hy,
        fun x hx => ProbeAlgebra.Word.Gate.append_old A d.b hg hs x hx⟩
  | inr d =>
    obtain ⟨y,z,hz⟩ := hb
    obtain ⟨x,_,hx,_,_⟩ := MergerAlgebra.Word.factors_of_old hz.symm
    exact (hw x hx.symm).elim

end Cell
namespace Attachment
variable {T : Object.{u}} {S R : Subobject T} (d : Attachment S R)

include d in
/-- The same gate statement holds in the final monoid, by conservation of
divisibility, including for final right factors not yet present at this cut. -/
theorem gateStep : OldGateStep S.submonoid R.submonoid := by
  intro w hw hn hb
  let w₀ := d.equiv.symm (⟨w,hw⟩ : R.object)
  have hew : d.embedding w₀ = w := congrArg Subtype.val (d.equiv.apply_symm_apply ⟨w,hw⟩)
  have hnew : ∀ x, d.cell.inclusion x ≠ w₀ := by
    intro x hx
    apply hn
    have hh := congrArg d.embedding hx
    rw [d.embedding_old,hew] at hh
    exact hh ▸ x.property
  have hbound : ∃ y, w₀ ∣ d.cell.inclusion y := by
    obtain ⟨y,hy,hwy⟩ := hb
    refine ⟨⟨y,hy⟩,(d.embedding.conservative.dvd_iff _ _).mp ?_⟩
    erw [hew,d.embedding_old]
    exact hwy
  obtain ⟨g,hg,hleast,hinput⟩ := d.cell.descent_gate w₀ hnew hbound
  refine ⟨g.val,g.property,?_,?_,?_⟩
  · simpa only [hew,d.embedding_old] using d.embedding.map_dvd hg
  · intro y hy hwy
    have hh : w₀ ∣ d.cell.inclusion (⟨y,hy⟩ : S.object) :=
      (d.embedding.conservative.dvd_iff _ _).mp (by
        erw [d.embedding_old,hew]
        exact hwy)
    exact S.inclusion.map_dvd (hleast _ hh)
  · intro x hx hgd
    have hh : d.cell.inclusion g ∣ w₀ * d.cell.inclusion (⟨x,hx⟩ : S.object) :=
      (d.embedding.conservative.dvd_iff _ _).mp (by
        erw [d.embedding.map_mul,d.embedding_old,d.embedding_old,hew]
        exact hgd)
    obtain ⟨y,hy⟩ := hinput _ hh
    have hh := congrArg d.embedding hy
    erw [d.embedding.map_mul,d.embedding_old,d.embedding_old,hew] at hh
    exact hh.symm ▸ y.property

end Attachment

namespace CellTower
variable {T : Object.{u}} {J : Type u} [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J] (D : CellTower T J) (n : ℕ → T) (A : Set (ℕ × T))

/-- Finite old-gate descent in a rearranged literal cell tower. Right factors
between base indices belong to the base by its conservative closure. -/
theorem finite_descent
    (hn : ∀ i, n i ∈ (D.stage ⊥).submonoid)
    (hbound : ∀ p ∈ A, ∃ N, p.2 ∣ n N)
    (hreplace : ∀ p ∈ A, ∀ N, ∃ l' d,
      (l',p.2*d) ∈ A ∧ p.1 ≤ l' ∧ n p.1*d = n l' ∧ n N ∣ p.2*d)
    (α : J) (p : ℕ × T) (hp : p ∈ A) (hα : p.2 ∈ (D.stage α).submonoid) :
    ∃ q ∈ A, q.2 ∈ (D.stage ⊥).submonoid ∧ Relation.ReflTransGen (Replaces n A) p q := by
  induction α using SuccOrder.limitRecOn generalizing p with
  | isMin α hmin => exact ⟨p,hp,hmin.eq_bot ▸ hα,Relation.ReflTransGen.refl⟩
  | succ α hne ih =>
    by_cases ho : p.2 ∈ (D.stage α).submonoid
    · exact ih p hp ho
    rcases D.step α with he | hcell
    · exact (ho (he ▸ hα)).elim
    · obtain ⟨N,hN⟩ := hbound p hp
      have hnN : n N ∈ (D.stage α).submonoid := D.mono bot_le (hn N)
      obtain ⟨g,_,_,hleast,hgate⟩ := hcell.some.gateStep p.2 hα ho ⟨n N,hnN,hN⟩
      obtain ⟨l',d,hA',hll',hd,hNd⟩ := hreplace p hp N
      have hdo : d ∈ (D.stage α).submonoid := D.mono bot_le (by
        rw [← ConservativeHull.factor_eq _ _ d hd]
        exact (D.stage ⊥).factors _ (hn _) _ (hn _))
      have hnew : p.2*d ∈ (D.stage α).submonoid := hgate d hdo ((hleast _ hnN hN).trans hNd)
      obtain ⟨q,hqA,hq0,hpath⟩ := ih (l',p.2*d) hA' hnew
      exact ⟨q,hqA,hq0,(Relation.ReflTransGen.single (show Replaces n A p (l',p.2*d) from
        ⟨hp,hA',hll',d,hd,rfl⟩)).trans hpath⟩
  | isSuccLimit α hlim ih =>
    obtain ⟨β,hβα,hmem⟩ := D.continuous α hlim p.2 hα
    exact ih β hβα p hp hmem

theorem finite_descent_terminal
    (hn : ∀ i, n i ∈ (D.stage ⊥).submonoid)
    (hbound : ∀ p ∈ A, ∃ N, p.2 ∣ n N)
    (hreplace : ∀ p ∈ A, ∀ N, ∃ l' d,
      (l',p.2*d) ∈ A ∧ p.1 ≤ l' ∧ n p.1*d = n l' ∧ n N ∣ p.2*d)
    (p : ℕ × T) (hp : p ∈ A) :
    ∃ q ∈ A, q.2 ∈ (D.stage ⊥).submonoid ∧ Relation.ReflTransGen (Replaces n A) p q := by
  apply D.finite_descent n A hn hbound hreplace ⊤ p hp
  rw [D.terminal]
  trivial

end CellTower
end
end PartitionConsistency.ConservativeMonoids


/-! ## GermActual -/

namespace PartitionConsistency.MonoidConstruction.Saturation
universe u
open ConservativeMonoids DiagramOrder
noncomputable section
variable (M : MonoidConstruction.Object.{u}) (K : Type u) [Nonempty K]

/-- The fully executed construction still begins with the given countable
base; flattening only inserts identity cuts between rounds. -/
theorem cells_bottom_countable [Countable M] :
    (((cells M K).stage ⊥).submonoid : Set (forgetMargins.obj (target M K))).Countable := by
  change ((blockStage M K (⊥ : RoundOrdinal) ⊥).submonoid : Set (forgetMargins.obj (target M K))).Countable
  rw [blockStage_base]
  let : Countable ((tower M K).obj ⊥) := (isoEquiv (botIso M K)).injective.countable
  exact Set.countable_range (fromStage M K ⊥)

end
end PartitionConsistency.MonoidConstruction.Saturation

namespace PartitionConsistency.LocalDiagramSystem.Vertex.Chain
universe u
open DiagramOrder DiagramForcing ConservativeMonoids
noncomputable section
variable {M : Object.{u}} {I : Type u} {q : Diagram M I} {v : Vertex q}
variable (C : Chain v) {J : Type u} [LinearOrder J] [OrderBot J] [OrderTop J]
  [SuccOrder J] [WellFoundedLT J]

/-- Finite gate descent, now applied in a literal rearrangement of the
constructed monoid, bounds the actual germs by countably many alignments. -/
theorem countable_quotient_of_cells (D : CellTower M J)
    (hbot : ((D.stage ⊥).submonoid : Set M).Countable) :
    Countable (componentStabilizer M.joins v ⧸ C.tailFixer M.joins) := by
  obtain ⟨E,hbase,hn⟩ := D.countable_reordering hbot (Set.range C.index) (Set.countable_range _)
  have halign : ∀ π : componentStabilizer M.joins v,
      ∃ p : ℕ × (E.stage ⊥).submonoid, (p.1,p.2.val) ∈ C.Alignments M.joins π := by
    intro π
    obtain ⟨p,hp⟩ := C.alignments_nonempty M.joins π
    obtain ⟨a,ha,hmem,_⟩ := E.finite_descent_terminal C.index (C.Alignments M.joins π)
      (fun i => hn (Set.mem_range_self i))
      (fun p hp => C.alignment_bounded M.joins π hp)
      (fun p hp N => C.alignment_replacement M.joins π hp N) p hp
    exact ⟨(a.1,⟨a.2,hmem⟩),ha⟩
  let chooseCode (c : componentStabilizer M.joins v ⧸ C.tailFixer M.joins) :
      ℕ × (E.stage ⊥).submonoid := (halign c.out).choose
  have hcode (c : componentStabilizer M.joins v ⧸ C.tailFixer M.joins) :
      ((chooseCode c).1,(chooseCode c).2.val) ∈ C.Alignments M.joins c.out :=
    (halign c.out).choose_spec
  have hinj : Function.Injective chooseCode := by
    intro c e he
    have hc := hcode c
    rw [he] at hc
    have hh := C.coset_eq_of_alignment M.joins c.out e.out hc (hcode e)
    simpa only [QuotientGroup.mk'_apply,Quotient.out_eq] using hh
  let : Countable (E.stage ⊥).submonoid := hbase.to_subtype
  exact hinj.countable

end
end PartitionConsistency.LocalDiagramSystem.Vertex.Chain

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction LocalDiagramSystem
noncomputable section

/-- Countable germs for every local component in the actual final monoid;
no rearrangement, countable-base, or gate assumptions remain. -/
theorem countable_germs {q : DiagramForcing.Diagram T I} {v : Vertex q}
    (C : Vertex.Chain v) :
    Countable (Vertex.componentStabilizer T.joins v ⧸ C.tailFixer T.joins) := by
  let : Countable Base.object := show Countable (Multiplicative ℕ) from inferInstance
  exact LocalDiagramSystem.Vertex.Chain.countable_quotient_of_cells
    (M := ConservativeMonoids.forgetMargins.obj T) C (Saturation.cells Base.object K)
    (Saturation.cells_bottom_countable Base.object K)

end
end PartitionConsistency.ConcreteSystem


/-! ## ConcreteSelector -/

/-! The selector for the actual saturated monoid and the prescribed Cohen
length. This supplies all countability/regularity hypotheses from the
construction, rather than leaving them as properties of an abstract action. -/
namespace PartitionConsistency.ConcreteSystem
open CardinalParameters DiagramForcing LocalDiagramSystem TailSelector
noncomputable section

instance : Nonempty κ := Ordinal.nonempty_toType_iff.mpr
  Cardinal.isRegular_aleph_one.ord_pos.ne'

theorem κ_countable_bound (f : ℕ → κ) : ∃ a : κ, ∀ n, f n < a :=
  CardinalParameters.countable_bound Cardinal.isRegular_aleph_one
    Cardinal.aleph0_lt_aleph_one f

theorem κ_initial_countable (a : κ) : (Set.Iio a).Countable := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply Cardinal.lt_aleph_one_iff.mp
  simpa only [κ,Cardinal.mk_toType,Cardinal.card_ord] using
    Cardinal.mk_Iio_lt a (by simp [κ])

variable {q : Diagram T I} {v : Vertex q} (C : Vertex.Chain v)

/-- Each actual component chain has a dense set of conditions at which the
least distinguishing-bound construction selects one of its countably many
residual symmetries. -/
theorem component_selector_dense (p : CohenForcing.Condition I κ) :
    ∃ r, r ≤ p ∧ (C.tailData T.joins).Good r := by
  let : Countable (C.tailData T.joins).Cosets := countable_germs C
  exact (C.tailData T.joins).good_dense κ_countable_bound κ_initial_countable p

/-- The selected coset is unique on compatible conditions and transforms
by left multiplication when the Cohen condition is moved. -/
theorem component_selected_covariant (p : CohenForcing.Condition I κ)
    (c : (C.tailData T.joins).Cosets)
    (hp : (C.tailData T.joins).Selected p c)
    (σ : Vertex.componentStabilizer T.joins v) :
    (C.tailData T.joins).Selected (p.permute σ.val.val)
      ((σ : (C.tailData T.joins).Cosets) * c) :=
  hp.permute (C.tailData T.joins) σ

end
end PartitionConsistency.ConcreteSystem


/-! ## ConcreteCode -/

/-! The exact cardinality of the *actual ordinal name* for the persistent
least-code ordering in the executed concrete construction. No assertion of
genericity over an uncountable collection of ambient sets is used. -/
namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing ForcingQuotient LocalDiagramSystem SetForcingNames.SymmetricSystem
noncomputable section

/-- Every possible order type has cardinality exactly the label-fiber
cardinal. The hypotheses are just the outside-list condition at which the
quotient construction is made, and a stronger initial Cohen condition. -/
theorem code_ordinalType_cardinal {q : Diagram T I} {v : Vertex q} (C : Vertex.Chain v)
    (b : T) (hb : b ≠ 1) (E : S.Name)
    (hE : ∀ π ∈ SupportFilter.Fix (q.sub T.e).range, π • E = E)
    (t : Diagram T I) (ht : t.sub b = q.sub T.e)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : P, z ≤ (d₀,t) →
      ¬ S.atomic.MemF z (labelClass aleph0_le_μ (posetCode κ) E j)
        (localList aleph0_le_μ (posetCode κ) cardinal_T.le (q.sub T.e)))
    (d : CohenForcing.Condition I κ) (hd : d ≤ d₀.restrict (q.sub T.e).range)
    (θ : Ordinal)
    (hθ : S.atomic.EqF ((d,v.diagram) : P)
      (ChainCode.ordinalType aleph0_le_μ (posetCode κ) cardinal_T.le size_lt finiteMergers
        T.joins E (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE) C)
      (Name.check θ.toZFSet)) : θ.card = μ := by
  apply le_antisymm
  · exact ChainCode.ordinalType_cardinal_le aleph0_le_μ (posetCode κ) cardinal_T.le
      size_lt finiteMergers T.joins E
      (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE) C μ_countable_power
      (cardinal_κ ▸ aleph_one_le_μ) T.e complement_cardinal d θ hθ
  · obtain ⟨m,_,hm,hi⟩ := Saturation.square_ideal_probes Base.object K v.index b hb v.ideal
    have hl := ChainCode.ordinalType_lower_count aleph0_le_μ (posetCode κ) cardinal_T.le
      size_lt finiteMergers T.joins C T.e b m (fun i => (hm i).1)
      (fun i => (hm i).2.2.1) (fun i => (hm i).2.2.2) hi E hE t ht d₀ hd₀ j hj hout d hd θ hθ
    rw [cardinal_K] at hl
    by_contra hn
    have hs : θ.card ≤ Cardinal.continuum := Order.lt_succ_iff.mp (lt_of_not_ge hn)
    have hc : μ ≤ Cardinal.continuum := hl.trans
      ((mul_le_mul' hs le_rfl).trans_eq (Cardinal.mul_eq_self Cardinal.aleph0_le_continuum))
    exact (Order.lt_succ Cardinal.continuum).not_ge hc

end
end PartitionConsistency.ConcreteSystem


/-! ## ConcretePreAssignment -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing ForcingQuotient LocalDiagramSystem SetForcingNames.SymmetricSystem
noncomputable section

/-- The literal common label subset has the advertised cardinality, not
merely an abstract isomorphic fiber. -/
theorem labelFiberSet_cardinal {q : Diagram T I} (v : Vertex q) :
    Cardinal.mk (labelFiberSet v) = μ := by
  let f : (labelSystem (M := T) (I := I)).vertexFiber v → I := fun x => x.val.val
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  have he : (labelSystem (M := T) (I := I)).vertexFiber v ≃ labelFiberSet v :=
    Equiv.ofInjective f hf
  rw [← Cardinal.mk_congr he]
  exact Saturation.labelFiber_cardinal Base.object K aleph_one_le_μ μ_countable_power
    (by change Cardinal.mk (Multiplicative ℕ) ≤ μ; simpa using aleph0_le_μ) cardinal_K v

/-- The count needed for assigning the preliminary ranks is supplied by the
executed construction and the outside-list condition. -/
theorem preliminary_ordinalCount {q : Diagram T I} {v : Vertex q} (C : Vertex.Chain v)
    (b : T) (hb : b ≠ 1) (E : S.Name)
    (hE : ∀ π ∈ SupportFilter.Fix (q.sub T.e).range, π • E = E)
    (t : Diagram T I) (ht : t.sub b = q.sub T.e)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : P, z ≤ (d₀,t) →
      ¬ S.atomic.MemF z (labelClass aleph0_le_μ (posetCode κ) E j)
        (localList aleph0_le_μ (posetCode κ) cardinal_T.le (q.sub T.e)))
    (d : CohenForcing.Condition I κ) (hd : d ≤ d₀.restrict (q.sub T.e).range) :
    ChainCode.OrdinalCount aleph0_le_μ (posetCode κ) cardinal_T.le size_lt finiteMergers
      T.joins E (supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE) C d := by
  intro e hed θ he
  rw [labelFiberSet_cardinal v]
  exact code_ordinalType_cardinal C b hb E hE t ht d₀ hd₀ j hj hout e (hed.trans hd) θ he

end
end PartitionConsistency.ConcreteSystem


/-! ## ConcreteQuotient -/

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing ForcingQuotient LocalDiagramSystem SetForcingNames.SymmetricSystem
noncomputable section

/-- All count and selector hypotheses of the equivariant assignment are
satisfied by the executed construction. The condition used for the graph
retains exactly the Cohen information in the smaller root. -/
theorem quotient_bijection_above (q : Diagram T I) (b : T) (hb : b ≠ 1) (E : S.Name)
    (hE : ∀ π ∈ SupportFilter.Fix (q.sub T.e).range, π • E = E)
    (t : Diagram T I) (ht : t.sub b = q.sub T.e)
    (d₀ : CohenForcing.Condition I κ) (hd₀ : d₀.support ⊆ t.range)
    (j : I) (hj : j ∈ t.range)
    (hout : ∀ z : P, z ≤ (d₀,t) →
      ¬ S.atomic.MemF z (labelClass aleph0_le_μ (posetCode κ) E j)
        (localList aleph0_le_μ (posetCode κ) cardinal_T.le (q.sub T.e))) :
    ∃ f : S.Name, S.Forces ![f,labelSet aleph0_le_μ (posetCode κ),
      quotientName aleph0_le_μ (posetCode κ) E] ((d₀.restrict (q.sub T.e).range,q) : P)
      ((SetLanguage.surjection 0 1 2).conj (SetLanguage.injection 0 1 2)) := by
  let dbase := d₀.restrict (q.sub T.e).range
  have hroot := supported_mono aleph0_le_μ (q.self_le_sub T.e) E hE
  refine ⟨ChainCode.assignmentGraph aleph0_le_μ (posetCode κ) cardinal_T.le size_lt
    finiteMergers T.joins T.margin E hroot,?_⟩
  apply ChainCode.assignmentGraph_bijection aleph0_le_μ (posetCode κ) cardinal_T.le size_lt
    finiteMergers T.joins T.margin E hroot T.e complement_cardinal dbase
    (fun a d => component_selector_dense (Vertex.orbitChain T.joins T.margin a) d)
    (fun d hd a g => ?_) (posetCode_injective κ)
  apply preliminary_ordinalCount (Vertex.orbitChain T.joins T.margin a)
    b hb E hE t ht d₀ hd₀ j hj hout
  have hfix : dbase.permute g.val = dbase :=
    CohenForcing.Condition.permute_eq_of_fixes_support g.val dbase (fun k hk =>
      (SupportFilter.mem_Fix _ _).mp g.property k
        (Diagram.range_antitone (q.self_le_sub T.e) (d₀.support_restrict_subset _ hk)))
  change d.permute g.val ≤ dbase
  rw [← hfix]
  exact (CohenForcing.Condition.permuteOrderIso g.val).monotone hd

/-- Densely below every condition which forces a quotient to be nonwellorderable,
there is an actual supported graph bijecting the label set with that quotient.
There is no inaccessible-cardinal or quotient-classification premise. -/
theorem nonwellorderable_quotient_bijection (E : S.Name) (s : P)
    (hno : S.Forces ![quotientName aleph0_le_μ (posetCode κ) E] s
      (SetLanguage.wellorderable 0).neg) :
    ∃ r, r ≤ s ∧ ∃ f : S.Name,
      S.Forces ![f,labelSet aleph0_le_μ (posetCode κ),
        quotientName aleph0_le_μ (posetCode κ) E] r
        ((SetLanguage.surjection 0 1 2).conj (SetLanguage.injection 0 1 2)) := by
  obtain ⟨emb⟩ := (Cardinal.le_def T I).mp size_lt.le
  let : Nonempty (Diagram T I) := ⟨⟨emb⟩⟩
  obtain ⟨a,has⟩ := exists_condition_below s
  obtain ⟨J,hJ,hfix⟩ := name_support aleph0_le_μ E
  have hU : Cardinal.mk ↥(J ∪ a.1.support) ≤ Cardinal.mk T := by
    rw [cardinal_T]
    exact (Cardinal.mk_union_le _ _).trans
      ((add_le_add hJ (a.1.cardinal_support.trans aleph0_le_μ)).trans_eq
        (Cardinal.add_eq_self aleph0_le_μ))
  obtain ⟨p,hp,hcover⟩ := Diagram.extend_through size_lt T.e complement_cardinal a.2 hU
  have hpa : p ≤ a.2 := ⟨T.e,hp⟩
  have hps : ((a.1,p) : P) ≤ s :=
    (WithTop.coe_le_coe.mpr (show (a.1,p) ≤ a from ⟨le_rfl,hpa⟩)).trans has
  have hEp : ∀ π ∈ SupportFilter.Fix p.range, π • E = E := by
    intro π hπ
    exact hfix π ((SupportFilter.mem_Fix _ _).mpr (fun k hk =>
      (SupportFilter.mem_Fix _ _).mp hπ k (hcover (Or.inl hk))))
  obtain ⟨d,hd,t,b,hb,hbn,hdt,j,hjt,hout⟩ := outsideClassSet_denseBelow
    aleph0_le_μ (posetCode κ) cardinal_T.le size_lt T.e complement_cardinal p E hEp a.1
      (S.atomic.forceFormula_mono hps hno) a.1 le_rfl
  obtain ⟨q,hq,_⟩ := Diagram.extend_through size_lt T.e complement_cardinal p
    (J := ∅) (by simp)
  have hroot : ∀ π ∈ SupportFilter.Fix (q.sub T.e).range, π • E = E := by
    rwa [hq]
  obtain ⟨f,hf⟩ := quotient_bijection_above q b hbn E hroot t (hb.trans hq.symm)
    d hdt j hjt (by simpa only [S,hq] using hout)
  have hr : d.restrict (q.sub T.e).range ≤ a.1 := by
    intro z hz
    exact ⟨hd hz,by
      rw [hq]
      exact hcover (Or.inr ((CohenForcing.Condition.mem_support _ _).mpr
        ⟨z.1.2,z.2,hz⟩))⟩
  exact ⟨(d.restrict (q.sub T.e).range,q),
    (WithTop.coe_le_coe.mpr (show (d.restrict (q.sub T.e).range,q) ≤ (a.1,p)
      from ⟨hr,⟨T.e,hq⟩⟩)).trans hps,f,hf⟩

end
end PartitionConsistency.ConcreteSystem

end OAI
