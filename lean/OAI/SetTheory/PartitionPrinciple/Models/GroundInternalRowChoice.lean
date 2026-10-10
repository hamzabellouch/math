import OAI.SetTheory.PartitionPrinciple.Definability.GroundInternalRowSetZF
import OAI.SetTheory.PartitionPrinciple.Definability.GroundOutsideRowCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundSeparatedRowConditions

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (N : TransitiveGround.{u})

theorem exists_function_choosing_subsets
    (powers : Realize N.sets powerSet Fin.elim0)
    (separation : SeparationSchema N.sets)
    (choice : Realize N.sets SetFormula.choice Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ N.sets) :
    ∃ f ∈ N.sets, ∀ S ∈ N.sets, S ⊆ R → S.Nonempty →
      ∃ x ∈ S, ZFSet.pair S x ∈ f ∧ ∀ z ∈ S, ZFSet.pair S z ∈ f → z = x := by
  obtain ⟨W, hW, subsets⟩ := N.power_witness powers hR
  let A := ZFSet.sep (fun S => S.Nonempty) W
  have hA : A ∈ N.sets := by
    have selected := N.bounded_separation_mem separation (BoundedFormula.nonemptyFormula 0)
      Fin.elim0 (fun i => Fin.elim0 i) hW
    have eq : ZFSet.sep (fun S => BoundedFormula.Truth (BoundedFormula.nonemptyFormula 0)
        (extend S Fin.elim0)) W = A := by
      apply ZFSet.ext
      intro S
      simp only [A, ZFSet.mem_sep, BoundedFormula.truth_nonemptyFormula]
      rfl
    exact eq ▸ selected
  obtain ⟨f, hf, code⟩ := N.choice_witness choice hA
    (fun S hS => (ZFSet.mem_sep.1 hS).2)
  refine ⟨f, hf, ?_⟩
  intro S hS subset nonempty
  have member : S ∈ A := ZFSet.mem_sep.2 ⟨(subsets S hS).2 subset, nonempty⟩
  obtain ⟨x, chosen, unique⟩ := code.function.2 S member
  exact ⟨x, code.chosen S x chosen, chosen, fun z _ hz => unique z hz⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

theorem internalRow_not_choice
    (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
    (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    (unbounded : ∀ B : L, ∃ i : L, ¬ i ≤ B)
    (countableBound : ∀ A ∈ M.sets, A ⊆ s.carrier → M.groundEmbeddable A ZFSet.omega →
      ∃ D : L, ∀ i : L, s.encode i ∈ A → i ≤ D)
    (separate : ∀ B D : L, B ≤ D → ∃ g : G, g ∈ a.principalFix B ∧
      ∀ x : L, x ≤ D → x ≤ a.iso g D → x ≤ B)
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (groundChoice : Realize M.sets SetFormula.choice Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (order : s.conditionOrder ∈ M.sets) (graph : a.actionGraph s b ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
      (natSetCode 2) ZFSet.omega)
    let F := a.principalSupportFamily (⊥ : L) directed
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
        (natSetCode 2) ZFSet.omega)),
      H.GenericFor (formulaFamily (act.symmetricDomain c (M.nameDomain c) F)) →
      ZFRealization ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q}) →
      ¬ Realize ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q})
      SetFormula.choice Fin.elim0 := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act c F H generic zf allegedChoice
  let dom := act.symmetricDomain c (M.nameDomain c) F
  let N : TransitiveGround := ⟨dom.values {q | H.mem q}, dom.values_transitive {q | H.mem q}⟩
  have hRows := M.nonbottom_carrier_mem s separation hL
  have hTwo := M.natSetCode_mem separation infinite 2
  have carrier : c.carrier ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers
    separation infinite (M.prod_mem pairing unions powers separation hRows hC) hTwo
  have hRname : M.internalRowSetName s C hL ∈ dom.names :=
    ⟨M.internalRowSetName_mem s C pairing unions powers separation collection infinite hL hC,
      M.internalRowSetName_hs a s b C pairing unions powers separation infinite hL hC hG graph directed⟩
  have hR : Name.eval {q | H.mem q} (M.internalRowSetName s C hL) ∈ N.sets :=
    (dom.mem_values {q | H.mem q} _).2 ⟨_, hRname, rfl⟩
  have nPowers : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  obtain ⟨f, hf, selection⟩ := N.exists_function_choosing_subsets nPowers zf.2.1 allegedChoice hR
  obtain ⟨fname, hfname, rfl⟩ := (dom.mem_values {q | H.mem q} f).1 hf
  have hsF : HereditarilySymmetric act c F fname := hfname.2
  obtain ⟨B, fixedF⟩ := hsF.symmetric
  let Sname := M.internalOutsideRowsName s C hL B
  have hSname : Sname ∈ dom.names :=
    ⟨M.internalOutsideRowsName_mem s C pairing unions powers separation collection infinite hL hC order B,
      M.internalOutsideRowsName_hs a s b C pairing unions powers separation infinite hL hC hG graph directed B⟩
  have hS : Name.eval {q | H.mem q} Sname ∈ N.sets :=
    (dom.mem_values {q | H.mem q} _).2 ⟨Sname, hSname, rfl⟩
  obtain ⟨x, hx, chosen, unique⟩ := selection _ hS
    (M.eval_internalOutsideRowsName_subset s C hL B H)
    (M.eval_internalOutsideRowsName_nonempty s C hL B (unbounded B) H)
  obtain ⟨i, outside, rowValue⟩ := (M.mem_eval_internalOutsideRowsName s C hL B H x).1 hx
  let rowName := M.internalRowName s C hL i
  have hRowName : rowName ∈ dom.names :=
    ⟨M.internalRowName_mem s C pairing unions powers separation collection infinite hL hC i,
      M.internalRowName_hs a s b C pairing unions powers separation infinite hL hC hG graph directed i⟩
  let sn : dom.names := ⟨Sname, hSname⟩
  let xn : dom.names := ⟨rowName, hRowName⟩
  let fn : dom.names := ⟨fname, hfname⟩
  let env := extend sn (extend xn (extend fn Fin.elim0))
  have rowEq : Name.eval {q | H.mem q} rowName = x :=
    (M.eval_internalRowName s C hL i H).trans rowValue
  have truth : Realize (dom.values {q | H.mem q})
      (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula (evalAssignment {q | H.mem q} env) := by
    apply (realize_uniqueFiber_values dom {q | H.mem q} 0 1 2 env).2
    change Name.eval {q | H.mem q} rowName ∈ Name.eval {q | H.mem q} Sname ∧
      ZFSet.pair (Name.eval {q | H.mem q} Sname) (Name.eval {q | H.mem q} rowName) ∈
        Name.eval {q | H.mem q} fname ∧
      ∀ z ∈ Name.eval {q | H.mem q} Sname,
        ZFSet.pair (Name.eval {q | H.mem q} Sname) z ∈ Name.eval {q | H.mem q} fname →
          z = Name.eval {q | H.mem q} rowName
    rw [rowEq]
    exact ⟨hx, chosen, unique⟩
  obtain ⟨p, _, forced⟩ := (forcing_truth dom H generic
    (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula env).1 truth
  let used := rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p)
  obtain ⟨hUsed, usedSmall⟩ := M.countablePartialFunctions_rowSupport pairing unions powers separation
    infinite groundChoice hRows hC hTwo (SetMembers.raw_mem p)
  have usedSubset : used ⊆ s.carrier := by
    intro z hz
    exact ((s.mem_nonbottom_carrier z).1 (rowUsedRows_subset s.nonbottom.carrier C
      (natSetCode 2) (SetMembers.raw p) hz)).1
  obtain ⟨D₀, bound₀⟩ := countableBound used hUsed usedSubset usedSmall
  obtain ⟨D₁, first, containsB⟩ := directed D₀ B
  obtain ⟨D, second, containsI⟩ := directed D₁ i.val
  have bound : ∀ j : {j : L // j ≠ ⊥}, s.encode j.val ∈ used → j.val ≤ D :=
    fun j hj => le_trans (bound₀ j.val hj) (le_trans first second)
  obtain ⟨g, fixed, overlap⟩ := separate B D (le_trans containsB second)
  obtain ⟨r, _, rp, rgp⟩ := M.internalRowAction_common_extension_of_separated a s b C pairing unions
    powers separation infinite hL hC hG graph groundChoice g B D fixed overlap p bound
  obtain ⟨K, kr, groundGeneric, _, symmetricGeneric⟩ :=
    M.exists_joint_generic c act F small carrier r
  have maps := M.conditionMapFamily_mem_of_actionGraph act c b pairing unions powers separation
    collection carrier hG (M.internalRowActionGraph_mem a s b C pairing unions powers separation
      infinite hL hC hG graph)
  have groundClosed : ∀ g τ, τ ∈ (M.nameDomain c).names → act.act c g τ ∈ (M.nameDomain c).names :=
    M.act_mem c act b pairing unions powers separation collection carrier maps
  have closed : ∀ g τ, τ ∈ dom.names → act.act c g τ ∈ dom.names :=
    fun g τ hτ => act.symmetricDomain_translated c (M.nameDomain c) F groundClosed g hτ
  have equal := act.uniqueFiber_eq_of_fixed_names c dom closed g sn xn fn
    (M.internalOutsideRowsName_action a s b C pairing unions powers separation infinite hL hC hG graph B g fixed)
    (fixedF fixed) p forced K symmetricGeneric (K.upward kr rp) (K.upward kr rgp)
  change Name.eval {q | K.mem q} (M.internalRowName s C hL i) =
    Name.eval {q | K.mem q} (act.act c g (M.internalRowName s C hL i)) at equal
  rw [M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph,
    M.eval_internalRowName, M.eval_internalRowName] at equal
  have moved : a.iso g i.val ≠ i.val := a.moved_ne_of_separated g B D i.val overlap containsI outside
  have distinct : s.encode i.val ≠ s.encode (a.iso g i.val) :=
    fun eq => moved (s.injective eq).symm
  exact M.binaryGenericRow_ne pairing unions powers separation infinite groundChoice hRows hC
    (s.nonbottom.encode_mem i) (s.nonbottom.encode_mem (a.nonbottom.iso g i)) distinct
    uncountable K groundGeneric equal

theorem exists_internalRow_ZF_not_choice
    (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
    (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    (unbounded : ∀ B : L, ∃ i : L, ¬ i ≤ B)
    (countableBound : ∀ A ∈ M.sets, A ⊆ s.carrier → M.groundEmbeddable A ZFSet.omega →
      ∃ D : L, ∀ i : L, s.encode i ∈ A → i ≤ D)
    (separate : ∀ B D : L, B ≤ D → ∃ g : G, g ∈ a.principalFix B ∧
      ∀ x : L, x ≤ D → x ≤ a.iso g D → x ≤ B)
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (groundChoice : Realize M.sets SetFormula.choice Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (order : s.conditionOrder ∈ M.sets) (graph : a.actionGraph s b ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
      (natSetCode 2) ZFSet.omega)) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
      (natSetCode 2) ZFSet.omega)
    let F := a.principalSupportFamily (⊥ : L) directed
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C)
        (natSetCode 2) ZFSet.omega)),
      H.mem p ∧ H.GenericFor (M.codedFamily c) ∧
      H.GenericFor (formulaFamily (M.nameDomain c)) ∧
      H.GenericFor (formulaFamily (act.symmetricDomain c (M.nameDomain c) F)) ∧
      M.sets ⊆ (act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q} ∧
      ZFRealization ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q}) ∧
      ¬ Realize ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q})
      SetFormula.choice Fin.elim0 := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  obtain ⟨H, hp, ground, ordinary, symmetric, includes, zf, _, _, _, _⟩ :=
    M.exists_internalRow_ZF_with_rowSet a s b C directed small pairing unions powers separation
      collection infinite groundChoice hL hC hG order graph uncountable p
  exact ⟨H, hp, ground, ordinary, symmetric, includes, zf,
    M.internalRow_not_choice a s b C directed unbounded countableBound separate small pairing
      unions powers separation collection infinite groundChoice hL hC hG order graph uncountable
      H symmetric zf⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
