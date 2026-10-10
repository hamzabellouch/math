import OAI.SetTheory.PartitionPrinciple.Definability.GroundRegularFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundProjectedRowChooserWitnesses

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps
universe u v

namespace Name

theorem rank_eval_le_code_rank {P : Type u} {s : Presentation P} (H : Set P) (tau : Name s) :
    ZFSet.rank (eval H tau) ≤ ZFSet.rank tau.val := by
  induction tau using inductionOn with
  | step tau ih =>
    apply ZFSet.rank_le_iff.2
    intro x hx
    obtain ⟨sigma, p, entry, _active, rfl⟩ := (mem_eval H tau x).1 hx
    exact (ih sigma p entry).trans_lt (entry_rank_lt entry)

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem ordinalCode_rank_mem {x : ZFSet.{u}} (hx : x ∈ M.sets) :
    ordinalCode (ZFSet.rank x) ∈ M.sets := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have witnesses : ∀ y ∈ x, ∃ beta ∈ M.sets,
        Realize M.sets (cumulativeRankValueFormula 0 1)
          (extend y (extend beta Fin.elim0)) := by
      intro y hy
      have hyM := M.transitive hx hy
      have hRank := ih y hy hyM
      refine ⟨ordinalCode (ZFSet.rank y), hRank, ?_⟩
      exact (M.realize_cumulativeRankValueFormula pairing unions powers separation collection
        0 1 _ (Fin.cases hyM (Fin.cases hRank (fun i => Fin.elim0 i)))).2 rfl
    obtain ⟨B, hB, collected⟩ := M.collection_witness collection
      (cumulativeRankValueFormula 0 1) Fin.elim0 (fun i => Fin.elim0 i) hx witnesses
    let O := ZFSet.sep ordinalSetProperty B
    have hO : O ∈ M.sets := by
      have selected := M.bounded_separation_mem separation (BoundedFormula.ordinalFormula 0)
        Fin.elim0 (fun i => Fin.elim0 i) hB
      have equal : ZFSet.sep (fun z => BoundedFormula.Truth
          (BoundedFormula.ordinalFormula 0) (extend z Fin.elim0)) B = O := by
        apply ZFSet.ext
        intro z
        rw [ZFSet.mem_sep, ZFSet.mem_sep]
        apply and_congr Iff.rfl
        exact (BoundedFormula.truth_ordinalFormula 0 _).trans (ordinalSetProperty_iff z).symm
      exact equal ▸ selected
    have ordinals : ∀ beta ∈ O, ordinalSetProperty beta := fun _ member => (ZFSet.mem_sep.1 member).2
    let U := ZFSet.sUnion O
    have hU : U ∈ M.sets := M.union_mem unions hO
    have ordinalU : ordinalSetProperty U := ordinalSetProperty_sUnion ordinals
    have bound : ZFSet.rank x ≤ Order.succ (ZFSet.rank U) := by
      apply ZFSet.rank_le_iff.2
      intro y hy
      obtain ⟨beta, hb, rankValue⟩ := collected y hy
      have equal : beta = ordinalCode (ZFSet.rank y) :=
        (M.realize_cumulativeRankValueFormula pairing unions powers separation collection
          0 1 _ (Fin.cases (M.transitive hx hy)
            (Fin.cases (M.transitive hB hb) (fun i => Fin.elim0 i)))).1 rankValue
      have member : ordinalCode (ZFSet.rank y) ∈ O :=
        ZFSet.mem_sep.2 ⟨equal ▸ hb, ordinalSetProperty_ordinalCode _⟩
      have subset : ordinalCode (ZFSet.rank y) ⊆ U :=
        fun z hz => ZFSet.mem_sUnion.2 ⟨_, member, hz⟩
      have rankLe : ZFSet.rank y ≤ ZFSet.rank U := by
        simpa only [rank_ordinalCode] using ZFSet.rank_mono subset
      exact rankLe.trans_lt (Order.lt_succ _)
    have hSucc : insert U U ∈ M.sets := M.insert_mem pairing unions hU hU
    have hNext : insert (insert U U) (insert U U) ∈ M.sets :=
      M.insert_mem pairing unions hSucc hSucc
    apply M.transitive hNext
    rw [ordinalSetProperty_eq_code_rank U ordinalU, ← ordinalCode_succ, ← ordinalCode_succ,
      mem_ordinalCode_iff]
    exact Order.lt_succ_iff.2 bound

theorem ordinal_eval_mem {P : Type u} (s : Presentation P) (H : Set P)
    (tau : Name s) (ground : tau.val ∈ M.sets)
    (ordinal : ordinalSetProperty (Name.eval H tau)) : Name.eval H tau ∈ M.sets := by
  have codeGround := M.ordinalCode_rank_mem pairing unions powers separation collection ground
  have successorGround := M.insert_mem pairing unions codeGround codeGround
  apply M.transitive successorGround
  rw [ordinalSetProperty_eq_code_rank (Name.eval H tau) ordinal,
    ← ordinalCode_succ, mem_ordinalCode_iff]
  exact Order.lt_succ_iff.2 (Name.rank_eval_le_code_rank H tau)

theorem ordinaryExtension_ordinal_mem {P : Type u} [Preorder P]
    (s : Presentation P) (H : ConditionFilter P) {delta : ZFSet.{u}}
    (member : delta ∈ (M.ordinaryExtension s H).sets) (ordinal : ordinalSetProperty delta) :
    delta ∈ M.sets := by
  obtain ⟨tau, ground, rfl⟩ := (M.mem_ordinaryExtension s H delta).1 member
  exact M.ordinal_eval_mem pairing unions powers separation collection s {p | H.mem p} tau ground ordinal

theorem symmetricExtension_ordinal_mem {P : Type u} [PartialOrder P]
    (s : Presentation P) {G : Type v} [Group G] (a : PosetAction G P)
    (F : NormalSubgroupFamily G) (H : ConditionFilter P) {delta : ZFSet.{u}}
    (member : delta ∈ (M.symmetricExtension s a F H).sets) (ordinal : ordinalSetProperty delta) :
    delta ∈ M.sets :=
  M.ordinaryExtension_ordinal_mem pairing unions powers separation collection s H
    (M.symmetricExtension_subset_ordinaryExtension s a F H member) ordinal

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
