import OAI.SetTheory.PartitionPrinciple.Geometry.GroundAttachmentEmbeddings

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def taggedComponentGraph (P I B N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ ZFSet.prod {P} N, ∃ i ∈ I, ∃ n ∈ N, ∃ q ∈ B,
    z = ZFSet.pair x i ∧ x = ZFSet.pair P n ∧ n = ZFSet.pair i q)
    (ZFSet.prod (ZFSet.prod {P} N) I)

theorem pair_mem_taggedComponentGraph (P I B N x i : ZFSet.{u}) :
    ZFSet.pair x i ∈ taggedComponentGraph P I B N ↔
      i ∈ I ∧ ∃ q ∈ B, ZFSet.pair i q ∈ N ∧ x = ZFSet.pair P (ZFSet.pair i q) := by
  rw [taggedComponentGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, _, j, hj, n, hn, q, hq, equal, value, rfl⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, q, hq, hn, value⟩
  · rintro ⟨hi, q, hq, hn, rfl⟩
    have hx : ZFSet.pair P (ZFSet.pair i q) ∈ ZFSet.prod {P} N := ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hn⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hi⟩, _, hx, i, hi, _, hn, q, hq, rfl, rfl, rfl⟩

theorem taggedComponentGraph_function {P I B N : ZFSet.{u}} (subset : N ⊆ ZFSet.prod I B) :
    ZFSet.IsFunc (ZFSet.prod {P} N) I (taggedComponentGraph P I B N) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨p, hp, n, hn, rfl⟩ := ZFSet.mem_prod.1 hx
  obtain rfl := ZFSet.mem_singleton.1 hp
  obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 (subset hn)
  refine ⟨i, (pair_mem_taggedComponentGraph _ _ _ _ _ _).2 ⟨hi, q, hq, hn, rfl⟩, ?_⟩
  intro j hj
  obtain ⟨_, r, _, _, equal⟩ := (pair_mem_taggedComponentGraph _ _ _ _ _ _).1 hj
  exact ((ZFSet.pair_inj.1 ((ZFSet.pair_inj.1 equal).2)).1).symm

namespace BoundedFormula

def taggedComponentFormula : BoundedFormula 6 :=
  exMem 1 (exMem 3 (exMem 5 (exMem 7
    (.conj (orderedPairFormula 4 3 2)
      (.conj (orderedPairFormula 3 9 1) (orderedPairFormula 1 2 0))))))

theorem truth_taggedComponentFormula (env : Fin 6 → ZFSet.{u}) :
    Truth taggedComponentFormula env ↔
      ∃ x ∈ env 1, ∃ i ∈ env 2, ∃ n ∈ env 3, ∃ q ∈ env 4,
        env 0 = ZFSet.pair x i ∧ x = ZFSet.pair (env 5) n ∧ n = ZFSet.pair i q := by
  simp only [taggedComponentFormula, truth_exMem, Truth, truth_orderedPairFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem taggedComponentGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P I B N : ZFSet.{u}} (hP : P ∈ M.sets) (hI : I ∈ M.sets)
    (hB : B ∈ M.sets) (hN : N ∈ M.sets) : taggedComponentGraph P I B N ∈ M.sets := by
  have hSingle : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  have hF := M.prod_mem pairing unions powers separation hSingle hN
  let params := extend (ZFSet.prod {P} N) (extend I (extend N (extend B (extend P Fin.elim0))))
  have selected := M.bounded_separation_mem separation BoundedFormula.taggedComponentFormula params
    (Fin.cases hF (Fin.cases hI (Fin.cases hN (Fin.cases hB (Fin.cases hP (fun j => Fin.elim0 j))))))
    (M.prod_mem pairing unions powers separation hF hI)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.taggedComponentFormula
      (extend z params)) (ZFSet.prod (ZFSet.prod {P} N) I) = taggedComponentGraph P I B N := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, taggedComponentGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_taggedComponentFormula _)
  exact equal ▸ selected
end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
