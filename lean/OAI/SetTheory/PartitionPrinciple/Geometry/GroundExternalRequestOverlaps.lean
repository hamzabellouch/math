import OAI.SetTheory.PartitionPrinciple.Definability.GroundExternalRequestSetRecognition

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def externalRequestOverlapGraph
    (Requests P G Rectangles Maps U r A : ZFSet.{u}) : ZFSet.{u} :=
  let V := externalTileVertices Requests Rectangles U
  ZFSet.sep (fun z => ∃ a ∈ V, ∃ b ∈ V, ∃ q ∈ Requests,
    ∃ i ∈ externalRequestTags, ∃ x ∈ U, ∃ j ∈ externalRequestTags, ∃ y ∈ U,
      z = ZFSet.pair a b ∧ a = ZFSet.pair (ZFSet.pair q i) x ∧
        b = ZFSet.pair (ZFSet.pair q j) y ∧
        ExternalRequestOverlapCode P G Rectangles Maps (ZFSet.sUnion (ZFSet.sUnion Maps)) r A
          (natSetCode 0) (natSetCode 1) (natSetCode 2) q i x j y) (ZFSet.prod V V)

theorem pair_mem_externalRequestOverlapGraph (Requests P G Rectangles Maps U r A a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ externalRequestOverlapGraph Requests P G Rectangles Maps U r A ↔
      a ∈ externalTileVertices Requests Rectangles U ∧ b ∈ externalTileVertices Requests Rectangles U ∧
        ∃ q ∈ Requests, ∃ i ∈ externalRequestTags, ∃ x ∈ U, ∃ j ∈ externalRequestTags, ∃ y ∈ U,
          a = ZFSet.pair (ZFSet.pair q i) x ∧ b = ZFSet.pair (ZFSet.pair q j) y ∧
            ExternalRequestOverlapCode P G Rectangles Maps (ZFSet.sUnion (ZFSet.sUnion Maps)) r A
              (natSetCode 0) (natSetCode 1) (natSetCode 2) q i x j y := by
  rw [externalRequestOverlapGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a', ha, b', hb, q, hq, i, hi, x, hx, j, hj, y, hy, equal, left, right, overlap⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, q, hq, i, hi, x, hx, j, hj, y, hy, left, right, overlap⟩
  · rintro ⟨ha, hb, q, hq, i, hi, x, hx, j, hj, y, hy, left, right, overlap⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, a, ha, b, hb, q, hq, i, hi, x, hx, j, hj, y, hy,
      rfl, left, right, overlap⟩

theorem externalRequestOverlapGraph_subset (Requests P G Rectangles Maps U r A : ZFSet.{u}) :
    externalRequestOverlapGraph Requests P G Rectangles Maps U r A ⊆
      ZFSet.prod (externalTileVertices Requests Rectangles U) (externalTileVertices Requests Rectangles U) := by
  intro z member
  unfold externalRequestOverlapGraph at member
  exact (ZFSet.mem_sep.1 member).1

theorem externalRequestOverlapGraph_symmetric {Requests P G Rectangles Maps U r A a b : ZFSet.{u}}
    (entry : ZFSet.pair a b ∈ externalRequestOverlapGraph Requests P G Rectangles Maps U r A) :
    ZFSet.pair b a ∈ externalRequestOverlapGraph Requests P G Rectangles Maps U r A := by
  obtain ⟨ha, hb, q, hq, i, hi, x, hx, j, hj, y, hy, left, right, overlap⟩ :=
    (pair_mem_externalRequestOverlapGraph _ _ _ _ _ _ _ _ _ _).1 entry
  exact (pair_mem_externalRequestOverlapGraph _ _ _ _ _ _ _ _ _ _).2
    ⟨hb, ha, q, hq, j, hj, y, hy, i, hi, x, hx, right, left, overlap.symm⟩

namespace BoundedFormula

def externalRequestOverlapEntryFormula {n}
    (z V Requests Tags U P G Rectangles Maps F r A zero first second : Fin n) : BoundedFormula n :=
  exMem V (exMem V.succ (exMem Requests.succ.succ (exMem Tags.succ.succ.succ
    (exMem U.succ.succ.succ.succ (exMem Tags.succ.succ.succ.succ.succ
      (exMem U.succ.succ.succ.succ.succ.succ
        (.conj (orderedPairFormula z.succ.succ.succ.succ.succ.succ.succ 6 5)
          (.conj (orderedTripleFormula 6 4 3 2)
            (.conj (orderedTripleFormula 5 4 1 0)
              (externalRequestOverlapFormula P.succ.succ.succ.succ.succ.succ.succ
                G.succ.succ.succ.succ.succ.succ.succ Rectangles.succ.succ.succ.succ.succ.succ.succ
                Maps.succ.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ.succ
                r.succ.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ.succ
                zero.succ.succ.succ.succ.succ.succ.succ first.succ.succ.succ.succ.succ.succ.succ
                second.succ.succ.succ.succ.succ.succ.succ 4 3 2 1 0))))))))))

theorem truth_externalRequestOverlapEntryFormula {n}
    (z V Requests Tags U P G Rectangles Maps F r A zero first second : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalRequestOverlapEntryFormula z V Requests Tags U P G Rectangles Maps F r A zero first second) env ↔
      ∃ a ∈ env V, ∃ b ∈ env V, ∃ q ∈ env Requests,
        ∃ i ∈ env Tags, ∃ x ∈ env U, ∃ j ∈ env Tags, ∃ y ∈ env U,
          env z = ZFSet.pair a b ∧ a = ZFSet.pair (ZFSet.pair q i) x ∧
            b = ZFSet.pair (ZFSet.pair q j) y ∧
            ExternalRequestOverlapCode (env P) (env G) (env Rectangles) (env Maps) (env F) (env r) (env A)
              (env zero) (env first) (env second) q i x j y := by
  simp only [externalRequestOverlapEntryFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_orderedTripleFormula, truth_externalRequestOverlapFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalTileVertices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Requests Rectangles U : ZFSet.{u}} (hRequests : Requests ∈ M.sets)
    (hRectangles : Rectangles ∈ M.sets) (hU : U ∈ M.sets) :
    externalTileVertices Requests Rectangles U ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨U, hU⟩
  have hFirst : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  have hSecond : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions hFirst hFirst
  have single : ({natSetCode 2} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hSecond hSecond
  exact M.binary_union_mem pairing unions
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hRequests (M.unorderedPair_mem pairing hZero hFirst)) hU)
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation
        (M.prod_mem pairing unions powers separation single hRectangles) single) hU)

theorem externalRequestOverlapGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Requests P G Rectangles Maps U r A : ZFSet.{u}}
    (hRequests : Requests ∈ M.sets) (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hRectangles : Rectangles ∈ M.sets) (hMaps : Maps ∈ M.sets) (hU : U ∈ M.sets)
    (hr : r ∈ M.sets) (hA : A ∈ M.sets) :
    externalRequestOverlapGraph Requests P G Rectangles Maps U r A ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨U, hU⟩
  have hFirst : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  have hSecond : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions hFirst hFirst
  have single : ({natSetCode 2} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hSecond hSecond
  have hTags : externalRequestTags ∈ M.sets :=
    M.insert_mem pairing unions hZero (M.insert_mem pairing unions hFirst single)
  have hV := M.externalTileVertices_mem pairing unions powers separation hRequests hRectangles hU
  have hF := M.union_mem unions (M.union_mem unions hMaps)
  let params := extend (externalTileVertices Requests Rectangles U) (extend Requests
    (extend externalRequestTags (extend U (extend P (extend G (extend Rectangles
      (extend Maps (extend (ZFSet.sUnion (ZFSet.sUnion Maps)) (extend r (extend A (extend (natSetCode 0)
        (extend (natSetCode 1) (extend (natSetCode 2) Fin.elim0)))))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalRequestOverlapEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14) params
    (Fin.cases hV (Fin.cases hRequests (Fin.cases hTags (Fin.cases hU (Fin.cases hP (Fin.cases hG
      (Fin.cases hRectangles (Fin.cases hMaps (Fin.cases hF (Fin.cases hr (Fin.cases hA
        (Fin.cases hZero (Fin.cases hFirst (Fin.cases hSecond (fun i => Fin.elim0 i)))))))))))))))
    (M.prod_mem pairing unions powers separation hV hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalRequestOverlapEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14)
      (extend z params)) (ZFSet.prod (externalTileVertices Requests Rectangles U)
        (externalTileVertices Requests Rectangles U)) = externalRequestOverlapGraph Requests P G Rectangles Maps U r A := by
    apply ZFSet.ext
    intro z
    rw [externalRequestOverlapGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalRequestOverlapEntryFormula
      0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
