import OAI.SetTheory.PartitionPrinciple.Definability.BoundedRelationImageEquality
import OAI.SetTheory.PartitionPrinciple.Definability.MapFamilyApplicationGraphs

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def rowAssignmentActionGraph (G Q C B J rowMaps assignmentMaps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ g ∈ G, ∃ x ∈ Q, ∃ y ∈ Q, ∃ p ∈ C, ∃ A ∈ B, ∃ q ∈ C, ∃ D ∈ B,
    ∃ rf ∈ ⋃₀ ⋃₀ rowMaps, ∃ af ∈ ⋃₀ ⋃₀ assignmentMaps,
      z = ZFSet.pair (ZFSet.pair g x) y ∧ x = ZFSet.pair p A ∧ y = ZFSet.pair q D ∧
      ZFSet.pair g rf ∈ rowMaps ∧ ZFSet.pair p q ∈ rf ∧
      ZFSet.pair g af ∈ assignmentMaps ∧ D = relationImage A J af)
    (ZFSet.prod (ZFSet.prod G Q) Q)

theorem mem_rowAssignmentActionGraph (G Q C B J rowMaps assignmentMaps z : ZFSet.{u}) :
    z ∈ rowAssignmentActionGraph G Q C B J rowMaps assignmentMaps ↔
      ∃ g ∈ G, ∃ x ∈ Q, ∃ y ∈ Q, ∃ p ∈ C, ∃ A ∈ B, ∃ q ∈ C, ∃ D ∈ B,
        ∃ rf ∈ ⋃₀ ⋃₀ rowMaps, ∃ af ∈ ⋃₀ ⋃₀ assignmentMaps,
          z = ZFSet.pair (ZFSet.pair g x) y ∧ x = ZFSet.pair p A ∧ y = ZFSet.pair q D ∧
          ZFSet.pair g rf ∈ rowMaps ∧ ZFSet.pair p q ∈ rf ∧
          ZFSet.pair g af ∈ assignmentMaps ∧ D = relationImage A J af := by
  rw [rowAssignmentActionGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    obtain ⟨g,hg,x,hx,y,hy,p,hp,A,hA,q,hq,D,hD,rf,hrf,af,haf,equal,rest⟩ := h
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg,hx⟩,hy⟩,
      g,hg,x,hx,y,hy,p,hp,A,hA,q,hq,D,hD,rf,hrf,af,haf,equal,rest⟩

theorem pair_mem_rowAssignmentActionGraph (G Q C B J rowMaps assignmentMaps g p A q D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair p A)) (ZFSet.pair q D) ∈
      rowAssignmentActionGraph G Q C B J rowMaps assignmentMaps ↔
      g ∈ G ∧ ZFSet.pair p A ∈ Q ∧ ZFSet.pair q D ∈ Q ∧ p ∈ C ∧ A ∈ B ∧ q ∈ C ∧ D ∈ B ∧
      ∃ rf af, ZFSet.pair g rf ∈ rowMaps ∧ ZFSet.pair p q ∈ rf ∧
        ZFSet.pair g af ∈ assignmentMaps ∧ D = relationImage A J af := by
  rw [mem_rowAssignmentActionGraph]
  constructor
  · rintro ⟨g',hg,x,hx,y,hy,p',hp,A',hA,q',hq,D',hD,rf,_,af,_,equal,xEq,yEq,rest⟩
    obtain ⟨outerSource,target⟩ := ZFSet.pair_injective equal
    obtain ⟨rfl,innerSource⟩ := ZFSet.pair_injective outerSource
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective (innerSource.trans xEq)
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective (target.trans yEq)
    exact ⟨hg,innerSource.symm ▸ hx,target.symm ▸ hy,hp,hA,hq,hD,rf,af,rest⟩
  · rintro ⟨hg,hx,hy,hp,hA,hq,hD,rf,af,indexed,row,indexedA,image⟩
    exact ⟨g,hg,_,hx,_,hy,p,hp,A,hA,q,hq,D,hD,rf,pair_second_mem_doubleUnion indexed,
      af,pair_second_mem_doubleUnion indexedA,rfl,rfl,rfl,indexed,row,indexedA,image⟩

namespace BoundedFormula

def rowAssignmentActionEntryFormula {n} (z G Q C B J rowRange assignmentRange rowMaps assignmentMaps : Fin n) :
    BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ.succ.succ.succ
  exMem G (exMem Q.succ (exMem Q.succ.succ (exMem C.succ.succ.succ
    (exMem B.succ.succ.succ.succ (exMem C.succ.succ.succ.succ.succ
      (exMem B.succ.succ.succ.succ.succ.succ (exMem rowRange.succ.succ.succ.succ.succ.succ.succ
        (exMem assignmentRange.succ.succ.succ.succ.succ.succ.succ.succ
          (.conj (orderedTripleFormula (lift z) 8 7 6)
            (.conj (orderedPairFormula 7 5 4) (.conj (orderedPairFormula 6 3 2)
              (.conj (pairMembershipFormula 8 1 (lift rowMaps))
                (.conj (pairMembershipFormula 5 3 1)
                  (.conj (pairMembershipFormula 8 0 (lift assignmentMaps))
                    (relationImageEqualityFormula 2 4 (lift J) 0)))))))))))))))

theorem truth_rowAssignmentActionEntryFormula {n}
    (z G Q C B J rowRange assignmentRange rowMaps assignmentMaps : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rowAssignmentActionEntryFormula z G Q C B J rowRange assignmentRange rowMaps assignmentMaps) env ↔
      ∃ g ∈ env G, ∃ x ∈ env Q, ∃ y ∈ env Q, ∃ p ∈ env C, ∃ A ∈ env B, ∃ q ∈ env C, ∃ D ∈ env B,
        ∃ rf ∈ env rowRange, ∃ af ∈ env assignmentRange,
          env z = ZFSet.pair (ZFSet.pair g x) y ∧ x = ZFSet.pair p A ∧ y = ZFSet.pair q D ∧
          ZFSet.pair g rf ∈ env rowMaps ∧ ZFSet.pair p q ∈ rf ∧
          ZFSet.pair g af ∈ env assignmentMaps ∧ D = relationImage A (env J) af := by
  simp only [rowAssignmentActionEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_relationImageEqualityFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowAssignmentActionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G Q C B J rowMaps assignmentMaps : ZFSet.{u}}
    (hG : G ∈ M.sets) (hQ : Q ∈ M.sets) (hC : C ∈ M.sets) (hB : B ∈ M.sets) (hJ : J ∈ M.sets)
    (hRows : rowMaps ∈ M.sets) (hAssignments : assignmentMaps ∈ M.sets) :
    rowAssignmentActionGraph G Q C B J rowMaps assignmentMaps ∈ M.sets := by
  have hRowRange := M.union_mem unions (M.union_mem unions hRows)
  have hAssignmentRange := M.union_mem unions (M.union_mem unions hAssignments)
  let params : Fin 9 → ZFSet.{u} :=
    ![G,Q,C,B,J,⋃₀ ⋃₀ rowMaps,⋃₀ ⋃₀ assignmentMaps,rowMaps,assignmentMaps]
  have members : ∀ j, params j ∈ M.sets := Fin.cases hG (Fin.cases hQ (Fin.cases hC
    (Fin.cases hB (Fin.cases hJ (Fin.cases hRowRange (Fin.cases hAssignmentRange
      (Fin.cases hRows (Fin.cases hAssignments (fun j => Fin.elim0 j)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.rowAssignmentActionEntryFormula 0 1 2 3 4 5 6 7 8 9) params members
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hG hQ) hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.rowAssignmentActionEntryFormula 0 1 2 3 4 5 6 7 8 9) (extend z params))
      (ZFSet.prod (ZFSet.prod G Q) Q) = rowAssignmentActionGraph G Q C B J rowMaps assignmentMaps := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, rowAssignmentActionGraph, ZFSet.mem_sep,
      BoundedFormula.truth_rowAssignmentActionEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end OAI
