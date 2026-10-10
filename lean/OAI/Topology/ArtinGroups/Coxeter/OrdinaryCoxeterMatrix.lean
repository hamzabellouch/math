import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRel

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} (Q:ReversibleQuiver V A)

noncomputable def ordinaryCoxeterMatrix : CoxeterMatrix V := by
  classical
  refine { M := fun α β => if α=β then 1 else if OrthogonalVertices Q α β then 2
      else if Nonempty (SimpleEdge Q α β) then 3 else 0
           isSymm := ?_, diagonal := ?_, off_diagonal := ?_ }
  · apply Matrix.ext
    intro α β
    have ho:OrthogonalVertices Q α β↔OrthogonalVertices Q β α :=
      ⟨OrthogonalVertices.symm Q,OrthogonalVertices.symm Q⟩
    have he:Nonempty (SimpleEdge Q α β)↔Nonempty (SimpleEdge Q β α) :=
      ⟨fun ⟨e⟩=>⟨e.reverse Q⟩,fun ⟨e⟩=>⟨e.reverse Q⟩⟩
    change (if β=α then 1 else if OrthogonalVertices Q β α then 2
      else if Nonempty (SimpleEdge Q β α) then 3 else 0) =
      (if α=β then 1 else if OrthogonalVertices Q α β then 2
      else if Nonempty (SimpleEdge Q α β) then 3 else 0)
    simp only [eq_comm (a:=α) (b:=β),ho,he]
  · intro α; simp
  · intro α β h
    simp only [h,ite_false]
    split
    · norm_num
    · split <;> norm_num

lemma ordinaryCoxeterMatrix_orthogonal {α β:V} (h:OrthogonalVertices Q α β) :
    ordinaryCoxeterMatrix Q α β=2 := by
  classical
  simp [ordinaryCoxeterMatrix,h.1,h]

lemma ordinaryCoxeterMatrix_adjacent {α β:V} (e:SimpleEdge Q α β) :
    ordinaryCoxeterMatrix Q α β=3 := by
  classical
  have ho:¬OrthogonalVertices Q α β:=fun h=>h.2 e.arrow e.source e.target
  simp [ordinaryCoxeterMatrix,e.distinct,ho,show Nonempty (SimpleEdge Q α β) from ⟨e⟩]

lemma PositiveBraidRel.coxeter_eq {v w:List V} (h:PositiveBraidRel Q v w) :
    (ordinaryCoxeterMatrix Q).toCoxeterSystem.wordProd v=
      (ordinaryCoxeterMatrix Q).toCoxeterSystem.wordProd w := by
  let cs := (ordinaryCoxeterMatrix Q).toCoxeterSystem
  change cs.wordProd v=cs.wordProd w
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | cons α h ih => simpa only [CoxeterSystem.wordProd_cons] using congrArg (cs.simple α*·) ih
  | @orthogonal α β h w =>
    have hb:=cs.wordProd_braidWord_eq α β
    have hab:ordinaryCoxeterMatrix Q α β=2:=ordinaryCoxeterMatrix_orthogonal Q h
    have hba:=ordinaryCoxeterMatrix_orthogonal Q (h.symm Q)
    simp only [CoxeterSystem.braidWord,hab,hba,CoxeterSystem.alternatingWord] at hb
    change cs.wordProd [α,β]=cs.wordProd [β,α] at hb
    simpa only [CoxeterSystem.wordProd_cons,CoxeterSystem.wordProd_nil,_root_.mul_one,_root_.mul_assoc]
      using congrArg (·*cs.wordProd w) hb
  | @adjacent α β e w =>
    have hb:=cs.wordProd_braidWord_eq α β
    have hab:=ordinaryCoxeterMatrix_adjacent Q e
    have hba:=ordinaryCoxeterMatrix_adjacent Q (e.reverse Q)
    simp only [CoxeterSystem.braidWord,hab,hba,CoxeterSystem.alternatingWord] at hb
    change cs.wordProd [β,α,β]=cs.wordProd [α,β,α] at hb
    simpa only [CoxeterSystem.wordProd_cons,CoxeterSystem.wordProd_nil,_root_.mul_one,_root_.mul_assoc]
      using congrArg (·*cs.wordProd w) hb.symm

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
