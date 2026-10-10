import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PrismGrid
import OAI.Topology.ArtinGroups.Harmonic.PrismFlag

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma predAbove_succ_succAbove {n:ℕ} (k i:Fin (n+1)) :
    k.predAbove (k.succ.succAbove i)=i := by
  by_cases hi:i≤k
  · rw [Fin.succAbove_succ_of_le _ _ hi,Fin.predAbove_castSucc_of_le _ _ hi]
  · rw [Fin.succAbove_succ_of_lt _ _ (not_le.mp hi),Fin.predAbove_succ_of_le _ _ (not_le.mp hi).le]

lemma prismGrid_face_right {n:ℕ} (k i:Fin (n+1)) :
    prismGrid k (k.succ.succAbove i)=(i,if i≤k then (0:Fin 2) else 1) := by
  rw [prismGrid_apply,predAbove_succ_succAbove]
  by_cases hi:i≤k
  · rw [Fin.succAbove_succ_of_le _ _ hi]
    simp only [Fin.castSucc_le_castSucc_iff,hi,ite_true]
  · rw [Fin.succAbove_succ_of_lt _ _ (not_le.mp hi)]
    have hh:¬i.succ≤k.castSucc:=by
      simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc] at hi ⊢
      omega
    simp only [hi,hh,ite_false]

lemma prismGrid_face_adjacent {n:ℕ} (k l:Fin (n+1)) (hkl:l.val=k.val+1) (i:Fin (n+1)) :
    prismGrid l (k.succ.succAbove i)=prismGrid k (k.succ.succAbove i) := by
  have hd:k.succ=l.castSucc:=Fin.ext hkl.symm
  rw [prismGrid_face_right,hd,prismGrid_apply,Fin.predAbove_succAbove]
  have he:i<l ↔ i≤k:=by
    simp only [Fin.lt_def,Fin.le_iff_val_le_val]
    omega
  simp only [succAbove_le_castSucc_iff,he]

lemma prismMarginals_face_right {n:ℕ} (k:Fin (n+1)) (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    (prismMarginals k (Convexity.StdSimplex.map k.succ.succAbove z)).1=z ∧
    (prismMarginals k (Convexity.StdSimplex.map k.succ.succAbove z)).2.val=prismPrefix z k+z.weights k := by
  constructor
  · change Convexity.StdSimplex.map k.predAbove (Convexity.StdSimplex.map k.succ.succAbove z)=z
    rw [← Convexity.StdSimplex.map_comp]
    have he:k.predAbove∘k.succ.succAbove=id:=funext (predAbove_succ_succAbove k)
    rw [he,Convexity.StdSimplex.map_id]
  · change (Convexity.StdSimplex.map (prismFlag k) (Convexity.StdSimplex.map k.succ.succAbove z)).weights 0=_
    rw [← Convexity.StdSimplex.map_comp,prismPrefix_add,simplex_map_weights]
    rw [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic]
      have he:=congrArg Prod.snd (prismGrid_face_right k i)
      change prismFlag k (k.succ.succAbove i)=(if i≤k then (0:Fin 2) else 1) at he
      simp only [Function.comp_apply,he]
      by_cases hi:i≤k <;> simp [hi]
    · intro _ _; rfl

lemma prismMarginals_face_adjacent {n:ℕ} (k l:Fin (n+1)) (hkl:l.val=k.val+1)
    (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    prismMarginals l (Convexity.StdSimplex.map k.succ.succAbove z)=
      prismMarginals k (Convexity.StdSimplex.map k.succ.succAbove z) := by
  apply Prod.ext
  · change Convexity.StdSimplex.map l.predAbove (Convexity.StdSimplex.map k.succ.succAbove z)=
      Convexity.StdSimplex.map k.predAbove (Convexity.StdSimplex.map k.succ.succAbove z)
    rw [← Convexity.StdSimplex.map_comp,← Convexity.StdSimplex.map_comp]
    congr 1
    funext i
    exact congrArg Prod.fst (prismGrid_face_adjacent k l hkl i)
  · apply Subtype.ext
    change (Convexity.StdSimplex.map (prismFlag l) (Convexity.StdSimplex.map k.succ.succAbove z)).weights 0=
      (Convexity.StdSimplex.map (prismFlag k) (Convexity.StdSimplex.map k.succ.succAbove z)).weights 0
    rw [← Convexity.StdSimplex.map_comp,← Convexity.StdSimplex.map_comp]
    have he:prismFlag l∘k.succ.succAbove=prismFlag k∘k.succ.succAbove:=by
      funext i
      exact congrArg Prod.snd (prismGrid_face_adjacent k l hkl i)
    rw [he]

lemma prismPrefix_step {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) (k l:Fin (n+1)) (hkl:l.val=k.val+1) :
    prismPrefix z l=prismPrefix z k+z.weights k := by
  rw [prismPrefix_add]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_Iio,Finset.mem_Iic,Fin.lt_def,Fin.le_iff_val_le_val]
    omega
  · intro _ _; rfl

lemma prismSimplex_face_right {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1))×I)
    (hp:p.2.val=prismPrefix p.1 k+p.1.weights k) :
    prismSimplex k p=Convexity.StdSimplex.map k.succ.succAbove p.1 := by
  have hm:prismMarginals k (Convexity.StdSimplex.map k.succ.succAbove p.1)=p:=by
    apply Prod.ext
    · exact (prismMarginals_face_right k p.1).1
    · apply Subtype.ext; exact (prismMarginals_face_right k p.1).2.trans hp.symm
  simpa only [hm] using (prismSimplex_marginals k (Convexity.StdSimplex.map k.succ.succAbove p.1))

lemma prismSimplex_face_adjacent {n:ℕ} (k l:Fin (n+1)) (hkl:l.val=k.val+1)
    (p:Convexity.StdSimplex ℝ (Fin (n+1))×I) (hp:p.2.val=prismPrefix p.1 k+p.1.weights k) :
    prismSimplex l p=Convexity.StdSimplex.map k.succ.succAbove p.1 := by
  have hm:prismMarginals l (Convexity.StdSimplex.map k.succ.succAbove p.1)=p:=by
    rw [prismMarginals_face_adjacent k l hkl]
    apply Prod.ext
    · exact (prismMarginals_face_right k p.1).1
    · apply Subtype.ext; exact (prismMarginals_face_right k p.1).2.trans hp.symm
  simpa only [hm] using (prismSimplex_marginals l (Convexity.StdSimplex.map k.succ.succAbove p.1))

lemma nervePrism_face_adjacent {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (k l:Fin (n.len+1)) (hkl:l.val=k.val+1) :
    (nerve Q).map (SimplexCategory.δ k.succ).op (nervePrism f g h x l)=
      (nerve Q).map (SimplexCategory.δ k.succ).op (nervePrism f g h x k) := by
  apply nerve.ext_of_isThin
  funext i
  change orderCylinder f g h (x.obj ((prismGrid l (k.succ.succAbove i)).1),
      (prismGrid l (k.succ.succAbove i)).2)=
    orderCylinder f g h (x.obj ((prismGrid k (k.succ.succAbove i)).1),
      (prismGrid k (k.succ.succAbove i)).2)
  rw [prismGrid_face_adjacent k l hkl]

end HarmonicArtin

end OAI
