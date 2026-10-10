import Mathlib
import OAI.Topology.ArtinGroups.Realizations.NervePrismValue

namespace OAI

namespace HarmonicArtin
universe u
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma prismSimplex_zero {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    prismSimplex 0 (z,(0:I))=Convexity.StdSimplex.map Fin.succ z := by
  have hm:prismMarginals 0 (Convexity.StdSimplex.map Fin.succ z)=(z,(0:I)):=by
    apply Prod.ext
    · change Convexity.StdSimplex.map (0:Fin (n+1)).predAbove (Convexity.StdSimplex.map Fin.succ z)=z
      rw [← Convexity.StdSimplex.map_comp]
      have he:(0:Fin (n+1)).predAbove∘Fin.succ=id:=by
        funext i; exact Fin.predAbove_succ_of_le _ _ (Fin.zero_le _)
      rw [he,Convexity.StdSimplex.map_id]
    · apply Subtype.ext
      change (Convexity.StdSimplex.map (prismFlag 0) (Convexity.StdSimplex.map Fin.succ z)).weights 0=0
      rw [← Convexity.StdSimplex.map_comp, simplex_map_weights]
      rw [FunOnFinite.linearMap_apply_apply]
      apply Finset.sum_eq_zero
      intro i hi
      have hn:prismFlag (0:Fin (n+1)) i.succ≠0:=by simp [prismFlag]
      exact (hn (Finset.mem_filter.mp hi).2).elim
  simpa only [hm] using prismSimplex_marginals 0 (Convexity.StdSimplex.map Fin.succ z)

lemma prismSimplex_one {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    prismSimplex (Fin.last n) (z,(1:I))=Convexity.StdSimplex.map Fin.castSucc z := by
  have hm:prismMarginals (Fin.last n) (Convexity.StdSimplex.map Fin.castSucc z)=(z,(1:I)):=by
    apply Prod.ext
    · change Convexity.StdSimplex.map (Fin.last n).predAbove (Convexity.StdSimplex.map Fin.castSucc z)=z
      rw [← Convexity.StdSimplex.map_comp]
      have he:(Fin.last n).predAbove∘Fin.castSucc=id:=by
        funext i; exact Fin.predAbove_castSucc_of_le _ _ (Fin.le_last _)
      rw [he,Convexity.StdSimplex.map_id]
    · apply Subtype.ext
      change (Convexity.StdSimplex.map (prismFlag (Fin.last n)) (Convexity.StdSimplex.map Fin.castSucc z)).weights 0=1
      rw [← Convexity.StdSimplex.map_comp, simplex_map_weights]
      rw [FunOnFinite.linearMap_apply_apply]
      have he:Finset.univ.filter (fun i:Fin (n+1)=>(prismFlag (Fin.last n)∘Fin.castSucc) i=0)=Finset.univ:=by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,iff_true,Function.comp_apply]
        simp only [prismFlag,Fin.castSucc_le_castSucc_iff,Fin.le_last,ite_true]
      rw [he]; exact z.total_of_fintype
  simpa only [hm] using prismSimplex_marginals (Fin.last n) (Convexity.StdSimplex.map Fin.castSucc z)

lemma nervePrism_zero_face {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    (nerve Q).map (SimplexCategory.δ (0:Fin (n.len+2))).op (nervePrism f g h x 0)=
      (nerveMap g.toFunctor).app (op n) x := by
  apply nerve.ext_of_isThin
  funext i
  change orderCylinder f g h (x.obj ((0:Fin (n.len+1)).predAbove i.succ),
    if i.succ≤(0:Fin (n.len+1)).castSucc then (0:Fin 2) else 1)=g (x.obj i)
  rw [Fin.predAbove_succ_of_le _ _ (Fin.zero_le _)]
  have hn:¬i.succ≤(0:Fin (n.len+1)).castSucc:=by
    simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc,Fin.val_zero]; omega
  simp only [hn,ite_false]
  change (if (1:Fin 2)=0 then f (x.obj i) else g (x.obj i))=g (x.obj i)
  simp

lemma nervePrism_one_face {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n)) :
    (nerve Q).map (SimplexCategory.δ (Fin.last (n.len+1))).op (nervePrism f g h x (Fin.last n.len))=
      (nerveMap f.toFunctor).app (op n) x := by
  apply nerve.ext_of_isThin
  funext i
  change orderCylinder f g h (x.obj ((Fin.last n.len).predAbove ((Fin.last (n.len+1)).succAbove i)),
    if (Fin.last (n.len+1)).succAbove i≤(Fin.last n.len).castSucc then (0:Fin 2) else 1)=f (x.obj i)
  rw [Fin.succAbove_last]
  rw [Fin.predAbove_castSucc_of_le _ _ (Fin.le_last _)]
  simp only [Fin.castSucc_le_castSucc_iff,Fin.le_last,ite_true]
  change (if (0:Fin 2)=0 then f (x.obj i) else g (x.obj i))=f (x.obj i)
  simp

lemma nervePrismSimplex_zero {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
    nervePrismSimplex f g h x z 0=realizeSimplex (nerve Q) ((nerveMap g.toFunctor).app (op n) x) z := by
  have hz:(z,(0:I))∈PrismCell (0:Fin (n.len+1)):=by
    constructor
    · rw [prismPrefix_zero]; rfl
    · rw [prismPrefix_zero,zero_add]; exact z.weights_nonneg 0
  change nervePrismValue f g h x (z,0)=_
  rw [nervePrismValue_eq f g h x 0 _ hz]
  change realizeSimplex _ (nervePrism f g h x 0) (prismSimplex 0 (z,0))=_
  rw [prismSimplex_zero]
  have hh:=realizeSimplex_natural (nerve Q) (SimplexCategory.δ (0:Fin (n.len+2))) (nervePrism f g h x 0) z
  rw [nervePrism_zero_face] at hh
  exact hh.symm

lemma nervePrismSimplex_one {P Q:Type u} [Preorder P] [Preorder Q]
    (f g:P→oQ) (h:∀p,f p≤g p) {n:SimplexCategory} (x:(nerve P).obj (op n))
    (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
    nervePrismSimplex f g h x z 1=realizeSimplex (nerve Q) ((nerveMap f.toFunctor).app (op n) x) z := by
  have hz:(z,(1:I))∈PrismCell (Fin.last n.len):=by
    constructor
    · change prismPrefix z (Fin.last n.len)≤1
      have hh:=prismPrefix_last z
      linarith [z.weights_nonneg (Fin.last n.len)]
    · rw [prismPrefix_last]; rfl
  change nervePrismValue f g h x (z,1)=_
  rw [nervePrismValue_eq f g h x (Fin.last n.len) _ hz]
  change realizeSimplex _ (nervePrism f g h x (Fin.last n.len)) (prismSimplex (Fin.last n.len) (z,1))=_
  rw [prismSimplex_one]
  have hh:=realizeSimplex_natural (nerve Q) (SimplexCategory.δ (Fin.last (n.len+1)))
    (nervePrism f g h x (Fin.last n.len)) z
  rw [nervePrism_one_face] at hh
  change _=realizeSimplex _ _ (Convexity.StdSimplex.map (Fin.last (n.len+1)).succAbove z) at hh
  rw [Fin.succAbove_last] at hh
  exact hh.symm

lemma realizeSimplex_map {X Y:SSet} (u:X⟶Y) {n:SimplexCategory} (x:X.obj (op n))
    (z:Convexity.StdSimplex ℝ (Fin (n.len+1))) :
    SSet.toTop.map u (realizeSimplex X x z)=realizeSimplex Y (u.app (op n) x) z := by
  have hh:=ConcreteCategory.congr_hom (NatTrans.congr_app (sSetTopAdj.unit.naturality u) (op n)) x
  have ht:=congrArg (fun q=>TopCat.toSSetObjEquiv _ _ q z) hh
  exact ht.symm

end HarmonicArtin

end OAI
