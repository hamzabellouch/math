import Mathlib

namespace OAI

namespace HarmonicArtin
open CategoryTheory Opposite Simplicial

attribute [local instance] Classical.decEq Classical.propDecidable

def prismGrid {n:ℕ} (k:Fin (n+1)) : Fin (n+2) →o Fin (n+1) × Fin 2 where
  toFun i:=(k.predAbove i,if i≤ k.castSucc then 0 else 1)
  monotone' :=by
    intro i j hij
    refine ⟨k.predAbove_right_monotone hij,?_⟩
    by_cases hi:i≤ k.castSucc <;> by_cases hj:j≤ k.castSucc
    · simp only [hi,hj,ite_true]; exact le_rfl
    · simpa only [hi,hj,ite_true,ite_false] using (show (0:Fin 2)≤1 by decide)
    · exact (hi (hij.trans hj)).elim
    · simp only [hi,hj,ite_false]; exact le_rfl

lemma prismGrid_apply {n:ℕ} (k:Fin (n+1)) (i:Fin (n+2)) :
    prismGrid k i = (k.predAbove i,if i≤k.castSucc then (0:Fin 2) else 1) := rfl

def orderCylinder {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→o Q) (h:∀p,f p≤ g p) : P × Fin 2 →o Q where
  toFun p:=if p.2=0 then f p.1 else g p.1
  monotone' :=by
    intro p q hpq
    by_cases hp:p.2=0 <;> by_cases hq:q.2=0
    · simp only [hp,hq,ite_true]; exact f.monotone hpq.1
    · simp only [hp,hq,ite_true,ite_false]; exact (h p.1).trans (g.monotone hpq.1)
    · have hh:p.2≤0:=hq ▸ hpq.2
      exact (hp (le_antisymm hh (Fin.zero_le _))).elim
    · simp only [hp,hq,ite_false]; exact g.monotone hpq.1

noncomputable def nervePrism {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→o Q) (h:∀p,f p≤ g p) {n:SimplexCategory}
    (x:(nerve P).obj (op n)) (k:Fin (n.len+1)) : (nerve Q).obj (op ⦋n.len+1⦌) :=
  ((orderCylinder f g h).comp ((x.toOrderHom.prodMap (OrderHom.id)).comp (prismGrid k))).toFunctor

def prismOrdinal {n m:SimplexCategory} (u:n⟶m) (k:Fin (n.len+1)) : ⦋n.len+1⦌⟶⦋m.len+1⦌ :=
  SimplexCategory.mkHom {
    toFun i:=if i≤ k.castSucc then (u.toOrderHom (k.predAbove i)).castSucc
      else (u.toOrderHom (k.predAbove i)).succ
    monotone':=by
      intro i j hij
      have hh:=u.toOrderHom.monotone (k.predAbove_right_monotone hij)
      by_cases hi:i≤ k.castSucc <;> by_cases hj:j≤ k.castSucc
      · simp only [hi,hj,ite_true]; exact Fin.castSucc_le_castSucc_iff.mpr hh
      · simp only [hi,hj,ite_true,ite_false]
        exact le_trans (Fin.castSucc_le_castSucc_iff.mpr hh) (by simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ]; omega)
      · exact (hi (hij.trans hj)).elim
      · simp only [hi,hj,ite_false]; exact Fin.succ_le_succ_iff.mpr hh }

lemma prismGrid_natural {n m:SimplexCategory} (u:n⟶m) (k:Fin (n.len+1)) (i:Fin (n.len+2)) :
    prismGrid (u.toOrderHom k) ((prismOrdinal u k).toOrderHom i)=
      (u.toOrderHom ((prismGrid k i).1),(prismGrid k i).2) := by
  by_cases hi:i≤ k.castSucc
  · have hk:k.predAbove i≤ k:=by
      have hh:=k.predAbove_right_monotone hi
      simpa only [Fin.predAbove_castSucc_self] using hh
    have hu:=u.toOrderHom.monotone hk
    change ((u.toOrderHom k).predAbove (if i≤k.castSucc then
        (u.toOrderHom (k.predAbove i)).castSucc else (u.toOrderHom (k.predAbove i)).succ),
      if (if i≤k.castSucc then (u.toOrderHom (k.predAbove i)).castSucc
        else (u.toOrderHom (k.predAbove i)).succ)≤(u.toOrderHom k).castSucc then (0:Fin 2) else 1)=
      (u.toOrderHom (k.predAbove i),if i≤k.castSucc then (0:Fin 2) else 1)
    simp only [hi,ite_true,Fin.castSucc_le_castSucc_iff.mpr hu,Fin.predAbove_castSucc_of_le _ _ hu]
  · have hk:k≤ k.predAbove i:=by
      have hh:k.succ≤ i:=by
        simp only [Fin.le_iff_val_le_val,Fin.val_succ]
        have hh:=not_le.mp hi
        simpa only [Fin.lt_def,Fin.val_castSucc,Nat.succ_le_iff] using hh
      have hh:=k.predAbove_right_monotone hh
      simpa only [Fin.predAbove_succ_self] using hh
    have hu:=u.toOrderHom.monotone hk
    have hlu:¬(u.toOrderHom (k.predAbove i)).succ≤(u.toOrderHom k).castSucc:=by
      simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc] at hu ⊢
      omega
    change ((u.toOrderHom k).predAbove (if i≤k.castSucc then
        (u.toOrderHom (k.predAbove i)).castSucc else (u.toOrderHom (k.predAbove i)).succ),
      if (if i≤k.castSucc then (u.toOrderHom (k.predAbove i)).castSucc
        else (u.toOrderHom (k.predAbove i)).succ)≤(u.toOrderHom k).castSucc then (0:Fin 2) else 1)=
      (u.toOrderHom (k.predAbove i),if i≤k.castSucc then (0:Fin 2) else 1)
    simp only [hi,ite_false,hlu,Fin.predAbove_succ_of_le _ _ hu]

lemma nervePrism_natural {P Q:Type*} [Preorder P] [Preorder Q]
    (f g:P→o Q) (h:∀p,f p≤ g p) {n m:SimplexCategory} (u:n⟶m)
    (x:(nerve P).obj (op m)) (k:Fin (n.len+1)) :
    nervePrism f g h ((nerve P).map u.op x) k =
      (nerve Q).map (prismOrdinal u k).op (nervePrism f g h x (u.toOrderHom k)) := by
  apply nerve.ext_of_isThin
  funext i
  have he:=prismGrid_natural u k i
  change orderCylinder f g h ((x.obj ((u.toOrderHom ((prismGrid k i).1)))),(prismGrid k i).2)=
    orderCylinder f g h (x.obj ((prismGrid (u.toOrderHom k) ((prismOrdinal u k).toOrderHom i)).1),
      (prismGrid (u.toOrderHom k) ((prismOrdinal u k).toOrderHom i)).2)
  rw [he]

end HarmonicArtin

end OAI
