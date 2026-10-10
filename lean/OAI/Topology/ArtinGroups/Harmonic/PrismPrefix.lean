import Mathlib

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial

attribute [local instance] Classical.decEq Classical.propDecidable

def prismPrefix {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) (k:Fin (n+1)) : ℝ :=
  ∑i∈Finset.Iio k,z.weights i

def PrismCell {n:ℕ} (k:Fin (n+1)) : Set (Convexity.StdSimplex ℝ (Fin (n+1)) × I) :=
  {p | prismPrefix p.1 k ≤ p.2.val ∧ p.2.val ≤ prismPrefix p.1 k + p.1.weights k}

lemma continuous_prismPrefix {n:ℕ} (k:Fin (n+1)) : Continuous (fun z:Convexity.StdSimplex ℝ (Fin (n+1))=>prismPrefix z k) := by
  unfold prismPrefix
  fun_prop

lemma prismCell_closed {n:ℕ} (k:Fin (n+1)) : IsClosed (PrismCell k) := by
  apply IsClosed.inter
  · exact isClosed_le ((continuous_prismPrefix k).comp continuous_fst) (continuous_subtype_val.comp continuous_snd)
  · exact isClosed_le (continuous_subtype_val.comp continuous_snd)
      (((continuous_prismPrefix k).comp continuous_fst).add ((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp continuous_fst))

lemma prismPrefix_nonneg {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) (k:Fin (n+1)) : 0≤ prismPrefix z k :=
  Finset.sum_nonneg (fun i _=>z.weights_nonneg i)

lemma prismPrefix_add {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) (k:Fin (n+1)) :
    prismPrefix z k+z.weights k=∑i∈Finset.Iic k,z.weights i := by
  rw [Finset.Iic_eq_cons_Iio]
  simp only [Finset.sum_cons,prismPrefix,add_comm]

lemma prismPrefix_last {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) :
    prismPrefix z (Fin.last n)+z.weights (Fin.last n)=1 := by
  rw [prismPrefix_add]
  have he:(Finset.Iic (Fin.last n):Finset (Fin (n+1)))=Finset.univ:=by
    ext i; simp only [Finset.mem_Iic,Finset.mem_univ,iff_true]; exact Fin.le_last i
  rw [he]; exact z.total_of_fintype

lemma prismPrefix_zero {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+1))) : prismPrefix z 0=0 := by
  unfold prismPrefix
  apply Finset.sum_eq_zero
  intro i hi
  exact ((not_lt_of_ge (Fin.zero_le i)) (Finset.mem_Iio.mp hi)).elim

lemma prismPrefix_succ {n:ℕ} (z:Convexity.StdSimplex ℝ (Fin (n+2))) (k:Fin (n+1)) :
    prismPrefix z k.succ=prismPrefix z k.castSucc+z.weights k.castSucc := by
  rw [prismPrefix_add]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_Iio,Finset.mem_Iic,Fin.lt_def,Fin.le_iff_val_le_val,
      Fin.val_succ,Fin.val_castSucc]
    omega
  · intro _ _; rfl

lemma prismCell_cover {n:ℕ} (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) : ∃k,p∈PrismCell k := by
  let A:Finset (Fin (n+1)):=Finset.univ.filter (fun k=>p.2.val≤ prismPrefix p.1 k+p.1.weights k)
  have hA:A.Nonempty:=by
    refine ⟨Fin.last n,?_⟩
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [prismPrefix_last]
    exact p.2.property.2
  let k:=A.min' hA
  have hk:k∈A:=Finset.min'_mem A hA
  refine ⟨k,?_,(Finset.mem_filter.mp hk).2⟩
  by_cases hz:k=0
  · rw [hz,prismPrefix_zero]; exact p.2.property.1
  · let j:Fin (n+1):=⟨k.val-1,lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    have hj:j<k:=by dsimp [j]; exact Nat.sub_lt (Fin.pos_iff_ne_zero.mpr hz) (by omega)
    have hjn:j∉A:=fun hm=>(not_le_of_gt hj) (Finset.min'_le A j hm)
    have hh:prismPrefix p.1 j+p.1.weights j<p.2.val:=by
      simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hjn
    have he:prismPrefix p.1 k=prismPrefix p.1 j+p.1.weights j:=by
      rw [prismPrefix_add]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_Iio,Finset.mem_Iic,Fin.lt_def,Fin.le_iff_val_le_val]
        dsimp [j]
        have hp:=Fin.pos_iff_ne_zero.mpr hz
        omega
      · intro _ _; rfl
    rw [he]
    exact hh.le

noncomputable def prismLeft {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) : ℝ :=
  min (p.1.weights k) (max 0 (p.2.val-prismPrefix p.1 k))

lemma prismLeft_nonneg {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) : 0≤ prismLeft k p :=
  le_min (p.1.weights_nonneg k) (le_max_left _ _)
lemma prismLeft_le {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) : prismLeft k p≤ p.1.weights k :=
  min_le_left _ _
lemma prismLeft_cell {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) (hp:p∈PrismCell k) :
    prismLeft k p=p.2.val-prismPrefix p.1 k := by
  rw [prismLeft,max_eq_right (sub_nonneg.mpr hp.1),min_eq_right (by linarith [hp.2])]

noncomputable def prismWeights {n:ℕ} (k:Fin (n+1)) (p:Convexity.StdSimplex ℝ (Fin (n+1)) × I) :
    Fin (n+2)→ℝ :=
  k.castSucc.insertNth (prismLeft k p) (Function.update p.1.weights k (p.1.weights k-prismLeft k p))

noncomputable def prismSimplex {n:ℕ} (k:Fin (n+1)) :
    C(Convexity.StdSimplex ℝ (Fin (n+1)) × I,Convexity.StdSimplex ℝ (Fin (n+2))) where
  toFun p := {
    weights := Finsupp.equivFunOnFinite.symm (prismWeights k p)
    nonneg := by
      change ∀ index, 0 ≤ prismWeights k p index
      intro i
      obtain rfl|⟨j,rfl⟩:=Fin.eq_self_or_eq_succAbove k.castSucc i
      · simpa only [prismWeights,Fin.insertNth_apply_same] using prismLeft_nonneg k p
      · simp only [prismWeights,Fin.insertNth_apply_succAbove]
        by_cases hj:j=k
        · subst j
          simp only [Function.update_self]
          exact sub_nonneg.mpr (prismLeft_le k p)
        · rw [Function.update_of_ne hj]
          exact p.1.weights_nonneg j
    total := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      change (∑ index, prismWeights k p index) = 1
      simp only [prismWeights, Fin.sum_insertNth]
      rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
      have hs:=Finset.sum_sdiff (by simp : ({k}:Finset (Fin (n+1)))⊆Finset.univ) (f:=p.1.weights)
      simp only [Finset.sum_singleton,p.1.total_of_fintype] at hs
      linarith }
  continuous_toFun:=by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
    apply continuous_pi
    intro i
    obtain rfl|⟨j,rfl⟩:=Fin.eq_self_or_eq_succAbove k.castSucc i
    · change Continuous (fun p=>prismWeights k p k.castSucc)
      simp only [prismWeights,Fin.insertNth_apply_same]
      unfold prismLeft
      exact ((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp continuous_fst).min (continuous_const.max
        ((continuous_subtype_val.comp continuous_snd).sub ((continuous_prismPrefix k).comp continuous_fst)))
    · change Continuous (fun p=>prismWeights k p (k.castSucc.succAbove j))
      simp only [prismWeights,Fin.insertNth_apply_succAbove]
      by_cases hj:j=k
      · subst j
        simp only [Function.update_self]
        unfold prismLeft
        exact ((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp continuous_fst).sub
          (((Convexity.StdSimplex.continuous_weights_apply ℝ k).comp continuous_fst).min
            (continuous_const.max ((continuous_subtype_val.comp continuous_snd).sub
              ((continuous_prismPrefix k).comp continuous_fst))))
      · simp only [Function.update_of_ne hj]
        exact (Convexity.StdSimplex.continuous_weights_apply ℝ j).comp continuous_fst

end HarmonicArtin

end OAI
