import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PrismPrefix

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval
open Simplicial CategoryTheory Opposite

attribute [local instance] Classical.decEq Classical.propDecidable

lemma linearMap_insertNth {n:ℕ} {Y:Type*} [Fintype Y]
    (φ:Fin (n+1)→Y) (k:Fin (n+1)) (a:ℝ) (v:Fin n→ℝ) :
    FunOnFinite.linearMap ℝ ℝ φ (k.insertNth a v)=
      Pi.single (φ k) a+FunOnFinite.linearMap ℝ ℝ (φ∘k.succAbove) v := by
  ext y
  simp only [FunOnFinite.linearMap_apply_apply,Pi.add_apply,Pi.single_apply,
    Finset.sum_filter]
  rw [Fin.sum_univ_succAbove _ k]
  simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,Function.comp_apply]
  simp only [eq_comm (a:=y) (b:=φ k)]

lemma collapse_insertNth {n:ℕ} (k:Fin (n+1)) (a:ℝ) (v:Fin (n+1)→ℝ) :
    FunOnFinite.linearMap ℝ ℝ k.predAbove (k.castSucc.insertNth a v)=Pi.single k a+v := by
  rw [linearMap_insertNth,Fin.predAbove_castSucc_self]
  have he:k.predAbove∘k.castSucc.succAbove=id:=funext (Fin.predAbove_succAbove k)
  rw [he,FunOnFinite.linearMap_id,LinearMap.id_apply]
  ext i
  simp only [Pi.add_apply,Pi.single_apply]
  by_cases hi:i=k <;> simp only [hi,ite_true,ite_false]

lemma succAbove_le_castSucc_iff {n:ℕ} (k i:Fin (n+1)) :
    k.castSucc.succAbove i≤k.castSucc ↔ i<k := by
  by_cases hi:i<k
  · rw [Fin.succAbove_castSucc_of_lt _ _ hi]
    simp only [Fin.castSucc_le_castSucc_iff,hi,iff_true]; exact hi.le
  · rw [Fin.succAbove_castSucc_of_le _ _ (not_lt.mp hi)]
    simp only [Fin.le_iff_val_le_val,Fin.val_succ,Fin.val_castSucc,
      Fin.lt_def] at hi ⊢
    omega

def prismFlag {n:ℕ} (k:Fin (n+1)) (i:Fin (n+2)) : Fin 2 :=
  if i≤k.castSucc then 0 else 1

lemma flag_insertNth {n:ℕ} (k:Fin (n+1)) (a:ℝ) (v:Fin (n+1)→ℝ) :
    FunOnFinite.linearMap ℝ ℝ (prismFlag k) (k.castSucc.insertNth a v) 0=
      a+∑i∈Finset.Iio k,v i := by
  rw [linearMap_insertNth]
  simp only [Pi.add_apply,prismFlag,le_refl,ite_true,Pi.single_eq_same,
    FunOnFinite.linearMap_apply_apply,Finset.sum_filter,Function.comp_apply,
    succAbove_le_castSucc_iff]
  congr 1
  rw [←Finset.sum_filter]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
    by_cases hi:i<k <;> simp [hi]
  · intro _ _; rfl

lemma simplex_map_weights {Source Target : Type*} [Finite Source] [Finite Target]
    (function : Source → Target) (simplex : Convexity.StdSimplex ℝ Source) :
    ⇑(Convexity.StdSimplex.map function simplex).weights =
      FunOnFinite.linearMap ℝ ℝ function simplex.weights := by
  change ⇑(Finsupp.mapDomain function simplex.weights) =
    Finsupp.equivFunOnFinite (Finsupp.mapDomain function
      (Finsupp.equivFunOnFinite.symm (Finsupp.equivFunOnFinite simplex.weights)))
  rw [Equiv.symm_apply_apply]
  rfl

lemma prismSimplex_collapse {n:ℕ} (k:Fin (n+1))
    (p:Convexity.StdSimplex ℝ (Fin (n+1))×I) :
    Convexity.StdSimplex.map k.predAbove (prismSimplex k p)=p.1 := by
  apply Convexity.StdSimplex.ext
  apply DFunLike.coe_injective
  rw [simplex_map_weights]
  change FunOnFinite.linearMap ℝ ℝ k.predAbove (k.castSucc.insertNth _ _)=_
  rw [collapse_insertNth]
  ext i
  by_cases hi:i=k
  · subst i; simp only [Pi.add_apply,Pi.single_eq_same,Function.update_self]; ring
  · simp only [Pi.add_apply,Pi.single_eq_of_ne hi,Function.update_of_ne hi,zero_add]

lemma prismSimplex_time {n:ℕ} (k:Fin (n+1))
    (p:Convexity.StdSimplex ℝ (Fin (n+1))×I)
    (hp:p∈PrismCell k) :
    (Convexity.StdSimplex.map (prismFlag k) (prismSimplex k p)).weights 0=p.2.val := by
  rw [simplex_map_weights]
  change FunOnFinite.linearMap ℝ ℝ (prismFlag k) (k.castSucc.insertNth _ _) 0=_
  rw [flag_insertNth]
  have he:(∑i∈Finset.Iio k,Function.update p.1.weights k
      (p.1.weights k-prismLeft k p) i)=prismPrefix p.1 k:=by
    apply Finset.sum_congr rfl
    intro i hi
    exact Function.update_of_ne (ne_of_lt (Finset.mem_Iio.mp hi)) _ _
  rw [he,prismLeft_cell k p hp]
  ring

lemma simplex_insertNth_decomp {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    k.castSucc.insertNth (w.weights k.castSucc)
      (fun i=>w.weights (k.castSucc.succAbove i))=w.weights := by
  funext i
  obtain rfl|⟨j,rfl⟩:=Fin.eq_self_or_eq_succAbove k.castSucc i
  · exact Fin.insertNth_apply_same _ _ _
  · exact Fin.insertNth_apply_succAbove _ _ _ _

lemma simplex_flag_nonneg_le_one {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    (Convexity.StdSimplex.map (prismFlag k) w).weights 0∈Set.Icc (0:ℝ) 1 := by
  constructor
  · exact (Convexity.StdSimplex.map (prismFlag k) w).weights_nonneg 0
  · have hs:=(Convexity.StdSimplex.map (prismFlag k) w).total_of_fintype
    rw [Fin.sum_univ_two] at hs
    linarith [(Convexity.StdSimplex.map (prismFlag k) w).weights_nonneg 1]

noncomputable def prismMarginals {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    Convexity.StdSimplex ℝ (Fin (n+1))×I :=
  (Convexity.StdSimplex.map k.predAbove w,
    ⟨(Convexity.StdSimplex.map (prismFlag k) w).weights 0,simplex_flag_nonneg_le_one k w⟩)

lemma prismMarginals_coordinates {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    ⇑(prismMarginals k w).1.weights=Pi.single k (w.weights k.castSucc)+
      (fun i=>w.weights (k.castSucc.succAbove i)) ∧
    (prismMarginals k w).2.val=w.weights k.castSucc+
      ∑i∈Finset.Iio k,w.weights (k.castSucc.succAbove i) := by
  have he:=simplex_insertNth_decomp k w
  constructor
  · change ⇑(Convexity.StdSimplex.map k.predAbove w).weights = _
    rw [simplex_map_weights]
    nth_rw 1 [←he]; exact collapse_insertNth _ _ _
  · change (Convexity.StdSimplex.map (prismFlag k) w).weights 0 = _
    rw [simplex_map_weights]
    nth_rw 1 [←he]; exact flag_insertNth _ _ _

lemma prismMarginals_prefix {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    prismPrefix (prismMarginals k w).1 k=∑i∈Finset.Iio k,w.weights (k.castSucc.succAbove i) := by
  unfold prismPrefix
  rw [(prismMarginals_coordinates k w).1]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply,Pi.single_eq_of_ne (ne_of_lt (Finset.mem_Iio.mp hi)),zero_add]

lemma prismMarginals_cell {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    prismMarginals k w∈PrismCell k := by
  have hc:=prismMarginals_coordinates k w
  change prismPrefix (prismMarginals k w).1 k≤(prismMarginals k w).2.val ∧
    (prismMarginals k w).2.val≤prismPrefix (prismMarginals k w).1 k+(prismMarginals k w).1.weights k
  rw [prismMarginals_prefix,hc.1,hc.2]
  simp only [Pi.add_apply,Pi.single_eq_same]
  constructor <;> linarith [w.weights_nonneg k.castSucc,w.weights_nonneg (k.castSucc.succAbove k)]

lemma prismSimplex_marginals {n:ℕ} (k:Fin (n+1))
    (w:Convexity.StdSimplex ℝ (Fin (n+2))) :
    prismSimplex k (prismMarginals k w)=w := by
  have hl:prismLeft k (prismMarginals k w)=w.weights k.castSucc:=by
    rw [prismLeft_cell _ _ (prismMarginals_cell k w),prismMarginals_prefix,
      (prismMarginals_coordinates k w).2]
    ring
  apply Convexity.StdSimplex.ext
  apply DFunLike.coe_injective
  change k.castSucc.insertNth _ _=w.weights
  rw [hl]
  convert simplex_insertNth_decomp k w using 1
  congr 1
  funext i
  rw [(prismMarginals_coordinates k w).1]
  by_cases hi:i=k
  · subst i
    simp only [Function.update_self,Pi.add_apply,Pi.single_eq_same]; ring
  · simp only [Function.update_of_ne hi,Pi.add_apply,Pi.single_eq_of_ne hi,zero_add]

lemma prismMarginals_simplex {n:ℕ} (k:Fin (n+1))
    (p:Convexity.StdSimplex ℝ (Fin (n+1))×I)
    (hp:p∈PrismCell k) : prismMarginals k (prismSimplex k p)=p := by
  apply Prod.ext
  · exact prismSimplex_collapse k p
  · apply Subtype.ext; exact prismSimplex_time k p hp

end HarmonicArtin

end OAI
