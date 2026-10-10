import Mathlib
import OAI.Topology.ArtinGroups.DeligneDefinitions
import OAI.Topology.ArtinGroups.Coxeter.ReducedWordProperty

namespace OAI

namespace HarmonicArtin
universe v
variable {S : Type v}
open CoxeterExchange

lemma wordArtin_altList (M : CoxeterMatrix S) (i j : S) (n : ℕ) :
    wordArtin M (altList i j n) = PresentedGroup.mk (braidRelators M) (alternating i j n) := by
  induction n generalizing i j with
  | zero => simp [wordArtin,alternating]
  | succ n ih =>
    simp only [altList_succ,wordArtin,List.map_cons,List.prod_cons,alternating,map_mul]
    rw [← ih]
    rfl

lemma wordArtin_braid (M : CoxeterMatrix S) (i j : S) :
    wordArtin M (altList i j (M i j)) = wordArtin M (altList j i (M i j)) := by
  rw [wordArtin_altList,wordArtin_altList]
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨(i,j),rfl⟩

theorem wordArtin_eq_of_reduced [Finite S] (M : CoxeterMatrix S)
    (u v : List S)
    (hu : M.toCoxeterSystem.IsReduced u) (hv : M.toCoxeterSystem.IsReduced v)
    (he : wordCoxeter M u=wordCoxeter M v) : wordArtin M u=wordArtin M v := by
  classical
  let := Fintype.ofFinite S
  exact reduced_word_property M.toCoxeterSystem (generator M) (wordArtin_braid M)
    u v hu hv he

noncomputable def reducedExpression (M : CoxeterMatrix S) (w : M.Group) : List S :=
  Classical.choose (M.toCoxeterSystem.exists_isReduced w)

lemma reducedExpression_reduced (M : CoxeterMatrix S) (w : M.Group) :
    M.toCoxeterSystem.IsReduced (reducedExpression M w) :=
  (Classical.choose_spec (M.toCoxeterSystem.exists_isReduced w)).1

lemma wordCoxeter_reducedExpression (M : CoxeterMatrix S) (w : M.Group) :
    wordCoxeter M (reducedExpression M w)=w :=
  (Classical.choose_spec (M.toCoxeterSystem.exists_isReduced w)).2.symm

noncomputable def positiveLift (M : CoxeterMatrix S) (w : M.Group) : Artin M :=
  wordArtin M (reducedExpression M w)

lemma positiveLift_word [Finite S] (M : CoxeterMatrix S) (u : List S)
    (hu : M.toCoxeterSystem.IsReduced u) :
    positiveLift M (wordCoxeter M u)=wordArtin M u :=
  wordArtin_eq_of_reduced M _ u (reducedExpression_reduced M _) hu
    (wordCoxeter_reducedExpression M _)

@[simp] lemma positiveLift_one [Finite S] (M : CoxeterMatrix S) : positiveLift M 1=1 := by
  have hr : M.toCoxeterSystem.IsReduced ([] : List S) := by simp [CoxeterSystem.IsReduced]
  simpa only [wordCoxeter,List.map_nil,List.prod_nil,wordArtin] using positiveLift_word M [] hr

lemma wordArtin_append (M : CoxeterMatrix S) (u v : List S) :
    wordArtin M (u++v)=wordArtin M u*wordArtin M v := by
  simp only [wordArtin,List.map_append,List.prod_append]

lemma positiveLift_mul [Finite S] (M : CoxeterMatrix S) (a b : M.Group)
    (hab : M.toCoxeterSystem.length (a*b) =
      M.toCoxeterSystem.length a+M.toCoxeterSystem.length b) :
    positiveLift M (a*b)=positiveLift M a*positiveLift M b := by
  let u := reducedExpression M a
  let v := reducedExpression M b
  have hru := reducedExpression_reduced M a
  have hrv := reducedExpression_reduced M b
  have hu : M.toCoxeterSystem.wordProd u=a := wordCoxeter_reducedExpression M a
  have hv : M.toCoxeterSystem.wordProd v=b := wordCoxeter_reducedExpression M b
  have hr : M.toCoxeterSystem.IsReduced (u++v) := by
    change M.toCoxeterSystem.length (M.toCoxeterSystem.wordProd (u++v))=(u++v).length
    rw [M.toCoxeterSystem.wordProd_append,hu,hv,hab,List.length_append]
    rw [← hu,← hv,hru.eq,hrv.eq]
  have hp : wordCoxeter M (u++v)=a*b := by
    change M.toCoxeterSystem.wordProd (u++v)=a*b
    rw [M.toCoxeterSystem.wordProd_append,hu,hv]
  rw [← hp,positiveLift_word M (u++v) hr,wordArtin_append]
  rfl

lemma wordArtin_mem_parabolic (M : CoxeterMatrix S) (J : Set S) (u : List S)
    (hu : ∀ i ∈ u, i ∈ J) : wordArtin M u ∈ artinParabolic M J := by
  induction u with
  | nil => exact (artinParabolic M J).one_mem
  | cons i u ih =>
    change generator M i*wordArtin M u ∈ artinParabolic M J
    exact (artinParabolic M J).mul_mem (Subgroup.subset_closure ⟨i,hu i (by simp),rfl⟩)
      (ih (fun k hk => hu k (List.mem_cons_of_mem i hk)))

lemma positiveLift_mem_parabolic [Finite S] (M : CoxeterMatrix S) (J : Set S)
    (w : M.Group) (hw : w ∈ coxeterParabolic M J) :
    positiveLift M w ∈ artinParabolic M J := by
  obtain ⟨u,hu,hr,he⟩ :=
    (mem_parabolic_iff_reduced_word M.toCoxeterSystem J w).mp hw
  change wordCoxeter M u=w at he
  rw [← he,positiveLift_word M u hr]
  exact wordArtin_mem_parabolic M J u hu

end HarmonicArtin

end OAI
