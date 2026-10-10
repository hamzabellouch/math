import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V:Type*} [Fintype V] [DecidableEq V]

def integralQuadratic (C:Matrix V V ℤ) (x:V → ℤ) : ℤ :=
  ∑ i,∑ j,C i j*x i*x j

lemma integralQuadratic_even (C:Matrix V V ℤ) (hs:∀ i j,C i j=C j i)
    (hd:∀ i,C i i=2) (x:V → ℤ) : Even (integralQuadratic C x) := by
  have hh:∀ s:Finset V,Even (∑ i∈s,∑ j∈s,C i j*x i*x j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha,Finset.sum_add_distrib]
      have he : (∑ j∈s,C j a*x j*x a)=∑ j∈s,C a j*x a*x j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hs j a]
        ring
      rw [he,hd a]
      obtain ⟨k,hk⟩:=ih
      refine ⟨x a*x a+(∑ j∈s,C a j*x a*x j)+k,?_⟩
      rw [hk]
      ring
  exact hh Finset.univ

omit [DecidableEq V] in
lemma integralQuadratic_cast (C:Matrix V V ℤ) (x:V → ℤ) :
    (integralQuadratic C x:ℝ)=(fun i=>(x i:ℝ)) ⬝ᵥ
      ((C.map (Int.cast:ℤ → ℝ)) *ᵥ (fun i=>(x i:ℝ))) := by
  simp only [integralQuadratic,Int.cast_sum,Int.cast_mul,Matrix.mulVec,dotProduct,
    Finset.mul_sum,Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma integralQuadratic_ge_two (C:Matrix V V ℤ) (hs:∀ i j,C i j=C j i)
    (hd:∀ i,C i i=2) (hp:(C.map (Int.cast:ℤ → ℝ)).PosDef)
    (x:V → ℤ) (hx:x≠0) : 2 ≤ integralQuadratic C x := by
  have hx':(fun i=>(x i:ℝ))≠0 := by
    intro h
    apply hx
    ext i
    have hh:=congrFun h i
    change (x i:ℝ)=0 at hh
    change x i=0
    exact_mod_cast hh
  have hpos:=hp.dotProduct_mulVec_pos hx'
  simp only [star_trivial] at hpos
  rw [← integralQuadratic_cast] at hpos
  have hpos':0 < integralQuadratic C x := by exact_mod_cast hpos
  obtain ⟨k,hk⟩:=integralQuadratic_even C hs hd x
  omega

theorem integral_root_sign (C:Matrix V V ℤ) (hs:∀ i j,C i j=C j i)
    (hd:∀ i,C i i=2) (hoff:∀ i j,i≠j → C i j≤0)
    (hp:(C.map (Int.cast:ℤ → ℝ)).PosDef)
    (x:V → ℤ) (hq:integralQuadratic C x=2) :
    (∀ i,0 ≤ x i) ∨ (∀ i,x i≤0) := by
  by_contra hh
  obtain ⟨hn,hp'⟩:=not_or.mp hh
  obtain ⟨i,hi⟩:=not_forall.mp hn
  obtain ⟨j,hj⟩:=not_forall.mp hp'
  let p:V → ℤ:=fun i=>max (x i) 0
  let n:V → ℤ:=fun i=>min (x i) 0
  have hpne:p≠0 := by
    intro h
    have h':p j=0:=congrFun h j
    have hh:0 < x j:=lt_of_not_ge hj
    simp [p,max_eq_left hh.le] at h'
    omega
  have hnne:n≠0 := by
    intro h
    have h':n i=0:=congrFun h i
    have hh:x i < 0:=lt_of_not_ge hi
    simp [n,min_eq_left hh.le] at h'
    omega
  have hpp:=integralQuadratic_ge_two C hs hd hp p hpne
  have hnn:=integralQuadratic_ge_two C hs hd hp n hnne
  have hpnon:∀i,0 ≤ p i:=fun i=>le_max_right _ _
  have hnnon:∀i,n i≤0:=fun i=>min_le_right _ _
  have hdis:∀i,p i*n i=0 := by
    intro i
    by_cases h:0 ≤ x i
    · simp [p,n,max_eq_left h,min_eq_right h]
    · simp [p,n,max_eq_right (le_of_not_ge h),min_eq_left (le_of_not_ge h)]
  have hcross:0 ≤ ∑ i,∑ j,C i j*p i*n j := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij:i=j
    · subst j
      rw [mul_assoc,hdis,mul_zero]
    · exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonpos_of_nonneg (hoff i j hij) (hpnon i)) (hnnon j)
  have he : integralQuadratic C x=integralQuadratic C p+integralQuadratic C n+
      2*(∑ i,∑ j,C i j*p i*n j) := by
    have hx:∀ i,x i=p i+n i := by
      intro i
      simp [p,n]
    have hecross:(∑ i,∑ j,C i j*n i*p j)=∑ i,∑ j,C i j*p i*n j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hs j i]
      ring
    unfold integralQuadratic
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [hx i,hx j]
    simp only [mul_add,add_mul,Finset.sum_add_distrib]
    rw [hecross]
    ring
  omega

end HarmonicArtin

end OAI
