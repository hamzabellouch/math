import Mathlib

namespace OAI

noncomputable section
namespace Lech.IntegerWeights
open Function

 
def SeparatelyAffine {ι : Type*} [DecidableEq ι] (f : (ι → ℤ) → ℝ) : Prop :=
  ∀ (m : ι → ℤ) (i : ι) (a : ℤ),
    f (update m i a)=f (update m i 0)+(a:ℝ)*(f (update m i 1)-f (update m i 0))

 
lemma integer_affine_of_step (g : ℤ → ℝ)
    (hg : ∀ a,g a+g (a+2)=2*g (a+1)) (a : ℤ) :
    g a=g 0+(a:ℝ)*(g 1-g 0) := by
  have hs (a : ℤ) : g (a+1)-g a=g 1-g 0 := by
    induction a using Int.induction_on with
    | zero => simp
    | succ k ih =>
        have he := hg (k:ℤ)
        rw [show (k:ℤ)+1+1=k+2 by omega]
        linarith
    | pred k ih =>
        have he := hg (-(k:ℤ)-1)
        rw [show -(k:ℤ)-1+1= -k by omega]
        rw [show -(k:ℤ)-1+2= -k+1 by omega,
          show -(k:ℤ)-1+1= -k by omega] at he
        linarith
  induction a using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have he := hs (k:ℤ)
      push_cast at *
      nlinarith
  | pred k ih =>
      have he := hs (-(k:ℤ)-1)
      rw [show -(k:ℤ)-1+1= -k by omega] at he
      push_cast at *
      nlinarith

lemma separatelyAffine_of_step {ι : Type*} [DecidableEq ι]
    (f : (ι → ℤ) → ℝ)
    (hf : ∀ m i,f m+f (Pi.single i 1+(Pi.single i 1+m))=2*f (Pi.single i 1+m)) :
    SeparatelyAffine f := by
  intro m i a
  apply integer_affine_of_step (fun t => f (update m i t))
  intro x
  have he (t : ℤ) : Pi.single i 1+update m i t=update m i (t+1) := by
    funext j
    by_cases hj : j=i
    · subst j; simp [add_comm]
    · simp [hj]
  simpa only [he,show x+1+1=x+2 by omega] using hf (update m i x) i

lemma affine_eq_sum_of_slopes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℤ) → ℝ) (hf : SeparatelyAffine f) (c : ℝ)
    (hc : ∀ m i,f (update m i 1)-f (update m i 0)=c) (m : ι → ℤ) :
    f m=f (fun _ => 0)+c*∑ i,(m i:ℝ) := by
  let v (s : Finset ι) : ι → ℤ := fun i => if i∈s then m i else 0
  have hv (s : Finset ι) : f (v s)=f (fun _ => 0)+c*∑ i∈s,(m i:ℝ) := by
    induction s using Finset.induction_on with
    | empty => simp [v]
    | @insert i s hi ih =>
        have he : v (insert i s)=update (v s) i (m i) := by
          funext j
          by_cases hj : j=i
          · subst j; simp [v]
          · simp [v,hj]
        have hzero : update (v s) i 0=v s := by
          have hv0 : v s i=0 := by simp [v,hi]
          rw [←hv0,update_eq_self]
        rw [he,hf (v s) i (m i),hc,hzero,ih,Finset.sum_insert hi]
        ring
  simpa [v] using hv Finset.univ

lemma cons_update_zero {n : ℕ} (m : Fin (n+1) → ℤ) (a : ℤ) :
    update m 0 a=Fin.cons a (Fin.tail m) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

 

theorem symmetric_affine_diagonal_constant (n : ℕ) (f : (Fin n → ℤ) → ℝ)
    (hf : SeparatelyAffine f)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) m,f (m ∘ σ)=f m)
    (hdiag : ∀ m,f (fun i => m i+1)=f m) :
    ∀ m,f m=f (fun _ => 0) := by
  induction n with
  | zero => intro m; congr 1; funext i; exact Fin.elim0 i
  | succ n ih =>
    let g : (Fin n → ℤ) → ℝ := fun m => f (Fin.cons 1 m)-f (Fin.cons 0 m)
    have hhead (m : Fin n → ℤ) (a : ℤ) :
        f (Fin.cons a m)=f (Fin.cons 0 m)+(a:ℝ)*g m := by
      simpa only [Fin.update_cons_zero] using hf (Fin.cons 0 m) 0 a
    have hg : SeparatelyAffine g := by
      intro m i a
      have h1 := hf (Fin.cons 1 m) i.succ a
      have h0 := hf (Fin.cons 0 m) i.succ a
      simp only [←Fin.cons_update] at h1 h0
      dsimp only [g]
      rw [h1,h0]
      ring
    have hgsym (σ : Equiv.Perm (Fin n)) (m : Fin n → ℤ) : g (m ∘ σ)=g m := by
      let σ' : Equiv.Perm (Fin (n+1)) := Equiv.Perm.decomposeFin.symm (0,σ)
      have he (a : ℤ) : Fin.cons a (m ∘ σ)=(Fin.cons a m) ∘ σ' := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [σ']
        · simp [σ']
      dsimp only [g]
      rw [he,he,hsym,hsym]
    have hgdiag (m : Fin n → ℤ) : g (fun i => m i+1)=g m := by
      have he (a : ℤ) : Fin.cons a (fun i => m i+1)=(fun (i : Fin (n+1)) => (Fin.cons (α := fun _ => ℤ) (a-(1:ℤ)) m i : ℤ)+(1:ℤ)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      dsimp only [g]
      rw [he,he,hdiag,hdiag]
      norm_num only [sub_self,zero_sub]
      rw [hhead m (-1)]
      dsimp only [g]
      norm_num
    have hgconst := ih g hg hgsym hgdiag
    let c := g (fun _ => 0)
    have hzero (m : Fin (n+1) → ℤ) : f (update m 0 1)-f (update m 0 0)=c := by
      rw [cons_update_zero,cons_update_zero]
      exact hgconst (Fin.tail m)
    have hc (m : Fin (n+1) → ℤ) (i : Fin (n+1)) :
        f (update m i 1)-f (update m i 0)=c := by
      let σ : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 i
      calc
        _=f ((update m i 1) ∘ σ)-f ((update m i 0) ∘ σ) := by rw [hsym,hsym]
        _=f (update (m ∘ σ) 0 1)-f (update (m ∘ σ) 0 0) := by
          rw [update_comp_equiv,update_comp_equiv]
          simp [σ]
        _=c := hzero _
    have hformula := affine_eq_sum_of_slopes f hf c hc
    have hcone := hdiag (fun _ => 0)
    rw [hformula (fun _ => 0+1)] at hcone
    have hc0 : c=0 := by
      simp only [Int.cast_one,zero_add,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcone
      have hn : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr (by omega)
      nlinarith
    intro m
    rw [hformula m,hc0,zero_mul,add_zero]
end Lech.IntegerWeights

end

end OAI
