import Mathlib
import OAI.RingTheory.Multiplicity.OrderedRootBasis

namespace OAI

noncomputable section
namespace Lech.UniversalSplitting
open Polynomial
universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

 

lemma degree_fill (t : R) (a b c : S) (hab : b+algebraMap R S t*a=1)
    (Q : Submodule R S) (d : ℕ)
    (hh : ∀ e : ℕ,e≤d → a^e*b^(d-e)*c∈Q) (extra : ℕ) :
    ∀ e k : ℕ,e+k+extra=d → a^e*b^k*c∈Q := by
  induction extra with
  | zero =>
      intro e k he
      have hk : k=d-e := by omega
      rw [hk]
      exact hh e (by omega)
  | succ extra ih =>
      intro e k he
      have h₁ := ih e (k+1) (by omega)
      have h₂ := ih (e+1) k (by omega)
      have hl := Q.add_mem h₁ (Q.smul_mem t h₂)
      convert hl using 1
      rw [Algebra.smul_def,pow_succ,pow_succ]
      calc
        a^e*b^k*c = a^e*b^k*c*(b+algebraMap R S t*a) := by rw [hab,mul_one]
        _ = _ := by ring

lemma power_in_homogeneous_span (t : R) (x c : S) (Q : Submodule R S) (d e : ℕ) (he : e≤d)
    (hh : ∀ j : ℕ,j≤d → (-x)^j*(1+algebraMap R S t*x)^(d-j)*c∈Q) : x^e*c∈Q := by
  have ha := degree_fill t (-x) (1+algebraMap R S t*x) c (by ring) Q d hh (d-e) e 0 (by omega)
  simp only [pow_zero,mul_one] at ha
  have hb := Q.smul_mem ((-1:R)^e) ha
  convert hb using 1
  simp only [Algebra.smul_def,map_pow,map_neg,map_one,←mul_assoc,←mul_pow,neg_mul,one_mul,neg_neg]

 
def binaryPower (t : R) : (n : ℕ) → (Fin n → S) → PowerIndex n → S
  | 0,_,_ => 1
  | n+1,rs,e => (-rs 0)^e.1.val * (1+algebraMap R S t*rs 0)^(n-e.1.val) *
      binaryPower t n (fun i => rs i.succ) e.2

lemma powerMonomial_mem_binary_span (t : R) (n : ℕ) (rs : Fin n → S) (e : PowerIndex n) :
    powerMonomial n rs e ∈ Submodule.span R (Set.range (binaryPower t n rs)) := by
  induction n with
  | zero => exact Submodule.subset_span ⟨e,rfl⟩
  | succ n ih =>
      let Q := Submodule.span R (Set.range (binaryPower t (n+1) rs))
      apply power_in_homogeneous_span t (rs 0) (powerMonomial n (fun i => rs i.succ) e.2) Q n e.1.val
        (by have := e.1.isLt; omega)
      intro j hj
      let a := (-rs 0)^j*(1+algebraMap R S t*rs 0)^(n-j)
      have ht := ih (fun i => rs i.succ) e.2
      have hs : Submodule.span R (Set.range (binaryPower t n (fun i => rs i.succ))) ≤
          Q.comap (LinearMap.mulLeft R a) := by
        apply Submodule.span_le.mpr
        rintro x ⟨e',rfl⟩
        exact Submodule.subset_span ⟨(⟨j,by omega⟩,e'),rfl⟩
      exact hs ht

variable {n : ℕ} {f : R[X]}
lemma Data.binaryPower_span_eq_top (d : Data R n f) (hf : f.natDegree≤n) (ht : f.coeff n=1) (t : R) :
    Submodule.span R (Set.range (binaryPower t n d.roots))=⊤ := by
  obtain ⟨b,hb⟩ := d.exists_power_basis_of_top hf ht
  apply top_unique
  rw [←b.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨e,rfl⟩
  rw [hb]
  exact powerMonomial_mem_binary_span t n d.roots e

instance powerIndexFintype (n : ℕ) : Fintype (PowerIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Fin (n+1) × PowerIndex n))

 

theorem Data.exists_binary_basis (d : Data R n f) (hf : f.natDegree≤n) (ht : f.coeff n=1) (t : R) :
    ∃ b : Module.Basis (PowerIndex n) R d.S, ∀ e,b e=binaryPower t n d.roots e := by
  classical
  obtain ⟨b,hb⟩ := d.exists_power_basis_of_top hf ht
  let : Module.Finite R d.S := d.finite
  let g := Finsupp.linearCombination R (binaryPower t n d.roots)
  have hg : Function.Surjective g := by
    apply LinearMap.range_eq_top.mp
    rw [Finsupp.range_linearCombination]
    exact d.binaryPower_span_eq_top hf ht t
  have hbij := OrzechProperty.bijective_of_surjective_of_injective b.repr.symm.toLinearMap g
    b.repr.symm.injective hg
  let bb : Module.Basis (PowerIndex n) R d.S := Module.Basis.ofRepr (LinearEquiv.ofBijective g hbij).symm
  refine ⟨bb,?_⟩
  intro e
  change (LinearEquiv.ofBijective g hbij) (Finsupp.single e 1)=_
  simp [g]
 
def powerWeight (n : ℕ) (i : Fin n) : ℕ := n-(i.val+1)

def powerExponent : (n : ℕ) → PowerIndex n → Fin n → ℕ
  | 0,_ => Fin.elim0
  | n+1,e => Fin.cons e.1.val (powerExponent n e.2)

lemma powerWeight_succ (n : ℕ) (i : Fin n) : powerWeight (n+1) i.succ=powerWeight n i := by
  simp [powerWeight,Fin.val_succ,Nat.add_sub_add_right]

lemma powerExponent_bound (n : ℕ) (e : PowerIndex n) (i : Fin n) :
    powerExponent n e i≤powerWeight n i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun i => ?_) i
      · change e.1.val≤n+1-(0+1)
        have := e.1.isLt
        omega
      · change powerExponent n e.2 i≤powerWeight (n+1) i.succ
        rw [powerWeight_succ]
        exact ih e.2 i

lemma binaryPower_prod (t : R) (n : ℕ) (rs : Fin n → S) (e : PowerIndex n) :
    binaryPower t n rs e = ∏ i,(-rs i)^(powerExponent n e i)*
      (1+algebraMap R S t*rs i)^(powerWeight n i-powerExponent n e i) := by
  induction n with
  | zero => simp [binaryPower]
  | succ n ih =>
      rw [Fin.prod_univ_succ]
      simp only [powerExponent,Fin.cons_zero,Fin.cons_succ,powerWeight_succ]
      change _ = (-rs 0)^e.1.val*(1+algebraMap R S t*rs 0)^(n-e.1.val)*_
      rw [←ih]
      rfl

end Lech.UniversalSplitting

end

end OAI
