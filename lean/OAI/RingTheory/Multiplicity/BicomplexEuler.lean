import Mathlib
import OAI.RingTheory.Multiplicity.TensorCechEuler

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ell : TorsionLength I)

lemma finiteHomologyEuler_shifted_window (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n k N : ℕ) (hN : k+n≤N)
    (hz : ∀ q,q<0 ∨ (n:ℤ)<q → ell.realValue (K.homology q)=0) :
    finiteHomologyEuler ell K (-(k:ℤ)) N=(-1:ℝ)^k*finiteHomologyEuler ell K 0 n := by
  unfold finiteHomologyEuler
  rw [show N+1=k+(n+1)+(N-k-n) by omega,Finset.sum_range_add,Finset.sum_range_add]
  have hfirst : (∑ j∈Finset.range k,(-1:ℝ)^j*ell.realValue (K.homology (-(k:ℤ)+j)))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hz _ (Or.inl (by have := Finset.mem_range.mp hj; omega)),mul_zero]
  have hlast : (∑ j∈Finset.range (N-k-n),(-1:ℝ)^(k+(n+1)+j)*
      ell.realValue (K.homology (-(k:ℤ)+(k+(n+1)+j:ℕ))))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hz _ (Or.inr (by omega)),mul_zero]
  rw [hfirst,hlast,zero_add,add_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  rw [mul_assoc]
  congr 2
  congr 1
  push_cast
  ring_nf

namespace BicomplexTotal

lemma single_euler (K : Row (R:=R)) (p a : ℤ) (w : ℕ)
    (ht : ∀ q,powerTorsion I (K.homology q)) :
    finiteHomologyEuler ell (total ((single (Row (R:=R)) (.up ℤ) p).obj K) (.up ℤ)) a w=
      finiteHomologyEuler ell K (a-p) w := by
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hp := (powerTorsion I).prop_of_iso (singleHomologyIso K p (a+k)).symm (ht (-p+(a+k)))
  have he := ell.eq_of_iso (singleHomologyIso K p (a+k)) hp (ht _)
  change (ell.value _).toReal=(ell.value _).toReal
  rw [he]
  have hi : -p+(a+(k:ℤ))=a-p+k := by ring
  rw [hi]

 

lemma euler_rows (K : Double (R:=R)) (h n N : ℕ) (hN : h+n≤N)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (K.X p))
    (hq : ∀ p q,q<0 ∨ (n:ℤ)<q → IsZero ((K.X p).homology q))
    (hf : ∀ p q,ell.finiteClass ((K.X p).homology q)) :
    finiteHomologyEuler ell (total K (.up ℤ)) (-(h:ℤ)) N=
      ∑ k∈Finset.range (h+1),(-1:ℝ)^k*finiteHomologyEuler ell (K.X (-(h:ℤ)+k)) 0 n := by
  have he := FiniteComplex.euler_devissage ell functor (splitting) (-(h:ℤ)) N
    (-(h:ℤ)) (h+1) K (fun p hp => hb p (by omega))
    (fun p q => ell.finiteClass.prop_of_iso (singleHomologyIso (K.X p) p q).symm (hf p (-p+q)))
    (fun p => ?_) (fun p => ?_)
  · change finiteHomologyEuler ell (total K (.up ℤ)) _ _=_ at he
    rw [he]
    apply Finset.sum_congr rfl
    intro k hk
    change finiteHomologyEuler ell (total ((single (Row (R:=R)) (.up ℤ) (-(h:ℤ)+k)).obj (K.X (-(h:ℤ)+k))) (.up ℤ)) _ _=_
    rw [single_euler ell _ _ _ _ (fun q => (hf _ q).1)]
    have heq : -(h:ℤ)-(-(h:ℤ)+k)=-(k:ℤ) := by ring
    rw [heq]
    apply finiteHomologyEuler_shifted_window ell _ n k N (by have := Finset.mem_range.mp hk; omega)
    intro q hq'
    exact ell.realValue_zero (hq _ _ hq')
  · apply IsZero.of_iso _ (singleHomologyIso (K.X p) p _)
    by_cases hp : p < -(h:ℤ) ∨ 0<p
    · exact (homologyFunctor _ _ _).map_isZero (hb p hp)
    · exact hq p _ (Or.inl (by omega))
  · apply IsZero.of_iso _ (singleHomologyIso (K.X p) p _)
    by_cases hp : p < -(h:ℤ) ∨ 0<p
    · exact (homologyFunctor _ _ _).map_isZero (hb p hp)
    · exact hq p _ (Or.inr (by omega))
end BicomplexTotal
end Lech

end

end OAI
