import OAI.RingTheory.DirectFiniteness.QuotientField

namespace OAI

noncomputable section
open scoped Classical
open Polynomial Module
namespace KaplanskyCounterexample.Prescription
variable (K : Type) [Field K] [CharP K 2]

def rootSubfield (h : ℕ) : Subfield K :=
  RingHom.eqLocusField (iterateFrobenius K 2 h) (RingHom.id K)

@[simp] lemma mem_rootSubfield (h : ℕ) (x : K) : x ∈ rootSubfield K h ↔ x^(2^h)=x := Iff.rfl

variable [Fintype K]

lemma rootSubfield_card_le (h : ℕ) (hh : 0 < h) :
    Fintype.card (rootSubfield K h) ≤ 2^h := by
  let p : K[X] := X^(2^h)-X
  have hq : 1 < (2:ℕ)^h := one_lt_pow₀ (by decide) (Nat.ne_of_gt hh)
  have hdeg : p.natDegree=2^h := by
    change (X^(2^h)-X : K[X]).natDegree=2^h
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq)]
    simp
  have hp : p ≠ 0 := by
    intro hz
    have hz' : p.natDegree=0 := hz ▸ natDegree_zero
    omega
  let f (x : rootSubfield K h) : p.roots.toFinset :=
    ⟨x.val,by
      rw [Multiset.mem_toFinset,mem_roots hp]
      change eval x.val (X^(2^h)-X : K[X])=0
      simp only [eval_sub,eval_pow,eval_X]
      exact sub_eq_zero.mpr x.property⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (show x.val=y.val from congrArg (fun z : p.roots.toFinset => z.val) he)
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at hc
  exact hc.trans ((Multiset.toFinset_card_le _).trans (hdeg ▸ card_roots' p))

lemma rootSubfield_card (h : ℕ) (hh : 0 < h) [Algebra (ZMod 2) K]
    (hd : h ∣ finrank (ZMod 2) K) :
    Fintype.card (rootSubfield K h)=2^h := by
  let F := GaloisField 2 h
  let : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F=2^h := by
    rw [Fintype.card_eq_nat_card,GaloisField.card 2 h (Nat.ne_of_gt hh)]
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (K := F) (L := K)
    (by rwa [GaloisField.finrank 2 (Nat.ne_of_gt hh)])
  let g (x : F) : rootSubfield K h := ⟨f x,by
    change (f x)^(2^h)=f x
    rw [← map_pow,← hF,FiniteField.pow_card]⟩
  have hg : Function.Injective g := by
    intro x y he
    exact f.injective (congrArg Subtype.val he)
  apply le_antisymm (rootSubfield_card_le K h hh)
  exact hF ▸ Fintype.card_le_of_injective g hg

end KaplanskyCounterexample.Prescription
end

end OAI
