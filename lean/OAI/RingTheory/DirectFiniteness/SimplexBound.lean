import OAI.RingTheory.DirectFiniteness.Pairing

namespace OAI

universe u_1

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.PolynomialPairing
variable {Q : Type u_1} [Field Q] [Fintype Q] {q n d t : ℕ}

omit [Field Q] [Fintype Q] in
lemma cube_card_le_simplex (a : Fin q ≃ Q) (htq : t ≤ q)
    (hcut : n * (t-1) ≤ d) : t^n ≤ (simplexPoints a n d).card := by
  let f : (Fin n → Fin t) → Simplex n q d := fun x => ⟨fun i =>
    ⟨(x i).val,(x i).isLt.trans_le htq⟩,by
      apply le_trans _ hcut
      calc
        (∑ i : Fin n, (x i).val) ≤ ∑ _i : Fin n, (t-1) := by
          apply Finset.sum_le_sum
          intro i _
          have := (x i).isLt
          omega
        _ = n*(t-1) := by simp⟩
  let g : (Fin n → Fin t) → simplexPoints a n d := fun x =>
    ⟨point a (f x).val,(mem_simplexPoints a).mpr ⟨f x,rfl⟩⟩
  have hg : Function.Injective g := by
    intro x y h
    funext i
    apply Fin.ext
    have hh := a.injective (congrFun (congrArg Subtype.val h) i)
    change (x i).val = (y i).val
    exact congrArg (fun z : Fin q => z.val) hh
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] using
    Fintype.card_le_of_injective g hg

lemma small_cube_cutoff (hn : 0 < n) (hq : 2*n ≤ q) :
    n * (q/(2*n)-1) ≤ (q-2)/2 ∧ q ≤ 4*n*(q/(2*n)) := by
  have hd : 0 < 2*n := by omega
  have ht : 0 < q/(2*n) := Nat.div_pos hq hd
  have hm := Nat.div_mul_le_self q (2*n)
  have hr := Nat.mod_lt q hd
  have he := Nat.mod_add_div q (2*n)
  have hs := Nat.sub_add_cancel (show 1 ≤ q/(2*n) by omega)
  constructor
  · apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    have hq2 : 2 ≤ q := by omega
    have hsub := Nat.sub_add_cancel hq2
    nlinarith
  · nlinarith

omit [Field Q] [Fintype Q] in
lemma simplex_density_bound (a : Fin q ≃ Q) (hn : 0 < n) (hq : 2*n ≤ q) :
    q^n ≤ (4*n)^n * (simplexPoints a n ((q-2)/2)).card := by
  obtain ⟨hcut,hfloor⟩ := small_cube_cutoff hn hq
  have hc := cube_card_le_simplex a (Nat.div_le_self q (2*n)) hcut
  calc
    q^n ≤ (4*n*(q/(2*n)))^n := Nat.pow_le_pow_left hfloor n
    _ = (4*n)^n * (q/(2*n))^n := mul_pow _ _ _
    _ ≤ (4*n)^n * (simplexPoints a n ((q-2)/2)).card := Nat.mul_le_mul_left _ hc

end KaplanskyCounterexample.PolynomialPairing
end

end OAI
