import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.Parabolic

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma exists_right_parabolic_decomposition (J : Set S) (w : W) :
    ∃ v a : W, a ∈ parabolic cs J ∧
      (∀ b ∈ parabolic cs J, cs.length v ≤ cs.length (v*b)) ∧
      w = v*a ∧ cs.length w = cs.length v + cs.length a := by
  obtain ⟨a,v,ha,hv,he,hl⟩ := exists_parabolic_decomposition cs J w⁻¹
  refine ⟨v⁻¹,a⁻¹,(parabolic cs J).inv_mem ha,?_,?_,?_⟩
  · intro b hb
    have h := hv b⁻¹ ((parabolic cs J).inv_mem hb)
    rw [← cs.length_inv (v⁻¹*b),mul_inv_rev,inv_inv,cs.length_inv]
    simpa only [cs.length_inv] using h
  · simpa only [mul_inv_rev,inv_inv] using congrArg Inv.inv he
  · simpa only [cs.length_inv,Nat.add_comm] using hl

lemma exists_right_descent {w : W} (hw : w ≠ 1) :
    ∃ i : S, cs.length (w*cs.simple i)+1=cs.length w := by
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced w⁻¹
  cases u with
  | nil => simp only [cs.wordProd_nil] at he; exact (hw (inv_eq_one.mp he)).elim
  | cons i u =>
    refine ⟨i, ?_⟩
    have hured : cs.IsReduced u := by simpa using hu.drop 1
    have he' : cs.simple i * w⁻¹ = cs.wordProd u := by
      rw [he,cs.wordProd_cons,cs.simple_mul_simple_cancel_left]
    have hlen := hu.eq
    rw [← he,List.length_cons] at hlen
    rw [← cs.length_inv (w*cs.simple i),mul_inv_rev,cs.inv_simple,he',hured.eq]
    simpa only [cs.length_inv] using hlen.symm

end HarmonicArtin.CoxeterExchange

end OAI
