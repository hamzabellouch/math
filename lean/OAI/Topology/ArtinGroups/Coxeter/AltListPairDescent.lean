import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.Parabolic
import OAI.Topology.ArtinGroups.Coxeter.AltList
import OAI.Topology.ArtinGroups.Geometry.TrigPhaseSqPrimitive

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

lemma altList_of_pair_descent (i j : B) (a : W)
    (ha : a ∈ parabolic cs ({i,j} : Set B))
    (hi : cs.length (cs.simple i*a) < cs.length a) :
    cs.IsReduced (altList i j (cs.length a)) ∧
      cs.wordProd (altList i j (cs.length a)) = a := by
  have hia : cs.simple i*a ∈ parabolic cs ({i,j} : Set B) :=
    (parabolic cs _).mul_mem (simple_mem_parabolic cs _ (by simp)) ha
  obtain ⟨u,hu,hr,he⟩ := (mem_parabolic_iff_reduced_word cs _ _).mp hia
  have hd := cs.length_simple_mul a i
  have hlen : u.length+1=cs.length a := by rw [← hr.eq,he]; omega
  have hprod : cs.wordProd (i::u)=a := by
    rw [cs.wordProd_cons,he,cs.simple_mul_simple_cancel_left]
  have hred : cs.IsReduced (i::u) := by
    change cs.length (cs.wordProd (i::u)) = (i::u).length
    rw [hprod,List.length_cons,hlen]
  have hshape := reduced_pair_cons_eq_alt cs i j u hred hu
  rw [hlen] at hshape
  rw [← hshape]
  exact ⟨hred,hprod⟩

variable [Fintype B] [DecidableEq B]

lemma pair_double_descent (i j : B) (hij : i ≠ j) (a : W)
    (ha : a ∈ parabolic cs ({i,j} : Set B))
    (hi : cs.length (cs.simple i*a) < cs.length a)
    (hj : cs.length (cs.simple j*a) < cs.length a) :
    0 < M i j ∧ cs.length a=M i j ∧
      cs.wordProd (altList i j (M i j))=a ∧
      cs.wordProd (altList j i (M i j))=a := by
  obtain ⟨hired,hiprod⟩ := altList_of_pair_descent cs i j a ha hi
  obtain ⟨hjred,hjprod⟩ := altList_of_pair_descent cs j i a
    (by simpa only [Set.pair_comm] using ha) hj
  have hpow : (cs.simple i*cs.simple j)^(cs.length a)=1 := by
    rw [← wordProd_altList_difference, hiprod,hjprod,mul_inv_cancel]
  have hdvd := (Geometric.simple_pair_pow_eq_one_iff cs i j hij (cs.length a)).mp hpow
  have hn : 0 < cs.length a := by omega
  have hm : M i j ≠ 0 := by
    intro hzero
    rw [hzero, zero_dvd_iff] at hdvd
    omega
  have hm2 : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
  have hle := reduced_altList_le cs i j (cs.length a) hm2 hired
  have hmle := Nat.le_of_dvd hn hdvd
  have heq : cs.length a=M i j := by omega
  exact ⟨by omega, heq, by simpa only [heq] using hiprod,
    by simpa only [heq] using hjprod⟩

lemma double_descent_prefix (i j : B) (hij : i ≠ j) (w : W)
    (hi : cs.length (cs.simple i*w) < cs.length w)
    (hj : cs.length (cs.simple j*w) < cs.length w) :
    ∃ v : W, 0 < M i j ∧ cs.length w=M i j+cs.length v ∧
      w = cs.wordProd (altList i j (M i j))*v ∧
      w = cs.wordProd (altList j i (M i j))*v := by
  obtain ⟨a,v,ha,hv,he,hlen⟩ := exists_parabolic_decomposition cs ({i,j} : Set B) w
  have hai : cs.length (cs.simple i*a) < cs.length a := by
    apply (descent_parabolic_factor cs _ ha hv (by simp : i ∈ ({i,j}:Set B))).mp
    simpa only [← he] using hi
  have haj : cs.length (cs.simple j*a) < cs.length a := by
    apply (descent_parabolic_factor cs _ ha hv (by simp : j ∈ ({i,j}:Set B))).mp
    simpa only [← he] using hj
  obtain ⟨hm,hlenA,hip,hjp⟩ := pair_double_descent cs i j hij a ha hai haj
  exact ⟨v,hm, by simpa only [hlenA] using hlen, by simpa only [hip] using he,
    by simpa only [hjp] using he⟩

end HarmonicArtin.CoxeterExchange

end OAI
