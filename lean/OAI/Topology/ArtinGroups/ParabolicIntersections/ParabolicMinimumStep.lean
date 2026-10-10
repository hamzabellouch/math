import OAI.Topology.ArtinGroups.Coxeter.Parabolic
import OAI.Topology.ArtinGroups.Coxeter.RightParabolicDecomposition

namespace OAI

/-! The Coxeter coset step used in the standard-parabolic retraction. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

/-- A nonminimal element has a left descent in the parabolic colors. -/
theorem exists_parabolic_left_descent (J : Set S) (w : W)
    (hw : ¬ IsParabolicMinimum cs J w) :
    ∃ t ∈ J, cs.length (cs.simple t*w) < cs.length w := by
  obtain ⟨a,v,ha,hv,he,hlen⟩ := exists_parabolic_decomposition cs J w
  have ha1 : a ≠ 1 := by
    intro ha1
    have hwv : w=v := by simpa only [ha1,one_mul] using he
    exact hw (hwv ▸ hv)
  obtain ⟨l,hl,hr,haeq⟩ := (mem_parabolic_iff_reduced_word cs J a).mp ha
  cases l with
  | nil => exact (ha1 (by simpa only [cs.wordProd_nil] using haeq.symm)).elim
  | cons t l =>
    refine ⟨t,hl t (by simp),?_⟩
    have htail : ∀ i ∈ l, i ∈ J := fun i hi => hl i (List.mem_cons_of_mem t hi)
    have htailp := wordProd_mem_parabolic cs J l htail
    have he' : cs.simple t*w=cs.wordProd l*v := by
      rw [he,←haeq,cs.wordProd_cons,←mul_assoc,cs.simple_mul_simple_cancel_left]
    rw [he',length_mul_of_minimum cs J v hv _ htailp]
    rw [←haeq,hr.eq] at hlen
    have hredtail : cs.IsReduced l := by simpa only [List.drop_succ_cons,List.drop_zero] using hr.drop 1
    rw [hredtail.eq]
    simp only [List.length_cons] at hlen
    omega

/-- Multiplying a minimal left-coset representative by one simple
reflection either remains minimal or crosses a wall of the parabolic. -/
theorem parabolic_minimum_step (J : Set S) (v : W)
    (hv : IsParabolicMinimum cs J v) (s : S) :
    IsParabolicMinimum cs J (v*cs.simple s) ∨
      ∃ t ∈ J, v*cs.simple s=cs.simple t*v := by
  by_cases hmin : IsParabolicMinimum cs J (v*cs.simple s)
  · exact Or.inl hmin
  right
  obtain ⟨t,ht,hdes⟩ := exists_parabolic_left_descent cs J _ hmin
  have htmin := hv (cs.simple t) (simple_mem_parabolic cs J ht)
  have hright := cs.length_mul_simple v s
  have hleft := cs.length_simple_mul (v*cs.simple s) t
  have hascent : cs.length (v*cs.simple s)=cs.length v+1 := by
    rcases hright with hr | hr
    · exact hr
    · have hbound := cs.length_mul_le (cs.simple t*(v*cs.simple s)) (cs.simple s)
      have hs : cs.simple s*cs.simple s=1 := by
        simpa only [mul_one] using cs.simple_mul_simple_cancel_left (w:=1) s
      rw [mul_assoc,mul_assoc,hs,mul_one,cs.length_simple] at hbound
      omega
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced v
  have hured : cs.IsReduced (u++[s]) := by
    change cs.length (cs.wordProd (u++[s]))=(u++[s]).length
    rw [cs.wordProd_append,cs.wordProd_singleton,←he,List.length_append,List.length_singleton,hascent,he,hu.eq]
  obtain ⟨j,hj,hdel⟩ := simple_exchange cs hured t (by
    simpa only [cs.wordProd_append,cs.wordProd_singleton,←he] using hdes)
  by_cases hju : j<u.length
  · rw [List.eraseIdx_append_of_lt_length hju,cs.wordProd_append,
      cs.wordProd_append,cs.wordProd_singleton,←he,←mul_assoc] at hdel
    have hd := mul_right_cancel hdel
    have hb := cs.length_wordProd_le (u.eraseIdx j)
    rw [←hd,List.length_eraseIdx,ite_eq_left hju,←hu.eq,←he] at hb
    have hpos : 0 < cs.length v := by
      rw [he,hu.eq]
      omega
    omega
  · have hjend : j=u.length := by
      simp only [List.length_append,List.length_singleton] at hj
      omega
    rw [hjend,List.eraseIdx_append_of_length_le (by omega),Nat.sub_self,
      List.eraseIdx_zero,List.tail_cons,List.append_nil,←he] at hdel
    have htv : cs.simple t*(v*cs.simple s)=v := by
      simpa only [cs.wordProd_append,cs.wordProd_singleton,←he] using hdel
    refine ⟨t,ht,?_⟩
    calc v*cs.simple s = cs.simple t*(cs.simple t*(v*cs.simple s)) := by
           rw [cs.simple_mul_simple_cancel_left]
         _ = cs.simple t*v := by rw [htv]

end HarmonicArtin.ParabolicIntersections

end OAI
