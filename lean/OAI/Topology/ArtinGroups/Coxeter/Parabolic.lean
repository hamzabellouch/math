import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.Signs

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

lemma exists_reduced_subword (u : List B) :
    ∃ v, v.Sublist u ∧ cs.IsReduced v ∧ cs.wordProd v = cs.wordProd u := by
  induction u with
  | nil => exact ⟨[], .refl _, by simp [CoxeterSystem.IsReduced], rfl⟩
  | cons i u ih =>
    obtain ⟨v,hv,hr,he⟩ := ih
    rcases cs.length_simple_mul (cs.wordProd v) i with ha | hd
    · refine ⟨i::v, List.cons_sublist_cons.mpr hv, ?_, ?_⟩
      · simpa only [CoxeterSystem.IsReduced, cs.wordProd_cons, List.length_cons, hr.eq] using ha
      · simp only [cs.wordProd_cons, he]
    · obtain ⟨j,hj,hjprod⟩ := simple_exchange cs hr i (by omega)
      refine ⟨v.eraseIdx j, List.Sublist.cons i ((v.eraseIdx_sublist j).trans hv), ?_, ?_⟩
      · change cs.length (cs.wordProd (v.eraseIdx j)) = (v.eraseIdx j).length
        rw [← hjprod, List.length_eraseIdx, ite_eq_left hj]
        have := hr.eq
        omega
      · rw [← hjprod, he, cs.wordProd_cons]

def parabolic (J : Set B) : Subgroup W := Subgroup.closure (cs.simple '' J)

lemma simple_mem_parabolic (J : Set B) {i : B} (hi : i ∈ J) :
    cs.simple i ∈ parabolic cs J := Subgroup.subset_closure ⟨i,hi,rfl⟩

lemma wordProd_mem_parabolic (J : Set B) (u : List B) (hu : ∀ i ∈ u, i ∈ J) :
    cs.wordProd u ∈ parabolic cs J := by
  induction u with
  | nil => simpa only [cs.wordProd_nil] using (parabolic cs J).one_mem
  | cons i u ih =>
    rw [cs.wordProd_cons]
    exact (parabolic cs J).mul_mem (simple_mem_parabolic cs J (hu i (by simp)))
      (ih (fun j hj => hu j (List.mem_cons_of_mem i hj)))

lemma mem_parabolic_iff_word (J : Set B) (w : W) :
    w ∈ parabolic cs J ↔ ∃ u : List B, (∀ i ∈ u, i ∈ J) ∧ cs.wordProd u = w := by
  constructor
  · intro hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx
      exact ⟨[i], by simpa, by simp⟩
    | one => exact ⟨[], by simp, by simp⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨u,hu,rfl⟩ := ihx
      obtain ⟨v,hv,rfl⟩ := ihy
      exact ⟨u++v, fun i hi => (List.mem_append.mp hi).elim (hu i) (hv i), cs.wordProd_append u v⟩
    | inv x hx ih =>
      obtain ⟨u,hu,rfl⟩ := ih
      exact ⟨u.reverse, by simpa only [List.mem_reverse] using hu, cs.wordProd_reverse u⟩
  · rintro ⟨u,hu,rfl⟩
    exact wordProd_mem_parabolic cs J u hu

lemma mem_parabolic_iff_reduced_word (J : Set B) (w : W) :
    w ∈ parabolic cs J ↔
      ∃ u : List B, (∀ i ∈ u, i ∈ J) ∧ cs.IsReduced u ∧ cs.wordProd u = w := by
  constructor
  · intro hw
    obtain ⟨u,hu,rfl⟩ := (mem_parabolic_iff_word cs J w).mp hw
    obtain ⟨v,hv,hr,he⟩ := exists_reduced_subword cs u
    exact ⟨v, fun i hi => hu i (hv.subset hi), hr, he⟩
  · rintro ⟨u,hu,hr,rfl⟩
    exact wordProd_mem_parabolic cs J u hu

def IsParabolicMinimum (J : Set B) (w : W) : Prop :=
  ∀ a ∈ parabolic cs J, cs.length w ≤ cs.length (a*w)

lemma length_word_mul_of_minimum (J : Set B) (w : W) (hw : IsParabolicMinimum cs J w)
    (u : List B) (hu : cs.IsReduced u) (hJ : ∀ i ∈ u, i ∈ J) :
    cs.length (cs.wordProd u * w) = u.length + cs.length w := by
  induction u with
  | nil => simp
  | cons i u ih =>
    have hured : cs.IsReduced u := by simpa using hu.drop 1
    have huJ : ∀ j ∈ u, j ∈ J := fun j hj => hJ j (List.mem_cons_of_mem i hj)
    have hi := ih hured huJ
    obtain ⟨v,hv,hvprod⟩ := cs.exists_isReduced w
    have huv : cs.IsReduced (u++v) := by
      change cs.length (cs.wordProd (u++v)) = (u++v).length
      rw [cs.wordProd_append, ← hvprod, hi, List.length_append, ← hv.eq, ← hvprod]
    rcases cs.length_simple_mul (cs.wordProd u * w) i with ha | hd
    · simpa only [cs.wordProd_cons, mul_assoc, List.length_cons, hi, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ha
    · exfalso
      have hd' : cs.length (cs.simple i * cs.wordProd (u++v)) < cs.length (cs.wordProd (u++v)) := by
        rw [cs.wordProd_append, ← hvprod]
        omega
      obtain ⟨j,hj,he⟩ := simple_exchange cs huv i hd'
      by_cases hju : j < u.length
      · rw [List.eraseIdx_append_of_lt_length hju, cs.wordProd_append,
          cs.wordProd_append, ← mul_assoc] at he
        have he' := mul_right_cancel he
        have hb := cs.length_wordProd_le (u.eraseIdx j)
        rw [List.length_eraseIdx, ite_eq_left hju, ← he', ← cs.wordProd_cons, hu.eq] at hb
        simp only [List.length_cons] at hb
        omega
      · have hjv : j-u.length < v.length := by simp only [List.length_append] at hj; omega
        rw [List.eraseIdx_append_of_length_le (by omega), cs.wordProd_append,
          cs.wordProd_append, ← hvprod] at he
        let a := (cs.wordProd u)⁻¹ * cs.simple i * cs.wordProd u
        have haJ : a ∈ parabolic cs J :=
          (parabolic cs J).mul_mem ((parabolic cs J).mul_mem
            ((parabolic cs J).inv_mem (wordProd_mem_parabolic cs J u huJ))
            (simple_mem_parabolic cs J (hJ i (by simp))))
            (wordProd_mem_parabolic cs J u huJ)
        have he' : a*w = cs.wordProd (v.eraseIdx (j-u.length)) := by
          dsimp [a]
          calc
            _ = (cs.wordProd u)⁻¹ * (cs.simple i * (cs.wordProd u*w)) := by group
            _ = _ := by rw [he]; group
        have hmin := hw a haJ
        rw [he'] at hmin
        have hb := cs.length_wordProd_le (v.eraseIdx (j-u.length))
        rw [List.length_eraseIdx, ite_eq_left hjv, ← hv.eq, ← hvprod] at hb
        have hvpos : 0 < cs.length w := by rw [hvprod, hv.eq]; omega
        omega

lemma length_mul_of_minimum (J : Set B) (w : W) (hw : IsParabolicMinimum cs J w)
    (a : W) (ha : a ∈ parabolic cs J) :
    cs.length (a*w) = cs.length a + cs.length w := by
  obtain ⟨u,hu,hr,rfl⟩ := (mem_parabolic_iff_reduced_word cs J a).mp ha
  rw [length_word_mul_of_minimum cs J w hw u hr hu, hr.eq]

lemma exists_parabolic_decomposition (J : Set B) (w : W) :
    ∃ a v : W, a ∈ parabolic cs J ∧ IsParabolicMinimum cs J v ∧
      w = a*v ∧ cs.length w = cs.length a + cs.length v := by
  classical
  have hex : ∃ n : ℕ, ∃ b : W, b ∈ parabolic cs J ∧ cs.length (b*w) = n :=
    ⟨cs.length w, 1, (parabolic cs J).one_mem, by simp⟩
  obtain ⟨b,hb,hlen⟩ := Nat.find_spec hex
  have hmin : IsParabolicMinimum cs J (b*w) := by
    intro c hc
    rw [hlen]
    apply Nat.find_min' hex
    exact ⟨c*b, (parabolic cs J).mul_mem hc hb, by rw [mul_assoc]⟩
  refine ⟨b⁻¹, b*w, (parabolic cs J).inv_mem hb, hmin, by group, ?_⟩
  simpa only [inv_mul_cancel_left] using
    length_mul_of_minimum cs J (b*w) hmin b⁻¹ ((parabolic cs J).inv_mem hb)

lemma parabolic_minimum_unique (J : Set B) {v w : W}
    (hv : IsParabolicMinimum cs J v) (hw : IsParabolicMinimum cs J w)
    (h : ∃ a ∈ parabolic cs J, w = a*v) : w = v := by
  obtain ⟨a,ha,rfl⟩ := h
  have he := length_mul_of_minimum cs J v hv a ha
  have hle := hw a⁻¹ ((parabolic cs J).inv_mem ha)
  simp only [inv_mul_cancel_left] at hle
  have hzero : cs.length a = 0 := by omega
  have haone : a=1 := cs.length_eq_zero_iff.mp hzero
  simp [haone]

lemma descent_parabolic_factor (J : Set B) {a v : W}
    (ha : a ∈ parabolic cs J) (hv : IsParabolicMinimum cs J v)
    {i : B} (hi : i ∈ J) :
    cs.length (cs.simple i * (a*v)) < cs.length (a*v) ↔
      cs.length (cs.simple i*a) < cs.length a := by
  rw [← mul_assoc, length_mul_of_minimum cs J v hv a ha,
    length_mul_of_minimum cs J v hv (cs.simple i*a)
      ((parabolic cs J).mul_mem (simple_mem_parabolic cs J hi) ha)]
  omega

end HarmonicArtin.CoxeterExchange

end OAI
