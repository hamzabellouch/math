import OAI.RingTheory.DirectFiniteness.GroupEmbedding

namespace OAI

universe u_1 u_2

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Planar
variable {V : Type u_1} {F : Type u_2} (Inc : V → F → Prop)

def incidenceColoring : (incidenceGraph Inc).Coloring Bool :=
  SimpleGraph.Coloring.mk Sum.isLeft (by
    intro x y h
    cases x <;> cases y <;> simp_all [incidenceGraph])

lemma incidence_walk_even {u : V ⊕ F} (w : (incidenceGraph Inc).Walk u u) : Even w.length := by
  exact ((incidenceColoring Inc).even_length_iff_congr w).mpr Iff.rfl

lemma getVert_even_left {v : V} {z : V ⊕ F} (w : (incidenceGraph Inc).Walk (.inl v) z)
    (i : ℕ) (hi : 2*i ≤ w.length) : ∃ x : V, w.getVert (2*i)=.inl x := by
  have he : Even (w.take (2*i)).length := by rw [SimpleGraph.Walk.take_length,inf_eq_left.mpr hi]; exact even_two_mul i
  have hc := ((incidenceColoring Inc).even_length_iff_congr (w.take (2*i))).mp he
  cases hx : w.getVert (2*i) with
  | inl x => exact ⟨x,rfl⟩
  | inr f =>
    change (true = true ↔ Sum.isLeft (w.getVert (2*i)) = true) at hc
    rw [hx] at hc
    exact False.elim (Bool.noConfusion (hc.mp rfl))

lemma getVert_odd_right {v : V} {z : V ⊕ F} (w : (incidenceGraph Inc).Walk (.inl v) z)
    (i : ℕ) (hi : 2*i+1 ≤ w.length) : ∃ f : F, w.getVert (2*i+1)=.inr f := by
  obtain ⟨x,hx⟩ := getVert_even_left Inc w i (by omega)
  have ha := w.adj_getVert_succ (by omega : 2*i < w.length)
  rw [hx] at ha
  cases hf : w.getVert (2*i+1) with
  | inl y =>
    rw [hf] at ha
    exact False.elim ha
  | inr f => exact ⟨f,rfl⟩

/-- A cycle based at a point yields its literal cyclic list of point and
line vertices, without repeated vertices on either side. -/
lemma cycle_polygon_left {v : V} (w : (incidenceGraph Inc).Walk (.inl v) (.inl v))
    (hw : w.IsCycle) {k : ℕ} (hk : w.length=2*k) :
    ∃ (point : Fin k → V) (line : Fin k → F), Function.Injective point ∧ Function.Injective line ∧
      (∀ i, Inc (point i) (line i)) ∧ (∀ i, Inc (point (finRotate k i)) (line i)) := by
  have hkp : 0 < k := by have := hw.three_le_length; omega
  have hp (i : Fin k) := getVert_even_left Inc w i.val (by omega)
  have hl (i : Fin k) := getVert_odd_right Inc w i.val (by omega)
  let point (i : Fin k) := (hp i).choose
  let line (i : Fin k) := (hl i).choose
  have hpoint (i : Fin k) : w.getVert (2*i.val)=.inl (point i) := (hp i).choose_spec
  have hline (i : Fin k) : w.getVert (2*i.val+1)=.inr (line i) := (hl i).choose_spec
  have hnext (i : Fin k) : w.getVert (2*i.val+2)=.inl (point (finRotate k i)) := by
    have hk2 : 2 ≤ k := by have := hw.three_le_length; omega
    by_cases hi : i.val+1 < k
    · have hh : (finRotate k i).val=i.val+1 := by
        rw [finRotate_apply]
        exact Fin.val_add_one_of_lt' hi
      rw [show 2*i.val+2=2*(finRotate k i).val by omega]
      exact hpoint _
    · have hi' : i.val=k-1 := by omega
      have hrot : finRotate k i=⟨0,hkp⟩ := by
        apply Fin.ext
        rw [finRotate_apply,Fin.val_add]
        simp [hi',Nat.sub_add_cancel (by omega : 1 ≤ k)]
      rw [show 2*i.val+2=w.length by omega,SimpleGraph.Walk.getVert_length,hrot]
      simpa using (hpoint ⟨0,hkp⟩)
  refine ⟨point,line,?_,?_,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    have he := hw.getVert_injOn' (show 2*i.val ≤ w.length-1 by omega)
      (show 2*j.val ≤ w.length-1 by omega) ((hpoint i).trans ((congrArg Sum.inl hij).trans (hpoint j).symm))
    omega
  · intro i j hij
    apply Fin.ext
    have he := hw.getVert_injOn' (show 2*i.val+1 ≤ w.length-1 by omega)
      (show 2*j.val+1 ≤ w.length-1 by omega) ((hline i).trans ((congrArg Sum.inr hij).trans (hline j).symm))
    omega
  · intro i
    have ha := w.adj_getVert_succ (by omega : 2*i.val < w.length)
    rw [hpoint,hline] at ha
    exact ha
  · intro i
    have ha := w.adj_getVert_succ (by omega : 2*i.val+1 < w.length)
    rw [hline,show 2*i.val+1+1=2*i.val+2 by omega,hnext] at ha
    exact ha

lemma cycle_polygon {z : V ⊕ F} (w : (incidenceGraph Inc).Walk z z) (hw : w.IsCycle) :
    ∃ k, w.length=2*k ∧ 2 ≤ k ∧ ∃ (point : Fin k → V) (line : Fin k → F),
      Function.Injective point ∧ Function.Injective line ∧
      (∀ i, Inc (point i) (line i)) ∧ (∀ i, Inc (point (finRotate k i)) (line i)) := by
  obtain ⟨k,hk⟩ := incidence_walk_even Inc w
  have hk' : w.length=2*k := by omega
  refine ⟨k,hk',by have := hw.three_le_length; omega,?_⟩
  cases z with
  | inl v => exact cycle_polygon_left Inc w hw hk'
  | inr f =>
    have ha := w.adj_getVert_succ (by have := hw.three_le_length; omega : 0 < w.length)
    simp only [SimpleGraph.Walk.getVert_zero,zero_add] at ha
    cases hz : w.getVert 1 with
    | inr g =>
      rw [hz] at ha
      exact False.elim ha
    | inl v =>
      have hm : (.inl v : V ⊕ F) ∈ w.support := hz ▸ w.getVert_mem_support 1
      exact cycle_polygon_left Inc (w.rotate (.inl v) hm) (hw.rotate hm)
        ((w.length_rotate _ _).trans hk')

/-- A convenient girth criterion phrased in the actual incidence lists. -/
lemma incidence_girth_of_no_short_polygon
    (h : ∀ k, 2 ≤ k → k ≤ 5 → ∀ (point : Fin k → V) (line : Fin k → F),
      Function.Injective point → Function.Injective line →
      (∀ i, Inc (point i) (line i)) → (∀ i, Inc (point (finRotate k i)) (line i)) → False) :
    12 ≤ (incidenceGraph Inc).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro z w hw
  obtain ⟨k,hk,hk2,point,line,hp,hl,hinc,hnext⟩ := cycle_polygon Inc w hw
  have hn : 6 ≤ k := by
    by_contra hh
    exact h k hk2 (by omega) point line hp hl hinc hnext
  exact_mod_cast (show 12 ≤ w.length by omega)

end KaplanskyCounterexample.Planar
end

end OAI
