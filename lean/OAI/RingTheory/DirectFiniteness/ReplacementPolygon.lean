import OAI.RingTheory.DirectFiniteness.TradePolygon

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

omit [Fintype Q] in
lemma replacement_adj_holes_ne
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    {r s : R} (hrs : r ≠ s) {o o' : O} {a b : Q} (ha : a ≠ 0) {x : A}
    (hx : x ∈ F.replacementLine r o.val a) (hy : x ∈ F.replacementLine s o'.val b) : o ≠ o' := by
  intro he
  subst o'
  have hxW := (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hx)
  have hyW := (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hy)
  have hz := Submodule.disjoint_def.mp (F.W_disjoint hrs) (x-o.val) hxW hyW
  have hxo := sub_eq_zero.mp hz
  exact Finset.disjoint_left.mp (F.replacementLine_hole_free S O hO r o a ha) hx (hxo ▸ o.property)

omit [Fintype Q] in
lemma replacement_opposite_holes_ne {r s : R} (hrs : r ≠ s)
    {o o' : O} {a b : Q} {x y : A}
    (hx : x ∈ F.replacementLine r o.val a) (hy : y ∈ F.replacementLine r o'.val b)
    (hxy : y-x ∈ F.W s) (hne : y ≠ x) : o ≠ o' := by
  intro he
  subst o'
  have hxW := (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hx)
  have hyW := (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hy)
  have hW : y-x ∈ F.W r := by convert (F.W r).sub_mem hyW hxW using 1; abel
  exact hne (sub_eq_zero.mp (Submodule.disjoint_def.mp (F.W_disjoint hrs) _ hW hxy))

omit [Fintype Q] in
lemma no_replacement_quad
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (point : Fin 4 → A) (line : Fin 4 → NewIndex (Q := Q) (R := R) O)
    (hne : ∀ i, point (finRotate 4 i) ≠ point i)
    (hadj : ∀ i, (line i).1 ≠ (line (finRotate 4 i)).1)
    (halt : (line 0).1=(line 2).1 ∧ (line 1).1=(line 3).1)
    (hx : ∀ i, point i ∈ F.replacementLine (line i).1 (line i).2.1.val (line i).2.2.val)
    (hy : ∀ i, point (finRotate 4 i) ∈ F.replacementLine (line i).1 (line i).2.1.val (line i).2.2.val) : False := by
  have h01 : (line 0).1 ≠ (line 1).1 := hadj 0
  have h12 : (line 1).1 ≠ (line 2).1 := hadj 1
  have h23 : (line 2).1 ≠ (line 3).1 := hadj 2
  have h30 : (line 3).1 ≠ (line 0).1 := hadj 3
  have hw (i : Fin 4) : point (finRotate 4 i)-point i ∈ F.W (line i).1 := by
    convert (F.W (line i).1).sub_mem
      ((mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ (hy i)))
      ((mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ (hx i))) using 1; abel
  have ho01 := F.replacement_adj_holes_ne S O hO h01 (line 0).2.2.property (hy 0) (hx 1)
  have ho12 := F.replacement_adj_holes_ne S O hO h12 (line 1).2.2.property (hy 1) (hx 2)
  have ho23 := F.replacement_adj_holes_ne S O hO h23 (line 2).2.2.property (hy 2) (hx 3)
  have ho30 := F.replacement_adj_holes_ne S O hO h30 (line 3).2.2.property (hy 3) (hx 0)
  have ho02 : (line 0).2.1 ≠ (line 2).2.1 := by
    apply F.replacement_opposite_holes_ne O h01 (hy 0)
      (show point 2 ∈ F.replacementLine (line 0).1 (line 2).2.1.val (line 2).2.2.val by rw [halt.1]; exact hx 2)
      (hw 1) (hne 1)
  have ho13 : (line 1).2.1 ≠ (line 3).2.1 := by
    apply F.replacement_opposite_holes_ne O h12 (hy 1)
      (show point 3 ∈ F.replacementLine (line 1).1 (line 3).2.1.val (line 3).2.2.val by rw [halt.2]; exact hx 3)
      (hw 2) (hne 2)
  have hinj : Function.Injective (fun i : Fin 4 => (line i).2.1.val) := by
    intro i j hij
    have he : (line i).2.1=(line j).2.1 := Subtype.ext hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨u,_,hu⟩ := F.replacementLine_step (hx 0) (hy 0) (hne 0)
  obtain ⟨v,_,hv⟩ := F.replacementLine_step (hx 1) (hy 1) (hne 1)
  change F.exc (line 0).1 u=point 1-point 0 at hu
  change F.exc (line 1).1 v=point 2-point 1 at hv
  have hp1 : point 1=point 0+F.exc (line 0).1 u := eq_add_of_sub_eq' hu.symm
  have hp2 : point 2=point 0+F.exc (line 0).1 u+F.exc (line 1).1 v := by
    rw [← hp1]
    exact eq_add_of_sub_eq' hv.symm
  have hw0 : point 1-point 0 ∈ F.W (line 0).1 := hw 0
  have hw1 : point 2-point 1 ∈ F.W (line 1).1 := hw 1
  have hw2 : point 3-point 2 ∈ F.W (line 0).1 := by
    rw [halt.1]; exact hw 2
  have hw3 : point 0-point 3 ∈ F.W (line 1).1 := by
    rw [halt.2]; exact hw 3
  have hd : (point 3-point 0)-(point 2-point 1)=0 := by
    apply Submodule.disjoint_def.mp (F.W_disjoint h01)
    · have hh := (F.W (line 0).1).add_mem hw2 hw0
      convert hh using 1; abel
    · have hh := (F.W (line 1).1).sub_mem ((F.W (line 1).1).neg_mem hw3) hw1
      convert hh using 1; abel
  have hp3 : point 3=point 0+F.exc (line 1).1 v := by
    change F.exc (line 1).1 v=point 2-point 1 at hv
    rw [← hv] at hd
    exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hd)).trans (add_comm _ _)
  apply hO.rectangles (line 0).1 (line 1).1 (point 0) u v (fun i => (line i).2.1.val) hinj
    (fun i => (line i).2.1.property)
  intro i
  have hm := (F.W (line i).1).neg_mem ((mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ (hx i)))
  have he : -(point i-(line i).2.1.val)=(line i).2.1.val-point i := by abel
  rw [he] at hm
  fin_cases i
  · exact hm
  · change (line 1).2.1.val-(point 0+F.exc (line 0).1 u) ∈ F.W (line 1).1
    rw [← hp1]
    exact hm
  · change (line 2).2.1.val-(point 0+F.exc (line 0).1 u+F.exc (line 1).1 v) ∈ F.W (line 0).1
    rw [← hp2,halt.1]
    exact hm
  · change (line 3).2.1.val-(point 0+F.exc (line 1).1 v) ∈ F.W (line 1).1
    rw [← hp3,halt.2]
    exact hm

omit [Fintype Q] in
lemma no_replacement_polygon
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (point : Fin k → A) (line : Fin k → NewIndex (Q := Q) (R := R) O)
    (hne : ∀ i, point (finRotate k i) ≠ point i)
    (hadj : ∀ i, (line i).1 ≠ (line (finRotate k i)).1)
    (hx : ∀ i, point i ∈ F.replacementLine (line i).1 (line i).2.1.val (line i).2.2.val)
    (hy : ∀ i, point (finRotate k i) ∈ F.replacementLine (line i).1 (line i).2.1.val (line i).2.2.val) : False := by
  choose u hu hv using fun i => F.replacementLine_step (hx i) (hy i) (hne i)
  let step (i : Fin k) : PolygonStep Q R E := .inr ⟨(line i).1,u i,hu i⟩
  have hz := F.closed_of_points step point (fun i => (hv i).symm)
  have hs : ∀ i, (step i).label ≠ (step (finRotate k i)).label := by
    intro i he
    exact hadj i (Sum.inr.inj he)
  have hc (r : R) (hr : ∃ i, (line i).1=r) :
      (Finset.univ.filter (fun i => (line i).1=r)).card=2 := by
    have he := F.exceptional_occurs_twice_single_slope step hk5 hz hs r
      (by obtain ⟨i,hi⟩ := hr; exact ⟨i,congrArg Sum.inr hi⟩) 0
      (by intro i g hg; cases hg)
    simpa only [step,PolygonStep.label,Sum.inr.injEq] using he
  have hk4 := (all_labels_twice_length (fun i => (line i).1) hk3 hk5 (by
    intro r hr
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hr
    exact hc r ⟨i,hi⟩)).1
  subst k
  exact F.no_replacement_quad S O hO point line hne hadj
    (four_labels_alternate (fun i => (line i).1) hadj hc) hx hy

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
