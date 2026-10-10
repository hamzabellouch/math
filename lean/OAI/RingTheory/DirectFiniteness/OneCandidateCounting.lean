import OAI.RingTheory.DirectFiniteness.ReplacementGeometry

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]

omit [Fintype A] in
lemma one_position_recovery {I : Type u_5} [Fintype I] [DecidableEq I]
    (a : I) (v v' : I → A) (hz : ∑ i, v i = 0) (hz' : ∑ i, v' i = 0)
    (he : ∀ i, i ≠ a → v i = v' i) : v = v' := by
  have hsum : ∑ i, (v i-v' i) = 0 := by rw [Finset.sum_sub_distrib,hz,hz',sub_self]
  have hsingle : ∑ i, (v i-v' i) = v a-v' a := by
    apply Finset.sum_eq_single a
    · intro b _ hb; exact sub_eq_zero.mpr (he b hb)
    · simp
  have ha : v a = v' a := sub_eq_zero.mp (hsingle.symm.trans hsum)
  funext i
  by_cases hi : i=a
  · simpa [hi] using ha
  · exact he i hi

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)
variable (j : R × Q) (C : AffineCoset (F.U j))

local instance oneCodeIndexNeZero : NeZero (2 : ℕ) := inferInstance

abbrev OneCode := Σ r : R, (Fin 2 → Fin k) × (Fin k → Bool) ×
  ↥(C.val ∩ T r) × ↥(C.val ∩ T r) × (Fin k → Q)

namespace OneCode
abbrev other (z : OneCode F T k j C) := z.1
abbrev idx (z : OneCode F T k j C) := z.2.1
abbrev tag (z : OneCode F T k j C) := z.2.2.1
abbrev point (z : OneCode F T k j C) := z.2.2.2.1
abbrev nextPoint (z : OneCode F T k j C) := z.2.2.2.2.1
abbrev exc (z : OneCode F T k j C) := z.2.2.2.2.2

def lab (z : OneCode F T k j C) (i : Fin k) : (R × Q) ⊕ R :=
  if z.tag F T k j C i then .inl j else .inr (z.other F T k j C)
def known (z : OneCode F T k j C) (i : Fin k) : A :=
  if i=z.idx F T k j C 0 then (z.nextPoint F T k j C).val - (z.point F T k j C).val
    else F.exc (z.other F T k j C) (z.exc F T k j C i)
end OneCode

structure CoveredOne (c : Rooted F T k j C) (z : OneCode F T k j C) : Prop where
  root_eq : c.root = z.idx F T k j C 0
  lab : ∀ i, (c.cycle.step i).label = z.lab F T k j C i
  point : c.cycle.point (z.idx F T k j C 0) = (z.point F T k j C).val
  known : ∀ i, i ≠ z.idx F T k j C 1 →
    (c.cycle.step i).vector F = z.known F T k j C i

lemma CoveredOne.unique {c d : Rooted F T k j C} {z : OneCode F T k j C}
    (hc : CoveredOne F T k j C c z) (hd : CoveredOne F T k j C d z) : c=d := by
  have hv : (fun i => (c.cycle.step i).vector F) = fun i => (d.cycle.step i).vector F := by
    apply one_position_recovery (z.idx F T k j C 1) _ _ (c.cycle.closed F T) (d.cycle.closed F T)
    intro i hi
    exact (hc.known i hi).trans (hd.known i hi).symm
  have hs : c.cycle.step = d.cycle.step := by
    funext i
    exact PolygonStep.eq_of_label_vector_eq F ((hc.lab i).trans (hd.lab i).symm) (congrFun hv i)
  have hp := Candidate.points_eq F T c.cycle d.cycle hs (z.idx F T k j C 0)
    (hc.point.trans hd.point.symm)
  exact Rooted.ext F T k j C (Candidate.ext F T hs hp) (hc.root_eq.trans hd.root_eq.symm)

lemma one_label_codec (c : Rooted F T k j C) (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (hg : c.cycle.labels.card = 1) : k=4 ∧
      ∃ z : OneCode F T k j C, CoveredOne F T k j C c z := by
  have hj : j ∈ c.cycle.labels := (mem_genericLabels _ _).mpr ⟨c.root,c.label_eq⟩
  have hlabels : c.cycle.labels = {j} := by
    obtain ⟨l,hl⟩ := Finset.card_eq_one.mp hg
    rw [hl] at hj
    have he : j=l := Finset.mem_singleton.mp hj
    rw [hl,he]
  have honly (i : Fin k) (g : GenericStep Q R E) (hi : c.cycle.step i = .inl g) : g.label = j := by
    have hh : g.label ∈ c.cycle.labels := (mem_genericLabels _ _).mpr ⟨i,by rw [hi]; rfl⟩
    simpa only [hlabels,Finset.mem_singleton] using hh
  obtain ⟨hk,hall⟩ := F.one_generic_rectangle c.cycle.step hk3 hk5 (c.cycle.closed F T)
    c.cycle.adjacent j honly
  have hjall : Sum.inl j ∈ Finset.univ.image (fun i => (c.cycle.step i).label) :=
    Finset.mem_image.mpr ⟨c.root,Finset.mem_univ _,c.label_eq⟩
  obtain ⟨l,hlne,hlabs⟩ := pair_set_of_card_two hall hjall
  have hlex : ∃ r : R, l = Sum.inr r := by
    cases l with
    | inr r => exact ⟨r,rfl⟩
    | inl j' =>
      have hh : Sum.inl j' ∈ Finset.univ.image (fun i => (c.cycle.step i).label) := by rw [hlabs]; simp
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hh
      have hh : j' ∈ c.cycle.labels := (mem_genericLabels _ _).mpr ⟨i,hi⟩
      have he : j'=j := by simpa only [hlabels,Finset.mem_singleton] using hh
      exact False.elim (hlne (congrArg Sum.inl he))
  obtain ⟨r,rfl⟩ := hlex
  have hexceptional (i : Fin k) (e : ExceptionalStep Q R) (hi : c.cycle.step i = .inr e) : e.label = r := by
    have hh : Sum.inr e.label ∈ Finset.univ.image (fun i => (c.cycle.step i).label) :=
      Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by rw [hi]; rfl⟩
    simpa only [hlabs,Finset.mem_insert,Finset.mem_singleton,Sum.inr.injEq,
      reduceCtorEq,false_or] using hh
  have hnext : ∃ e : ExceptionalStep Q R, c.cycle.step (finRotate k c.root) = .inr e := by
    cases hi : c.cycle.step (finRotate k c.root) with
    | inr e => exact ⟨e,rfl⟩
    | inl g =>
      have hh := honly _ g hi
      exact False.elim (c.cycle.adjacent c.root (c.label_eq.trans (by rw [hi]; exact congrArg Sum.inl hh.symm)))
  have hprev : ∃ e : ExceptionalStep Q R, c.cycle.step ((finRotate k).symm c.root) = .inr e := by
    cases hi : c.cycle.step ((finRotate k).symm c.root) with
    | inr e => exact ⟨e,rfl⟩
    | inl g =>
      have hh := honly _ g hi
      apply False.elim
      apply c.cycle.adjacent ((finRotate k).symm c.root)
      simp only [Equiv.apply_symm_apply]
      rw [hi,c.label_eq]
      exact congrArg Sum.inl hh
  obtain ⟨en,hen⟩ := hnext
  obtain ⟨ep,hep⟩ := hprev
  have hpT : c.cycle.point c.root ∈ T r := by
    have hh := (c.cycle.exceptional _ ep hep).2
    simpa only [Equiv.apply_symm_apply,hexceptional _ ep hep] using hh
  have hnT : c.cycle.point (finRotate k c.root) ∈ T r := by
    simpa only [hexceptional _ en hen] using (c.cycle.exceptional _ en hen).1
  have hnC : c.cycle.point (finRotate k c.root) ∈ C.val := by
    have hm := (AffineCoset.add_mem_iff _ C _ _ (F.vector_mem_U c.label_eq)).mpr c.point_mem
    rw [← c.cycle.shift c.root] at hm
    convert hm using 1; abel
  have hrmem : c.root ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j) := by simp [c.label_eq]
  obtain ⟨a,har,hgen⟩ := pair_set_of_card_two (c.cycle.count_eq_two F T hk5 j hj) hrmem
  have hgen' (i : Fin k) : (c.cycle.step i).label = .inl j ↔ i=c.root ∨ i=a := by
    have hh : i ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j) ↔
        i ∈ ({c.root,a} : Finset (Fin k)) := by rw [hgen]
    simpa using hh
  let tag (index : Fin k) : Bool := Sum.elim (fun _ => true) (fun _ => false) (c.cycle.step index)
  let exc (index : Fin k) : Q :=
    Sum.elim (fun _ => 0) (fun exceptional => exceptional.scalar) (c.cycle.step index)
  let z : OneCode F T k j C := ⟨r,![c.root,a],tag,
    ⟨c.cycle.point c.root,Finset.mem_inter.mpr ⟨c.point_mem,hpT⟩⟩,
    ⟨c.cycle.point (finRotate k c.root),Finset.mem_inter.mpr ⟨hnC,hnT⟩⟩,exc⟩
  refine ⟨hk,z,rfl,?_,rfl,?_⟩
  · intro i
    cases hi : c.cycle.step i with
    | inl g => simp [z,OneCode.lab,OneCode.tag,tag,hi,PolygonStep.label,honly i g hi]
    | inr e => simp [z,OneCode.lab,OneCode.tag,OneCode.other,tag,hi,PolygonStep.label,hexceptional i e hi]
  · intro i hia
    change i ≠ a at hia
    change _ = if i=c.root then c.cycle.point (finRotate k c.root)-c.cycle.point c.root else F.exc r (exc i)
    by_cases hir : i=c.root
    · subst i; rw [ite_eq_left rfl]; exact (c.cycle.shift _).symm
    rw [ite_eq_right hir]
    cases hi : c.cycle.step i with
    | inl g =>
      have hh := (hgen' i).mp (by rw [hi]; exact congrArg Sum.inl (honly i g hi))
      exact False.elim (hh.elim hir hia)
    | inr e => simp [PolygonStep.vector,exc,hi,hexceptional i e hi]

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
