import OAI.RingTheory.DirectFiniteness.TradeDegree

namespace OAI

universe u_1

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

lemma exists_trade_step (i : F.TradeIndex O P T) {x y : A}
    (hx : x ∈ F.tradeLine O P T i) (hy : y ∈ F.tradeLine O P T i) (hne : y ≠ x) :
    ∃ s : PolygonStep Q R E, s.label=F.tradeLabel O P T i ∧ s.vector F=y-x ∧
      (∀ g : GenericStep Q R E, s=.inl g → g.component ∈ (P ⟨g.label,AffineCoset.of (F.U g.label) x⟩).val) ∧
      (∀ e : ExceptionalStep Q R, s=.inr e → x ∈ F.replacementRegion O e.label ∧ y ∈ F.replacementRegion O e.label) := by
  cases i with
  | inl l =>
    obtain ⟨c,e,he,hP,hv⟩ := F.live_step O P T l.2 hx hy hne
    refine ⟨.inl ⟨l.1,c,e,he⟩,rfl,hv,?_,?_⟩
    · intro g hg
      cases Sum.inl.inj hg
      exact hP
    · intro g hg; cases hg
  | inr h =>
    obtain ⟨t,ht,hv⟩ := F.replacementLine_step hx hy hne
    refine ⟨.inr ⟨h.1,t,ht⟩,rfl,hv,?_,?_⟩
    · intro g hg; cases hg
    · intro g hg
      cases Sum.inr.inj hg
      constructor
      · exact (F.mem_replacementRegion O _ _).mpr ⟨h.2.1.val,h.2.1.property,
          (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hx)⟩
      · exact (F.mem_replacementRegion O _ _).mpr ⟨h.2.1.val,h.2.1.property,
          (mem_cosetPoints _ _ _).mp (F.replacementLine_subset _ _ _ hy)⟩

lemma no_generic_trade_polygon (hP : F.SuccessfulSlabs O P) {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (point : Fin k → A) (line : Fin k → F.TradeIndex O P T)
    (hne : ∀ i, point (finRotate k i) ≠ point i)
    (hadj : ∀ i, F.tradeLabel O P T (line i) ≠ F.tradeLabel O P T (line (finRotate k i)))
    (hx : ∀ i, point i ∈ F.tradeLine O P T (line i))
    (hy : ∀ i, point (finRotate k i) ∈ F.tradeLine O P T (line i))
    (hg : ∃ i j, F.tradeLabel O P T (line i)=.inl j) : False := by
  choose step hlabel hvec hplane hexc using fun i => F.exists_trade_step O P T (line i) (hx i) (hy i) (hne i)
  let c : Candidate F (F.replacementRegion O) k := {
    step := step
    point := point
    shift := fun i => (hvec i).symm
    adjacent := fun i => by rw [hlabel,hlabel]; exact hadj i
    exceptional := hexc
    generic := by obtain ⟨i,j,hj⟩ := hg; exact ⟨i,j,(hlabel i).trans hj⟩ }
  obtain ⟨v,hv,hn⟩ := hP.candidates k hk3 hk5 c
  obtain ⟨p,rfl⟩ := (c.mem_deps_iff F (F.replacementRegion O) v).mp hv
  rw [c.constraintVector_at F (F.replacementRegion O) hk3 hk5 p] at hn
  exact hn (hplane p.val.1 p.val.2 p.property)

end DirectionFrame

lemma four_labels_alternate {L : Type u_1} [DecidableEq L] (lab : Fin 4 → L)
    (hadj : ∀ i, lab i ≠ lab (finRotate 4 i))
    (hc : ∀ l, (∃ i, lab i=l) → (Finset.univ.filter (fun i => lab i=l)).card=2) :
    lab 0=lab 2 ∧ lab 1=lab 3 := by
  have h01 : lab 0 ≠ lab 1 := hadj 0
  have h12 : lab 1 ≠ lab 2 := hadj 1
  have h23 : lab 2 ≠ lab 3 := hadj 2
  have h30 : lab 3 ≠ lab 0 := hadj 3
  constructor
  · by_contra hh
    have ht := hc (lab 0) ⟨0,rfl⟩
    have he : (∑ i : Fin 4, if lab i=lab 0 then (1:ℕ) else 0)=2 := by simpa using ht
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at he
    change ((if True then 1 else 0) + ((if lab 1=lab 0 then 1 else 0) + ((if lab 2=lab 0 then 1 else 0) + ((if lab 3=lab 0 then 1 else 0) + 0))))=2 at he
    norm_num [h01.symm,Ne.symm hh,h30] at he
  · by_contra hh
    have ht := hc (lab 1) ⟨1,rfl⟩
    have he : (∑ i : Fin 4, if lab i=lab 1 then (1:ℕ) else 0)=2 := by simpa using ht
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at he
    change ((if lab 0=lab 1 then 1 else 0) + ((if lab 1=lab 1 then 1 else 0) + ((if lab 2=lab 1 then 1 else 0) + ((if lab 3=lab 1 then 1 else 0) + 0))))=2 at he
    norm_num [h01,h12.symm,Ne.symm hh] at he

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
