import OAI.RingTheory.DirectFiniteness.TradeLines

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

def LiveLine (j : R × Q) := {l : Finset A // (∃ x, (T.part j).through x=l) ∧ Disjoint l O}
def LiveIndex := Σ j, F.LiveLine O P T j
def NewIndex := R × O × {a : Q // a ≠ 0}
def TradeIndex := F.LiveIndex O P T ⊕ NewIndex (Q := Q) (R := R) O

def tradeLine : F.TradeIndex O P T → Finset A
  | .inl g => g.2.val
  | .inr h => F.replacementLine h.1 h.2.1.val h.2.2.val

def tradeLabel : F.TradeIndex O P T → (R × Q) ⊕ R
  | .inl g => .inl g.1
  | .inr h => .inr h.1

instance [Fintype R] : Fintype (F.LiveIndex O P T) := by unfold LiveIndex LiveLine; infer_instance
instance [Fintype R] : Fintype (F.TradeIndex O P T) := by unfold TradeIndex NewIndex; infer_instance

lemma live_through {j : R × Q} (l : F.LiveLine O P T j) {x : A} (hx : x ∈ l.val) :
    (T.part j).through x=l.val := by
  obtain ⟨a,ha⟩ := l.property.1
  exact ((T.part j).stable a x (ha ▸ hx)).trans ha

lemma live_full {j : R × Q} (l : F.LiveLine O P T j) : FullLine (Q := Q) l.val := by
  obtain ⟨x,hx⟩ := l.property.1
  rw [← hx]
  exact (T.part j).full x

lemma tradeLine_full (i : F.TradeIndex O P T) : FullLine (Q := Q) (F.tradeLine O P T i) := by
  cases i with
  | inl l => exact F.live_full O P T l.2
  | inr h => exact F.replacementLine_full h.1 h.2.1.val h.2.2.val

lemma tradeLine_avoid (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (i : F.TradeIndex O P T) : Disjoint (F.tradeLine O P T i) O := by
  cases i with
  | inl g => exact g.2.property.2
  | inr h => exact F.replacementLine_hole_free S O hO h.1 h.2.1 h.2.2.val h.2.2.property

lemma same_label_eq (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    {i i' : F.TradeIndex O P T} (hl : F.tradeLabel O P T i=F.tradeLabel O P T i')
    {x : A} (hx : x ∈ F.tradeLine O P T i) (hx' : x ∈ F.tradeLine O P T i') : i=i' := by
  cases i with
  | inl g => cases i' with
    | inl g' =>
      obtain ⟨j,l⟩ := g
      obtain ⟨j',l'⟩ := g'
      have hj := Sum.inl.inj hl
      change j=j' at hj
      subst j'
      have he : l=l' := Subtype.ext ((F.live_through O P T l hx).symm.trans (F.live_through O P T l' hx'))
      subst l'
      rfl
    | inr h => cases hl
  | inr h => cases i' with
    | inl g => cases hl
    | inr h' =>
      obtain ⟨r,o,a⟩ := h
      obtain ⟨r',o',a'⟩ := h'
      have hr := Sum.inr.inj hl
      change r=r' at hr
      subst r'
      obtain ⟨ho,ha⟩ := F.replacementLine_same_label S O hO hx hx'
      exact congrArg Sum.inr (Prod.ext rfl (Prod.ext ho (Subtype.ext ha)))

lemma live_step {j : R × Q} (l : F.LiveLine O P T j) {x y : A}
    (hx : x ∈ l.val) (hy : y ∈ l.val) (hne : y ≠ x) :
    ∃ c : Q, ∃ e : E, e ≠ 0 ∧ e ∈ (P ⟨j,AffineCoset.of (F.U j) x⟩).val ∧ F.u j (c,e)=y-x := by
  have he := F.live_through O P T l hx
  exact T.generic j x (he ▸ l.property.2) x (he ▸ hx) y (he ▸ hy) hne

lemma tradeLine_step_mem (i : F.TradeIndex O P T) {x y : A}
    (hx : x ∈ F.tradeLine O P T i) (hy : y ∈ F.tradeLine O P T i) :
    y-x ∈ Sum.elim F.U F.exceptional (F.tradeLabel O P T i) := by
  by_cases hne : y=x
  · simp [hne]
  cases i with
  | inl g =>
    obtain ⟨c,e,_,_,he⟩ := F.live_step O P T g.2 hx hy hne
    exact ⟨(c,e),he⟩
  | inr h =>
    obtain ⟨t,_,ht⟩ := F.replacementLine_step hx hy hne
    exact ⟨t,ht⟩

lemma removed_iff (j : R × Q) (x : A) :
    ¬ Disjoint ((T.part j).through x) O ↔ ∃ o ∈ O, x ∈ cosetPoints (F.D j) o := by
  rw [Finset.not_disjoint_iff]
  constructor
  · rintro ⟨o,ho,hoO⟩
    refine ⟨o,hoO,?_⟩
    have he := (T.part j).stable x o ho
    rw [T.axis j o hoO] at he
    rw [he]
    exact (T.part j).self x
  · rintro ⟨o,ho,hx⟩
    have hh : x ∈ (T.part j).through o := (T.axis j o ho) ▸ hx
    have he := (T.part j).stable o x hh
    exact ⟨o,he ▸ (T.part j).self o,ho⟩

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
