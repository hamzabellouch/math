import OAI.RingTheory.DirectFiniteness.TradeFamily

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

def KeptAt (x : A) := {j : R × Q // Disjoint ((T.part j).through x) O}
def RemovedAt (x : A) := {j : R × Q // ¬ Disjoint ((T.part j).through x) O}
def NewAt (x : A) := {i : NewIndex (Q := Q) (R := R) O //
  x ∈ F.replacementLine i.1 i.2.1.val i.2.2.val}
def LiveAt (x : A) := {i : F.LiveIndex O P T // x ∈ i.2.val}

instance (x : A) : Fintype (F.NewAt O x) := by unfold NewAt NewIndex; infer_instance
instance (x : A) : Fintype (F.LiveAt O P T x) := by unfold LiveAt; infer_instance
instance (x : A) : Fintype (F.KeptAt O P T x) := by unfold KeptAt; infer_instance
instance (x : A) : Fintype (F.RemovedAt O P T x) := by unfold RemovedAt; infer_instance

lemma liveAt_card (x : A) : Fintype.card (F.LiveAt O P T x) = Fintype.card (F.KeptAt O P T x) := by
  let f : F.LiveAt O P T x → F.KeptAt O P T x := fun g =>
    ⟨g.val.1,by rw [F.live_through O P T g.val.2 g.property]; exact g.val.2.property.2⟩
  apply Fintype.card_congr (Equiv.ofBijective f ?_)
  constructor
  · rintro ⟨⟨j,l⟩,hx⟩ ⟨⟨j',l'⟩,hx'⟩ he
    have hj : j=j' := congrArg Subtype.val he
    subst j'
    have hl : l=l' := Subtype.ext ((F.live_through O P T l hx).symm.trans (F.live_through O P T l' hx'))
    subst l'
    rfl
  · intro j
    refine ⟨⟨⟨j.val,⟨(T.part j.val).through x,⟨⟨x,rfl⟩,j.property⟩⟩⟩,(T.part j.val).self x⟩,?_⟩
    rfl

/-- The second coordinate of a point on a replacement line. -/
def newCoord {x : A} (i : F.NewAt O x) : Q :=
  ((F.mem_replacementLine i.val.1 i.val.2.1.val x i.val.2.2.val).mp i.property).choose

omit [Fintype Q] [Fintype R] in
lemma newCoord_spec {x : A} (i : F.NewAt O x) :
    F.w i.val.1 (i.val.2.2.val,F.newCoord O i)=x-i.val.2.1.val :=
  ((F.mem_replacementLine i.val.1 i.val.2.1.val x i.val.2.2.val).mp i.property).choose_spec

def newLabel {x : A} (i : F.NewAt O x) : R × Q :=
  (i.val.1, F.newCoord O i / i.val.2.2.val)

omit [Fintype Q] [Fintype R] in
lemma newLabel_axis {x : A} (i : F.NewAt O x) :
    x ∈ cosetPoints (F.D (F.newLabel O i)) i.val.2.1.val := by
  apply (mem_cosetPoints _ _ _).mpr
  refine ⟨i.val.2.2.val,?_⟩
  change F.w i.val.1 (i.val.2.2.val,i.val.2.2.val*(F.newCoord O i / i.val.2.2.val)) = _
  rw [mul_div_cancel₀ _ i.val.2.2.property]
  exact F.newCoord_spec O i

omit [Fintype Q] [Fintype R] in
lemma newLabel_injective (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (x : A) : Function.Injective (F.newLabel O (x := x)) := by
  intro i i' he
  have hr := congrArg (fun j : R × Q => j.1) he
  change i.val.1=i'.val.1 at hr
  have hx := F.replacementLine_same_label S O hO i.property
    (show x ∈ F.replacementLine i.val.1 i'.val.2.1.val i'.val.2.2.val by rw [hr]; exact i'.property)
  apply Subtype.ext
  exact Prod.ext hr (Prod.ext hx.1 (Subtype.ext hx.2))

omit [Fintype R] in
lemma newLabel_surjective (x : A) (hx : x ∉ O) (j : F.RemovedAt O P T x) :
    ∃ i : F.NewAt O x, F.newLabel O i=j.val := by
  obtain ⟨o,ho,haxis⟩ := (F.removed_iff O P T j.val x).mp j.property
  obtain ⟨a,ha⟩ := (mem_cosetPoints _ _ _).mp haxis
  have han : a ≠ 0 := by
    intro hz
    subst a
    rw [map_zero] at ha
    have hxo : x=o := sub_eq_zero.mp ha.symm
    exact hx (hxo ▸ ho)
  let i : F.NewAt O x := ⟨(j.val.1,⟨o,ho⟩,⟨a,han⟩),
    (F.mem_replacementLine j.val.1 o x a).mpr ⟨a*j.val.2,ha⟩⟩
  refine ⟨i,Prod.ext rfl ?_⟩
  have hc : F.newCoord O i=a*j.val.2 := congrArg Prod.snd (F.winj j.val.1 ((F.newCoord_spec O i).trans ha.symm))
  change F.newCoord O i / a=j.val.2
  rw [hc,mul_div_cancel_left₀ _ han]

lemma newAt_card (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (x : A) (hx : x ∉ O) : Fintype.card (F.NewAt O x) = Fintype.card (F.RemovedAt O P T x) := by
  let f : F.NewAt O x → F.RemovedAt O P T x := fun i =>
    ⟨F.newLabel O i,(F.removed_iff O P T _ x).mpr ⟨i.val.2.1.val,i.val.2.1.property,F.newLabel_axis O i⟩⟩
  apply Fintype.card_congr (Equiv.ofBijective f ?_)
  constructor
  · intro i i' he
    exact F.newLabel_injective S O hO x (congrArg Subtype.val he)
  · intro j
    obtain ⟨i,hi⟩ := F.newLabel_surjective O P T x hx j
    exact ⟨i,Subtype.ext hi⟩

lemma trade_degree (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (x : A) (hx : x ∉ O) :
    Fintype.card {i : F.TradeIndex O P T // x ∈ F.tradeLine O P T i} = Fintype.card R*Fintype.card Q := by
  let : Fintype (NewIndex (Q := Q) (R := R) O) := by unfold NewIndex; infer_instance
  have he : Fintype.card {i : F.TradeIndex O P T // x ∈ F.tradeLine O P T i} =
      Fintype.card (F.LiveAt O P T x)+Fintype.card (F.NewAt O x) := by
    let e : {i : F.TradeIndex O P T // x ∈ F.tradeLine O P T i} ≃
        F.LiveAt O P T x ⊕ F.NewAt O x := {
      toFun := fun i => match i with
        | ⟨.inl g,hg⟩ => .inl ⟨g,hg⟩
        | ⟨.inr h,hh⟩ => .inr ⟨h,hh⟩
      invFun := fun i => match i with
        | .inl g => ⟨.inl g.val,g.property⟩
        | .inr h => ⟨.inr h.val,h.property⟩
      left_inv := by rintro ⟨g,hg⟩; cases g <;> rfl
      right_inv := by intro g; cases g <;> rfl }
    exact (Fintype.card_congr e).trans Fintype.card_sum
  rw [he,F.liveAt_card O P T x,F.newAt_card S O P T hO x hx]
  change Fintype.card {j : R × Q // Disjoint ((T.part j).through x) O} +
    Fintype.card {j : R × Q // ¬ Disjoint ((T.part j).through x) O} = _
  rw [Fintype.card_subtype_compl, Nat.add_sub_of_le (Fintype.card_subtype_le _),Fintype.card_prod]

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
