import OAI.RingTheory.DirectFiniteness.IncidenceCycles

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]

lemma finRotate_ne_self_large {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : finRotate k i ≠ i := by
  let : NeZero k := ⟨by omega⟩
  intro he
  have hval := congrArg Fin.val he
  rw [finRotate_apply,Fin.val_add] at hval
  have hone : (1 : Fin k).val=1 := by
    change 1 % k=1
    exact Nat.mod_eq_of_lt (by omega)
  rw [hone] at hval
  by_cases hi : i.val+1 < k
  · rw [Nat.mod_eq_of_lt hi] at hval
    omega
  · have hh : i.val+1=k := by omega
    rw [hh,Nat.mod_self] at hval
    omega

namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

omit [Fintype Q] [Fintype A] in
lemma label_spaces_disjoint {l l' : (R × Q) ⊕ R} (hne : l ≠ l') :
    Disjoint (Sum.elim F.U F.exceptional l) (Sum.elim F.U F.exceptional l') := by
  cases l with
  | inl j => cases l' with
    | inl j' => exact F.U_disjoint (fun h => hne (congrArg Sum.inl h))
    | inr r => exact F.U_exceptional_disjoint j r
  | inr r => cases l' with
    | inl j => exact (F.U_exceptional_disjoint j r).symm
    | inr r' => exact F.exceptional_disjoint (fun h => hne (congrArg Sum.inr h))

lemma no_short_trade_polygon
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (hP : F.SuccessfulSlabs O P)
    {k : ℕ} (hk2 : 2 ≤ k) (hk5 : k ≤ 5)
    (point : Fin k → A) (line : Fin k → F.TradeIndex O P T)
    (hpoint : Function.Injective point) (hline : Function.Injective line)
    (hx : ∀ i, point i ∈ F.tradeLine O P T (line i))
    (hy : ∀ i, point (finRotate k i) ∈ F.tradeLine O P T (line i)) : False := by
  have hne (i : Fin k) : point (finRotate k i) ≠ point i :=
    fun he => finRotate_ne_self_large hk2 i (hpoint he)
  have hadj (i : Fin k) : F.tradeLabel O P T (line i) ≠ F.tradeLabel O P T (line (finRotate k i)) := by
    intro he
    have hi := hline (F.same_label_eq S O P T hO he (hy i) (hx (finRotate k i)))
    exact finRotate_ne_self_large hk2 i hi.symm
  by_cases hk : k=2
  · subst k
    have hm0 : point 1-point 0 ∈ Sum.elim F.U F.exceptional (F.tradeLabel O P T (line 0)) :=
      F.tradeLine_step_mem O P T (line 0) (hx 0) (hy 0)
    have hm1 : point 1-point 0 ∈ Sum.elim F.U F.exceptional (F.tradeLabel O P T (line 1)) :=
      F.tradeLine_step_mem O P T (line 1) (hy 1) (hx 1)
    exact hne 0 (sub_eq_zero.mp (Submodule.disjoint_def.mp (F.label_spaces_disjoint (hadj 0)) _ hm0 hm1))
  have hk3 : 3 ≤ k := by omega
  by_cases hg : ∃ i j, F.tradeLabel O P T (line i)=.inl j
  · exact F.no_generic_trade_polygon O P T hP hk3 hk5 point line hne hadj hx hy hg
  have hn (i : Fin k) : ∃ t : NewIndex (Q := Q) (R := R) O, line i=.inr t := by
    cases ht : line i with
    | inl t => exact False.elim (hg ⟨i,t.1,by rw [ht]; rfl⟩)
    | inr t => exact ⟨t,rfl⟩
  choose new hnew using hn
  apply F.no_replacement_polygon S O hO hk3 hk5 point new hne
  · intro i he
    apply hadj i
    rw [hnew,hnew]
    exact congrArg Sum.inr he
  · intro i
    simpa only [hnew,tradeLine] using hx i
  · intro i
    simpa only [hnew,tradeLine] using hy i

lemma trade_incidence_girth
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (hP : F.SuccessfulSlabs O P) :
    12 ≤ (Planar.incidenceGraph
      (fun (x : {x : A // x ∉ O}) (i : F.TradeIndex O P T) => x.val ∈ F.tradeLine O P T i)).egirth := by
  apply Planar.incidence_girth_of_no_short_polygon
  intro k hk2 hk5 point line hp hl hx hy
  exact F.no_short_trade_polygon S O P T hO hP hk2 hk5 (fun i => (point i).val) line
    (Subtype.val_injective.comp hp) hl hx hy

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
