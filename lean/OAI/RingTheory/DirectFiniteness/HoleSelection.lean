import OAI.RingTheory.DirectFiniteness.HoleEvents

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry

lemma exists_avoiding_three {α : Type u_1} {I : Type u_2} {J : Type u_3} {H : Type u_4} [Fintype α] [Fintype I] [Fintype J] [Fintype H]
    (C : I → Finset α) (B : J → Finset α) (T : H → Finset α)
    (hC : ∀ i, (C i).card = 2) (hB : ∀ j, (B j).card = 4)
    {k : ℕ} (hk : 0 < k) (hT : ∀ h, (T h).card = k) (p : Set.Icc (0 : ℝ) 1) :
    ∃ O : Finset α, (∀ i, ¬ C i ⊆ O) ∧ (∀ j, ¬ B j ⊆ O) ∧ (∀ h, ¬ T h ⊆ O) ∧
      (Fintype.card α : ℝ) * p.val -
        (Fintype.card I * 2 * p.val^2 + Fintype.card J * 4 * p.val^4 +
            Fintype.card H * k * p.val^k) ≤ O.card := by
  let D : I ⊕ J ⊕ H → Finset α := Sum.elim C (Sum.elim B T)
  have hD : ∀ i, (D i).Nonempty := by
    intro i
    rw [← Finset.card_pos]
    cases i with
    | inl i => change 0 < (C i).card; rw [hC]; decide
    | inr i => cases i with
      | inl j => change 0 < (B j).card; rw [hB]; decide
      | inr h => change 0 < (T h).card; rw [hT]; exact hk
  obtain ⟨O,hO,hs⟩ := exists_avoiding_card D hD p
  refine ⟨O,(fun i => hO (.inl i)),(fun j => hO (.inr (.inl j))),
    (fun h => hO (.inr (.inr h))),?_⟩
  have hh : (∑ i, ((D i).card : ℝ) * p.val ^ (D i).card) =
      Fintype.card I * 2 * p.val^2 + Fintype.card J * 4 * p.val^4 +
            Fintype.card H * k * p.val^k := by
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp only [D,Sum.elim_inl,Sum.elim_inr,hC,hB,hT]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    push_cast
    ring
  rw [hh] at hs
  exact hs

namespace HoleEvents
variable {Q : Type u_5} {A : Type u_6} {R : Type u_7} [Field Q] [AddCommGroup A] [Module Q A]
  [Fintype Q] [Fintype A] [Fintype R]
variable (S : Finset A) (W : R → Submodule Q A) (U : R × Q → Submodule Q A)

structure GoodHoles (e : R → Q → A) (O : Finset A) : Prop where
  source : O ⊆ S
  collision : ∀ r, ∀ x ∈ O, ∀ y ∈ O, y-x ∈ W r → y=x
  occupancy : ∀ j r x, (O.filter (fun o => o-x ∈ U j ⊔ W r)).card ≤ 100
  rectangles : ∀ r r' x u v (f : Fin 4 → A), Function.Injective f →
    (∀ i, f i ∈ O) → (∀ i, f i - corner e r r' x u v i ∈ W (sideLabel r r' i)) → False

omit [Fintype Q] [Fintype A] [Fintype R] in
lemma goodHoles_of_avoiding (e : R → Q → A) (O : Finset S)
    (hp : ∀ i : PairIndex S W, ¬ pairSet S W i ⊆ O)
    (ho : ∀ i : OccupancyIndex S W U 101, ¬ occupancySet S W U i ⊆ O)
    (hr : ∀ i : RectangleIndex S W e, ¬ rectangleSet S W i ⊆ O) :
    GoodHoles S W U e (O.image Subtype.val) := by
  have hmem (x : S) : x.val ∈ O.image Subtype.val ↔ x ∈ O := by
    constructor
    · rintro hx
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
      exact Subtype.val_injective he ▸ hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  · intro r x hx y hy hdiff
    obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
    by_contra hne
    let i : PairIndex S W := ⟨r,x',y',(fun h => hne (congrArg Subtype.val h)),hdiff⟩
    apply hp i
    intro z hz
    change z ∈ ({x', y'} : Finset S) at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx'
    · rcases Finset.mem_singleton.mp hz with rfl
      exact hy'
  · intro j r x
    let C := (O.image Subtype.val).filter (fun o => o-x ∈ U j ⊔ W r)
    by_contra hn
    have hcard : Fintype.card (Fin 101) ≤ Fintype.card C := by
      simp only [Fintype.card_fin,Fintype.card_coe]
      change ¬ C.card ≤ 100 at hn
      exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
    let g : Fin 101 → S := fun i => ⟨(f i).val,by
      obtain ⟨o,_,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (f i).property).1
      exact he ▸ o.property⟩
    have hg : Function.Injective g := by
      intro i j hij
      apply f.injective
      apply Subtype.ext
      exact congrArg (fun z : S => z.val) hij
    let a : OccupancyIndex S W U 101 := ⟨j,r,x,g,hg,fun i =>
      (Finset.mem_filter.mp (f i).property).2⟩
    apply ho a
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    apply (hmem _).mp
    exact (Finset.mem_filter.mp (f i).property).1
  · intro r r' x u v f hf hfo hfw
    let g : Fin 4 → S := fun i => ⟨f i,by
      obtain ⟨o,_,he⟩ := Finset.mem_image.mp (hfo i)
      exact he ▸ o.property⟩
    have hg : Function.Injective g := fun i j h => hf (congrArg Subtype.val h)
    let a : RectangleIndex S W e := ⟨r,r',x,u,v,g,hg,hfw⟩
    apply hr a
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    exact (hmem _).mp (hfo i)

omit [Fintype Q] [Fintype A] [Fintype R] in
lemma GoodHoles.mono {e : R → Q → A} {O P : Finset A}
    (hO : GoodHoles S W U e O) (hP : P ⊆ O) : GoodHoles S W U e P := by
  refine ⟨hP.trans hO.source,?_,?_,?_⟩
  · exact fun r x hx y hy h => hO.collision r x (hP hx) y (hP hy) h
  · intro j r x
    exact (Finset.card_le_card (Finset.filter_subset_filter _ hP)).trans (hO.occupancy j r x)
  · exact fun r r' x u v f hf hfo hfw => hO.rectangles r r' x u v f hf (fun i => hP (hfo i)) hfw

lemma exists_goodHoles (e : R → Q → A) (p : Set.Icc (0 : ℝ) 1) :
    ∃ O : Finset A, GoodHoles S W U e O ∧
      (S.card : ℝ) * p.val -
        (Fintype.card (PairIndex S W) * 2 * p.val^2 +
         Fintype.card (RectangleIndex S W e) * 4 * p.val^4 +
         Fintype.card (OccupancyIndex S W U 101) * 101 * p.val^101) ≤ O.card := by
  obtain ⟨O,hp,hr,ho,hsize⟩ := exists_avoiding_three
    (pairSet S W) (rectangleSet (e := e) S W) (occupancySet (k := 101) S W U)
    (pairSet_card S W) (rectangleSet_card S W) (by decide : 0 < 101)
    (occupancySet_card S W U) p
  refine ⟨O.image Subtype.val,goodHoles_of_avoiding S W U e O hp ho hr,?_⟩
  rw [Finset.card_image_of_injective _ Subtype.val_injective]
  simpa only [Fintype.card_coe, Nat.cast_ofNat] using hsize

end HoleEvents
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
