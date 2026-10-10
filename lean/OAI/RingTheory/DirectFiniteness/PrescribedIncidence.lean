import OAI.RingTheory.DirectFiniteness.SimplexBound

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
open FiniteGeometry PolynomialPairing

structure Successful {Q : Type} [Field Q] [Fintype Q] {q n : ℕ}
    (a : Fin q ≃ Q) (ℓ : ℕ)
    (pair : Finset (Fin n → Q) × Finset (Finset (Fin n → Q))) : Prop where
  holes_subset : pair.1 ⊆ simplexPoints a n ((q-2)/2)
  lower : 2*q^n ≤ pair.1.card*(ℓ+1)^2
  upper : pair.1.card*(ℓ+1)^2 ≤ 7*q^n
  full : ∀ L ∈ pair.2, FullLine (Q := Q) L
  avoid : ∀ L ∈ pair.2, ∀ v ∈ L, v ∉ pair.1
  regular : ∀ v : {v : Fin n → Q // v ∉ pair.1},
    Fintype.card {L : pair.2 // v.val ∈ L.val}=ℓ+1
  girth : 12 ≤ (Planar.incidenceGraph
    (fun (v : {v : Fin n → Q // v ∉ pair.1}) (L : pair.2) => v.val ∈ L.val)).egirth

namespace DirectionFrame
variable {Q A R E : Type} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q]
  (F : FiniteGeometry.DirectionFrame Q A R E) (S O : Finset A)
  (P : SlabVariable F → Plane Q E) (T : F.Preliminary O P)

lemma tradeLine_injective
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O) :
    Function.Injective (F.tradeLine O P T) := by
  intro i j hij
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp
    ((F.tradeLine_full O P T i).card ▸ Fintype.one_lt_card (α := Q))
  have hxj : x ∈ F.tradeLine O P T j := hij ▸ hx
  have hyj : y ∈ F.tradeLine O P T j := hij ▸ hy
  have hl : F.tradeLabel O P T i=F.tradeLabel O P T j := by
    by_contra hne
    have hz := Submodule.disjoint_def.mp (F.label_spaces_disjoint hne) (y-x)
      (F.tradeLine_step_mem O P T i hx hy) (F.tradeLine_step_mem O P T j hxj hyj)
    exact hxy (sub_eq_zero.mp hz).symm
  exact F.same_label_eq S O P T hO hl hx hxj

end DirectionFrame

/-- A faithful set of full lines from the successful geometric trade; the
bijection retains degrees and ordinary incidence girth exactly. -/
lemma successful_of_indexed {Q : Type} [Field Q] [Fintype Q] {q n ℓ : ℕ}
    (a : Fin q ≃ Q) (O : Finset (Fin n → Q))
    (hO : O ⊆ simplexPoints a n ((q-2)/2))
    (hlow : 2*q^n ≤ O.card*(ℓ+1)^2) (hhigh : O.card*(ℓ+1)^2 ≤ 7*q^n)
    {I : Type} [Fintype I] (L : I → Finset (Fin n → Q)) (hinj : Function.Injective L)
    (hfull : ∀ i, FullLine (Q := Q) (L i))
    (havoid : ∀ i v, v ∈ L i → v ∉ O)
    (hdeg : ∀ v : {v : Fin n → Q // v ∉ O}, Fintype.card {i : I // v.val ∈ L i}=ℓ+1)
    (hgirth : 12 ≤ (Planar.incidenceGraph
      (fun (v : {v : Fin n → Q // v ∉ O}) (i : I) => v.val ∈ L i)).egirth) :
    ∃ pair, Successful (n := n) a ℓ pair := by
  let lines := Finset.univ.image L
  let f (i : I) : lines := ⟨L i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact hinj (congrArg Subtype.val h)
    · intro l
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp l.property
      exact ⟨i,Subtype.ext hi⟩
  let e := Equiv.ofBijective f hf
  refine ⟨(O,lines),⟨hO,hlow,hhigh,?_,?_,?_,?_⟩⟩
  · intro l hl
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hl
    exact hfull i
  · intro l hl v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hl
    exact havoid i v hv
  · intro v
    have ec := e.subtypeEquiv (p := fun i => v.val ∈ L i)
      (q := fun l => v.val ∈ l.val) (fun _ => Iff.rfl)
    exact (Fintype.card_congr ec).symm.trans (hdeg v)
  · let g : (Planar.incidenceGraph (fun (v : {v : Fin n → Q // v ∉ O}) (i : I) => v.val ∈ L i)) ≃g
        (Planar.incidenceGraph (fun (v : {v : Fin n → Q // v ∉ O}) (l : lines) => v.val ∈ l.val)) :=
      { toEquiv := Equiv.sumCongr (Equiv.refl _) e
        map_rel_iff' := by intro v w; cases v <;> cases w <;> rfl }
    exact g.egirth_eq ▸ hgirth

/-- Uniformity in every enumeration and realization of F_(2^217), required
by the literal outer search (whose field is the lexicographic quotient). -/
lemma succeeds_217 (Q : Type) [Field Q] [Fintype Q] [CharP Q 2]
    (hq : Fintype.card Q=sourceQ) (a : Fin sourceQ ≃ Q) :
    ∃ pair : Finset (Fin 1200 → Q) × Finset (Finset (Fin 1200 → Q)),
      Successful a sourcePrime pair := by
  let R := Fin (sourceD/sourceQ)
  let E := Fin 119 → Q
  have hRcard : Fintype.card R=sourceD/sourceQ := Fintype.card_fin _
  have hr : Fintype.card R*sourceQ=sourceD := by
    rw [hRcard]
    exact Nat.div_mul_cancel sourceD_q_dvd
  obtain ⟨F⟩ := exists_coordinate_frame Q R (by
    simpa only [R,Fintype.card_fin,hq] using source_frame_size)
  let S := simplexPoints a 1200 ((sourceQ-2)/2)
  have hn : Fintype.card (Fin 1200 → Q)=sourceQ^1200 := by
    simp only [Fintype.card_fun,Fintype.card_fin,hq]
  have hE : Fintype.card E=sourceQ^119 := by
    simp only [E,Fintype.card_fun,Fintype.card_fin,hq]
  have hdensity : Fintype.card (Fin 1200 → Q) ≤ sourceQ^72*S.card := by
    rw [hn]
    have hs := simplex_density_bound (n := 1200) a (by decide) (by have := sourceQ_large; omega)
    rw [show 4*1200=4800 from rfl] at hs
    exact hs.trans (Nat.mul_le_mul_right S.card sourceQ_density)
  obtain ⟨O,hO,hlo,hhi⟩ := F.exists_sized_goodHoles S hq hE
    (sourceQ_large.trans' (by decide)) sourceD_bounds.1 (le_of_eq hr)
    hdensity (by rw [hn]; exact sourceD_square_le)
  have hRbound : Fintype.card R ≤ 2*(Fintype.card Q)^100 := by
    rw [hq,hRcard]
    exact (Nat.div_le_self sourceD sourceQ).trans sourceD_bounds.2
  obtain ⟨P,hP⟩ := F.exists_successfulSlabs_large S O hO (by rw [hq]; exact sourceQ_very_large)
    hRbound (by simp only [Module.finrank_pi,Fintype.card_fin])
  obtain ⟨T⟩ := F.exists_preliminary O P hP
  refine successful_of_indexed a O hO.source ?_ ?_ (F.tradeLine O P T)
    (DirectionFrame.tradeLine_injective F S O P T hO) (F.tradeLine_full O P T)
    (fun i v hv ho => Finset.disjoint_left.mp (F.tradeLine_avoid S O P T hO i) hv ho)
    ?_ (F.trade_incidence_girth S O P T hO hP)
  · simpa only [hn,sourceD] using hlo
  · have hb := hhi.trans (Nat.mul_le_mul_right (Fintype.card (Fin 1200 → Q)) (by decide : 3 ≤ 7))
    simpa only [hn,sourceD] using hb
  · intro v
    have hd := F.trade_degree S O P T hO v.val v.property
    rw [hq,hr] at hd
    simpa only [Fintype.card_eq_nat_card,sourceD] using hd

end KaplanskyCounterexample.Prescription
end

end OAI
