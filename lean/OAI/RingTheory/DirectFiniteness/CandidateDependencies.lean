import OAI.RingTheory.DirectFiniteness.OneCandidateCounting

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]

abbrev SlabVariable (F : DirectionFrame Q A R E) := Σ j : R × Q, AffineCoset (F.U j)

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) {k : ℕ} (c : Candidate F T k)

abbrev Occurrence := {p : Fin k × GenericStep Q R E // c.step p.1 = .inl p.2}

omit [Fintype A] in
lemma occurrence_index_injective : Function.Injective (fun p : c.Occurrence F T => p.val.1) := by
  intro p p' h
  apply Subtype.ext
  apply Prod.ext h
  have hs : c.step p.val.1 = c.step p'.val.1 := congrArg c.step h
  exact Sum.inl.inj (p.property.symm.trans (hs.trans p'.property))

instance : Fintype (c.Occurrence F T) :=
  Fintype.ofInjective (fun p => p.val.1) (c.occurrence_index_injective F T)

omit [Fintype A] in
lemma occurrence_card : Fintype.card (c.Occurrence F T) = c.positions.card := by
  let f : c.Occurrence F T → c.positions := fun p => ⟨p.val.1,by
    change p.val.1 ∈ Finset.univ.filter (fun i => (c.step i).label.isLeft)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [p.property]
    rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p p' hp
      exact c.occurrence_index_injective F T (congrArg Subtype.val hp)
    · intro i
      have hi : (c.step i.val).label.isLeft = true := (Finset.mem_filter.mp i.property).2
      cases h : c.step i.val with
      | inl g => exact ⟨⟨(i.val,g),h⟩,rfl⟩
      | inr e => simp only [h,PolygonStep.label,Sum.isLeft_inr,Bool.false_eq_true] at hi
  simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective f hf)

def occurrenceVariable (p : c.Occurrence F T) : SlabVariable F :=
  ⟨p.val.2.label,AffineCoset.of (F.U p.val.2.label) (c.point p.val.1)⟩

def occurrenceVector (p : c.Occurrence F T) : E := p.val.2.component

lemma occurrenceVariable_injective (hk3 : 3 ≤ k) (hk5 : k ≤ 5) :
    Function.Injective (c.occurrenceVariable F T) := by
  intro p p' h
  by_contra hp
  have hi : p.val.1 ≠ p'.val.1 := fun hi => hp (c.occurrence_index_injective F T hi)
  obtain ⟨⟨i,g⟩,hg⟩ := p
  obtain ⟨⟨i',g'⟩,hg'⟩ := p'
  have hl : g.label = g'.label := congrArg Sigma.fst h
  have hc : AffineCoset.of (F.U g.label) (c.point i) =
      AffineCoset.of (F.U g.label) (c.point i') := by
    have hh := congrArg (fun v : SlabVariable F => v.2.val) h
    apply Subtype.ext
    change cosetPoints (F.U g.label) (c.point i) = cosetPoints (F.U g.label) (c.point i')
    change cosetPoints (F.U g.label) (c.point i) = cosetPoints (F.U g'.label) (c.point i') at hh
    rw [hl] at hh ⊢
    exact hh
  exact F.distinct_generic_cosets c.step c.point hk3 hk5 c.shift c.adjacent hi
    (by rw [hg]; rfl) (by rw [hg']; exact congrArg Sum.inl hl.symm) hc

def deps : Finset (SlabVariable F) := Finset.univ.image (c.occurrenceVariable F T)

lemma deps_card (hk3 : 3 ≤ k) (hk5 : k ≤ 5) : (c.deps F T).card = 2*c.labels.card := by
  rw [deps,Finset.card_image_of_injective _ (c.occurrenceVariable_injective F T hk3 hk5),
    Finset.card_univ,c.occurrence_card F T,c.positions_card F T hk5]

lemma deps_nonempty : (c.deps F T).Nonempty := by
  obtain ⟨i,j,hi⟩ := c.generic
  cases hs : c.step i with
  | inl g => exact ⟨_,Finset.mem_image.mpr ⟨⟨(i,g),hs⟩,Finset.mem_univ _,rfl⟩⟩
  | inr e => simp [hs,PolygonStep.label] at hi

lemma deps_card_le_four (hk3 : 3 ≤ k) (hk5 : k ≤ 5) : (c.deps F T).card ≤ 4 := by
  rw [c.deps_card F T hk3 hk5]
  have := (c.labels_card_bounds F T hk5).2
  omega

lemma mem_deps_iff (v : SlabVariable F) : v ∈ c.deps F T ↔
    ∃ p : c.Occurrence F T, c.occurrenceVariable F T p = v := by
  simp [deps]

lemma mem_deps_iff_rooted (j : R × Q) (C : AffineCoset (F.U j)) :
    (⟨j,C⟩ : SlabVariable F) ∈ c.deps F T ↔
      ∃ i : Fin k, (c.step i).label = .inl j ∧ c.point i ∈ C.val := by
  rw [c.mem_deps_iff F T]
  constructor
  · rintro ⟨p,hp⟩
    have hl : p.val.2.label = j := congrArg Sigma.fst hp
    have hC : cosetPoints (F.U p.val.2.label) (c.point p.val.1) = C.val :=
      congrArg (fun v : SlabVariable F => v.2.val) hp
    refine ⟨p.val.1,?_,?_⟩
    · rw [p.property]; exact congrArg Sum.inl hl
    · rw [← hC]; exact self_mem_cosetPoints _ _
  · rintro ⟨i,hi,hC⟩
    cases hs : c.step i with
    | inr e => simp [hs,PolygonStep.label] at hi
    | inl g =>
      rw [hs] at hi
      have hj : g.label=j := Sum.inl.inj hi
      subst j
      refine ⟨⟨(i,g),hs⟩,?_⟩
      change Sigma.mk g.label (AffineCoset.of (F.U g.label) (c.point i)) = (⟨g.label,C⟩ : SlabVariable F)
      rw [AffineCoset.eq_of_mem _ hC]

def constraintVector (v : SlabVariable F) : E :=
  if h : ∃ p : c.Occurrence F T, c.occurrenceVariable F T p = v
    then c.occurrenceVector F T h.choose else 0

lemma constraintVector_at (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (p : c.Occurrence F T) :
    c.constraintVector F T (c.occurrenceVariable F T p) = c.occurrenceVector F T p := by
  have hex : ∃ p' : c.Occurrence F T, c.occurrenceVariable F T p' = c.occurrenceVariable F T p := ⟨p,rfl⟩
  rw [constraintVector,dite_eq_left hex]
  congr 1
  exact c.occurrenceVariable_injective F T hk3 hk5 hex.choose_spec

lemma constraintVector_nonzero (v : SlabVariable F) (hv : v ∈ c.deps F T) :
    c.constraintVector F T v ≠ 0 := by
  have hex := (c.mem_deps_iff F T v).mp hv
  rw [constraintVector,dite_eq_left hex]
  exact hex.choose.val.2.nonzero

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
