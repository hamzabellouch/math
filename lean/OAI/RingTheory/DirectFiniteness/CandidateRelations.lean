import OAI.RingTheory.DirectFiniteness.CyclicLabels

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

structure GenericStep (Q : Type u_5) (R : Type u_6) (E : Type u_7) [Zero E] where
  label : R × Q
  scalar : Q
  component : E
  nonzero : component ≠ 0

structure ExceptionalStep (Q : Type u_8) (R : Type u_9) [Zero Q] where
  label : R
  scalar : Q
  nonzero : scalar ≠ 0

abbrev PolygonStep (Q : Type u_10) (R : Type u_11) (E : Type u_12) [Zero Q] [Zero E] := GenericStep Q R E ⊕ ExceptionalStep Q R

namespace PolygonStep

def label : PolygonStep Q R E → (R × Q) ⊕ R
  | .inl g => .inl g.label
  | .inr e => .inr e.label

def bundle : PolygonStep Q R E → R
  | .inl g => g.label.1
  | .inr e => e.label

def wcoord : PolygonStep Q R E → Q × Q
  | .inl g => (g.scalar,g.scalar*g.label.2)
  | .inr e => (0,e.scalar)

def ecoord : PolygonStep Q R E → E
  | .inl g => g.component
  | .inr _ => 0

def vector (F : DirectionFrame Q A R E) : PolygonStep Q R E → A
  | .inl g => F.u g.label (g.scalar,g.component)
  | .inr e => F.exc e.label e.scalar

omit [Module Q E] in
lemma ecoord_nonzero {s : PolygonStep Q R E} {j : R × Q} (hs : s.label = .inl j) :
    s.ecoord ≠ 0 := by
  cases s with
  | inl g => exact g.nonzero
  | inr e => cases hs

lemma vector_ne_zero (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) :
    s.vector F ≠ 0 := by
  cases s with
  | inl g =>
    intro h
    have hz : (g.scalar,g.component) = 0 := F.u_injective g.label (h.trans (F.u _).map_zero.symm)
    exact g.nonzero (congrArg Prod.snd hz)
  | inr e =>
    intro h
    exact e.nonzero (F.exc_injective e.label (h.trans (F.exc _).map_zero.symm))

def blockLabel (s : PolygonStep Q R E) (b : Fin 2) : R ⊕ (R × Q) :=
  if b = 0 then .inl s.bundle else
    match s with
    | .inl g => .inr g.label
    | .inr e => .inl e.label

def blockVector (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) (b : Fin 2) : A :=
  if b = 0 then F.w s.bundle s.wcoord else
    match s with
    | .inl g => F.e g.label g.component
    | .inr _ => 0

lemma blockVector_mem (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) (b : Fin 2) :
    s.blockVector F b ∈ Sum.elim (fun r => (F.w r).range) (fun j => (F.e j).range)
      (s.blockLabel b) := by
  fin_cases b
  · cases s with
    | inl g => exact ⟨(g.scalar,g.scalar*g.label.2),rfl⟩
    | inr e => exact ⟨(0,e.scalar),rfl⟩
  · cases s with
    | inl g => exact ⟨g.component,rfl⟩
    | inr e => exact ⟨0,(F.w e.label).map_zero⟩

lemma sum_blocks (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) :
    ∑ b : Fin 2, s.blockVector F b = s.vector F := by
  cases s <;> simp [blockVector,vector,bundle,wcoord,DirectionFrame.u_apply,
    Fin.sum_univ_succ]

lemma filter_blocks_E (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) (j : R × Q) :
    ∑ b : Fin 2, (if s.blockLabel b = .inr j then s.blockVector F b else 0) =
      if s.label = .inl j then F.e j s.ecoord else 0 := by
  rw [Fin.sum_univ_two]
  cases s with
  | inl g =>
    dsimp [blockLabel,blockVector,label,bundle,wcoord,ecoord]
    by_cases h : g.label = j <;> simp_all
  | inr e => simp [blockLabel,label,bundle]

lemma filter_blocks_W (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) (r : R) :
    ∑ b : Fin 2, (if s.blockLabel b = .inl r then s.blockVector F b else 0) =
      if s.bundle = r then F.w r s.wcoord else 0 := by
  rw [Fin.sum_univ_two]
  cases s with
  | inl g =>
    dsimp [blockLabel,blockVector,bundle,wcoord]
    by_cases h : g.label.1 = r <;> simp_all
  | inr e =>
    dsimp [blockLabel,blockVector,bundle,wcoord]
    by_cases h : e.label = r <;> simp_all

end PolygonStep

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

lemma polygon_component_sums {k : ℕ} (s : Fin k → PolygonStep Q R E) (hk : k ≤ 5)
    (hz : ∑ i, (s i).vector F = 0) :
    (∀ j : R × Q, ∑ i ∈ Finset.univ.filter (fun i => (s i).label = .inl j), (s i).ecoord = 0) ∧
    (∀ r : R, ∑ i ∈ Finset.univ.filter (fun i => (s i).bundle = r), (s i).wcoord = 0) := by
  let lab (p : Fin k × Fin 2) := (s p.1).blockLabel p.2
  let v (p : Fin k × Fin 2) := (s p.1).blockVector F p.2
  have hcard : (Finset.univ : Finset (Fin k × Fin 2)).card ≤ 10 := by simp; omega
  have hvz : ∑ p : Fin k × Fin 2, v p = 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [v,PolygonStep.sum_blocks]
    exact hz
  have hsep := F.direct.grouped_sum Finset.univ hcard lab v
    (fun p _ => PolygonStep.blockVector_mem F _ _) hvz
  constructor
  · intro j
    have hh := hsep (.inr j)
    rw [Finset.sum_filter,Fintype.sum_prod_type] at hh
    simp_rw [lab,v,PolygonStep.filter_blocks_E] at hh
    apply F.einj j
    rw [map_zero,map_sum]
    simpa only [Finset.sum_filter] using hh
  · intro r
    have hh := hsep (.inl r)
    rw [Finset.sum_filter,Fintype.sum_prod_type] at hh
    simp_rw [lab,v,PolygonStep.filter_blocks_W] at hh
    apply F.winj r
    rw [map_zero,map_sum]
    simpa only [Finset.sum_filter] using hh

/-- Every occurring generic label occurs precisely twice in a candidate with
at most five steps. No exceptional-vector cancellation has been assumed. -/
lemma generic_occurs_twice {k : ℕ} (s : Fin k → PolygonStep Q R E) (hk : k ≤ 5)
    (hz : ∑ i, (s i).vector F = 0)
    (hadj : ∀ i, (s i).label ≠ (s (finRotate k i)).label)
    (j : R × Q) (hj : ∃ i, (s i).label = .inl j) :
    (Finset.univ.filter (fun i => (s i).label = .inl j)).card = 2 := by
  exact cyclic_label_count_eq_two (fun i => (s i).label) (fun i => (s i).ecoord)
    hk hadj (.inl j) hj (fun _ hi => PolygonStep.ecoord_nonzero hi)
    ((F.polygon_component_sums s hk hz).1 j)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
