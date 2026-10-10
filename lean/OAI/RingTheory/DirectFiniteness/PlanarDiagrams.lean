import OAI.RingTheory.DirectFiniteness.VertexMerging

namespace OAI

universe u u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u} {V : Type u_1} {F : Type u_2} {A : Type u_3} {B : Type u_4} [Fintype α] [AddCommGroup A] [AddCommGroup B]

omit [Fintype α] in
lemma fixed_compl_invariant (p : Perm α) (a : α) (ha : p a = a) (x : α) :
    p x ≠ a ↔ x ≠ a := by
  constructor
  · intro h hxa; subst x; exact h ha
  · intro h hpx; exact h (p.injective (hpx.trans ha.symm))

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →+ B)}

/-- Deleting a zero edge, including its now isolated endpoints, strictly
reduces the finite edge set and preserves all required balances. -/
lemma WeakBalanced.exists_smaller (D : WeakBalanced R Inc ι) (hR : R.GenusZero)
    (a : α) (ha : D.weight a = 0) :
    ∃ (β : Type u) (iβ : Fintype β) (S : Ribbon β),
      @Fintype.card β iβ < Fintype.card α ∧ @Ribbon.GenusZero β iβ S ∧
        Nonempty (@WeakBalanced β V F A B iβ _ _ S Inc ι) := by
  classical
  let D' := D.detach a ha
  obtain ⟨e, he, hwe⟩ := D'.exists_exception_nonzero
  have hea : e ≠ a := by
    intro h
    subst e
    exact hwe ha
  let hb := fixed_compl_invariant (R.detach a).black a (R.detach_fixed_black a)
  let hw := fixed_compl_invariant (R.detach a).white a (R.detach_fixed_white a)
  let S := (R.detach a).restrict (fun x => x ≠ a) hb hw
  have hcard : Fintype.card {x : α // x ≠ a} < Fintype.card α :=
    Fintype.card_subtype_lt (x := a) (by simp)
  refine ⟨{x : α // x ≠ a}, _, S, ?_,
    (R.detach a).planar_restrict (R.genusZero_detach hR a) (fun x : α => x ≠ a) hb hw, ?_⟩
  · convert hcard
  · exact ⟨D'.restrict (fun x => x ≠ a) hb hw e ((mem_cycleSet _ _ _).mp he) hea⟩

/-- A finite genus-zero comparison diagram, with its edge type retained. -/
structure PlanarDiagram (Inc : V → F → Prop) (ι : V → F → (A →+ B)) where
  Edge : Type u
  fintype : Fintype Edge
  ribbon : Ribbon Edge
  balanced : @WeakBalanced Edge V F A B fintype _ _ ribbon Inc ι
  genusZero : @Ribbon.GenusZero Edge fintype ribbon

attribute [instance] PlanarDiagram.fintype

def PlanarDiagram.edges (D : PlanarDiagram.{u} Inc ι) : ℕ := Fintype.card D.Edge

def PlanarDiagram.vertices (D : PlanarDiagram.{u} Inc ι) : ℕ :=
  Nat.card (Cycles D.ribbon.black) + Nat.card (Cycles D.ribbon.white)

lemma PlanarDiagram.exists_minimal (C : PlanarDiagram.{u} Inc ι) :
    ∃ D : PlanarDiagram.{u} Inc ι,
      (∀ E : PlanarDiagram.{u} Inc ι, D.edges ≤ E.edges) ∧
      (∀ E : PlanarDiagram.{u} Inc ι, E.edges = D.edges → D.vertices ≤ E.vertices) := by
  classical
  have hex : ∃ n : ℕ, ∃ D : PlanarDiagram.{u} Inc ι, D.edges = n := ⟨C.edges, C, rfl⟩
  obtain ⟨D, hD⟩ := Nat.find_spec hex
  have hv : ∃ v : ℕ, ∃ E : PlanarDiagram.{u} Inc ι,
      E.edges = Nat.find hex ∧ E.vertices = v := ⟨D.vertices, D, hD, rfl⟩
  obtain ⟨E, hE, hEv⟩ := Nat.find_spec hv
  refine ⟨E, ?_, ?_⟩
  · intro F
    rw [hE]
    exact Nat.find_min' hex ⟨F, rfl⟩
  · intro F hF
    rw [hEv]
    exact Nat.find_min' hv ⟨F, hF.trans hE, rfl⟩

/-- Curvature also rules out a disconnected comparison system: its Euler
characteristic is twice its positive number of components. -/
lemma Balanced.not_genusZero (D : Balanced R Inc ι) (hred : D.Reduced)
    (hinj : ∀ v f, Inc v f → Function.Injective (ι v f))
    (hind : ∀ v f g, Inc v f → Inc v g → f ≠ g →
      ∀ a b, ι v f a + ι v g b = 0 → a = 0)
    (hgirth : 12 ≤ (incidenceGraph Inc).egirth) : ¬ R.GenusZero := by
  classical
  intro hR
  have hb := D.black_degree hred hinj hind
  have hw := D.white_degree
  have hf := D.face_degree hred hb hgirth
  have hb' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.black))) => hb c)
  have hw' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.white))) => hw c)
  have hf' := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Cycles R.face))) => hf c)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, cycles_sum_card] at hb'
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_add_distrib,
    cycles_sum_card, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hw' hf'
  have hc : 0 < Nat.card (Quotient R.components) := by
    have : Nonempty (Quotient R.components) := ⟨Quotient.mk _ D.exceptionEdge⟩
    exact Nat.card_pos
  unfold Ribbon.GenusZero at hR
  simp only [Nat.card_eq_fintype_card] at hR hc
  omega

end KaplanskyCounterexample.Planar
end

end OAI
